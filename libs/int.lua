local has_bit, bit = pcall(require, "bit")
if not has_bit then
	has_bit, bit = pcall(require, "bit32")
	assert(has_bit, "bit32 or bit library required")
end

local band, bor, bxor, lshift, rshift = bit.band, bit.bor, bit.bxor, bit.lshift, bit.rshift
local byte = string.byte

local WORD_SIZE = 8
local WORD_RADIX = 2 ^ WORD_SIZE
local WORD_MASK = 2 ^ WORD_SIZE - 1

local function ctz(w)
	if w == 0 then
		return 32
	end

	local n = 1
	if band(w, 0x0000FFFF) == 0 then
		n = n + 16
		w = rshift(w, 16)
	end

	if band(w, 0x000000FF) == 0 then
		n = n + 8
		w = rshift(w, 8)
	end

	if band(w, 0x0000000F) == 0 then
		n = n + 4
		w = rshift(w, 4)
	end

	if band(w, 0x00000003) == 0 then
		n = n + 2
		w = rshift(w, 2)
	end

	return n - band(w, 1)
end

--- returns `z0, z1` that satisfies `z0 + z1 * W = a + b + carry`
local function addWithOverflow(a, b, carry)
	assert(a >= 0 and a < WORD_RADIX, "out of range")
	assert(b >= 0 and b < WORD_RADIX, "out of range")
	assert(carry >= 0 and carry <= 1, "out of range")

	local sum = a + b + carry
	return band(sum, WORD_MASK), rshift(sum, WORD_SIZE)
end

--- returns `z0, z1` that satisfies `z0 - z1 * W = a - b - borrow`
local function subWithOverflow(a, b, borrow)
	assert(a >= 0 and a < WORD_RADIX, "out of range")
	assert(b >= 0 and b < WORD_RADIX, "out of range")
	assert(borrow >= 0 and borrow <= 1, "out of range")

	local diff = (a - b - borrow)
	local z0 = band(diff, WORD_MASK)
	local z1 = band(rshift(diff, WORD_SIZE), 1)
	return z0, z1
end

--- returns `z0, z1` that satisfies `z0 + z1 * W = a + b * c + carry`
local function addMulWithOverflow(a, b, c, carry)
	assert(a >= 0 and a < WORD_RADIX, "out of range")
	assert(b >= 0 and b < WORD_RADIX, "out of range")
	assert(c >= 0 and c < WORD_RADIX, "out of range")
	assert(carry >= 0 and carry < WORD_RADIX, "out of range")

	local fused = a + b * c + carry
	local z0 = band(fused, WORD_MASK)
	local z1 = rshift(fused, WORD_SIZE)
	return z0, z1
end

--- returns `z0, z1` that satisfies `z0 - z1 * W = a - b * c - borrow`
local function subMulWithOverflow(a, b, c, borrow)
	assert(a >= 0 and a < WORD_RADIX, "out of range")
	assert(b >= 0 and b < WORD_RADIX, "out of range")
	assert(c >= 0 and c < WORD_RADIX, "out of range")
	assert(borrow >= 0 and borrow < WORD_RADIX, "out of range")

	local prod = b * c

	local i0 = band(prod, WORD_MASK)
	local i1 = rshift(prod, WORD_SIZE)
	local j0, j1 = subWithOverflow(a, i0, 0)
	local z0, k1 = subWithOverflow(j0, borrow, 0)
	return z0, i1 + k1 + j1
end

-- returns the largest index `i` such that `r[r_i + i + 1] == 0` and `r[r_i + i] ~= 0`
local function limb_normalize(r, r_i, r_n)
	while r_n > 0 and r[r_i + r_n - 1] == 0 do
		r_n = r_n - 1
	end

	return r_n
end

-- returns a number with the same sign as the difference between `a[a_i:a_n]` and `b[b_i:b_n]`
local function limb_compare(a, a_i, a_n, b, b_i, b_n)
	if a_n ~= b_n then
		return a_n - b_n
	end

	for i = a_n - 1, 0, -1 do
		local a_k = a[a_i + i]
		local b_k = b[b_i + i]

		if a_k ~= b_k then
			return a_k - b_k
		end
	end

	return 0
end

-- returns a number with the same sign as the difference between `a[a_i:a_n]` and `w`
local function limb_compare_scalar(a, a_i, a_n, w)
	if a_n > 1 then
		return a_n
	end

	if a_n == 0 then
		return -w
	end

	local a_k = a[a_i]
	return a_k - w
end

-- `r[r_i+b_n:] = a[a_i+a_b:a_n] + carry`
local function limb_add_propagate(r, r_i, a, a_i, a_n, b_n, carry)
	for i = b_n, a_n - 1 do
		r[r_i + i], carry = addWithOverflow(a[a_i + i], carry, 0)
	end

	r[r_i + a_n] = carry
end

-- `r[r_i:] = a[a_i:a_n] + b[b_i:b_n]`
local function limb_add_full(r, r_i, a, a_i, a_n, b, b_i, b_n)
	if b_n > a_n then
		a, a_i, a_n, b, b_i, b_n = b, b_i, b_n, a, a_i, a_n
	end

	if b_n == 0 then
		for i = 0, a_n - 1 do
			r[r_i + i] = a[a_i + i]
		end

		r[r_i + a_n] = 0
		return
	end

	local carry = 0

	for i = 0, b_n - 1 do
		r[r_i + i], carry = addWithOverflow(a[a_i + i], b[b_i + i], carry)
	end

	limb_add_propagate(r, r_i, a, a_i, a_n, b_n, carry)
end

-- `r[r_i+b_n:] = a[a_i+a_b:a_n] - borrow`
-- asserts that the subtraction would not underflow
local function limb_sub_propagate(r, r_i, a, a_i, a_n, b_n, borrow)
	for i = b_n, a_n - 1 do
		r[r_i + i], borrow = subWithOverflow(a[a_i + i], borrow, 0)
	end

	assert(borrow == 0, "subtraction underflow")
end

-- `r[r_i:] = a[a_i:a_n] + b[b_i:b_n]`
-- asserts that `a[a_i:a_n] >= b[b_i:b_n]`
local function limb_sub_full(r, r_i, a, a_i, a_n, b, b_i, b_n)
	local borrow = 0

	for i = 0, b_n - 1 do
		r[r_i + i], borrow = subWithOverflow(a[a_i + i], b[b_i + i], borrow)
	end

	limb_sub_propagate(r, r_i, a, a_i, a_n, b_n, borrow)
end

-- `r[r_i:] = a[a_i:a_n] * w`
local function limb_mul_scalar(r, r_i, a, a_i, a_n, w)
	local carry = 0

	for i = 0, a_n - 1 do
		r[r_i + i], carry = addMulWithOverflow(0, a[a_i + i], w, carry)
	end

	if carry == 0 then
		return a_n
	end

	r[r_i + a_n] = carry
	return a_n + 1
end

-- `r[r_i:] += a[a_i:a_n] * w`
local function limb_mul_add_scalar(r, r_i, a, a_i, a_n, w)
	local carry = 0

	for i = 0, a_n - 1 do
		r[r_i + i], carry = addMulWithOverflow(r[r_i + i], a[a_i + i], w, carry)
	end

	local i = a_n
	while carry > 0 do
		r[r_i + i], carry = addWithOverflow(r[r_i + i], carry, 0)
		i = i + 1
	end
end

-- `r[r_i:] -= a[a_i:a_n] * w`
-- asserts that `r[r_i:] >= a[a_i:a_n] * w`
local function limb_mul_sub_scalar(r, r_i, a, a_i, a_n, w)
	local borrow = 0

	for i = 0, a_n - 1 do
		r[r_i + i], borrow = subMulWithOverflow(r[r_i + i], a[a_i + i], w, borrow)
	end

	local i = a_n
	while borrow > 0 and r[r_i + i] ~= nil do
		r[r_i + i], borrow = subWithOverflow(r[r_i + i], borrow, 0)
		i = i + 1
	end

	assert(borrow == 0, "subtraction underflow")
end

local function limb_mul_add_long(r, r_i, a, a_i, a_n, b, b_i, b_n)
	assert(not rawequal(r, a), "in-place multiplication not supported")
	assert(not rawequal(r, b), "in-place multiplication not supported")

	for i = 0, b_n - 1 do
		limb_mul_add_scalar(r, r_i + i, a, a_i, a_n, b[b_i + i])
	end
end

local function limb_mul_sub_long(r, r_i, a, a_i, a_n, b, b_i, b_n)
	assert(not rawequal(r, a), "in-place multiplication not supported")
	assert(not rawequal(r, b), "in-place multiplication not supported")

	for i = 0, b_n - 1 do
		limb_mul_sub_scalar(r, r_i + i, a, a_i, a_n, b[b_i + i])
	end
end

local limb_mul_add_karatsuba
-- `r[r_i:] += a[a_i:a_n] * b[b_i:b_n]`
local function limb_mul_add(r, r_i, r_n, a, a_i, a_n, b, b_i, b_n)
	if b_n > a_n then
		a, a_i, a_n, b, b_i, b_n = b, b_i, b_n, a, a_i, a_n
	end

	if b_n > 64 then
		return limb_mul_add_karatsuba(r, r_i, r_n, a, a_i, a_n, b, b_i, b_n)
	end

	return limb_mul_add_long(r, r_i, a, a_i, a_n, b, b_i, b_n)
end

local limb_mul_sub_karatsuba
-- `r[r_i:] -= a[a_i:a_n] * b[b_i:b_n]`
local function limb_mul_sub(r, r_i, r_n, a, a_i, a_n, b, b_i, b_n)
	if b_n > a_n then
		a, a_i, a_n, b, b_i, b_n = b, b_i, b_n, a, a_i, a_n
	end

	if b_n > 64 then
		return limb_mul_sub_karatsuba(r, r_i, r_n, a, a_i, a_n, b, b_i, b_n)
	end

	return limb_mul_sub_long(r, r_i, a, a_i, a_n, b, b_i, b_n)
end

function limb_mul_add_karatsuba(r, r_i, r_n, a, a_i, a_n, b, b_i, b_n)
	-- a = a1 * B + a0, a0 < B
	-- b = b1 * B + b0, b0 < B

	-- r = a * b = (a1 * B + a0) * (b1 * B + b0)
	-- r = a1 * b1 * B^2 + (a1 * b0 + a0 * b1) * B + a0 * b0
	-- r = a1 * b1 * B^2 + ((a1 + a0) * (b1 + b0) - a1 * b1 - a0 * b0) * B + a0 * b0
	-- r = a1 * b1 * (B^2 + B) + (a1 - a0) * (b0 - b1) * B + a0 * b0 * (B + 1)

	-- r = p2 * B^2 + (p1 + p1 + p2) * B + p0
	-- r = p2 * B^2 + (p0 * B + p1 * B + p2 * B) + p0
	-- r = (p2 * B^2 + p2 * B) + (p0 * B + p0) + p1 * B

	local split = math.floor(b_n / 2) -- B
	local limbs_after_split = r_n - split -- limbs to add for p1 and p2
	local limbs_after_split2 = r_n - split * 2 -- limbs to add for p2 * B^2

	local a0, a0_i, a0_n = a, a_i, limb_normalize(a, a_i, split)
	local a1, a1_i, a1_n = a, a_i + split, limb_normalize(a, a_i + split, math.min(a_n - split, limbs_after_split))

	local b0, b0_i, b0_n = b, b_i, limb_normalize(b, b_i, split)
	local b1, b1_i, b1_n = b, b_i + split, limb_normalize(b, b_i + split, math.min(b_n - split, limbs_after_split))

	-- compute p2
	local p2_limbs = math.min(limbs_after_split, a1_n + b1_n)
	local p2 = {}
	for i = 1, p2_limbs do
		p2[i] = 0
	end

	limb_mul_add(p2, 1, p2_limbs, a1, a1_i, math.min(a1_n, p2_limbs), b1, b1_i, math.min(b1_n, p2_limbs))
	local p2_n = limb_normalize(p2, 1, p2_limbs)

	-- add p2 * B
	limb_add_full(r, r_i + split, r, r_i + split, limbs_after_split, p2, 1, p2_n)

	-- add p2 * B^2
	limb_add_full(r, r_i + split * 2, r, r_i + split * 2, limbs_after_split2, p2, 1, math.min(p2_n, limbs_after_split2))

	-- increase r_n by 1 to account for the carry from p2
	r_n = r_n + 1
	limbs_after_split = r_n - split

	-- compute p0
	local p0_limbs = a0_n + b0_n
	local p0 = p2 -- reuse temporary table
	for i = 1, p0_limbs do
		p0[i] = 0
	end

	limb_mul_add(p0, 1, p0_limbs, a0, a0_i, a0_n, b0, b0_i, b0_n)
	local p0_n = limb_normalize(p0, 1, p0_limbs)

	-- add p0
	limb_add_full(r, r_i, r, r_i, r_n, p0, 1, p0_n)

	-- add p0 * B
	limb_add_full(r, r_i + split, r, r_i + split, limbs_after_split, p0, 1, math.min(p0_n, limbs_after_split))
	r_n = limb_normalize(r, r_i, r_n + 1)
	limbs_after_split = r_n - split

	-- compute p1
	local a0x, a0x_i, a0x_n = a, a_i, math.min(a0_n, limbs_after_split)
	local b0x, b0x_i, b0x_n = b, b_i, math.min(b0_n, limbs_after_split)

	local j0_sign = limb_compare(a0x, a0x_i, a0x_n, a1, a1_i, a1_n)
	local j1_sign = limb_compare(b1, b1_i, b1_n, b0x, b0x_i, b0x_n)
	if j0_sign == 0 or j1_sign == 0 then
		-- j1 * j2 = p1 is zero
		return
	end

	-- j0 = a0 - a1
	-- j1 = b1 - b0
	local j0 = {}
	local j1 = {}
	for i = 1, a_n - split do
		j0[i] = 0
	end
	for i = 1, b_n - split do
		j1[i] = 0
	end

	if j0_sign > 0 then
		-- a0 > a1
		limb_sub_full(j0, 1, a0x, a0x_i, a0x_n, a1, a1_i, a1_n)
	else
		-- a0 < a1
		limb_sub_full(j0, 1, a1, a1_i, a1_n, a0x, a0x_i, a0x_n)
	end
	local j0_n = limb_normalize(j0, 1, a_n - split)

	if j1_sign > 0 then
		-- b1 > b0
		limb_sub_full(j1, 1, b1, b1_i, b1_n, b0x, b0x_i, b0x_n)
	else
		-- b1 < b0
		limb_sub_full(j1, 1, b0x, b0x_i, b0x_n, b1, b1_i, b1_n)
	end
	local j1_n = limb_normalize(j1, 1, b_n - split)

	if j0_sign * j1_sign > 0 then
		-- p1 = j0 * j1
		-- p1 = (-j0) * (-j1) = j0 * j1
		limb_mul_add(r, r_i + split, limbs_after_split, j0, 1, j0_n, j1, 1, j1_n)
	else
		-- p1 = (-j0) * j1 = -(j0 * j1)
		-- p1 = j0 * (-j1) = -(j0 * j1)
		limb_mul_sub(r, r_i + split, limbs_after_split, j0, 1, j0_n, j1, 1, j1_n)
	end
end

function limb_mul_sub_karatsuba(r, r_i, r_n, a, a_i, a_n, b, b_i, b_n)
	-- same as above, but inverted

	local split = math.floor(b_n / 2) -- B
	local limbs_after_split = r_n - split -- limbs to add for p1 and p2
	local limbs_after_split2 = r_n - split * 2 -- limbs to add for p2 * B^2

	local a0, a0_i, a0_n = a, a_i, limb_normalize(a, a_i, split)
	local a1, a1_i, a1_n = a, a_i + split, limb_normalize(a, a_i + split, math.min(a_n - split, limbs_after_split))

	local b0, b0_i, b0_n = b, b_i, limb_normalize(b, b_i, split)
	local b1, b1_i, b1_n = b, b_i + split, limb_normalize(b, b_i + split, math.min(b_n - split, limbs_after_split))

	-- compute p2
	local p2_limbs = math.min(limbs_after_split, a1_n + b1_n)
	local p2 = {}
	for i = 1, p2_limbs do
		p2[i] = 0
	end

	limb_mul_add(p2, 1, p2_limbs, a1, a1_i, math.min(a1_n, p2_limbs), b1, b1_i, math.min(b1_n, p2_limbs))
	local p2_n = limb_normalize(p2, 1, p2_limbs)

	-- add p2 * B
	limb_sub_full(r, r_i + split, r, r_i + split, limbs_after_split, p2, 1, p2_n)

	-- add p2 * B^2
	limb_sub_full(r, r_i + split * 2, r, r_i + split * 2, limbs_after_split2, p2, 1, math.min(p2_n, limbs_after_split2))

	-- compute p0
	local p0_limbs = a0_n + b0_n
	local p0 = p2 -- reuse temporary table
	for i = 1, p0_limbs do
		p0[i] = 0
	end

	limb_mul_add(p0, 1, p0_limbs, a0, a0_i, a0_n, b0, b0_i, b0_n)
	local p0_n = limb_normalize(p0, 1, p0_limbs)

	-- add p0
	limb_sub_full(r, r_i, r, r_i, r_n, p0, 1, p0_n)

	-- add p0 * B
	limb_sub_full(r, r_i + split, r, r_i + split, limbs_after_split, p0, 1, math.min(p0_n, limbs_after_split))

	-- compute p1
	local a0x, a0x_i, a0x_n = a, a_i, math.min(a0_n, limbs_after_split)
	local b0x, b0x_i, b0x_n = b, b_i, math.min(b0_n, limbs_after_split)

	local j0_sign = limb_compare(a0x, a0x_i, a0x_n, a1, a1_i, a1_n)
	local j1_sign = limb_compare(b1, b1_i, b1_n, b0x, b0x_i, b0x_n)
	if j0_sign == 0 or j1_sign == 0 then
		-- j1 * j2 = p1 is zero
		return
	end

	-- j0 = a0 - a1
	-- j1 = b1 - b0
	local j0 = {}
	local j1 = {}
	for i = 1, a_n - split do
		j0[i] = 0
	end
	for i = 1, b_n - split do
		j1[i] = 0
	end

	if j0_sign > 0 then
		-- a0 > a1
		limb_sub_full(j0, 1, a0x, a0x_i, a0x_n, a1, a1_i, a1_n)
	else
		-- a0 < a1
		limb_sub_full(j0, 1, a1, a1_i, a1_n, a0x, a0x_i, a0x_n)
	end
	local j0_n = limb_normalize(j0, 1, a_n - split)

	if j1_sign > 0 then
		-- b1 > b0
		limb_sub_full(j1, 1, b1, b1_i, b1_n, b0x, b0x_i, b0x_n)
	else
		-- b1 < b0
		limb_sub_full(j1, 1, b0x, b0x_i, b0x_n, b1, b1_i, b1_n)
	end
	local j1_n = limb_normalize(j1, 1, b_n - split)

	if j0_sign * j1_sign > 0 then
		-- p1 = j0 * j1
		-- p1 = (-j0) * (-j1) = j0 * j1
		limb_mul_sub(r, r_i + split, limbs_after_split, j0, 1, j0_n, j1, 1, j1_n)
	else
		-- p1 = (-j0) * j1 = -(j0 * j1)
		-- p1 = j0 * (-j1) = -(j0 * j1)
		limb_mul_add(r, r_i + split, limbs_after_split, j0, 1, j0_n, j1, 1, j1_n)
	end
end

-- `r[r_i:] = a[a_i:a_n] << shift`
local function limb_lshift(r, a, a_n, shift)
	local interior_shift = shift % WORD_SIZE
	local limb_shift = math.floor(shift / WORD_SIZE)

	if interior_shift == 0 then
		-- optimization for whole limb shifts
		for i = a_n, 1, -1 do
			r[i + limb_shift] = a[i]
		end

		for i = 1, limb_shift do
			r[i] = 0
		end

		return a_n + limb_shift
	end

	local carry = 0
	for src_i = a_n, 1, -1 do
		local src_digit = a[src_i]

		r[src_i + limb_shift + 1] = bor(rshift(src_digit, WORD_SIZE - interior_shift), carry)
		carry = band(lshift(src_digit, interior_shift), WORD_MASK)
	end

	r[limb_shift + 1] = carry

	for i = 1, limb_shift do
		r[i] = 0
	end

	return limb_shift + a_n + 1
end

-- `r[r_i:] = a[a_i:a_n] >> shift`
local function limb_rshift(r, a, a_n, shift)
	local interior_shift = shift % WORD_SIZE
	local limb_shift = math.floor(shift / WORD_SIZE)

	if interior_shift == 0 then
		-- optimization for whole limb shifts
		for i = 1, a_n - limb_shift do
			r[i] = a[i + limb_shift]
		end

		return a_n - limb_shift
	end

	a[a_n + 1] = 0 -- ensure we don't read out of bounds
	for dst_i = 1, a_n - limb_shift do
		local src_i = dst_i + limb_shift

		local src_digit = a[src_i] or 0
		local src_digit_next = a[src_i + 1] or 0
		local carry = band(lshift(src_digit_next, WORD_SIZE - interior_shift), WORD_MASK)
		r[dst_i] = bor(rshift(src_digit, interior_shift), carry)
	end

	return a_n - limb_shift
end

---@class bignum.integer
---@field limbs integer[]
---@field n integer number of limbs
---@field positive boolean
local Integer = {}
Integer.__index = Integer

--- Returns a new integer with an initial value of zero.
---@return bignum.integer
function Integer.new_zero()
	return setmetatable({ limbs = {}, n = 0, positive = true }, Integer)
end

--- Copies the magnitude of integer `a` into integer `r` and returns `r`.
--- Does not modify the sign of `r`.
---@param r bignum.integer
---@param a bignum.integer
---@return bignum.integer
function Integer.ucopy(r, a)
	if rawequal(r, a) then
		return r
	end

	r.n = a.n
	for i = 1, a.n do
		r.limbs[i] = a.limbs[i]
	end

	return r
end

--- Copies the value of integer `a` into integer `r` and returns `r`.
---@param r bignum.integer
---@param a bignum.integer
---@return bignum.integer
function Integer.copy(r, a)
	r.positive = a.positive
	return Integer.ucopy(r, a)
end

--- Returns a new integer with the same value as `a`.
---@param a bignum.integer
---@return bignum.integer
function Integer.dup(a)
	return Integer.copy(Integer.new_zero(), a)
end

--- Sets the value of integer `r` to the value of scalar `w` and returns `r`.
---@param r bignum.integer
---@param w integer
---@return bignum.integer
function Integer.set_scalar(r, w)
	r.positive = w >= 0
	r.n = 0

	w = math.floor(math.abs(w))
	if w == 0 then
		return r
	end

	while w > WORD_MASK do
		r.n = r.n + 1
		r.limbs[r.n] = band(w, WORD_MASK)
		w = math.floor(w / WORD_RADIX)
	end

	if w ~= 0 then
		r.n = r.n + 1
		r.limbs[r.n] = math.floor(w)
	end

	return r
end

local tbl_char2digit = {}
for c = 0, 255 do
	if c >= 48 and c <= 57 then
		tbl_char2digit[c + 1] = c - 48
	elseif c >= 65 and c <= 90 then
		tbl_char2digit[c + 1] = c - 55
	elseif c >= 97 and c <= 122 then
		tbl_char2digit[c + 1] = c - 87
	else
		tbl_char2digit[c + 1] = false
	end
end

---@param r bignum.integer
---@param str string
---@param base? integer
---@return bignum.integer
function Integer.set_string(r, str, base)
	local positive = true
	r.n = 0

	local i = 1
	if str:sub(i, i) == "-" then
		positive = false
		i = i + 1
	elseif str:sub(i, i) == "+" then
		i = i + 1
	end

	base = base or 10
	local prefix = str:sub(i, i + 1)
	if (prefix == "0x" or prefix == "0X") and (base == 16 or base == 10) then
		i = i + 2
		base = 16
	elseif (prefix == "0o" or prefix == "0O") and (base == 8 or base == 10) then
		i = i + 2
		base = 8
	elseif (prefix == "0b" or prefix == "0B") and (base == 2 or base == 10) then
		i = i + 2
		base = 2
	end

	local len = #str
	if i > len then
		return r
	end

	local has_exponent = false
	while i <= len do
		local digit = tbl_char2digit[byte(str, i) + 1]
		if not digit then
			error("invalid character '" .. str:sub(i, i) .. "'")
		end

		if digit >= base then
			if base == 10 and digit == 14 or base == 16 and digit == 25 then
				-- exponent E in base 10 or P in base 16

				i = i + 1
				has_exponent = true
				break
			end

			error("invalid character '" .. str:sub(i, i) .. "'")
		end

		-- r = r * base + digit
		Integer.umul_scalar(r, r, base)
		Integer.uadd_scalar(r, r, digit)

		i = i + 1
	end

	r.positive = positive
	if has_exponent then
		local exponent = Integer.new_zero()

		local e_positive = true
		if str:sub(i, i) == "-" then
			e_positive = false
			i = i + 1
		elseif str:sub(i, i) == "+" then
			i = i + 1
		end

		while i <= len do
			local digit = tbl_char2digit[byte(str, i) + 1]
			if not digit or digit >= 10 then
				error("invalid character '" .. str:sub(i, i) .. "'")
			end

			-- e = e * base + digit
			Integer.umul_scalar(exponent, exponent, 10)
			Integer.uadd_scalar(exponent, exponent, digit)

			i = i + 1
		end

		exponent.positive = e_positive
		local tmp = Integer.new_zero()
		local r_copy = Integer.dup(r)
		local base_i = Integer.from_scalar(base == 16 and 2 or 10)

		-- r = r * base^exponent
		Integer.upow(tmp, base_i, exponent)
		Integer.mul(r, r_copy, tmp)
	end

	return r
end

---@param w integer
---@return bignum.integer
function Integer.from_scalar(w)
	local self = Integer.new_zero()
	return Integer.set_scalar(self, w)
end

---@param str string
---@param base? integer
---@return bignum.integer
function Integer.from_string(str, base)
	return Integer.set_string(Integer.new_zero(), str, base)
end

---@param a bignum.integer
---@return integer
function Integer.to_scalar(a)
	local w = 0
	for i = a.n, 1, -1 do
		w = w * WORD_RADIX + a.limbs[i]
	end

	return a.positive and w or -w
end

---@param a bignum.integer
---@param base? integer
---@return string
function Integer.to_string(a, base)
	base = base or 10
end

---@param a bignum.integer
---@return boolean
function Integer.is_even(a)
	return a.n == 0 or band(a.limbs[1], 1) == 0
end

---@param a bignum.integer
---@return boolean
function Integer.is_odd(a)
	return a.n > 0 and band(a.limbs[1], 1) == 1
end

---@param a bignum.integer
---@return boolean
function Integer.is_zero(a)
	for i = a.n, 1, -1 do
		if a.limbs[i] ~= 0 then
			return false
		end
	end

	return true
end

---@param a bignum.integer
---@return boolean
function Integer.is_one(a)
	return a.n == 1 and a.limbs[1] == 1
end

---@param a bignum.integer
---@return boolean
function Integer.is_positive(a)
	return a.positive and a.n > 0
end

---@param a bignum.integer
---@return boolean
function Integer.is_negative(a)
	return not a.positive and a.n > 0
end

---@param a bignum.integer
---@return boolean
function Integer.is_power_of_two(a)
	if a.n == 0 then
		return false
	end

	for i = a.n, 1, -1 do
		local w = a.limbs[i]
		if w ~= 0 then
			if band(w, w - 1) ~= 0 then
				return false
			end

			for j = 1, i - 1 do
				if a.limbs[j] ~= 0 then
					return false
				end
			end

			break
		end
	end

	return true
end

---@param a bignum.integer
---@return integer
function Integer.count_set_bits(a)
	local n = 0
	for i = 1, a.n do
		local w = a.limbs[i]

		while w > 0 do
			w = band(w, w - 1)
			n = n + 1
		end
	end

	return n
end

---@param a bignum.integer
---@return integer
function Integer.count_trailing_zeros(a)
	for i = 1, a.n do
		local w = a.limbs[i]
		if w ~= 0 then
			return ctz(w) + (i - 1) * WORD_SIZE
		end
	end

	return -1
end

---@param a bignum.integer
---@return bignum.integer
function Integer.negate(a)
	a.positive = not a.positive
	return a
end

---@param a bignum.integer
function Integer.normalize(a)
	a.n = limb_normalize(a.limbs, 1, a.n)
	if a.n == 0 then
		a.positive = true
	end
end

function Integer.ucmp(a, b)
	return limb_compare(a.limbs, 1, a.n, b.limbs, 1, b.n)
end

function Integer.cmp(a, b)
	if a.positive == b.positive then
		-- (a) < (b) = a < b
		-- (-a) < (-b) = -(a < b)
		return a.positive and Integer.ucmp(a, b) or Integer.ucmp(b, a)
	else
		if a.positive then
			return 1
		else
			return -1
		end
	end
end

function Integer.ucmp_scalar(a, w)
	w = math.floor(math.abs(w))

	if w < WORD_RADIX then
		return limb_compare_scalar(a.limbs, 1, a.n, w)
	end

	local b = Integer.from_scalar(w)
	return Integer.ucmp(a, b)
end

function Integer.cmp_scalar(a, w)
	w = math.floor(w)
	if a.positive == (w >= 0) then
		-- (a) < (b) = a < b
		-- (-a) < (-b) = -(a < b)
		return a.positive and Integer.ucmp_scalar(a, w) or -Integer.ucmp_scalar(a, w)
	else
		if a.positive then
			return 1
		else
			return -1
		end
	end
end

function Integer.uadd(r, a, b)
	if a.n < b.n then
		a, b = b, a
	end

	limb_add_full(r.limbs, 1, a.limbs, 1, a.n, b.limbs, 1, b.n)
	r.n = limb_normalize(r.limbs, 1, a.n + 1)
	return r
end

function Integer.uadd_scalar(r, a, w)
	w = math.floor(math.abs(w))

	if w == 0 then
		return Integer.ucopy(r, a)
	elseif w < WORD_RADIX then
		limb_add_propagate(r.limbs, 1, a.limbs, 1, a.n, 0, w)
		r.n = limb_normalize(r.limbs, 1, a.n + 1)
		return r
	end

	local b = Integer.from_scalar(w)
	return Integer.uadd(r, a, b)
end

function Integer.usub(r, a, b)
	limb_sub_full(r.limbs, 1, a.limbs, 1, a.n, b.limbs, 1, b.n)
	r.n = limb_normalize(r.limbs, 1, a.n)
	return r
end

function Integer.usub_scalar(r, a, w)
	w = math.floor(math.abs(w))

	if w == 0 then
		return Integer.ucopy(r, a)
	elseif w < WORD_RADIX then
		limb_sub_propagate(r.limbs, 1, a.limbs, 1, a.n, 0, w)
		r.n = limb_normalize(r.limbs, 1, a.n)
		return r
	end

	local b = Integer.from_scalar(w)
	return Integer.usub(r, a, b)
end

function Integer.add(r, a, b)
	if a.positive == b.positive then
		-- (a) + (b) = a + b
		-- (-a) + (-b) = -(a + b)
		r.positive = a.positive
		return Integer.uadd(r, a, b)
	else
		local cmp = Integer.ucmp(a, b)
		if cmp > 0 then
			-- (a) + (-b) = a - b
			-- (-a) + (b) = -(a - b)
			r.positive = a.positive
			return Integer.usub(r, a, b)
		elseif cmp < 0 then
			-- (a) + (-b) = -(b - a)
			-- (-a) + (b) = b - a
			r.positive = b.positive
			return Integer.usub(r, b, a)
		else
			r.positive = true
			r.n = 0

			return r
		end
	end
end

function Integer.add_scalar(r, a, w)
	local w_pos = w >= 0
	w = math.floor(math.abs(w))
	if a.positive == w_pos then
		-- (a) + (b) = a + b
		-- (-a) + (-b) = -(a + b)
		r.positive = a.positive
		return Integer.uadd_scalar(r, a, w)
	else
		local cmp = Integer.ucmp_scalar(a, w)
		if cmp > 0 then
			-- (a) + (-b) = a - b
			-- (-a) + (b) = -(a - b)
			r.positive = a.positive
			return Integer.usub_scalar(r, a, w)
		elseif cmp < 0 then
			-- (a) + (-b) = -(b - a)
			-- (-a) + (b) = b - a
			if w < WORD_RADIX then
				if a.n == 0 then
					r.limbs[1] = w
					r.n = 1
				else
					assert(a.n == 1)
					r.limbs[1] = w - a.limbs[1]
					r.n = 1
				end

				r.positive = w_pos
				return r
			else
				Integer.set_scalar(r, w)
				r.positive = w_pos
				return Integer.usub(r, r, a)
			end
		else
			r.positive = true
			r.n = 0
			return r
		end
	end
end

function Integer.sub(r, a, b)
	if a.positive == b.positive then
		local cmp = Integer.ucmp(a, b)
		if cmp > 0 then
			-- (a) - (b) = a - b
			-- (-a) - (-b) = -(a - b)
			r.positive = a.positive
			return Integer.usub(r, a, b)
		elseif cmp < 0 then
			-- (a) - (b) = -(b - a)
			-- (-a) - (-b) = b - a
			r.positive = not a.positive
			return Integer.usub(r, b, a)
		else
			r.positive = true
			r.n = 0
			return r
		end
	else
		-- (a) - (-b) = a + b
		-- (-a) - (b) = -(a + b)
		r.positive = a.positive
		return Integer.uadd(r, a, b)
	end
end

function Integer.sub_scalar(r, a, w)
	local w_pos = w >= 0
	w = math.floor(math.abs(w))
	if a.positive == w_pos then
		local cmp = Integer.ucmp_scalar(a, w)
		if cmp > 0 then
			-- (a) - (b) = a - b
			-- (-a) - (-b) = -(a - b)
			r.positive = a.positive
			return Integer.usub_scalar(r, a, w)
		elseif cmp < 0 then
			-- (a) - (b) = -(b - a)
			-- (-a) - (-b) = b - a
			if w < WORD_RADIX then
				if a.n == 0 then
					r.limbs[1] = w
					r.n = 1
				else
					assert(a.n == 1)
					r.limbs[1] = w - a.limbs[1]
					r.n = 1
				end

				r.positive = not a.positive
				return r
			else
				Integer.set_scalar(r, w)
				r.positive = not a.positive
				return Integer.usub(r, r, a)
			end
		else
			r.positive = true
			r.n = 0
			return r
		end
	else
		-- (a) - (-b) = a + b
		-- (-a) - (b) = -(a + b)
		r.positive = a.positive
		return Integer.uadd_scalar(r, a, w)
	end
end

function Integer.umul(r, a, b)
	if b.n == 1 then
		return Integer.umul_scalar(r, a, b.limbs[1])
	end

	if a.n == 0 or b.n == 0 then
		r.positive = true
		r.n = 0
		return r
	end

	if Integer.is_power_of_two(a) then
		return Integer.ulshift(r, b, Integer.count_trailing_zeros(a))
	elseif Integer.is_power_of_two(b) then
		return Integer.ulshift(r, a, Integer.count_trailing_zeros(b))
	end

	r.n = a.n + b.n + 1
	for i = 1, r.n do
		r.limbs[i] = 0
	end

	limb_mul_add(r.limbs, 1, r.n, a.limbs, 1, a.n, b.limbs, 1, b.n)
	r.n = limb_normalize(r.limbs, 1, r.n)
	return r
end

function Integer.umul_scalar(r, a, w)
	w = math.floor(math.abs(w))

	if a.n == 0 or w == 0 then
		r.positive = true
		r.n = 0
		return r
	elseif w == 1 then
		return Integer.ucopy(r, a)
	end

	if w < 2 ^ 32 and band(w, w - 1) == 0 then
		local sh_amt = ctz(w)

		r.n = limb_lshift(r.limbs, a.limbs, a.n, sh_amt)
		return r
	end

	if w < WORD_RADIX then
		local n = limb_mul_scalar(r.limbs, 1, a.limbs, 1, a.n, w)
		r.n = limb_normalize(r.limbs, 1, n)
		return r
	end

	local b = Integer.from_scalar(w)
	return Integer.umul(r, a, b)
end

function Integer.mul(r, a, b)
	r.positive = a.positive == b.positive
	return Integer.umul(r, a, b)
end

function Integer.mul_scalar(r, a, w)
	r.positive = a.positive == (w >= 0)
	return Integer.umul_scalar(r, a, w)
end

function Integer.upow(r, a, b)
	if b.n == 0 then
		r.positive = true
		r.n = 1
		r.limbs[1] = 1
		return r
	elseif b.n == 1 then
		return Integer.upow_scalar(r, a, b.limbs[1])
    elseif a.n == 0 then
		r.positive = true
		r.n = 0
		return r
	end

	r.n = 1
	r.limbs[1] = 1

	local r0, r1 = r, Integer.new_zero()
	local a0, a1 = Integer.dup(a), Integer.new_zero()
	for i = 1, b.n - 1 do
		local w = b.limbs[i]
		for j = 1, WORD_SIZE do
			if band(w, 1) ~= 0 then
				Integer.umul(r1, r0, a0)
				r1, r0 = r0, r1
			end

			Integer.umul(a1, a0, a0)
			a1, a0 = a0, a1

			w = rshift(w, 1)
		end
	end

	local w = b.limbs[b.n]
	while w > 0 do
		if band(w, 1) ~= 0 then
			Integer.umul(r1, r0, a0)
			r1, r0 = r0, r1
		end

		Integer.umul(a1, a0, a0)
		a1, a0 = a0, a1

		w = rshift(w, 1)
	end

	if r0 ~= r then
		Integer.ucopy(r, r0)
	end

	return r
end

function Integer.upow_scalar(r, a, w)
	w = math.floor(math.abs(w))

	if w == 0 then
		r.positive = true
		r.n = 1
		r.limbs[1] = 1
		return r
    elseif a.n == 0 then
        r.positive = true
        r.n = 0
		return r
	elseif w == 1 then
		return Integer.ucopy(r, a)
	elseif w == 2 then
		return Integer.umul(r, a, a)
	end

	r.n = 1
	r.limbs[1] = 1

	if w < 2 ^ 32 then
		local r0, r1 = r, Integer.new_zero()
		local a0, a1 = Integer.dup(a), Integer.new_zero()

		while w > 0 do
			if band(w, 1) ~= 0 then
				Integer.umul(r1, r0, a0)
				r1, r0 = r0, r1
			end

			Integer.umul(a1, a0, a0)
			a1, a0 = a0, a1

			w = rshift(w, 1)
		end

		if r0 ~= r then
			Integer.ucopy(r, r0)
		end

		return r
	end

	local b = Integer.from_scalar(w)
	return Integer.upow(r, a, b)
end

function Integer.pow(r, a, b)
	if Integer.is_one(a) then
		r.positive = a.positive or Integer.is_even(b)
		r.n = 1
		r.limbs[1] = 1
		return r
	elseif Integer.is_negative(b) then
		r.n = 0
		r.positive = true
		return r
	end

	r.positive = a.positive or Integer.is_even(b)
	return Integer.upow(r, a, b)
end

function Integer.pow_scalar(r, a, w)
	if Integer.is_one(a) then
		r.positive = a.positive or band(w, 1) == 0
		r.n = 1
		r.limbs[1] = 1
		return r
	elseif w < 0 then
		r.n = 0
		r.positive = true
		return r
	end

	r.positive = a.positive or band(w, 1) == 0
	return Integer.upow_scalar(r, a, w)
end

function Integer.ulshift(r, a, sh_amt)
	if sh_amt == 0 then
		return Integer.ucopy(r, a)
	elseif sh_amt < 0 then
		return Integer.urshift(r, a, -sh_amt)
	end

	r.n = limb_lshift(r.limbs, a.limbs, a.n, sh_amt)
	return r
end

function Integer.urshift(r, a, sh_amt)
	if sh_amt == 0 then
		return Integer.ucopy(r, a)
	elseif sh_amt < 0 then
		return Integer.ulshift(r, a, -sh_amt)
	end

	r.n = limb_rshift(r.limbs, a.limbs, a.n, sh_amt)
	return r
end

function Integer.lshift(r, a, sh_amt)
	r.positive = a.positive
	return Integer.ulshift(r, a, sh_amt)
end

function Integer.rshift(r, a, sh_amt)
	r.positive = a.positive
	return Integer.urshift(r, a, sh_amt)
end

function Integer.uband(r, a, b)
	if a.n < b.n then
		a, b = b, a
	end

	r.n = b.n
	for i = 1, b.n do
		r.limbs[i] = band(a.limbs[i], b.limbs[i])
	end

	return r
end

function Integer.ubor(r, a, b)
	if a.n < b.n then
		a, b = b, a
	end

	r.n = a.n
	for i = 1, b.n do
		r.limbs[i] = bor(a.limbs[i], b.limbs[i])
	end

	for i = b.n + 1, a.n do
		r.limbs[i] = a.limbs[i]
	end

	return r
end

function Integer.ubxor(r, a, b)
	if a.n < b.n then
		a, b = b, a
	end

	r.n = a.n
	for i = 1, b.n do
		r.limbs[i] = bxor(a.limbs[i], b.limbs[i])
	end

	for i = b.n + 1, a.n do
		r.limbs[i] = a.limbs[i]
	end

	return r
end

return Integer
