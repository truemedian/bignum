local bit = require("bit")

local floor, ceil = math.floor, math.ceil
local lshift, rshift, band, bor, bxor, bnot = bit.lshift, bit.rshift, bit.band, bit.bor, bit.bxor, bit.bnot

--- Multiple Precision Natural Library
---
--- Provides operations for manipulating natural (non-negative integer) numbers.
---
--- The following notation is used for documentation:
--- `a[a0:an]` is the array `a` with offset `a0` (beginning at 0) and size `an`.
--- `a[a0:]` is the array `a` with offset `a0` and no specified size.
---
---@module mpn

---@class mpn.limb : integer a single digit of base `LIMB_RADIX`
---@class mpn.offset : integer offset from beginning of associated array
---@class mpn.size : integer number of limbs in associated array
---@class mpn.limbs_const array of limbs, with the least significant limb at index 1
---@field [integer] mpn.limb
---@class mpn.limbs : mpn.limbs_const array of limbs, with the least significant limb at index 1
---@class mpn.bitcount : integer

---@class mpn
local mpn = {}

local LIMB_SIZE = 4
local LIMB_RADIX = 2 ^ LIMB_SIZE
local LIMB_MAX = LIMB_RADIX - 1
local LIMB_NUMBER_PRECISION = ceil(64 / LIMB_SIZE)
local KARATSUBA_THRESHOLD = 2

--- Number of bits in a single limb.
mpn.LIMB_SIZE = LIMB_SIZE

--- The "base" of a limb, i.e. the number of possible values a limb can take.
mpn.LIMB_RADIX = LIMB_RADIX

--- The highest possible unsigned value of a limb.
mpn.LIMB_MAX = LIMB_MAX

--- The number of limbs required to represent a number with 64 bits of precision.
mpn.LIMB_NUMBER_PRECISION = LIMB_NUMBER_PRECISION

local __skip_check = false

--- Ensures the given `a[a0:n]` is a valid array of limbs.
---@param a mpn.limbs_const the array to validate
---@param a0 mpn.offset the 0-based offset where the number starts
---@param n mpn.size the number of limbs expected in the array
local function __validate_source(a, a0, n)
	if __skip_check then
		return
	end

	assert(type(a) == "table")
	assert(a0 >= 0, "expected non-negative offset, got " .. tostring(a0))
	assert(n >= 0, "expected non-negative size, got " .. tostring(n))

	for i = 1, n do
		local t = a[a0 + i]
		assert(t ~= nil, "missing digit at index " .. tostring(a0 + i))
		assert(t >= 0 and t < LIMB_RADIX, "digit out of range: " .. tostring(t) .. " at index " .. tostring(a0 + i))
	end
end

--- Ensures the given `r[r0:n]` is a valid array of limbs for a destination.
---@param r mpn.limbs_const the array to validate
---@param r0 mpn.offset the 0-based offset where the number starts
---@param n mpn.size the number of limbs that will be expected in the array
local function __validate_dest(r, r0, n)
	if __skip_check then
		return
	end

	assert(type(r) == "table")
	assert(r0 >= 0)
	assert(n >= 0)
end

--- Ensures the given `r[r0:n]` is a valid array of limbs for a destination after an operation.
---@param r mpn.limbs_const the array to validate
---@param r0 mpn.offset the 0-based offset where the number starts
---@param n mpn.size the number of limbs expected in the array
local function __validate_dest_suffix(r, r0, n)
	if __skip_check then
		return
	end

	for i = 1, n do
		local t = r[r0 + i]
		assert(t >= 0 and t < LIMB_RADIX)
	end
end

--- Ensures the given `x` is a valid limb.
---@param x mpn.limb
local function __validate_limb(x)
	if __skip_check then
		return
	end

	assert(x >= 0 and x < LIMB_RADIX, "bad limb " .. tostring(x))
end

--- Copy `n` limbs from `s[s0:n]` to `r[r0:n]` in increasing order.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param s mpn.limbs_const
---@param s0 mpn.offset
---@param n mpn.size
function mpn.copyi(r, r0, s, s0, n)
	__validate_dest(r, r0, n)
	__validate_source(s, s0, n)

	if rawequal(r, s) and r0 == s0 then
		__validate_dest_suffix(r, r0, n)
		return
	end

	for i = 1, n do
		r[r0 + i] = s[s0 + i]
	end

	__validate_dest_suffix(r, r0, n)
end

--- Copy `n` limbs from `s[s0:n]` to `r[r0:n]` in decreasing order.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param s mpn.limbs_const
---@param s0 mpn.offset
---@param n mpn.size
function mpn.copyd(r, r0, s, s0, n)
	__validate_dest(r, r0, n)
	__validate_source(s, s0, n)

	if rawequal(r, s) and r0 == s0 then
		__validate_dest_suffix(r, r0, n)
		return
	end

	for i = n, 1, -1 do
		r[r0 + i] = s[s0 + i]
	end

	__validate_dest_suffix(r, r0, n)
end

--- Returns the sign of the difference `a[a0:an] - x`.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param x mpn.limb
---@return integer
---@nodiscard
function mpn.cmp_1(a, a0, an, x)
	__validate_source(a, a0, an)
	__validate_limb(x)

	an = mpn.normalized_size(a, a0, an)

	if x == 0 then
		return an == 0 and 0 or 1
	elseif an ~= 1 then
		return an < 1 and -1 or 1
	end

	local a_k = a[a0 + 1]
	local b_k = x
	if a_k ~= b_k then
		return a_k < b_k and -1 or 1
	end

	return 0
end

--- Returns the sign of the difference `a[a0:an] - b[b0:bn]`.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
---@return integer
---@nodiscard
function mpn.cmp(a, a0, an, b, b0, bn)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)

	an = mpn.normalized_size(a, a0, an)
	bn = mpn.normalized_size(b, b0, bn)

	if an ~= bn then
		return an < bn and -1 or 1
	end

	for i = an, 1, -1 do
		local a_k = a[a0 + i]
		local b_k = b[b0 + i]
		if a_k ~= b_k then
			return a_k < b_k and -1 or 1
		end
	end

	return 0
end

--- Returns the sign of the difference `a[a0:n] - b[b0:n]`.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param n mpn.size
---@return integer
---@nodiscard
function mpn.cmp_n(a, a0, b, b0, n)
	__validate_source(a, a0, n)
	__validate_source(b, b0, n)

	for i = n, 1, -1 do
		local a_k = a[a0 + i]
		local b_k = b[b0 + i]
		if a_k ~= b_k then
			return a_k < b_k and -1 or 1
		end
	end

	return 0
end

--- Returns the shortest size `n` of `a[a0:an]` such that `a[a0 + n]` is the first non-zero element.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@return mpn.size
---@nodiscard
function mpn.normalized_size(a, a0, an)
	__validate_source(a, a0, an)

	while an > 0 and a[a0 + an] == 0 do
		an = an - 1
	end

	return an
end

--- Returns true if `a[a0:an]` is zero.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@return boolean
---@nodiscard
function mpn.is_zero(a, a0, an)
	return mpn.normalized_size(a, a0, an) == 0
end

--- Returns true if `a[a0:an]` is not zero.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@return boolean
---@nodiscard
function mpn.is_nonzero(a, a0, an)
	return mpn.normalized_size(a, a0, an) ~= 0
end

--- Fills `r[r0:n]` with zeroes.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param n mpn.size
function mpn.zero(r, r0, n)
	__validate_dest(r, r0, n)

	for i = 1, n do
		r[r0 + i] = 0
	end

	__validate_dest_suffix(r, r0, n)
end

--- Computes `r[r0:n] = a[a0:n] + y`. Returns the carried limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param y mpn.limb
---@return mpn.limb
function mpn.add_1(r, r0, a, a0, n, y)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_limb(y)

	-- the rest of the algorithm assumes there is at least one digit to operate on
	if n == 0 then
		__validate_dest_suffix(r, r0, n)
		return y
	end

	-- the first addition will always happen, and reduces the following additions to a single carry bit
	local t = a[a0 + 1] + y
	r[r0 + 1] = band(t, LIMB_MAX)

	for i = 2, n do
		-- check if the previous addition caused a carry
		if t <= LIMB_MAX then
			-- no carry necessary, so we can just copy the rest of the number
			mpn.copyi(r, r0 + i - 1, a, a0 + i - 1, n - i + 1)

			__validate_dest_suffix(r, r0, n)
			return 0
		end

		t = a[a0 + i] + 1
		r[r0 + i] = band(t, LIMB_MAX)
	end

	__validate_dest_suffix(r, r0, n)
	return t <= LIMB_MAX and 0 or 1
end

--- Computes `r[r0:n] = a[a0:n] + b[b0:n]`. Returns the carried limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param n mpn.size
---@return mpn.limb
function mpn.add_n(r, r0, a, a0, b, b0, n)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_source(b, b0, n)

	local carry = 0

	for i = 1, n do
		local t = a[a0 + i] + b[b0 + i] + carry
		r[r0 + i] = band(t, LIMB_MAX)
		carry = t > LIMB_MAX and 1 or 0
	end

	__validate_dest_suffix(r, r0, n)
	return carry
end

--- Computes `r[r0:an] = a[a0:an] + b[b0:bn]`. Returns the carried limb.
---
--- Requires `an >= bn >= 0`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
---@return mpn.limb
function mpn.add(r, r0, a, a0, an, b, b0, bn)
	__validate_dest(r, r0, an)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)
	assert(an >= bn)

	local carry = mpn.add_n(r, r0, a, a0, b, b0, bn)
	if an > bn then
		carry = mpn.add_1(r, r0 + bn, a, a0 + bn, an - bn, carry)
	end

	__validate_dest_suffix(r, r0, an)
	return carry
end

--- Computes `r[r0:n] = a[a0:n] - y`. Returns the borrowed limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param y mpn.limb
---@return mpn.limb
function mpn.sub_1(r, r0, a, a0, n, y)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_limb(y)

	-- the rest of the algorithm assumes there is at least one digit to operate on
	if n == 0 then
		__validate_dest_suffix(r, r0, n)
		-- FIXME: this is probably not correct
		return y
	end

	-- the first subtraction will always happen, and reduces the following subtractions to a single borrow bit
	local t = a[a0 + 1] - y
	r[r0 + 1] = band(t, LIMB_MAX)

	for i = 2, n do
		-- check if the previous subtraction caused a borrow
		if t >= 0 then
			-- no borrow necessary, so we can just copy the rest of the number
			mpn.copyi(r, r0 + i - 1, a, a0 + i - 1, n - i + 1)

			__validate_dest_suffix(r, r0, n)
			return 0
		end

		t = a[a0 + i] - 1
		r[r0 + i] = band(t, LIMB_MAX)
	end

	-- if we get here, then the last subtraction caused a borrow
	__validate_dest_suffix(r, r0, n)
	return t >= 0 and 0 or 1
end

--- Computes `r[r0:n] = a[a0:n] - b[b0:n]`. Returns the borrowed limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param n mpn.size
---@return mpn.limb
function mpn.sub_n(r, r0, a, a0, b, b0, n)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_source(b, b0, n)

	local borrow = 0

	for i = 1, n do
		local t = a[a0 + i] - b[b0 + i] - borrow
		r[r0 + i] = band(t, LIMB_MAX)
		borrow = t < 0 and 1 or 0
	end

	__validate_dest_suffix(r, r0, n)
	return borrow
end

--- Computes `r[r0:an] = a[a0:an] - b[b0:bn]`. Returns the borrowed limb.
---
--- Requires `an >= bn >= 0`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
---@return mpn.limb
function mpn.sub(r, r0, a, a0, an, b, b0, bn)
	__validate_dest(r, r0, an)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)
	assert(an >= bn)

	local borrow = mpn.sub_n(r, r0, a, a0, b, b0, bn)
	if an > bn then
		borrow = mpn.sub_1(r, r0 + bn, a, a0 + bn, an - bn, borrow)
	end

	__validate_dest_suffix(r, r0, an)
	return borrow
end

--- Computes `r[r0:n] = a[a0:n] * y`. Returns the carried limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param y mpn.limb
---@return mpn.limb
function mpn.mul_1(r, r0, a, a0, n, y)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_limb(y)

	local carry = 0

	for i = 1, n do
		local t = a[a0 + i] * y + carry
		r[r0 + i] = band(t, LIMB_MAX)
		carry = rshift(t, LIMB_SIZE)
	end

	__validate_dest_suffix(r, r0, n)
	return carry
end

--- Computes `r[r0:max(rn,an)] += a[a0:an] * y`. Returns the carried limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param rn mpn.size
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param y mpn.limb
---@return mpn.limb
function mpn.addmul_1(r, r0, rn, a, a0, an, y)
	__validate_source(r, r0, rn)
	__validate_source(a, a0, an)
	__validate_limb(y)

	rn = math.max(rn, an)
	local carry = 0

	for i = 1, an do
		local rk = r[r0 + i] + a[a0 + i] * y + carry
		r[r0 + i] = band(rk, LIMB_MAX)
		carry = rshift(rk, LIMB_SIZE)
	end

	for i = an + 1, rn do
		local rk = r[r0 + i] + carry
		r[r0 + i] = band(rk, LIMB_MAX)
		carry = rshift(rk, LIMB_SIZE)
	end

	__validate_dest_suffix(r, r0, rn)
	return carry
end

--- Computes `r[r0:max(rn,an)] -= a[a0:an] * y`. Returns the borrowed limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param rn mpn.size
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param y mpn.limb
---@return mpn.limb
function mpn.submul_1(r, r0, rn, a, a0, an, y)
	__validate_source(r, r0, rn)
	__validate_source(a, a0, an)
	__validate_limb(y)

	rn = math.max(rn, an)
	local borrow = 0

	for i = 1, an do
		local rk = (r[r0 + i] or 0) - a[a0 + i] * y - borrow
		borrow = rk < 0 and ceil(-rk / LIMB_RADIX) or 0
		r[r0 + i] = band(rk, LIMB_MAX)
	end

	for i = an + 1, rn do
		local rk = r[r0 + i] - borrow
		borrow = rk < 0 and ceil(-rk / LIMB_RADIX) or 0
		r[r0 + i] = band(rk, LIMB_MAX)
	end

	__validate_dest_suffix(r, r0, rn)
	return borrow
end

--- Computes `r[r0:2*n] = a[a0:n] * b[b0:n]`.
---
--- Requires `r` must not alias `a` or `b`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param n mpn.size
function mpn.mul_n(r, r0, a, a0, b, b0, n)
	return mpn.mul(r, r0, a, a0, n, b, b0, n)
end

--- Computes `r[r0:an+bn] = a[a0:an] * b[b0:bn]`.
---
--- Requires `r` must not alias `a` or `b`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
function mpn.mul(r, r0, a, a0, an, b, b0, bn)
	__validate_dest(r, r0, an + bn)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)
	assert(an >= bn)
	assert(not rawequal(r, a))
	assert(not rawequal(r, b))

	if bn >= KARATSUBA_THRESHOLD then
		mpn.zero(r, r0, an + bn)
		local xxx = mpn.addmul_karatsuba(r, r0, an + bn, a, a0, an, b, b0, bn)
		return
	elseif bn == 0 then
		-- multiplication by zero
		mpn.zero(r, r0, an + bn)
		__validate_dest_suffix(r, r0, an + bn)
		return
	end

	-- offset for the result carry
	local t = r0 + an
	local rn = an + 1

	-- do the first multiplication, this saves a loop to zero `r`.
    r[t + 1] = mpn.mul_1(r, r0, a, a0, an, b[b0 + 1])

	-- accumulate the rest of the single digit multiplications
	for i = 2, bn do
		r[t + i] = mpn.addmul_1(r, r0 + i - 1, rn - i + 1, a, a0, an, b[b0 + i])
	end

	__validate_dest_suffix(r, r0, an + bn)
end

--- Computes `r[r0:an+bn+1] += a[a0:an] * b[b0:bn]` using the Karatsuba algorithm.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param rn mpn.size
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
---@return mpn.limb
---@nodiscard
function mpn.addmul_karatsuba(r, r0, rn, a, a0, an, b, b0, bn)
	__validate_source(r, r0, an + bn)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)
	assert(an >= bn)
	assert(not rawequal(r, a))
	assert(not rawequal(r, b))

	local k = ceil(bn / 2)

	local a1 = a0 + k
	local a0n, a1n = mpn.normalized_size(a, a0, k), mpn.normalized_size(a, a1, an - k)

	local b1 = b0 + k
	local b0n, b1n = mpn.normalized_size(b, b0, k), mpn.normalized_size(b, b1, bn - k)

	local r0n = math.max(an + bn, rn)

	local r1 = r0 + k
	local r1n = r0n - k

	local r2 = r0 + 2 * k
	local r2n = r0n - 2 * k

	local tmp = {}

	local a0b0n = a0n + b0n
	if a0n > b0n then
		mpn.mul(tmp, 0, a, a0, a0n, b, b0, b0n)
	else
		mpn.mul(tmp, 0, b, b0, b0n, a, a0, a0n)
	end

	local c0 = mpn.add(r, r0, r, r0, r0n, tmp, 0, a0b0n) -- r += a0 * b0
	local c1 = mpn.add(r, r1, r, r1, r1n, tmp, 0, a0b0n) -- r += a0 * b0 * B

	local a1b1n = a1n + b1n
	if a1n > b1n then
		mpn.mul(tmp, 0, a, a1, a1n, b, b1, b1n)
	else
		mpn.mul(tmp, 0, b, b1, b1n, a, a1, a1n)
	end

	local c2 = mpn.add(r, r1, r, r1, r1n, tmp, 0, a1b1n) -- r += a1 * b1 * B
	local c3 = mpn.add(r, r2, r, r2, r2n, tmp, 0, a1b1n) -- r += a1 * b1 * B^2

	local j0s = mpn.cmp(a, a1, a1n, a, a0, a0n)
	local j1s = mpn.cmp(b, b1, b1n, b, b0, b0n)

	if j0s == 0 or j1s == 0 then
		-- one of the differences is zero, so the product is zero
		__validate_dest_suffix(r, r0, an + bn)
		return c0 + c1 + c2 + c3
	end

	local j0 = {}
	local j1 = {}

	if j0s > 0 then
		assert(mpn.sub(j0, 0, a, a1, a1n, a, a0, a0n) == 0)
	else
		assert(mpn.sub(j0, 0, a, a0, a0n, a, a1, a1n) == 0)
	end
	local j0n = mpn.normalized_size(j0, 0, math.max(a0n, a1n))

	if j1s > 0 then
		assert(mpn.sub(j1, 0, b, b1, b1n, b, b0, b0n) == 0)
	else
		assert(mpn.sub(j1, 0, b, b0, b0n, b, b1, b1n) == 0)
	end
	local j1n = mpn.normalized_size(j1, 0, math.max(b0n, b1n))

	if j1n > j0n then
		j0, j1 = j1, j0
		j0n, j1n = j1n, j0n
	end

	if j0s ~= j1s then
		local carry = mpn.addmul(r, r1, r1n, j0, 0, j0n, j1, 0, j1n) -- r += (j0 * j1) * B
		local rx0 = r1 + math.max(r1n, j0n + j1n)
		local rxn = rn + r0 - rx0
		local c4 = mpn.add_1(r, rx0, r, rx0, rxn, carry) -- propagate carry to r2
		return c0 + c1 + c2 + c3 + c4
	else
		local borrow = mpn.submul(r, r1, r1n, j0, 0, j0n, j1, 0, j1n) -- r -= (j0 * j1) * B
		local rx0 = r1 + math.max(r1n, j0n + j1n)
		local rxn = rn + r0 - rx0
		local c4 = mpn.sub_1(r, rx0, r, rx0, rxn, borrow) -- propagate borrow to r2
		return c0 + c1 + c2 + c3 - c4
	end
end

--- Computes `r[r0:an+bn+1] -= a[a0:an] * b[b0:bn]` using the Karatsuba algorithm.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param rn mpn.size
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
---@return mpn.limb
---@nodiscard
function mpn.submul_karatsuba(r, r0, rn, a, a0, an, b, b0, bn)
	__validate_source(r, r0, an + bn)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)
	assert(an >= bn)
	assert(not rawequal(r, a))
	assert(not rawequal(r, b))

	local k = ceil(bn / 2)

	local a1 = a0 + k
	local a0n, a1n = mpn.normalized_size(a, a0, k), mpn.normalized_size(a, a1, an - k)

	local b1 = b0 + k
	local b0n, b1n = mpn.normalized_size(b, b0, k), mpn.normalized_size(b, b1, bn - k)

	local r0n = math.max(an + bn, rn)

	local r1 = r0 + k
	local r1n = r0n - k

	local r2 = r0 + 2 * k
	local r2n = r0n - 2 * k

	local tmp = {}

	local a0b0n = a0n + b0n
	if a0n > b0n then
		mpn.mul(tmp, 0, a, a0, a0n, b, b0, b0n)
	else
		mpn.mul(tmp, 0, b, b0, b0n, a, a0, a0n)
	end

	local c0 = mpn.sub(r, r0, r, r0, r0n, tmp, 0, a0b0n) -- r -= a0 * b0
	local c1 = mpn.sub(r, r1, r, r1, r1n, tmp, 0, a0b0n) -- r -= a0 * b0 * B

	local a1b1n = a1n + b1n
	if a1n > b1n then
		mpn.mul(tmp, 0, a, a1, a1n, b, b1, b1n)
	else
		mpn.mul(tmp, 0, b, b1, b1n, a, a1, a1n)
	end

	local c2 = mpn.sub(r, r1, r, r1, r1n, tmp, 0, a1b1n) -- r -= a1 * b1 * B
	local c3 = mpn.sub(r, r2, r, r2, r2n, tmp, 0, a1b1n) -- r -= a1 * b1 * B^2

	local j0s = mpn.cmp(a, a1, a1n, a, a0, a0n)
	local j1s = mpn.cmp(b, b1, b1n, b, b0, b0n)

	if j0s == 0 or j1s == 0 then
		-- one of the differences is zero, so the product is zero
		__validate_dest_suffix(r, r0, an + bn)
		return c0 + c1 + c2 + c3
	end

	local j0 = {}
	local j1 = {}

	if j0s > 0 then
		assert(mpn.sub(j0, 0, a, a1, a1n, a, a0, a0n) == 0)
	else
		assert(mpn.sub(j0, 0, a, a0, a0n, a, a1, a1n) == 0)
	end
	local j0n = mpn.normalized_size(j0, 0, math.max(a0n, a1n))

	if j1s > 0 then
		assert(mpn.sub(j1, 0, b, b1, b1n, b, b0, b0n) == 0)
	else
		assert(mpn.sub(j1, 0, b, b0, b0n, b, b1, b1n) == 0)
	end
	local j1n = mpn.normalized_size(j1, 0, math.max(b0n, b1n))

	if j1n > j0n then
		j0, j1 = j1, j0
		j0n, j1n = j1n, j0n
	end

	if j0s ~= j1s then
		local borrow = mpn.submul(r, r1, r1n, j0, 0, j0n, j1, 0, j1n)
		local rx0 = r1 + math.max(r1n, j0n + j1n)
		local rxn = rn + r0 - rx0
		local c4 = mpn.sub_1(r, rx0, r, rx0, rxn, borrow) -- propagate borrow to r2
		return c0 + c1 + c2 + c3 + c4
	else
		local carry = mpn.addmul(r, r1, r1n, j0, 0, j0n, j1, 0, j1n)
		local rx0 = r1 + math.max(r1n, j0n + j1n)
		local rxn = rn + r0 - rx0
		local c4 = mpn.add_1(r, rx0, r, rx0, rxn, carry) -- propagate carry to r2
		return c0 + c1 + c2 + c3 - c4
	end
end

--- Computes `r[r0:max(an+bn,rn)] += a[a0:an] * b[b0:bn]`. Returns the carried limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param rn mpn.size
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
---@return mpn.limb
---@nodiscard
function mpn.addmul(r, r0, rn, a, a0, an, b, b0, bn)
	rn = math.max(an + bn, rn)

	__validate_source(r, r0, rn)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)
	assert(an >= bn)
	assert(not rawequal(r, a))
	assert(not rawequal(r, b))

	if bn >= KARATSUBA_THRESHOLD then
		-- use Karatsuba for large multiplications
		return mpn.addmul_karatsuba(r, r0, rn, a, a0, an, b, b0, bn)
	end

	-- accumulate the rest of the single digit multiplications
	local carry = 0
	for i = 1, bn do
		local tn = rn - i + 1
		local t = math.max(an, tn) + i - 1
		local c = mpn.addmul_1(r, r0 + i - 1, rn - i + 1, a, a0, an, b[b0 + i])
		carry = carry + mpn.add_1(r, r0 + t, r, r0 + t, rn - t, c)
	end

	__validate_dest_suffix(r, r0, rn)
	return carry
end

--- Computes `r[r0:max(an+bn,rn)] -= a[a0:an] * b[b0:bn]`. Returns the borrowed limb.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param rn mpn.size
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param bn mpn.size
---@return mpn.limb
---@nodiscard
function mpn.submul(r, r0, rn, a, a0, an, b, b0, bn)
	rn = math.max(an + bn, rn)

	__validate_source(r, r0, rn)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)
	assert(an >= bn)
	assert(not rawequal(r, a))
	assert(not rawequal(r, b))

	if bn >= KARATSUBA_THRESHOLD then
		-- use Karatsuba for large multiplications
		return mpn.submul_karatsuba(r, r0, rn, a, a0, an, b, b0, bn)
	end

	-- accumulate the rest of the single digit multiplications
	local borrow = 0
	for i = 1, bn do
		local tn = rn - i + 1
		local t = math.max(an, tn) + i - 1
		local c = mpn.submul_1(r, r0 + i - 1, tn, a, a0, an, b[b0 + i])
		borrow = borrow + mpn.sub_1(r, r0 + t, r, r0 + t, rn - t, c)
	end

	__validate_dest_suffix(r, r0, rn)
	return borrow
end

--- Computes `r[r0:2*n] = a[a0:n] * a[a0:n]`.
---
--- Requires `r` must not alias `a`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
function mpn.sqr(r, r0, a, a0, n)
	__validate_dest(r, r0, n * 2)
	__validate_source(a, a0, n)
	assert(not rawequal(r, a))

	for i = 1, 2 * n do
		r[r0 + i] = 0
	end

	-- accumulate all a[i] * a[j] for i != j
	for i = 0, n - 1 do
		local overflow = mpn.addmul_1(r, r0 + 2 * i + 1, 2 * n - 2 * i - 1, a, a0 + i + 1, n - i - 1, a[a0 + i + 1])
		mpn.add_1(r, r0 + 2 * i + n - i, r, r0 + 2 * i + n - i, 2 * n - 2 * i - n + i, overflow)
	end

	-- each a[i] * a[j] appears twice at each result digit, so we must double it.
	mpn.lshift(r, r0, r, r0, 2 * n, 1)

	-- accumulate all of the squares along the diagonal.
	for i = 0, n - 1 do
		local overflow = mpn.addmul_1(r, r0 + 2 * i, 2 * n - 2 * i, a, a0 + i, 1, a[a0 + i + 1])
		mpn.add_1(r, r0 + 2 * i + 1, r, r0 + 2 * i + 1, 2 * n - 2 * i - 1, overflow)
	end

	__validate_dest_suffix(r, r0, n * 2)
end

--- Computes `r[r0:*] = a[a0:n] << tcnt`. Returns the resulting size of `r`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param tcnt integer
---@return mpn.size
function mpn.lshift(r, r0, a, a0, n, tcnt)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)

	-- the rest of the algorithm assumes there is at least one digit to operate on
	if n == 0 then
		mpn.copyi(r, r0, a, a0, n)
		__validate_dest_suffix(r, r0, n)
		return 0
	end

	local mlmb = floor(tcnt / LIMB_SIZE)
	local cnt = tcnt - mlmb * LIMB_SIZE
	local tnc = LIMB_SIZE - cnt

	if cnt == 0 then -- shift by whole limbs only
		mpn.copyi(r, r0 + mlmb, a, a0, n)
		mpn.zero(r, r0, mlmb)
		__validate_dest_suffix(r, r0, n + mlmb)
		return n + mlmb
	end

	local low_limb = a[a0 + n]
	local overflow = rshift(low_limb, tnc)
	local high_limb = band(lshift(low_limb, cnt), LIMB_MAX)
	for i = n, 2, -1 do
		low_limb = a[a0 + i - 1]
		r[r0 + i + mlmb] = bor(high_limb, rshift(low_limb, tnc))
		high_limb = band(lshift(low_limb, cnt), LIMB_MAX)
	end

	r[r0 + 1 + mlmb] = high_limb

	mpn.zero(r, r0, mlmb)
	if overflow ~= 0 then
		r[r0 + n + mlmb + 1] = overflow
		__validate_dest_suffix(r, r0, n + mlmb + 1)
		return n + mlmb + 1
	end

	return n + mlmb
end

--- Computes `r[r0:n] = a[a0:n] >> tcnt`. Returns the resulting size of `r`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param tcnt integer
---@return mpn.size
function mpn.rshift(r, r0, a, a0, n, tcnt)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)

	-- the rest of the algorithm assumes there is at least one digit to operate on
	if n == 0 then
		mpn.copyi(r, r0, a, a0, n)
		__validate_dest_suffix(r, r0, n)
		return n
	end

	local mlmb = floor(tcnt / LIMB_SIZE)
	if mlmb >= n then
		return 0
	end

	local cnt = tcnt - mlmb * LIMB_SIZE
	local tnc = LIMB_SIZE - cnt

	if cnt == 0 then -- shift by whole limbs only
		mpn.copyi(r, r0, a, a0 + mlmb, n - mlmb)
		__validate_dest_suffix(r, r0, n - mlmb)
		return n - mlmb
	end

	local high_limb = a[a0 + 1 + mlmb]
	-- local overflow = band(lshift(high_limb, tnc), LIMB_MAX)
	local low_limb = rshift(high_limb, cnt)
	for i = 1, n - 1 - mlmb do
		high_limb = a[a0 + i + 1 + mlmb]
		r[r0 + i] = bor(low_limb, band(lshift(high_limb, tnc), LIMB_MAX))
		low_limb = rshift(high_limb, cnt)
	end

	r[r0 + n - mlmb] = low_limb

	__validate_dest_suffix(r, r0, n - mlmb)
	return n - mlmb
end

--- Computes `q[q0:qn] = n[n0:nn] / d[d0:dn]`, `r[r0:dn] = n[n0:nn] % d[d0:dn]`.
---
--- Clobbers `n`. Modifies and restores `d`.
---
--- Where `qn = nn - dn + 1`.
---@param q mpn.limbs
---@param q0 mpn.offset
---@param r mpn.limbs
---@param r0 mpn.offset
---@param n mpn.limbs
---@param n0 mpn.offset
---@param nn mpn.size
---@param d mpn.limbs
---@param d0 mpn.offset
---@param dn mpn.size
function mpn.divmod(q, q0, r, r0, n, n0, nn, d, d0, dn)
	__validate_dest(q, q0, math.max(0, nn - dn + 1))
	__validate_dest(r, r0, dn)
	__validate_source(n, n0, nn)
	__validate_source(d, d0, dn)

	assert(not rawequal(q, n))
	assert(not rawequal(q, d))
	assert(not rawequal(n, d))

	-- 0.1. dn != 0
	dn = mpn.normalized_size(d, d0, dn)

	-- 0.2. nn >= dn >= 1
	if dn == 0 then
		error("division by zero")
	elseif nn < dn then
		mpn.copyi(r, r0, n, n0, nn)
		mpn.zero(r, r0 + nn, dn - nn)
		mpn.zero(q, q0, math.max(0, nn - dn + 1))
		__validate_dest_suffix(q, q0, nn - dn + 1)
		__validate_dest_suffix(r, r0, dn)
		return
	end

	assert(d[d0 + dn] ~= 0, "divisor must be normalized")
	assert(nn >= dn and dn >= 1)

	local norm_shift, norm_test = 0, d[d0 + dn]
	while norm_test < LIMB_RADIX / 2 do
		norm_shift = norm_shift + 1
		norm_test = lshift(norm_test, 1)
	end

	assert(mpn.lshift(d, d0, d, d0, dn, norm_shift) == dn) -- cannot overflow, we shift only to the highest bit
	nn = mpn.lshift(n, n0, n, n0, nn, norm_shift)
	nn = mpn.normalized_size(n, n0, nn)

	-- 1. for j from 0 to nn - dn, set q[j] = 0
	for j = 1, nn - dn + 1 do
		q[q0 + j] = 0
	end

	-- 2. while n >= d * b^(nn - dn)
	-- normalization guarantees this can only loop once
	if mpn.cmp_n(n, n0 + nn - dn, d, d0, dn) >= 0 then
		-- 2.1 set q[nn - dn] += 1
		q[q0 + nn - dn + 1] = q[q0 + nn - dn + 1] + 1

		-- 2.2 n -= d * b^(nn - dn)
		mpn.sub_n(n, n0 + nn - dn, n, n0 + nn - dn, d, d0, dn)
	end
	assert(mpn.cmp_n(n, n0 + nn - dn, d, d0, dn) < 0)

	local dk = d[d0 + dn] * LIMB_RADIX + (dn - 1 > 0 and d[d0 + dn - 1] or 0)

	-- 3. for i from nn - 1 down to dn do
	for i = nn, dn + 1, -1 do
		local k = i - dn
		local nk = n[n0 + i] * LIMB_RADIX * LIMB_RADIX
			+ (i - 1 > 0 and n[n0 + i - 1] or 0) * LIMB_RADIX
			+ (i - 2 > 0 and n[n0 + i - 2] or 0)

		-- 3.1 if n[i] == d[dn] then
		--        set q[k] = b - 1
		--     else
		--        set q[k] = floor((n[i] * b + n[i - 1]) / d[dn])
		-- enhancement: use 3-limb division to reduce 3.2 to a single comparison
		local qk = (n[n0 + i] == d[d0 + dn]) and LIMB_MAX or floor(nk / dk)

		-- 3.2 while q[k] * (d[dn] * b + d[dn - 1]) > (n[i] * b^2 + n[i - 1] * b + n[i - 2])
		-- this can loop at most once because of the enhancement in 3.1
		if qk * dk > nk then
			qk = qk - 1
		end
		assert(qk * dk <= nk)

		-- 3.3 set n -= q[k] * d * b^(i - dn - 1)
		local overflow = mpn.submul_1(n, n0 + k - 1, nn - k + 1, d, d0, dn, qk)

		-- 3.4 if n < 0 then
		if overflow > 0 then
			-- 3.4.1 set x += d * b^(i - dn - 1)
			mpn.add(n, n0 + k - 1, n, n0 + k - 1, nn - k + 1, d, d0, dn)

			-- 3.4.2 set q[k] -= 1
			qk = qk - 1
		end

		q[q0 + k] = qk
	end

	-- 4. set r = n, fix d
	mpn.rshift(d, d0, d, d0, dn, norm_shift)
	mpn.rshift(r, r0, n, n0, dn, norm_shift)
end

--- Computes `r[r0:dn] = n[n0:nn] % d[d0:dn]`.
---
--- Clobbers `n`. Modifies and restores `d`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param n mpn.limbs
---@param n0 mpn.offset
---@param nn mpn.size
---@param d mpn.limbs
---@param d0 mpn.offset
---@param dn mpn.size
function mpn.mod(r, r0, n, n0, nn, d, d0, dn)
	-- A duplicate of the above algorithm but without storing the quotient.

	__validate_dest(r, r0, dn)
	__validate_source(n, n0, nn)
	__validate_source(d, d0, dn)

	assert(not rawequal(n, d))

	-- 0.1. dn != 0
	dn = mpn.normalized_size(d, d0, dn)

	-- 0.2. nn >= dn >= 1
	if dn == 0 then
		error("division by zero")
	elseif nn < dn then
		mpn.copyi(r, r0, n, n0, nn)
		mpn.zero(r, r0 + nn, dn - nn)
		__validate_dest_suffix(r, r0, dn)
		return
	end

	assert(d[d0 + dn] ~= 0, "divisor must be normalized")
	assert(nn >= dn and dn >= 1)

	local norm_shift, norm_test = 0, d[d0 + dn]
	while norm_test < LIMB_RADIX / 2 do
		norm_shift = norm_shift + 1
		norm_test = lshift(norm_test, 1)
	end

	assert(mpn.lshift(d, d0, d, d0, dn, norm_shift) == dn) -- cannot overflow, we shift only to the highest bit
	nn = mpn.lshift(n, n0, n, n0, nn, norm_shift)
	nn = mpn.normalized_size(n, n0, nn)

	-- 2. while n >= d * b^(nn - dn)
	-- normalization guarantees this can only loop once
	if mpn.cmp_n(n, n0 + nn - dn, d, d0, dn) >= 0 then
		-- 2.2 n -= d * b^(nn - dn)
		mpn.sub_n(n, n0 + nn - dn, n, n0 + nn - dn, d, d0, dn)
	end
	assert(mpn.cmp_n(n, n0 + nn - dn, d, d0, dn) < 0)

	local dk = d[d0 + dn] * LIMB_RADIX + (dn - 1 > 0 and d[d0 + dn - 1] or 0)

	-- 3. for i from nn - 1 down to dn do
	for i = nn, dn + 1, -1 do
		local k = i - dn
		local nk = n[n0 + i] * LIMB_RADIX * LIMB_RADIX
			+ (i - 1 > 0 and n[n0 + i - 1] or 0) * LIMB_RADIX
			+ (i - 2 > 0 and n[n0 + i - 2] or 0)

		-- 3.1 if n[i] == d[dn] then
		--        set q[k] = b - 1
		--     else
		--        set q[k] = floor((n[i] * b + n[i - 1]) / d[dn])
		-- enhancement: use 3-limb division to reduce 3.2 to a single comparison
		local qk = (n[n0 + i] == d[d0 + dn]) and LIMB_MAX or floor(nk / dk)

		-- 3.2 while q[k] * (d[dn] * b + d[dn - 1]) > (n[i] * b^2 + n[i - 1] * b + n[i - 2])
		-- this can loop at most once because of the enhancement in 3.1
		if qk * dk > nk then
			qk = qk - 1
		end
		assert(qk * dk <= nk)

		-- 3.3 set n -= q[k] * d * b^(i - dn - 1)
		local overflow = mpn.submul_1(n, n0 + k - 1, nn - k + 1, d, d0, dn, qk)

		-- 3.4 if n < 0 then
		if overflow > 0 then
			-- 3.4.1 set x += d * b^(i - dn - 1)
			mpn.add(n, n0 + k - 1, n, n0 + k - 1, nn - k + 1, d, d0, dn)

			-- 3.4.2 set q[k] -= 1
			qk = qk - 1
		end
	end

	-- 4. set r = n, fix d
	mpn.rshift(d, d0, d, d0, dn, norm_shift)
	mpn.rshift(r, r0, n, n0, dn, norm_shift)
end

--- Computes `q[q0:nn] = n[n0:nn] / z`, returns `n[n0:nn] % z`.
---@param q mpn.limbs
---@param q0 mpn.offset
---@param n mpn.limbs_const
---@param n0 mpn.offset
---@param nn mpn.size
---@param z mpn.limb
---@return mpn.limb
---@nodiscard
function mpn.divmod_1(q, q0, n, n0, nn, z)
	__validate_dest(q, q0, nn)
	__validate_source(n, n0, nn)
	__validate_limb(z)
	assert(z > 0)

	if nn == 0 then
		return 0
	end

	-- optimize space before we work backwards
	for i = #q + 1, n0 + nn do
		q[i] = 0
	end

	local remainder = 0
	for i = nn, 1, -1 do
		local partial = remainder * LIMB_RADIX + n[n0 + i]
		q[q0 + i] = band(floor(partial / z), LIMB_MAX)
		remainder = floor(partial % z)
	end

	return remainder
end

--- Returns `n[n0:nn] % z`.
---@param n mpn.limbs_const
---@param n0 mpn.offset
---@param nn mpn.size
---@param z mpn.limb
---@return mpn.limb
---@nodiscard
function mpn.mod_1(n, n0, nn, z)
	__validate_source(n, n0, nn)
	__validate_limb(z)
	assert(z > 0)

	if nn == 0 then
		return 0
	elseif nn == 1 then
		return floor(n[n0 + 1] % z)
	end

	local remainder = 0
	for i = nn, 1, -1 do
		local partial = remainder * LIMB_RADIX + n[n0 + i]
		remainder = floor(partial % z)
	end

	return remainder
end

--- Returns `gcd(x, y)`.
---@param x mpn.limb
---@param y mpn.limb
---@return mpn.limb
---@nodiscard
function mpn.gcd_11(x, y)
	__validate_limb(x)
	__validate_limb(y)
	if y == 0 then
		return x
	elseif x == 0 then
		return y
	end

	local g = 1
	while band(x, 1) == 0 and band(y, 1) == 0 do
		x = rshift(x, 1)
		y = rshift(y, 1)
		g = g * 2
	end

	while x > 0 do
		while band(x, 1) == 0 do
			x = rshift(x, 1)
		end

		while band(y, 1) == 0 do
			y = rshift(y, 1)
		end

		if x >= y then
			x = rshift(x - y, 1)
		else
			y = rshift(y - x, 1)
		end
	end

	return g * y
end

--- Returns `gcd(x, y)`, `p`, `q` such that `p * x + q * y = gcd(x, y)`.
---@param x mpn.limb
---@param y mpn.limb
---@return mpn.limb
---@return mpn.limb
---@return mpn.limb
---@nodiscard
function mpn.extgcd_11(x, y)
    __validate_limb(x)
    __validate_limb(y)
    if y == 0 then
        return x, 1, 0
    elseif x == 0 then
        return y, 0, 1
    end

    local g = 1
    while band(x, 1) == 0 and band(y, 1) == 0 do
        x = rshift(x, 1)
        y = rshift(y, 1)
        g = g * 2
    end

	local p, q, r, s = 1, 0, 0, 1
    while x > 0 do
        while band(x, 1) == 0 do
            x = rshift(x, 1)

			if band(p, 1) == 0 and band(q, 1) == 0 then
				p = rshift(p, 1)
				q = rshift(q, 1)
			else
				p = rshift(p + y, 1)
				q = rshift(q - x, 1)
			end
        end

        while band(y, 1) == 0 do
            y = rshift(y, 1)

			if band(r, 1) == 0 and band(s, 1) == 0 then
				r = rshift(r, 1)
				s = rshift(s, 1)
			else
				r = rshift(r + y, 1)
				s = rshift(s - x, 1)
			end
        end

        if x >= y then
            x = rshift(x - y, 1)
			p = p - r
			q = q - s
        else
            y = rshift(y - x, 1)
			r = r - p
			s = s - q
        end
    end

    return g * y, r, s
end

--- Returns `gcd(a[a0:n], y)`.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param y mpn.limb
---@return mpn.limb
---@nodiscard
function mpn.gcd_1(a, a0, n, y)
	__validate_source(a, a0, n)
	__validate_limb(y)
	assert(y > 0)

	local x = mpn.mod_1(a, a0, n, y)
	if y > x then
		return mpn.gcd_11(y, x)
	end

	return mpn.gcd_11(x, y)
end

--- Returns `gcd(a[a0:n], y)`, `p`, `q` such that `p * a + q * y = gcd(a[a0:n], y)`.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param y mpn.limb
---@return mpn.limb
---@return mpn.limb
---@return mpn.limb
---@nodiscard
function mpn.extgcd_1(a, a0, n, y)
	__validate_source(a, a0, n)
	__validate_limb(y)
	assert(y > 0)

	local x = mpn.mod_1(a, a0, n, y)
	if y > x then
		return mpn.extgcd_11(y, x)
	end

	return mpn.extgcd_11(x, y)
end


--- Computes `r[r0:an] = gcd(a[a0:an], b[b0:bn])`.
--- Clobbers both `a` and `b`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs
---@param b0 mpn.offset
---@param bn mpn.size
function mpn.gcd(r, r0, a, a0, an, b, b0, bn)
	__validate_dest(r, r0, an)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)

	if mpn.is_zero(b, b0, bn) then
		mpn.copyi(r, r0, a, a0, an)
		__validate_dest_suffix(r, r0, an)
		return an
	elseif mpn.is_zero(a, a0, an) then
		mpn.copyi(r, r0, b, b0, bn)
		__validate_dest_suffix(r, r0, bn)
		return bn
	end

	local i, j = 0, 0
	while band(a[a0 + 1], 1) == 0 do
		mpn.rshift(a, a0, a, a0, an, 1)
		i = i + 1
	end

	while band(b[b0 + 1], 1) == 0 do
		mpn.rshift(b, b0, b, b0, bn, 1)
		j = j + 1
	end

	local k = math.min(i, j)
	an = mpn.normalized_size(a, a0, an)
	bn = mpn.normalized_size(b, b0, bn)

	while true do
		assert(band(a[a0 + 1], 1) == 1)
		assert(band(b[b0 + 1], 1) == 1)

		if mpn.cmp(a, a0, an, b, b0, bn) >= 0 then
			a, b = b, a
			a0, b0 = b0, a0
			an, bn = bn, an
		end

		mpn.sub(b, b0, b, b0, bn, a, a0, an)

		assert(band(b[b0 + 1], 1) == 0)
		if mpn.is_zero(b, b0, bn) then
			local rn = mpn.lshift(r, r0, a, a0, an, k)
			__validate_dest_suffix(r, r0, an)
			return rn
		end

		while band(b[b0 + 1], 1) == 0 do
			mpn.rshift(b, b0, b, b0, bn, 1)
		end

		bn = mpn.normalized_size(b, b0, bn)
	end
end

--- Computes `r[r0:return] = a[a0:n] ^ y`. Returns the number of limbs in result.
---
--- Requires `r` must not alias `a`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param y mpn.limb
---@return mpn.size
function mpn.pow_1(r, r0, a, a0, n, y)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_limb(y)

	assert(not rawequal(r, a))

	if n == 0 then
		r[r0 + 1] = 1
		__validate_dest_suffix(r, r0, 1)
		return 1
	elseif y == 0 then
		r[r0 + 1] = 1
		__validate_dest_suffix(r, r0, 1)
		return 1
	end

	local rq = r
	local b, b0 = {}, 0
	local c, c0 = {}, 0
	local q, q0 = {}, 0

	mpn.copyi(c, c0, a, a0, n)

	-- find the first square we need to multiply by
	while y > 0 and band(y, 1) == 0 do
		mpn.sqr(b, b0, c, c0, n)
		c, c0, b, b0 = b, b0, c, c0
		n = mpn.normalized_size(c, c0, 2 * n)

		y = rshift(y, 1)
	end

	mpn.copyi(r, r0, c, c0, n)
	local rn = n

	mpn.sqr(b, b0, c, c0, n)
	c, c0, b, b0 = b, b0, c, c0
	n = mpn.normalized_size(c, c0, 2 * n)

	y = rshift(y, 1)

	while y > 0 do
		-- if the current bit is set, multiply by the current square
		if band(y, 1) ~= 0 then
			mpn.mul(q, q0, c, c0, n, r, r0, rn)
			r, r0, q, q0 = q, q0, r, r0
			rn = mpn.normalized_size(r, r0, rn + n)
		end

		-- square the current square
		mpn.sqr(b, b0, c, c0, n)
		c, c0, b, b0 = b, b0, c, c0
		n = mpn.normalized_size(c, c0, 2 * n)

		y = rshift(y, 1)
	end

	if r ~= rq then
		-- if we used a different result, copy it back
		mpn.copyi(rq, q0, r, r0, rn)
	end

	__validate_dest_suffix(r, r0, rn)
	return rn
end

--- Computes `r[r0:return] = a[a0:an] ^ b[b0:bn]`. Returns the number of limbs in result.
---
--- Requires `r` must not alias `a` or `b`, `a` must not alias `b`.
--- Clobbers `a` and `b`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs
---@param a0 mpn.offset
---@param an mpn.size
---@param b mpn.limbs
---@param b0 mpn.offset
---@param bn mpn.size
---@return mpn.size
function mpn.pow(r, r0, a, a0, an, b, b0, bn)
	__validate_dest(r, r0, an)
	__validate_source(a, a0, an)
	__validate_source(b, b0, bn)

	assert(not rawequal(r, a))
	assert(not rawequal(r, b))
	assert(not rawequal(a, b))

	if an == 0 then
		r[r0 + 1] = 1
		__validate_dest_suffix(r, r0, 1)
		return 1
	elseif bn == 0 then
		r[r0 + 1] = 1
		__validate_dest_suffix(r, r0, 1)
		return 1
	end

	local rq = r
	local ax, ax0 = {}, 0
	local ay, ay0 = {}, 0
	local bx, bx0 = {}, 0
	local q, q0 = {}, 0

	mpn.copyi(ay, ay0, a, a0, an)
	mpn.copyi(bx, bx0, b, b0, bn)

	-- find the first square we need to multiply by
	while not mpn.is_zero(bx, bx0, bn) and band(bx[bx0 + 1], 1) == 0 do
		mpn.sqr(ax, ax0, ay, ay0, an)
		ay, ay0, ax, ax0 = ax, ax0, ay, ay0
		an = mpn.normalized_size(ay, ay0, 2 * an)

		mpn.rshift(bx, bx0, bx, bx0, bn, 1)
		bn = mpn.normalized_size(bx, bx0, bn)
	end

	mpn.copyi(r, r0, ay, ay0, an)
	local rn = an

	mpn.sqr(ax, ax0, ay, ay0, an)
	ay, ay0, ax, ax0 = ax, ax0, ay, ay0
	an = mpn.normalized_size(ay, ay0, 2 * an)

	mpn.rshift(bx, bx0, bx, bx0, bn, 1)
	bn = mpn.normalized_size(bx, bx0, bn)

	while not mpn.is_zero(bx, bx0, bn) do
		-- if the current bit is set, multiply by the current square
		if band(bx[bx0 + 1], 1) ~= 0 then
			mpn.mul(q, q0, ay, ay0, an, r, r0, rn)
			r, r0, q, q0 = q, q0, r, r0
			rn = mpn.normalized_size(r, r0, rn + an)
		end

		-- square the current square
		mpn.sqr(ax, ax0, ay, ay0, an)
		ay, ay0, ax, ax0 = ax, ax0, ay, ay0
		an = mpn.normalized_size(ay, ay0, 2 * an)

		mpn.rshift(bx, bx0, bx, bx0, bn, 1)
		bn = mpn.normalized_size(bx, bx0, bn)
	end

	if r ~= rq then
		-- if we used a different result, copy it back
		mpn.copyi(rq, q0, r, r0, rn)
	end

	__validate_dest_suffix(r, r0, rn)
	return rn
end

--- Computes `r[r0:ceil(n/2)] = sqrt(s[s0:n])` and `e[e0:return] = s[s0:n] - (r[r0:] ^ 2)`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param e mpn.limbs
---@param e0 mpn.offset
---@param s mpn.limbs_const
---@param s0 mpn.offset
---@param n mpn.size
---@return mpn.size
function mpn.sqrtrem(r, r0, e, e0, s, s0, n)
	__validate_dest(r, r0, ceil(n / 2))
	__validate_dest(e, e0, n)
	__validate_source(s, s0, n)

	n = mpn.normalized_size(s, s0, n)

	-- naive binary search
	local x0, x0n = {}, 0
	local x1, x1n = {}, n
	mpn.copyi(x1, 0, s, s0, n)

	local m, mn = {}, 0
	local t, tn = {}, 0

	-- binary search for the square root
	while true do
		m[x1n + 1] = mpn.add(m, 0, x1, 0, x1n, x0, 0, x0n)
		mpn.rshift(m, 0, m, 0, x1n + 1, 1)
		mn = mpn.normalized_size(m, 0, x1n + 1)

		mpn.sqr(t, 0, m, 0, mn)
		tn = mpn.normalized_size(t, 0, 2 * mn)

		local cmp = mpn.cmp(t, 0, tn, s, s0, n)
		if cmp < 0 then
			x0, x0n, m, mn = m, mn, x0, x0n
		elseif cmp > 0 then
			x1, x1n, m, mn = m, mn, x1, x1n
		end

		if x1n - x0n <= 1 then
			local check = {}
			mpn.sub_1(check, 0, x1, 0, x1n, 1)

			if mpn.cmp(check, 0, x1n, x0, 0, x0n) == 0 then
				-- we have found the root, copy it to the result
				mpn.copyi(r, r0, x0, 0, x0n)

				if e then
					-- compute the remainder
					local overflow = mpn.sub(e, e0, s, s0, n, t, 0, tn)
					assert(overflow == 0)

					local en = mpn.normalized_size(e, e0, n)
					__validate_dest_suffix(e, e0, en)
					__validate_dest_suffix(r, r0, mn)
					return en
				end

				__validate_dest_suffix(r, r0, mn)
				return mpn.cmp(s, s0, n, t, 0, tn)
			end
		end
	end
end

--- Returns true if `a[a0:n]` is a perfect square.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@return boolean
---@nodiscard
function mpn.is_perfect_square(a, a0, n)
	__validate_source(a, a0, n)

	local r = {}
	local e = mpn.sqrtrem(r, 0, {}, 0, a, a0, n)
	return e == 0
end

--- Returns true if `a[a0:n]` is a power of two.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@return boolean
---@nodiscard
function mpn.is_power_of_two(a, a0, n)
	return mpn.popcount(a, a0, n) == 1
end

--- Returns the number of bits set in `a[a0:n]`.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@return mpn.bitcount
---@nodiscard
function mpn.popcount(a, a0, n)
	__validate_source(a, a0, n)

	local cnt = 0
	for i = 1, n do
		local w = a[a0 + i]
		while w > 0 do
			w = band(w, w - 1)
			cnt = cnt + 1
		end
	end

	return cnt
end

--- Returns `log2(a[a0:n])` rounded down to the nearest integer.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@return integer
function mpn.log2_floor(a, a0, n)
	__validate_source(a, a0, n)

	n = mpn.normalized_size(a, a0, n)
	if n == 0 then
		return -math.huge
	end

	local limb, x = a[a0 + n], 0
	while limb ~= 0 do
		limb = rshift(limb, 1)
		x = x + 1
	end

	return (n - 1) * LIMB_SIZE + x - 1
end

--- Returns `log2(a[a0:n])` rounded up to the nearest integer.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@return integer
function mpn.log2_ceil(a, a0, n)
	__validate_source(a, a0, n)

	n = mpn.normalized_size(a, a0, n)
	if n == 0 then
		return -math.huge
	end

	local limb, x = a[a0 + n], 0
	local non_exact = band(limb, limb - 1) ~= 0 -- if the limb is not a power of two, we need to round up

	while limb ~= 0 do
		limb = rshift(limb, 1)
		x = x + 1
	end

	if non_exact then
		return (n - 1) * LIMB_SIZE + x
	else -- we need to check that the rest of the number forms a power of two, otherwise round up
		for i = 1, n - 1 do
			if a[a0 + i] ~= 0 then
				return (n - 1) * LIMB_SIZE + x
			end
		end

		return (n - 1) * LIMB_SIZE + x - 1
	end
end

--- Stores the `width` bits starting at `idx` from `a[a0:n]` into `r[r0:n]`.
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@param idx mpn.size
---@param width mpn.size
function mpn.bextract(r, r0, a, a0, n, idx, width)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	assert(width >= 0, "width must be non-negative")

	if width == 0 then
		return 0
	end

	local limb_offset = rshift(idx, LIMB_SIZE)
	local inner_offset = band(idx, LIMB_MAX)

	local limb_width_max = ceil((width + inner_offset) / LIMB_SIZE)
	local limb_width = ceil(width / LIMB_SIZE)
	local limb_high = limb_width
	local available = math.max(0, n - limb_offset)
	local shift_n = math.min(limb_width_max, available)

	-- store the bits including any overflowed high bits in the result
	mpn.rshift(r, r0, a, a0 + limb_offset, shift_n, inner_offset)

	if limb_width_max ~= limb_width then
		r[r0 + limb_width_max] = 0
	end

	-- mask away the high bits we don't want
	local rem = width % LIMB_SIZE
	if rem ~= 0 then
		local high_mask = lshift(1, rem) - 1
		r[r0 + limb_high] = band(r[r0 + limb_high] or 0, high_mask)
	end

	__validate_dest_suffix(r, r0, limb_width)
	return limb_width
end

--- Computes `r[r0:n] = a[a0:n] & b[b0:n]`
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param n mpn.size
function mpn.band_n(r, r0, a, a0, b, b0, n)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_source(b, b0, n)

	for i = 1, n do
		r[r0 + i] = band(a[a0 + i], b[b0 + i])
	end

	__validate_dest_suffix(r, r0, n)
end

--- Computes `r[r0:n] = a[a0:n] | b[b0:n]`
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param n mpn.size
function mpn.bior_n(r, r0, a, a0, b, b0, n)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_source(b, b0, n)

	for i = 1, n do
		r[r0 + i] = bor(a[a0 + i], b[b0 + i])
	end

	__validate_dest_suffix(r, r0, n)
end

--- Computes `r[r0:n] = a[a0:n] ~ b[b0:n]`
---@param r mpn.limbs
---@param r0 mpn.offset
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param b mpn.limbs_const
---@param b0 mpn.offset
---@param n mpn.size
function mpn.bxor_n(r, r0, a, a0, b, b0, n)
	__validate_dest(r, r0, n)
	__validate_source(a, a0, n)
	__validate_source(b, b0, n)

	for i = 1, n do
		r[r0 + i] = bxor(a[a0 + i], b[b0 + i])
	end

	__validate_dest_suffix(r, r0, n)
end

--- Returns the index of the lowest `0` bit in `a[a0:n]`.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@return mpn.bitcount
function mpn.bscan0(a, a0, n)
	__validate_source(a, a0, n)

	for i = 1, n do
		local w = a[a0 + i]
		if w ~= LIMB_MAX then
			local idx = 0
			while true do
				if band(w, 1) == 0 then
					return (i - 1) * LIMB_SIZE + idx
				end
				w = rshift(w, 1)
				idx = idx + 1
			end
		end
	end

	return n * LIMB_SIZE -- all bits are set, return the next bit index
end

--- Returns the index of the lowest `1` bit in `a[a0:n]` or `infinity` if no such bit exists.
---@param a mpn.limbs_const
---@param a0 mpn.offset
---@param n mpn.size
---@return mpn.bitcount
function mpn.bscan1(a, a0, n)
	__validate_source(a, a0, n)

	for i = 1, n do
		local w = a[a0 + i]
		if w ~= 0 then
			local idx = 0
			while w > 0 do
				if band(w, 1) ~= 0 then
					return (i - 1) * LIMB_SIZE + idx
				end
				w = rshift(w, 1)
				idx = idx + 1
			end
		end
	end

	return math.huge
end

--- Returns the limb index and offset of bit `idx`.
---@return mpn.bitcount
---@return mpn.bitcount
function mpn.blimb(idx)
	local index = math.floor(idx / LIMB_SIZE) + 1
	local offset = idx % LIMB_SIZE
	return index, offset
end

return mpn
