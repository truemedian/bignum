--- Multiple Precision Integer Arithmetic

local bit = require("bit")
local mpn = require("mpn")

local max, min, abs, floor, ceil = math.max, math.min, math.abs, math.floor, math.ceil
local lshift, rshift, band, bor, bxor, bnot = bit.lshift, bit.rshift, bit.band, bit.bor, bit.bxor, bit.bnot

local LIMB_SIZE = mpn.LIMB_SIZE
local LIMB_RADIX = mpn.LIMB_RADIX
local LIMB_MAX = mpn.LIMB_MAX
local LIMB_NUMBER_PRECISION = mpn.LIMB_NUMBER_PRECISION

--- A multiple precision integer. Stored as an array of limbs, with the least
--- significant limb first.
---
--- Negative integers are represented in complement form, so the sign bit is
--- the high bit of the most significant limb
---@class mpz : mpn.limbs
---@field [0] mpn.size number of limbs in the integer
local mpz = {}
mpz.__index = mpz

--- Create a new multiple precision integer with the value of zero.
---@return mpz
---@nodiscard
function mpz.from_zero()
	return setmetatable({ [0] = 0 }, mpz)
end

--- Create a new multiple precision integer with the value of positive one.
---@return mpz
---@nodiscard
function mpz.from_one()
	return setmetatable({ [0] = 1, 1 }, mpz)
end

--- Create a new multiple precision integer with the value of `n`.
---@param n integer
---@return mpz
---@nodiscard
function mpz.from_number(n)
	local zr = mpz.from_zero()

	local sgn = n < 0 and -1 or 1
	n = floor(abs(n)) -- truncate towards zero

	local sz = 1
	while n > 0 do
		sz = sz + 1

		zr[sz] = bit.band(n, LIMB_MAX)
		n = floor(n / LIMB_RADIX)
	end

	zr[0] = sz * sgn
	return zr
end

--- Return a number approximation of the given integer. The value will only be exact within the integral range of a
--- Lua number, which is generally [-2^53, 2^53].
---@param a mpz
---@return number
---@nodiscard
function mpz.to_number(a)
	local result = 0

	local sz = abs(a[0])
	local sgn = a[0] < 0 and -1 or 1

	for i = max(1, sz - LIMB_NUMBER_PRECISION + 1), sz do
		result = result + a[i] * LIMB_RADIX ^ (i - 1)
	end

	return result * sgn
end

--- Returns the sign of the given integer, -1 for negative, 0 for zero, and 1 for positive
---@param a mpz
---@return integer
function mpz.sign(a)
	local sz = a[0]

	if sz < 0 then
		return -1
	elseif sz > 0 then
		return 1
	else
		return 0
	end
end

function mpz.cmpabs(a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	for i = max(1, sz_a - LIMB_NUMBER_PRECISION + 1), sz_a do
		if a[i] < b[i] then
			return -1
		elseif a[i] > b[i] then
			return 1
		end
	end

	return 0
end

function mpz.cmp(a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	for i = max(1, sz_a - LIMB_NUMBER_PRECISION + 1), sz_a do
		if a[i] < b[i] then
			return -1
		elseif a[i] > b[i] then
			return 1
		end
	end

	return 0
end

--- `r = -a`
---@param r mpz
---@param a mpz
function mpz.neg(r, a)
	local sz_sgn = a[0]
	local sz = abs(sz_sgn)

	r[0] = -sz_sgn
	mpn.copyi(r, 0, a, 0, sz)
end

--- `r = |a|`
---@param r mpz
---@param a mpz
function mpz.abs(r, a)
	local sz_sgn = a[0]
	local sz = abs(sz_sgn)

	r[0] = sz
	mpn.copyi(r, 0, a, 0, sz)
end

--- `r = a + y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.add_scalar(r, a, y)
	if abs(y) > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.add(r, a, b)
	elseif y < 0 then
		return mpz.sub_scalar(r, a, -y)
	end

	local sz_sgn_a = a[0]
	local sz_a = abs(a[0])

	if sz_sgn_a >= 0 then
		local carry = mpn.add_1(r, 0, a, 0, sz_a, y)
		r[sz_a + 1] = carry
		r[0] = sz_a + carry
	else -- a is negative
		if sz_a == 1 and r[1] < y then -- sign flip
			r[1] = y - r[1]
			r[0] = 1
		else
			mpn.sub_1(r, 0, a, 0, sz_a, y)
			r[0] = -mpn.normalized_size(r, 0, sz_a)
		end
	end
end

--- `r = a + b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.add(r, a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	local sz_a = abs(sz_sgn_a)
	local sz_b = abs(sz_sgn_b)

	if sz_a < sz_b then
		a, b = b, a
		sz_a, sz_b = sz_b, sz_a
		sz_sgn_a, sz_sgn_b = sz_sgn_b, sz_sgn_a
	end

	-- assert(sz_a >= sz_b)

	local sgn_a = sz_sgn_a < 0 and -1 or 1
	local sgn_b = sz_sgn_b < 0 and -1 or 1

	if sgn_a ~= sgn_b then
		if sz_a ~= sz_b then
			mpn.sub(r, 0, a, 0, sz_a, b, 0, sz_b)
			r[0] = sgn_a * mpn.normalized_size(r, 0, sz_a)
		else -- sz_a == sz_b
			local cmp = mpn.cmp_n(a, 0, b, 0, sz_a)
			if cmp < 0 then
				mpn.sub_n(r, 0, b, 0, a, 0, sz_a)
				r[0] = -sgn_a * mpn.normalized_size(r, 0, sz_a)
			elseif cmp > 0 then
				mpn.sub_n(r, 0, a, 0, b, 0, sz_a)
				r[0] = sgn_a * mpn.normalized_size(r, 0, sz_a)
			else
				r[0] = 0
			end
		end
	else
		local cy = mpn.add(r, 0, a, 0, sz_a, b, 0, sz_b)
		r[sz_a + 1] = cy
		r[0] = sgn_a * (sz_a + cy)
	end
end

--- `r = a - y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.sub_scalar(r, a, y)
	if abs(y) > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.add(r, a, b)
	elseif y < 0 then
		return mpz.sub_scalar(r, a, -y)
	end

	local sz_sgn_a = a[0]
	local sz_a = abs(a[0])

	if sz_sgn_a >= 0 then
		local carry = mpn.add_1(r, 0, a, 0, sz_a, y)
		r[sz_a + 1] = carry
		r[0] = -sz_a - carry
	else -- a is negative
		if sz_a == 1 and r[1] < y then -- sign flip
			r[1] = y - r[1]
			r[0] = -1
		else
			mpn.sub_1(r, 0, a, 0, sz_a, y)
			r[0] = mpn.normalized_size(r, 0, sz_a)
		end
	end
end

--- `r = x - b`
---@param r mpz
---@param x integer
---@param b mpz
function mpz.scalar_sub(r, x, b)
	error("todo")
end

--- `r = a - b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.sub(r, a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = -b[0]

	local sz_a = abs(sz_sgn_a)
	local sz_b = abs(sz_sgn_b)

	if sz_a < sz_b then
		a, b = b, a
		sz_a, sz_b = sz_b, sz_a
		sz_sgn_a, sz_sgn_b = sz_sgn_b, sz_sgn_a
	end

	-- assert(sz_a >= sz_b)

	local sgn_a = sz_sgn_a < 0 and -1 or 1
	local sgn_b = sz_sgn_b < 0 and -1 or 1

	if sgn_a ~= sgn_b then
		if sz_a ~= sz_b then
			mpn.sub(r, 0, a, 0, sz_a, b, 0, sz_b)
			r[0] = sgn_a * mpn.normalized_size(r, 0, sz_a)
		else -- sz_a == sz_b
			local cmp = mpn.cmp_n(a, 0, b, 0, sz_a)
			if cmp < 0 then
				mpn.sub_n(r, 0, b, 0, a, 0, sz_a)
				r[0] = -sgn_a * mpn.normalized_size(r, 0, sz_a)
			elseif cmp > 0 then
				mpn.sub_n(r, 0, a, 0, b, 0, sz_a)
				r[0] = sgn_a * mpn.normalized_size(r, 0, sz_a)
			else
				r[0] = 0
			end
		end
	else
		local cy = mpn.add(r, 0, a, 0, sz_a, b, 0, sz_b)
		r[sz_a + 1] = cy
		r[0] = sgn_a * (sz_a + cy)
	end
end

--- `r = a * y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.mul_scalar(r, a, y) end

--- `r = a * b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.mul(r, a, b) end

--- `r += a * y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.addmul_scalar(r, a, y) end

--- `r += a * b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.addmul(r, a, b) end

--- `r -= a * y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.submul_scalar(r, a, y) end

--- `r -= a * b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.submul(r, a, b) end

--- `r = a << y = a * 2 ^ y`
---@param r mpz
---@param a mpz
---@param y mpn.bitcount
function mpz.lshift(r, a, y)
	local szsgn_a = a[0]
	local sz_a = abs(szsgn_a)

	mpn.lshift(r, 0, a, 0, sz_a, y)

	if szsgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_a)
	else
		r[0] = mpn.normalized_size(r, 0, sz_a)
	end
end

--- `r = a >> y = a / 2 ^ y`
---@param r mpz
---@param a mpz
---@param y mpn.bitcount
function mpz.rshift(r, a, y)
	local szsgn_a = a[0]
	local sz_a = abs(szsgn_a)

	mpn.rshift(r, 0, a, 0, sz_a, y)

	if szsgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_a)
	else
		r[0] = mpn.normalized_size(r, 0, sz_a)
	end
end
