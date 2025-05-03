--- Multiple Precision Integer Arithmetic

local bit = require("bit")
local mpn = require("mpn")

local max, min, abs, floor, ceil = math.max, math.min, math.abs, math.floor, math.ceil
local lshift, rshift, band, bor, bxor, bnot = bit.lshift, bit.rshift, bit.band, bit.bor, bit.bxor, bit.bnot

local LIMB_SIZE = mpn.LIMB_SIZE
local LIMB_RADIX = mpn.LIMB_RADIX
local LIMB_MAX = mpn.LIMB_MAX
local LIMB_NUMBER_PRECISION = mpn.LIMB_NUMBER_PRECISION

--- Given a number, return the truncated integer value.
---@param x number
---@return integer
local function scalarabs(x)
	return floor(abs(x))
end

--- Given a number, return the truncated integer value.
---@param x number
---@return integer
local function scalar(x)
	if x >= 0 then
		return floor(x)
	else
		return ceil(x)
	end
end

--- A multiple precision integer. Stored as an array of limbs, with the least
--- significant limb first.
---
--- Negative integers are represented in complement form, so the sign bit is
--- the high bit of the most significant limb
---@class mpz : mpn.limbs
---@field [0] mpn.size number of limbs in the integer
local mpz = {}
mpz.__index = mpz

--- Create a duplicate of the given multiple precision integer.
---@param a mpz
---@return mpz
---@nodiscard
function mpz.dup(a)
	local sz_sgn_a = a[0]
	local sz_a = abs(a[0])

	local r = setmetatable({ [0] = sz_sgn_a }, mpz)
	mpn.copyi(r, 0, a, 0, sz_a)
	return r
end

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
	n = scalarabs(n) -- truncate towards zero

	local sz = 0
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

	local sz_sgn_a = a[0]
	local sz = abs(a[0])

	for i = max(1, sz - LIMB_NUMBER_PRECISION + 1), sz do
		result = result + a[i] * LIMB_RADIX ^ (i - 1)
	end

	if sz_sgn_a < 0 then
		result = -result
	end

	return result
end

--- Returns true if the given integer is zero, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_zero(a)
	return mpn.is_zero(a, 0, abs(a[0]))
end

--- Returns true if the given integer is positive, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_positive(a)
	return a[0] > 0
end

--- Returns true if the given integer is negative, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_negative(a)
	return a[0] < 0
end

--- Returns true if the given integer is a perfect square, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_perfect_square(a)
	local sz_a = a[0]
	if sz_a <= 0 then
		return false
	end

	return mpn.is_perfect_square(a, 0, sz_a)
end

--- Returns true if the given integer is a power of two, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_power_of_two(a)
	local sz_a = a[0]
	if sz_a <= 0 then
		return false
	end

	return mpn.is_power_of_two(a, 0, sz_a)
end

--- Returns the sign of the given integer, -1 for negative, 0 for zero, and 1 for positive
---@param a mpz
---@return integer
---@nodiscard
function mpz.sign(a)
	local sgn_a = a[0]

	if sgn_a < 0 then
		return -1
	elseif sgn_a > 0 then
		return 1
	else
		return 0
	end
end

--- Compare the absolute values of two integers.
--- Returns -1 if `|a| < |b|`, 0 if `|a| == |b|`, and 1 if `|a| > |b|`.
---@param a mpz
---@param b mpz
---@return integer
---@nodiscard
function mpz.cmpabs(a, b)
	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	return mpn.cmp(a, 0, sz_a, b, 0, sz_b)
end

--- Compare the values of two integers.
--- Returns -1 if `a < b`, 0 if `a == b`, and 1 if `a > b`.
---@param a mpz
---@param b mpz
---@return integer
---@nodiscard
function mpz.cmp(a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	if sz_sgn_a < 0 == sz_sgn_b < 0 then
		local sz_a = abs(sz_sgn_a)
		local sz_b = abs(sz_sgn_b)

		if sz_sgn_a < 0 then -- (-a) - (-b) = b - a
			return mpn.cmp(b, 0, sz_b, a, 0, sz_a)
		else -- a - b
			return mpn.cmp(a, 0, sz_a, b, 0, sz_b)
		end
	elseif sz_sgn_a < 0 then -- (-a) - b is guaranteed to be negative
		return -1
	else -- a - (-b) is guaranteed to be positive
		return 1
	end
end

--- Negates the given integer.
---
--- `r = -a`
---@param r mpz
---@param a mpz
function mpz.neg(r, a)
	local sz_sgn = a[0]
	local sz = abs(sz_sgn)

	r[0] = -sz_sgn
	mpn.copyi(r, 0, a, 0, sz)
end

--- Computes the absolute value of the given integer.
---
--- `r = |a|`
---@param r mpz
---@param a mpz
function mpz.abs(r, a)
	local sz = abs(a[0])

	r[0] = sz
	mpn.copyi(r, 0, a, 0, sz)
end

--- Computes the sum of an integer and a scalar.
---
--- `r = a + y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.add_scalar(r, a, y)
	if y < 0 then
		return mpz.sub_scalar(r, a, -y)
	end

	y = scalarabs(y)
	if y > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.add(r, a, b)
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

--- Computes the sum of two integers.
---
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

--- Computes the subtraction of an integer and a scalar.
---
--- `r = a - y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.sub_scalar(r, a, y)
	if y < 0 then
		return mpz.add_scalar(r, a, -y)
	end

	y = scalarabs(y)
	if abs(y) > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.add(r, a, b)
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

--- Computes the subtraction of a scalar and an integer.
---
--- `r = x - b`
---@param r mpz
---@param x integer
---@param b mpz
function mpz.scalar_sub(r, x, b)
	error("todo")
end

--- Computes the subtraction of two integers.
---
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

--- Computes the product of an integer and a scalar.
---
--- `r = a * y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.mul_scalar(r, a, y)
	if abs(y) > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.mul(r, a, b)
	end

	local sz_sgn_a = a[0]
	local sz_a = abs(sz_sgn_a)

	local sgn_y = y < 0 and -1 or 1
	y = abs(y)

	local cy = mpn.mul_1(r, 0, a, 0, abs(sz_a), y)
	r[sz_a + 1] = cy
	if sz_sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_a + 1) * sgn_y
	else
		r[0] = mpn.normalized_size(r, 0, sz_a + 1) * sgn_y
	end
end

--- Computes the product of two integers.
---
--- `r = a * b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.mul(r, a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	local sz_a = abs(sz_sgn_a)
	local sz_b = abs(sz_sgn_b)

	if sz_a == 0 or sz_b == 0 then
		r[0] = 0
		return
	end

	local cy = mpn.mul(r, 0, a, 0, sz_a, b, 0, sz_b)
	r[sz_a + sz_b + 1] = cy

	if sz_sgn_a < 0 == sz_sgn_b < 0 then
		-- both are negative or both are positive
		r[0] = mpn.normalized_size(r, 0, sz_a + sz_b + 1)
	else
		-- one is negative and the other is positive
		r[0] = -mpn.normalized_size(r, 0, sz_a + sz_b + 1)
	end
end

--- Computes the square of a scalar.
---
--- `r = x * x`
---@param r mpz
---@param x integer
function mpz.sqr_scalar(r, x)
	local a = mpz.from_number(x)
	return mpz.sqr(r, a)
end

--- Computes the square of an integer.
---
--- `r = a * a`
---@param r mpz
---@param a mpz
function mpz.sqr(r, a)
	local sz_sgn_a = a[0]
	local sz_a = abs(sz_sgn_a)

	if sz_a == 0 then
		r[0] = 0
		return
	end

	mpn.sqr(r, 0, a, 0, sz_a)
	r[0] = mpn.normalized_size(r, 0, 2 * sz_a)
end

--- Computes the arithmetic left shift of an integer by a given number of bits.
---
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

--- Computes the arithmetic right shift of an integer by a given number of bits.
---
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

--- Computes the truncated division and remainder of `a / y`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * y + r`, where `0 <= |r| < |y|` and `sign(r) = sign(a)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param y integer
function mpz.divrem_scalar(q, r, a, y)
	if abs(y) > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.divrem(q, r, a, b)
	end

	local sz_sgn_a = a[0]
	local sz_a = abs(sz_sgn_a)

	r[1] = mpn.divmod_1(q, 0, a, 0, sz_a, abs(y))
	if sz_sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, 1)
	else
		r[0] = mpn.normalized_size(r, 0, 1)
	end

	if sz_sgn_a < 0 == y < 0 then
		q[0] = mpn.normalized_size(q, 0, sz_a)
	else
		q[0] = -mpn.normalized_size(q, 0, sz_a)
	end
end

--- Computes the truncated division and remainder of `a / b`.
---
--- Clobbers `a`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(a)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.divrem_clobber(q, r, a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	local sz_a = abs(sz_sgn_a)
	local sz_b = abs(sz_sgn_b)
	local sz_q = sz_a - sz_b + 1

	mpn.divmod(q, 0, r, 0, a, 0, sz_a, b, 0, sz_b)
	if sz_sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_b)
	else
		r[0] = mpn.normalized_size(r, 0, sz_b)
	end

	if sz_sgn_a < 0 == sz_sgn_b < 0 then
		q[0] = mpn.normalized_size(q, 0, sz_q)
	else
		q[0] = -mpn.normalized_size(q, 0, sz_q)
	end
end

--- Computes the truncated division remainder of `a / b`.
---
--- Clobbers `a`.
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.rem_clobber(r, a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	local sz_a = abs(sz_sgn_a)
	local sz_b = abs(sz_sgn_b)
	local sz_q = sz_a - sz_b + 1

	mpn.mod(r, 0, a, 0, sz_a, b, 0, sz_b)
	if sz_sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_b)
	else
		r[0] = mpn.normalized_size(r, 0, sz_b)
	end
end

--- Computes the truncated division and remainder of `a / b`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(a)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.divrem(q, r, a, b)
	a = mpz.dup(a)
	return mpz.divrem_clobber(q, r, a, b)
end

--- Computes the truncated division remainder of `a / b`.
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.rem(r, a, b)
	a = mpz.dup(a)
	return mpz.rem_clobber(r, a, b)
end

--- Computes the floored division and remainder of `a / y`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * y + r`, where `0 <= |r| < |y|` and `sign(r) = sign(y)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param y integer
function mpz.divmod_scalar(q, r, a, y)
	mpz.divrem_scalar(q, r, a, y)

	local sz_sgn_a = a[0]
	if sz_sgn_a >= 0 and y > 0 then
		-- a is positive and y is positive, so we can use the result directly
		return
	elseif sz_sgn_a > 0 and y < 0 and r[0] ~= 0 then
		-- a is positive and y is negative, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r[0] = abs(r[0])
		mpz.sub_scalar(r, r, y)
	elseif sz_sgn_a < 0 and y > 0 and r[0] ~= 0 then
		-- a is negative and y is positive, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r[0] = -abs(r[0])
		mpz.add_scalar(r, r, y)
	elseif sz_sgn_a < 0 and y < 0 then
		-- a is negative and y is negative, q is correct, r must be negative
		r[0] = -abs(r[0])
	end
end

--- Computes the floored division and remainder of `a / y`.
---
--- Clobbers `a`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(a)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.divmod_clobber(q, r, a, b)
	mpz.divrem(q, r, a, b)

	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	if sz_sgn_a >= 0 and sz_sgn_b > 0 then
		-- a is positive and b is positive, so we can use the result directly
		return
	elseif sz_sgn_a > 0 and sz_sgn_b < 0 and r[0] ~= 0 then
		-- a is positive and b is negative, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r[0] = abs(r[0])
		mpz.sub(r, r, b)
	elseif sz_sgn_a < 0 and sz_sgn_b > 0 and r[0] ~= 0 then
		-- a is negative and b is positive, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r[0] = -abs(r[0])
		mpz.add(r, r, b)
	elseif sz_sgn_a < 0 and sz_sgn_b < 0 then
		-- a is negative and v is negative, q is correct, r must be negative
		r[0] = -abs(r[0])
	end
end

--- Computes the floored division remainder of `a / y`.
---
--- Clobbers `a`.
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.mod_clobber(r, a, b)
	mpz.rem_clobber(r, a, b)

	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	if sz_sgn_a >= 0 and sz_sgn_b > 0 then
		-- a is positive and b is positive, so we can use the result directly
		return
	elseif sz_sgn_a > 0 and sz_sgn_b < 0 and r[0] ~= 0 then
		-- a is positive and b is negative, q is negative and needs to be fixed
		r[0] = abs(r[0])
		mpz.sub(r, r, b)
	elseif sz_sgn_a < 0 and sz_sgn_b > 0 and r[0] ~= 0 then
		-- a is negative and b is positive, q is negative and needs to be fixed
		r[0] = -abs(r[0])
		mpz.add(r, r, b)
	elseif sz_sgn_a < 0 and sz_sgn_b < 0 then
		-- a is negative and v is negative, q is correct, r must be negative
		r[0] = -abs(r[0])
	end
end

--- Computes the floored division and remainder of `a / y`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(a)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.divmod(q, r, a, b)
	a = mpz.dup(a)
	return mpz.divmod_clobber(q, r, a, b)
end

--- Computes the floored division remainder of `a / y`.
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.mod(r, a, b)
	a = mpz.dup(a)
	return mpz.mod_clobber(r, a, b)
end

--- Computes the greatest common divisor of an integer and a scalar.
---
--- `r = gcd(a, y)`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.gcd_scalar(r, a, y)
	y = abs(y)

	if y > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.gcd(r, a, b)
	end

	local sz_a = abs(a[0])
	r[1] = mpn.gcd_1(a, 0, sz_a, y)
	r[0] = 1
end

--- Computes the greatest common divisor of two integers.
---
--- Clobbers `a` and `b`.
---
--- `r = gcd(a, b)`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.gcd_clobber(r, a, b)
	local sz_a = abs(a[0])
	local sz_b = abs(b[0])
	mpn.gcd(r, 0, a, 0, sz_a, b, 0, sz_b)
end

--- Computes the greatest common divisor of two integers.
---
--- `r = gcd(a, b)`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.gcd(r, a, b)
	a = mpz.dup(a)
	b = mpz.dup(b)
	return mpz.gcd_clobber(r, a, b)
end

--- Computes the exponentiation of an integer to a scalar power.
---
--- `r = a ^ y`
---@param r mpz
---@param a mpz
---@param y integer
function mpz.pow_scalar(r, a, y)
	if y < 0 then
		r[0] = 0
		return
	elseif y == 0 then
		r[0] = 1
		return
	end

	y = scalar(y)
	if y > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.pow(r, a, b)
	end

	local sz_sgn_a = a[0]
	local sz_a = abs(sz_sgn_a)

	local n = mpn.pow_1(r, 0, a, 0, sz_a, y)
	if sz_sgn_a < 0 and band(y, 1) == 1 then -- negative and odd power
		r[0] = -mpn.normalized_size(r, 0, n)
	else
		r[0] = mpn.normalized_size(r, 0, n)
	end
end

--- Computes the exponentiation of an integer to an integer power.
--- Clobbers `b`.
---
--- `r = a ^ b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.pow_clobber(r, a, b)
	local sz_sgn_a = a[0]
	local sz_sgn_b = b[0]

	if sz_sgn_b < 0 then
		r[0] = 0
		return
	elseif sz_sgn_b == 0 then
		r[0] = 1
		return
	end

	local sz_a = abs(sz_sgn_a)
	local sz_b = abs(sz_sgn_b)

	local n = mpn.pow(r, 0, a, 0, sz_a, b, 0, sz_b)
	if sz_sgn_a < 0 and band(b[1], 1) == 1 then -- negative and odd power
		r[0] = -mpn.normalized_size(r, 0, n)
	else
		r[0] = mpn.normalized_size(r, 0, n)
	end
end

--- Computes the exponentiation of an integer to an integer power.
---
--- `r = a ^ b`
---@param r mpz
---@param a mpz
---@param b mpz
function mpz.pow(r, a, b)
	b = mpz.dup(b)
	return mpz.pow_clobber(r, a, b)
end

--- Computes the square root and remainder of an integer.
---
--- `s = floor(sqrt(a))` and `r = a - s * s`.
---
--- If `a` is negative, sets `s = 0` and `r = 0`.
---@param s mpz
---@param r mpz
---@param a mpz
function mpz.sqrtrem(s, r, a)
	local sz_sgn_a = a[0]
	if sz_sgn_a <= 0 then
		s[0] = 0
		r[0] = 0
		return
	end

	local sz_a = abs(sz_sgn_a)
	local r_n = mpn.sqrtrem(s, 0, r, 0, a, 0, sz_a)

	s[0] = mpn.normalized_size(s, 0, ceil(sz_a / 2))
	r[0] = mpn.normalized_size(r, 0, r_n)
end

--- Computes the number of bits set in an integer.
---
--- This is always infinite for negative integers.
---@param a mpz
---@return integer
---@nodiscard
function mpz.popcount(a)
	local sz_sgn_a = a[0]
	if sz_sgn_a < 0 then
		return math.huge
	end

	local sz_a = abs(sz_sgn_a)
	return mpn.popcount(a, 0, sz_a)
end

--- Computes `floor(log2(abs(a)))`, the largest integer `k` such that `2^k <= |a|`.
---@param a mpz
---@return integer
---@nodiscard
function mpz.log2_floor(a)
	local sz_a = abs(a[0])
	return mpn.log2_floor(a, 0, sz_a)
end

--- Computes `ceil(log2(abs(a)))`, the smallest integer `k` such that `2^k > |a|`.
---@param a mpz
---@return integer
---@nodiscard
function mpz.log2_ceil(a)
	local sz_a = abs(a[0])
	return mpn.log2_ceil(a, 0, sz_a)
end

--- Returns `true` if the bit at index `idx` is set, `false` otherwise.
---@param a mpz
---@param idx mpn.bitcount
---@return boolean
---@nodiscard
function mpz.btest(a, idx)
	local sz_sgn_a = a[0]
	local sz_a = abs(sz_sgn_a)

	local lmb, off = mpn.blimb(idx)
    if sz_sgn_a <= 0 then
		if lmb > sz_a then
			return true
		end

		-- twos complement negation has the effect of flipping all bits above the first 1 bit.
        local flipped = mpn.bscan1(a, 0, lmb)
		if idx >= flipped then
			return band(a[lmb], lshift(1, off)) ~= 0
        else
			return band(a[lmb], lshift(1, off)) == 0
		end
	else
		if lmb > sz_a then
			return false
		end

		return band(a[lmb], lshift(1, off)) ~= 0
	end
end

--- Sets the bit at index `idx` to 1.
---@param a mpz
function mpz.bset(a, idx)
	local sz_sgn_a = a[0]
	local sz_a = abs(sz_sgn_a)

	local lmb, off = mpn.blimb(idx)
	if lmb > sz_a then
		mpn.zero(a, sz_a, lmb - sz_a)
	end

	sz_a = min(sz_a, lmb)
	if sz_sgn_a < 0 then
		-- convert to twos complement form
		mpn.bnot_n(a, 0, a, 0, sz_a)
		mpn.add_1(a, 0, a, 0, sz_a, 1)
	end

	a[lmb] = bor(a[lmb], lshift(1, off))

	if sz_sgn_a < 0 then
		-- convert back to magnitude
		mpn.bnot_n(a, 0, a, 0, sz_a)
		mpn.add_1(a, 0, a, 0, sz_a, 1)
	end
end

--- Sets the bit at index `idx` to 0.
---@param a mpz
function mpz.bclear(a, idx) end

--- Inverts the bit at index `idx` from `0 -> 1` or `1 -> 0`.
---@param a mpz
function mpz.binvert(a, idx) end

function mpz.bextract(r, a, idx, width)
	error("todo")
end

function mpz.band(r, a, b)
	-- r = (+a) & (+b) = (+a) & (+b)
	-- r = (-a) & (+b)
	-- r = (+a) & (-b)
	-- r = (-a) & (-b) = (~(+a) + 1) & (~(+a) + 1)

	error("todo")
end

function mpz.bor(r, a, b)
	error("todo")
end

function mpz.bxor(r, a, b)
	error("todo")
end

--- Computes the bitwise NOT of an integer.
---
--- `r = ~a`
---@param r mpz
---@param a mpz
function mpz.bnot(r, a)
	-- r = ~(+a) = -(+a) - 1 = (-a) - 1
	-- r = ~(-a) = -(-a) - 1 = (+a) - 1

	local sz_sgn_a = a[0]
	local sz_a = abs(sz_sgn_a)

	a[0] = -sz_sgn_a -- flip sign
	mpn.sub_1(r, 0, a, 0, sz_a, 1) -- subtract 1
end
