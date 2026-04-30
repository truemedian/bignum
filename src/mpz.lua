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

--- Create a new multiple precision integer with the value of `a`.
---
--- Returns 'r' for convenience.
---@param r mpz
---@param a mpz
---@return mpz
function mpz.clone(r, a)
	r[0] = a[0]
	mpn.copyi(r, 0, a, 0, abs(a[0]))
	return r
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

local digits = {}
for i = 0, 9 do
	digits[i] = string.char(48 + i)
end
for i = 10, 35 do
	digits[i] = string.char(87 + i)
end

--- Returns a string representation of the given integer.
---@param a mpz
---@param base? integer
---@return string
---@nodiscard
function mpz.to_string(a, base)
	base = base or 10
	assert(base >= 2 and base <= 36, "base must be between 2 and 36")

	-- the rest of the function assumes a has at least one non-zero limb
	if mpz.is_zero(a) then
		return "0"
	end

	local num = mpz.dup(a)

	local result = {}
	while not mpz.is_zero(num) do
		local digit = mpz.divrem_scalar(num, num, base)

		result[#result + 1] = digits[abs(digit)]
	end

	local n = #result
	for i = 1, n / 2 do
		result[i], result[n - i + 1] = result[n - i + 1], result[i]
	end

	if a[0] < 0 then
		return "-" .. table.concat(result)
	else
		return table.concat(result)
	end
end

--- Returns true if the given integer is zero, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_zero(a)
	return mpn.is_zero(a, 0, abs(a[0]))
end

--- Returns true if the given integer is one or negative one, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_one(a)
	local sz_a = abs(a[0])
	return sz_a == 1 and a[1] == 1
end

--- Returns true if the given integer is positive, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_positive(a)
	return a[0] > 0 and mpn.is_nonzero(a, 0, a[0])
end

--- Returns true if the given integer is negative, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_negative(a)
	return a[0] < 0 and mpn.is_nonzero(a, 0, abs(a[0]))
end

--- Returns true if the given integer is a perfect square, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_perfect_square(a)
	if not mpz.is_positive(a) then
		return false
	end

	local sz_a = a[0]
	return mpn.is_perfect_square(a, 0, sz_a)
end

--- Returns true if the given integer is a power of two, false otherwise.
---@param a mpz
---@return boolean
---@nodiscard
function mpz.is_power_of_two(a)
	if not mpz.is_positive(a) then
		return false
	end

	local sz_a = a[0]
	return mpn.is_power_of_two(a, 0, sz_a)
end

--- Returns the sign of the given integer, -1 for negative, 0 for zero, and 1 for positive
---@param a mpz
---@return integer
---@nodiscard
function mpz.sign(a)
	if mpz.is_zero(a) then
		return 0
	elseif a[0] < 0 then
		return -1
	else
		return 1
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
	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if sgn_a == sgn_b then
		return mpz.cmpabs(a, b) * sgn_a
	elseif sgn_a < 0 then
		return -1
	elseif sgn_a == 0 then
		return -sgn_b
	else
		return 1
	end
end

--- Negates the given integer in place.
---
--- Returns `r` for convenience.
---
--- `r = -r`
---@param r mpz
---@return mpz
function mpz.neg(r)
	r[0] = -r[0]
	return r
end

--- Negates the given integer.
---
--- `a` may alias `r`, but you should consier using `mpz.neg` instead.
---
--- Returns `r` for convenience.
---
--- `r = -a`
---@param r mpz
---@param a mpz
---@return mpz
function mpz.negate(r, a)
	local sz_sgn = a[0]
	local sz = abs(a[0])

	r[0] = -sz_sgn
	mpn.copyi(r, 0, a, 0, sz)
	return r
end

--- Computes the absolute value of the given integer.
---
--- Returns `r` for convenience.
---
--- `r = |r|`
---@param r mpz
---@return mpz
function mpz.abs(r)
	r[0] = abs(r[0])
	return r
end

--- Computes the absolute value of the given integer.
---
--- `a` may alias `r`, but you should consier using `mpz.neg` instead.
---
--- Returns `r` for convenience.
---
--- `r = |a|`
---@param r mpz
---@param a mpz
function mpz.absolute(r, a)
	local sz = abs(a[0])

	r[0] = sz
	mpn.copyi(r, 0, a, 0, sz)
	return r
end

--- Computes the sum of an integer and a scalar.
---
--- `a` may alias `r`.
---
--- Returns `r` for convenience.
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
		r[0] = mpn.normalized_size(r, 0, sz_a + 1)
	else -- a is negative
		if sz_a == 1 and a[1] < y then -- sign flip
			r[1] = y - a[1]
			r[0] = 1
		else
			mpn.sub_1(r, 0, a, 0, sz_a, y)
			r[0] = -mpn.normalized_size(r, 0, sz_a)
		end
	end

	return r
end

--- Computes the sum of two integers.
---
--- `a` may alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a + b`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.add(r, a, b)
	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	if sz_a < sz_b then
		a, b = b, a
		sz_a, sz_b = sz_b, sz_a
	end

	-- assert(sz_a >= sz_b) --> mpn.add and mpn.sub require that the first argument is larger.

	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

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
		r[0] = sgn_a * mpn.normalized_size(r, 0, sz_a + cy)
	end

	return r
end

--- Computes the subtraction of an integer and a scalar.
---
--- `a` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a - y`
---@param r mpz
---@param a mpz
---@param y integer
---@return mpz
function mpz.sub_scalar(r, a, y)
	if y < 0 then
		return mpz.add_scalar(r, a, -y)
	end

	y = scalar(y)
	if y > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.sub(r, a, b)
	end

	local sgn_a = mpz.sign(a)
	local sz_a = abs(a[0])

	if sgn_a > 0 then
		local cmp = mpn.cmp_1(a, 0, sz_a, y)
		if cmp > 0 then -- |a| > |y|
			mpn.sub_1(r, 0, a, 0, sz_a, y)
			r[0] = mpn.normalized_size(r, 0, sz_a)
		elseif cmp < 0 then -- |y| > |a|
			r[1] = y - a[1]
			r[0] = -1
		else
			r[0] = 0
		end
	else -- a is negative
		local carry = mpn.add_1(r, 0, a, 0, sz_a, y)
		r[sz_a + 1] = carry
		r[0] = -mpn.normalized_size(r, 0, sz_a + 1)
	end

	return r
end

--- Computes the subtraction of a scalar and an integer.
---
--- `b` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = x - b`
---@param r mpz
---@param x integer
---@param b mpz
function mpz.scalar_sub(r, x, b)
	if x < 0 then
		mpz.add_scalar(r, b, -x)
		return mpz.neg(r)
	end

	x = scalarabs(x)
	if x > LIMB_MAX then
		local a = mpz.from_number(x)
		return mpz.sub(r, a, b)
	end

	local sz_sgn_b = b[0]
	local sz_b = abs(b[0])

	if sz_sgn_b > 0 then
		local cmp = mpn.cmp_1(b, 0, sz_b, x)
		if cmp > 0 then -- |b| > |x|
			mpn.sub_1(r, 0, b, 0, sz_b, x)
			r[0] = -mpn.normalized_size(r, 0, sz_b)
		elseif cmp < 0 then -- |x| > |b|
			r[1] = x - b[1]
			r[0] = 1
		else
			r[0] = 0
		end
	else -- b is negative
		local carry = mpn.add_1(r, 0, b, 0, sz_b, x)
		r[sz_b + 1] = carry
		r[0] = mpn.normalized_size(r, 0, sz_b + 1)
	end

	return r
end

--- Computes the subtraction of two integers.
---
--- `a` may alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a - b`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.sub(r, a, b)
	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if sgn_a == 0 then
		return mpz.negate(r, b)
	elseif sgn_b == 0 then
		return mpz.clone(r, a)
	elseif sgn_a ~= sgn_b then
		-- a - (-b) = a + b
		-- (-a) - b = -(a + b)
		if sz_a < sz_b then
			a, b = b, a
			sz_a, sz_b = sz_b, sz_a
			-- do not swap signs, necessary for correct result sign
		end

		local cy = mpn.add(r, 0, a, 0, sz_a, b, 0, sz_b)
		r[sz_a + 1] = cy
		r[0] = sgn_a * mpn.normalized_size(r, 0, sz_a + cy)
		return r
	else
		local cmp = mpn.cmp(a, 0, sz_a, b, 0, sz_b)
		if cmp < 0 then -- |b| > |a|
			mpn.sub(r, 0, b, 0, sz_b, a, 0, sz_a)
			r[0] = -sgn_a * mpn.normalized_size(r, 0, sz_b)
		elseif cmp > 0 then -- |a| > |b|
			mpn.sub(r, 0, a, 0, sz_a, b, 0, sz_b)
			r[0] = sgn_a * mpn.normalized_size(r, 0, sz_a)
		else
			r[0] = 0
		end
	end

	return r
end

--- Computes the product of an integer and a scalar.
---
--- `a` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a * y`
---@param r mpz
---@param a mpz
---@param y integer
---@return mpz
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

	return r
end

--- Computes the product of two integers.
---
--- `a` may alias `b`.
--- `a` MUST NOT alias `r`.
--- `b` MUST NOT alias `r`.
---
---	Returns `r` for convenience.
---
--- `r = a * b`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.mul_noalias(r, a, b)
	assert(not rawequal(r, a), "aliasing detected")
	assert(not rawequal(r, b), "aliasing detected")

	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if sgn_a == 0 or sgn_b == 0 then
		r[0] = 0
		return r
	end

	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	if sz_a < sz_b then
		a, b = b, a
		sz_a, sz_b = sz_b, sz_a
		sgn_a, sgn_b = sgn_b, sgn_a
	end

	mpn.mul(r, 0, a, 0, sz_a, b, 0, sz_b)
	if sgn_a == sgn_b then
		-- both are negative or both are positive, result is positive
		r[0] = mpn.normalized_size(r, 0, sz_a + sz_b)
	else
		-- one is negative and the other is positive, result is negative
		r[0] = -mpn.normalized_size(r, 0, sz_a + sz_b)
	end

	return r
end

--- Computes the product of two integers.
---
--- `a` may alias `b`.
--- `a` may alias `r`, however it will incur the cost of a duplication.
--- `b` may alias `r`, however it will incur the cost of a duplication.
---
---	Returns `r` for convenience.
---
--- `r = a * b`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.mul(r, a, b)
	if rawequal(r, a) then
		a = mpz.dup(a)
	end

	if rawequal(r, b) then
		b = mpz.dup(b)
	end

	return mpz.mul_noalias(r, a, b)
end

--- Computes the square of a scalar.
---
--- Returns `r` for convenience.
---
--- `r = x * x`
---@param r mpz
---@param x integer
---@return mpz
function mpz.sqr_scalar(r, x)
	local a = mpz.from_number(x)
	return mpz.sqr(r, a)
end

--- Computes the square of an integer.
---
--- `a` MUST NOT alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a * a`
---@param r mpz
---@param a mpz
---@return mpz
function mpz.sqr_noalias(r, a)
	assert(not rawequal(r, a), "aliasing detected")

	local sz_a = abs(a[0])
	if sz_a == 0 then
		r[0] = 0
		return r
	end

	mpn.sqr(r, 0, a, 0, sz_a)
	r[0] = mpn.normalized_size(r, 0, 2 * sz_a)

	return r
end

--- Computes the square of an integer.
---
--- `a` may alias `r`, however it will incur the cost of a duplication.
---
--- Returns `r` for convenience.
---
--- `r = a * a`
---@param r mpz
---@param a mpz
---@return mpz
function mpz.sqr(r, a)
	if rawequal(r, a) then
		a = mpz.dup(a)
	end

	return mpz.sqr_noalias(r, a)
end

--- Computes the arithmetic left shift of an integer by a given number of bits.
---
--- `a` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a << y = a * 2 ^ y`
---@param r mpz
---@param a mpz
---@param y mpn.bitcount
---@return mpz
function mpz.lshift(r, a, y)
	if y < 0 then
		return mpz.rshift(r, a, -y)
	elseif y == 0 then
		return mpz.clone(r, a)
	end

	local sgn_a = mpz.sign(a)
	if sgn_a == 0 then
		r[0] = 0
		return r
	end

	local sz_a = abs(a[0])
	local sz_r = mpn.lshift(r, 0, a, 0, sz_a, y)

	if sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_r)
	else
		r[0] = mpn.normalized_size(r, 0, sz_r)
	end

	return r
end

--- Computes the arithmetic right shift of an integer by a given number of bits.
---
--- `a` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a >> y = a / 2 ^ y`
---@param r mpz
---@param a mpz
---@param y mpn.bitcount
---@return mpz
function mpz.rshift(r, a, y)
	if y < 0 then
		return mpz.lshift(r, a, -y)
	elseif y == 0 then
		return mpz.clone(r, a)
	end

	local sgn_a = mpz.sign(a)
	if sgn_a == 0 then
		r[0] = 0
		return r
	end

	local sz_a = abs(a[0])
	local sz_r = mpn.rshift(r, 0, a, 0, sz_a, y)

	if sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_r)
	else
		r[0] = mpn.normalized_size(r, 0, sz_r)
	end

	return r
end

--- Computes the truncated division and remainder of `a / y`.
---
--- `a` may alias `q`.
---
--- Returns the remainder `r`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * y + r`, where `0 <= |r| < |y|` and `sign(r) = sign(a)`.
---@param q mpz
---@param a mpz
---@param y integer
---@return integer
---@nodiscard
function mpz.divrem_scalar(q, a, y)
	if abs(y) > LIMB_MAX then
		local b = mpz.from_number(y)
		local r = mpz.from_zero()
		mpz.divrem(q, r, a, b)
		return mpz.to_number(r)
	end

	local sgn_y = y < 0 and -1 or 1
	y = scalarabs(y)
	assert(y ~= 0, "division by zero")

	local sz_a = abs(a[0])
	local sgn_a = mpz.sign(a)
	if sgn_a == 0 then
		q[0] = 0
		return 0
	end

	local r = mpn.divmod_1(q, 0, a, 0, sz_a, y) * sgn_a
	if sgn_a == sgn_y then
		q[0] = mpn.normalized_size(q, 0, sz_a)
	else
		q[0] = -mpn.normalized_size(q, 0, sz_a)
	end

	return r
end

--- Computes the truncated division and remainder of `a / b`.
---
--- `q` MUST NOT alias `r`.
--- `a` MUST NOT alias `q`.
--- `a` MUST NOT alias `b`.
--- `b` MUST NOT alias `q`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- `a` is clobbered.
---
--- Returns `q` for convenience.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(a)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.divrem_noalias(q, r, a, b)
	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	assert(sgn_b ~= 0, "division by zero")
	if sgn_a == 0 then
		r[0] = 0
		q[0] = 0
		return q
	end

	local sz_a = abs(a[0])
	local sz_b = abs(b[0])
	local sz_q = math.max(0, sz_a - sz_b + 1)

	mpn.divmod(q, 0, r, 0, a, 0, sz_a, b, 0, sz_b)
	if sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_b)
	else
		r[0] = mpn.normalized_size(r, 0, sz_b)
	end

	if sgn_a == sgn_b then
		q[0] = mpn.normalized_size(q, 0, sz_q)
	else
		q[0] = -mpn.normalized_size(q, 0, sz_q)
	end

	return q
end

--- Computes the truncated division and remainder of `a / b`.
---
--- `q` MUST NOT alias `r`.
--- `a` may alias `q`.
--- `a` may alias `r`.
--- `b` may alias `r`.
--- `b` may alias `q`.
---
--- Returns `q` for convenience.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(a)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.divrem(q, r, a, b)
	a = mpz.dup(a)

	if rawequal(q, b) then
		b = mpz.dup(b)
	end

	return mpz.divrem_noalias(q, r, a, b)
end

--- Computes the truncated division remainder of `a / b`.
---
--- `a` MUST NOT alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- `a` is clobbered.
---
--- Returns `r` for convenience.
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.rem_noalias(r, a, b)
	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	assert(sgn_b ~= 0, "division by zero")
	if sgn_a == 0 then
		r[0] = 0
		return r
	end

	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	mpn.mod(r, 0, a, 0, sz_a, b, 0, sz_b)
	if sgn_a < 0 then
		r[0] = -mpn.normalized_size(r, 0, sz_b)
	else
		r[0] = mpn.normalized_size(r, 0, sz_b)
	end

	return r
end

--- Computes the truncated division remainder of `a / b`.
---
--- `a` may alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- Returns `r` for convenience.
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.rem(r, a, b)
	a = mpz.dup(a)

	return mpz.rem_noalias(r, a, b)
end

--- Computes the floored division and remainder of `a / y`.
---
--- `a` may alias `q`.
---
--- Returns the remainder `r`.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * y + r`, where `0 <= |r| < |y|` and `sign(r) = sign(y)`.
---@param q mpz
---@param a mpz
---@param y integer
---@return integer
---@nodiscard
function mpz.divmod_scalar(q, a, y)
	local sgn_a = mpz.sign(a)
	local r = mpz.divrem_scalar(q, a, y)

	if abs(r) == 0 then
		return 0
	end

	if sgn_a >= 0 and y > 0 then
		-- a is positive and y is positive, so we can use the result directly
	elseif sgn_a > 0 and y < 0 then
		-- a is positive and y is negative, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r = r - abs(y)
	elseif sgn_a < 0 and y > 0 then
		-- a is negative and y is positive, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r = r + abs(y)
	end -- a is negative and y is negative, q is correct, r must be negative

	return r
end

--- Computes the floored division and remainder of `a / y`.
---
--- `q` MUST NOT alias `r`.
--- `a` MUST NOT alias `q`.
--- `a` MUST NOT alias `b`.
--- `b` MUST NOT alias `q`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- `a` is clobbered.
---
--- Returns `q` for convenience.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(b)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.divmod_noalias(q, r, a, b)
	mpz.divrem_noalias(q, r, a, b)

	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if sgn_a >= 0 and sgn_b > 0 then
		-- a is positive and b is positive, so we can use the result directly
	elseif sgn_a > 0 and sgn_b < 0 and r[0] ~= 0 then
		-- a is positive and b is negative, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r[0] = abs(r[0])

		local sz_sgn_b = b[0]
		mpz.add(r, r, b)
	elseif sgn_a < 0 and sgn_b > 0 and r[0] ~= 0 then
		-- a is negative and b is positive, q is negative and needs to be fixed
		mpz.sub_scalar(q, q, 1)
		r[0] = -abs(r[0])

		local sz_sgn_b = b[0]
		mpz.add(r, r, b)
	elseif sgn_a < 0 and sgn_b < 0 then
		-- a is negative and v is negative, q is correct, r must be negative
		r[0] = -abs(r[0])
	end

	return q
end

--- Computes the floored division and remainder of `a / y`.
---
--- `q` MUST NOT alias `r`.
--- `a` may alias `q`.
--- `a` may alias `r`.
--- `b` may alias `r`.
--- `b` may alias `q`.
---
--- Returns `q` for convenience.
---
--- The resulting quotient `q` and remainder `r` satisfy the equation:
---   `a = q * b + r`, where `0 <= |r| < |b|` and `sign(r) = sign(b)`.
---@param q mpz
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.divmod(q, r, a, b)
	a = mpz.dup(a)

	if rawequal(q, b) then
		b = mpz.dup(b)
	end

	return mpz.divmod_noalias(q, r, a, b)
end

--- Computes the floored division remainder of `a / y`.
---
--- `a` MUST NOT alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- `a` is clobbered.
---
--- Returns `r` for convenience.
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.mod_noalias(r, a, b)
	mpz.rem_noalias(r, a, b)

	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if sgn_a >= 0 and sgn_b > 0 then
		-- a is positive and b is positive, so we can use the result directly
	elseif sgn_a > 0 and sgn_b < 0 and r[0] ~= 0 then
		-- a is positive and b is negative, q is negative and needs to be fixed
		r[0] = abs(r[0])
		mpz.add(r, r, b)
	elseif sgn_a < 0 and sgn_b > 0 and r[0] ~= 0 then
		-- a is negative and b is positive, q is negative and needs to be fixed
		r[0] = -abs(r[0])
		mpz.add(r, r, b)
	elseif sgn_a < 0 and sgn_b < 0 then
		-- a is negative and v is negative, q is correct, r must be negative
		r[0] = -abs(r[0])
	end

	return r
end

--- Computes the floored division remainder of `a / y`.
---
--- `a` may alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- Returns `r` for convenience.
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.mod(r, a, b)
	a = mpz.dup(a)

	return mpz.mod_noalias(r, a, b)
end

--- Computes the greatest common divisor of an integer and a scalar.
---
--- Returns `r` for convenience.
---
--- `r = gcd(a, y)`
---@param r mpz
---@param a mpz
---@param y integer
---@return mpz
function mpz.gcd_scalar(r, a, y)
	y = scalarabs(y)

	if y > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.gcd(r, a, b)
	elseif y == 0 then
		return mpz.absolute(r, a)
	end

	local sz_a = abs(a[0])
	r[1] = mpn.gcd_1(a, 0, sz_a, y)
	r[0] = 1

	return r
end

--- Computes the greatest common divisor of two integers.
---
--- `a` MUST NOT alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- `a` is clobbered.
--- `b` is clobbered.
---
--- Returns `r` for convenience.
---
--- `r = gcd(a, b)`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.gcd_clobber(r, a, b)
	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	r[0] = mpn.gcd(r, 0, a, 0, sz_a, b, 0, sz_b)

	return r
end

--- Computes the greatest common divisor of two integers.
---
--- `a` may alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = gcd(a, b)`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.gcd(r, a, b)
	return mpz.gcd_clobber(r, mpz.dup(a), mpz.dup(b))
end

--- Computes the exponentiation of an integer to a scalar power.
---
--- `a` MUST NOT alias `r`.
---
--- Returns `r` for convenience.
---
--- `r = a ^ y`
---@param r mpz
---@param a mpz
---@param y integer
---@return mpz
function mpz.pow_scalar(r, a, y)
	if mpz.is_one(a) then
		if y <= 0 then
			if band(y, 1) == 1 then
				r[0] = mpz.sign(a)
			else
				r[0] = 1
			end
			return r
		end
	elseif y == 0 then
		r[0] = 1
		r[1] = 1
		return r
	elseif y < 0 or mpz.is_zero(a) then
		r[0] = 0
		return r
	end

	y = scalar(y)
	if y > LIMB_MAX then
		local b = mpz.from_number(y)
		return mpz.pow(r, a, b)
	end

	local sgn_a = mpz.sign(a)
	local sz_a = abs(a[0])

	local n = mpn.pow_1(r, 0, a, 0, sz_a, y)
	if sgn_a < 0 and band(y, 1) == 1 then -- negative and odd power
		r[0] = -mpn.normalized_size(r, 0, n)
	else
		r[0] = mpn.normalized_size(r, 0, n)
	end

	return r
end

--- Computes the exponentiation of an integer to an integer power.
---
--- `a` MUST NOT alias `b`.
--- `a` MUST NOT alias `r`.
--- `b` MUST NOT alias `r`.
---
--- `a` and `b` are clobbered.
---
--- Returns `r` for convenience.
---
--- `r = a ^ b`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.pow_noalias(r, a, b)
	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if mpz.is_one(a) then
		if sgn_b <= 0 then
			if band(b[1] or 0, 1) == 1 then
				r[0] = mpz.sign(a)
			else
				r[0] = 1
			end
			return r
		end
	elseif sgn_b == 0 then
		r[0] = 1
		return r
	elseif sgn_b < 0 or mpz.is_zero(a) then
		r[0] = 0
		return r
	end

	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	local n = mpn.pow(r, 0, a, 0, sz_a, b, 0, sz_b)
	if sgn_a < 0 and band(b[1], 1) == 1 then -- negative and odd power
		r[0] = -mpn.normalized_size(r, 0, n)
	else
		r[0] = mpn.normalized_size(r, 0, n)
	end

	return r
end

--- Computes the exponentiation of an integer to an integer power.
---
--- `a` may alias `b`.
--- `a` may alias `r`.
--- `b` may alias `r`.
---
---	Returns `r` for convenience.
---
--- `r = a ^ b`
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.pow(r, a, b)
	b = mpz.dup(b)
	a = mpz.dup(a)

	return mpz.pow_noalias(r, a, b)
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
	local sgn_a = mpz.sign(a)
	if sgn_a <= 0 then
		s[0] = 0
		r[0] = 0
		return
	end

	local sz_a = abs(a[0])
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
	local sgn_a = mpz.sign(a)
	local sz_a = abs(a[0])

	local lmb, off = mpn.blimb(idx)
	if sgn_a < 0 then
		if lmb > sz_a then
			return true
		end

		-- twos complement negation has the effect of flipping all bits above the first 1 bit.
		local flipped = mpn.bscan1(a, 0, lmb)
		if idx > flipped then
			return band(a[lmb], lshift(1, off)) == 0
		else
			return band(a[lmb], lshift(1, off)) ~= 0
		end
	else
		if lmb > sz_a then
			return false
		end

		return band(a[lmb], lshift(1, off)) ~= 0
	end
end

--- Sets the bit at index `idx` to 1.
---
--- Returns `r` for convenience.
---@param r mpz
---@param idx mpn.bitcount
---@return mpz
function mpz.bset(r, idx)
	local sgn_a = mpz.sign(r)
	local sz_a = abs(r[0])

	local lmb, off = mpn.blimb(idx)
	if sgn_a >= 0 then
		if lmb > sz_a then
			-- expand number to the new size
			mpn.zero(r, sz_a, lmb - sz_a)
			r[0] = lmb
		end

		-- set the bit
		r[lmb] = bor(r[lmb], lshift(1, off))
		return r
	end

	-- twos complement logic for negative numbers.
	if lmb > sz_a then
		-- any bit above the highest limb is guaranteed to be a 1.
		return r
	end

	-- find the "flip point" (the lowest set bit), above which all bits are inverted.
	local flipped = mpn.bscan1(r, 0, sz_a)
	if idx < flipped then
		local flmb, foff = mpn.blimb(flipped)

		-- below flip point, idx becomes the new flip point and everything between the old and new flip point must be inverted.
		if lmb ~= flmb then
			-- set the high bits on the least significant limb
			r[lmb] = bor(r[lmb], band(LIMB_MAX, lshift(LIMB_MAX, off)))
			-- fill the intermediate limbs
			for i = lmb + 1, flmb - 1 do
				r[i] = LIMB_MAX
			end
			-- set the low bits on the most significant limb
			r[flmb] = bor(r[flmb], rshift(LIMB_MAX, LIMB_SIZE - foff))
		else
			r[lmb] = bor(r[lmb], band(LIMB_MAX, rshift(LIMB_MAX, LIMB_SIZE - foff), lshift(LIMB_MAX, off)))
		end

		-- unset the flipped bit
		r[flmb] = band(r[flmb], bnot(lshift(1, foff)))
	elseif idx > flipped then
		-- above flip point, set to 1 in complement means set to 0.
		r[lmb] = band(r[lmb], bnot(lshift(1, off)))
	end -- idx == flipped, bit is already 1.

	return r
end

--- Sets the bit at index `idx` to 0.
---
--- Returns `r` for convenience.
---@param r mpz
---@param idx mpn.bitcount
---@return mpz
function mpz.bclear(r, idx)
	local sgn_a = mpz.sign(r)
	local sz_a = abs(r[0])

	local lmb, off = mpn.blimb(idx)
	if sgn_a >= 0 then
		if lmb > sz_a then
			-- any bit above the highest limb is guaranteed to be a 0.
			return r
		end

		-- just clear the bit
		r[lmb] = band(r[lmb], bnot(lshift(1, off)))
		return r
	end

	-- negative numbers are stored as magnitude but operates as twos complement.
	if lmb > sz_a then
		-- we must expand our number to the new size
		mpn.zero(r, sz_a, lmb - sz_a)

		r[0] = -lmb
		sz_a = lmb
	end

	-- twos complement negation has the effect of flipping all bits above the first 1 bit.
	local flipped = mpn.bscan1(r, 0, sz_a)
	if idx == flipped then
		-- set the low bits of lmb to 1 so bscan0 searches past the flipped bit.
		r[lmb] = bor(r[lmb], lshift(1, off + 1) - 1)

		-- index of the bit we need to set to 1, everything beneath it must be set to 0.
		local new_flipped = mpn.bscan0(r, lmb - 1, sz_a - lmb + 1) + (lmb - 1) * LIMB_SIZE
		local flmb, foff = mpn.blimb(new_flipped)

		if flmb > sz_a then
			-- we need to expand the number
			mpn.zero(r, sz_a, flmb - sz_a)
			r[0] = -flmb
		end

		if lmb ~= flmb then
			-- zero the intermediate limbs
			for i = lmb, flmb - 1 do
				r[i] = 0
			end
		end

		-- unset everything below foff
		r[flmb] = band(r[flmb], lshift(LIMB_MAX, foff))

		-- set the flipped bit
		r[flmb] = bor(r[flmb], lshift(1, foff))
	elseif idx > flipped then
		-- above flip point, set to 0 in complement means set to 1.
		r[lmb] = bor(r[lmb], lshift(1, off))
	end -- idx < flipped, below flip point is already 0.

	return r
end

--- Inverts the bit at index `idx` from `0 -> 1` or `1 -> 0`.
---@param a mpz
function mpz.binvert(a, idx)
	if mpz.btest(a, idx) then
		mpz.bclear(a, idx)
	else
		mpz.bset(a, idx)
	end
end

function mpz.bextract(r, a, idx, width)
	assert(idx >= 0, "idx must be non-negative")
	assert(width >= 0, "width must be non-negative")

	if width == 0 then
		r[0] = 0
		return r
	end

	if rawequal(r, a) then
		a = mpz.dup(a)
	end

	local limbs = ceil(width / LIMB_SIZE)
	mpn.zero(r, 0, limbs)

	for i = 0, width - 1 do
		if mpz.btest(a, idx + i) then
			local lmb, off = mpn.blimb(i)
			r[lmb] = bor(r[lmb], lshift(1, off))
		end
	end

	r[0] = mpn.normalized_size(r, 0, limbs)
	return r
end

--- Computes the bitwise AND of two integers.
---
---	No aliasing restrictions apply.
---
--- Returns `r` for convenience.
---@param r mpz
---@param a mpz
---@param b mpz
---@return mpz
function mpz.band(r, a, b)
	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	if sz_a < sz_b then
		a, b = b, a
		sz_a, sz_b = sz_b, sz_a
	end

	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if sgn_a >= 0 and sgn_b >= 0 then
		-- r = (+a) & (+b) = (+a) & (+b)
		mpn.band_n(r, 0, a, 0, b, 0, sz_b)
		r[0] = mpn.normalized_size(r, 0, sz_b)
		return r
	elseif sgn_a < 0 and sgn_b >= 0 then
		-- r = (--a) & (+b) = ~(-a - 1) & (+b)

		local a_borrow = 1
		for i = 1, sz_b do
			local t = a[i] - a_borrow
			a_borrow = t < 0 and 1 or 0

			r[i] = band(bnot(t), b[i])
		end

		r[0] = mpn.normalized_size(r, 0, sz_b)
		return r
	elseif sgn_a >= 0 and sgn_b < 0 then
		-- r = (+a) & (--b) = (+a) & ~(-b - 1)

		local b_borrow = 1
		for i = 1, sz_b do
			local t = b[i] - b_borrow
			b_borrow = t < 0 and 1 or 0

			r[i] = band(bnot(t), a[i])
		end

		if b_borrow == 0 then
			mpn.copyi(r, sz_b, a, sz_b, sz_a - sz_b)
			r[0] = mpn.normalized_size(r, 0, sz_a)
			return r
		end

		r[0] = mpn.normalized_size(r, 0, sz_b)
		return r
	else
		-- r = (--a) & (--b) = -(((-a - 1) | (-b - 1)) + 1)

		local a_borrow = 1
		local b_borrow = 1
		local r_carry = 1

		for i = 1, sz_b do
			local ta = a[i] - a_borrow
			if ta < 0 then
				ta = ta + LIMB_MAX + 1
				a_borrow = 1
			else
				a_borrow = 0
			end

			local tb = b[i] - b_borrow
			if tb < 0 then
				tb = tb + LIMB_MAX + 1
				b_borrow = 1
			else
				b_borrow = 0
			end

			local t = bor(ta, tb) + r_carry
			r[i] = band(t, LIMB_MAX)
			r_carry = t > LIMB_MAX and 1 or 0
		end

		assert(b_borrow == 0) -- b was 0

		for i = sz_b + 1, sz_a do
			local ta = a[i] - a_borrow
			if ta < 0 then
				ta = ta + LIMB_MAX + 1
				a_borrow = 1
			else
				a_borrow = 0
			end

			local t = ta + r_carry
			r[i] = band(t, LIMB_MAX)
			r_carry = t > LIMB_MAX and 1 or 0
		end

		assert(a_borrow == 0) -- a was 0

		r[sz_a + 1] = r_carry
		r[0] = -mpn.normalized_size(r, 0, sz_a + r_carry)
		return r
	end
end

function mpz.bor(r, a, b)
	local sz_a = abs(a[0])
	local sz_b = abs(b[0])

	if sz_a < sz_b then
		a, b = b, a
		sz_a, sz_b = sz_b, sz_a
	end

	local sgn_a = mpz.sign(a)
	local sgn_b = mpz.sign(b)

	if sgn_a == 0 then
		mpz.clone(r, b)
		return r
	elseif sgn_b == 0 then
		mpz.clone(r, a)
		return r
	end

	if sgn_a >= 0 and sgn_b >= 0 then
		-- r = (+a) | (+b) = (+a) | (+b)
		mpn.bior_n(r, 0, a, 0, b, 0, sz_b)
		mpn.copyi(r, sz_b, a, sz_b, sz_a - sz_b)
		r[0] = mpn.normalized_size(r, 0, sz_a)
		return r
	elseif sgn_a < 0 and sgn_b >= 0 then
		-- r = (--a) | (+b) = -(((-a - 1) & ~b) + 1)

		local a_borrow = 1
		local r_carry = 1

		for i = 1, sz_b do
			local ta = a[i] - a_borrow
			a_borrow = ta < 0 and 1 or 0

			local t = band(LIMB_MAX, ta, bnot(b[i])) + r_carry
			r[i] = band(t, LIMB_MAX)
			r_carry = t > LIMB_MAX and 1 or 0
		end

		assert(r_carry == 0) -- b was not normalized

		for i = sz_b + 1, sz_a do
			local ta = a[i] - a_borrow
			a_borrow = ta < 0 and 1 or 0

			local t = ta + r_carry
			r[i] = band(t, LIMB_MAX)
			r_carry = t > LIMB_MAX and 1 or 0
		end

		assert(a_borrow == 0) -- a was 0

		r[0] = -mpn.normalized_size(r, 0, sz_a)
		return r
	elseif sgn_a >= 0 and sgn_b < 0 then
		-- r = (+a) & (--b) = -((~a & (-b - 1)) + 1)

		local b_borrow = 1
		local r_carry = 1

		for i = 1, sz_b do
			local tb = b[i] - b_borrow
			b_borrow = tb < 0 and 1 or 0

			local t = band(LIMB_MAX, tb, bnot(a[i])) + r_carry
			r[i] = band(t, LIMB_MAX)
			r_carry = t > LIMB_MAX and 1 or 0
		end

		assert(r_carry == 0)
		assert(b_borrow == 0) -- b was 0

		r[0] = -mpn.normalized_size(r, 0, sz_b)
		return r
	else
		-- r = (--a) & (--b) = -((-a - 1) & (-b - 1) + 1)

		local a_borrow = 1
		local b_borrow = 1
		local r_carry = 1

		for i = 1, sz_b do
			local ta = a[i] - a_borrow
			if ta < 0 then
				ta = ta + LIMB_RADIX
				a_borrow = 1
			else
				a_borrow = 0
			end

			local tb = b[i] - b_borrow
			if tb < 0 then
				tb = tb + LIMB_RADIX
				b_borrow = 1
			else
				b_borrow = 0
			end

			local t = band(ta, tb) + r_carry
			r[i] = band(t, LIMB_MAX)
			r_carry = t > LIMB_MAX and 1 or 0
		end

		assert(b_borrow == 0) -- b was 0
		assert(r_carry == 0)

		r[0] = -mpn.normalized_size(r, 0, sz_b)
		return r
	end
end

function mpz.bxor(r, a, b)
	local ab = mpz.from_zero()
	local ao = mpz.from_zero()
	local nab = mpz.from_zero()

	mpz.band(ab, a, b)
	mpz.bor(ao, a, b)
	mpz.bnot(nab, ab)
	mpz.band(r, ao, nab)
	return r
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

	r[0] = -sz_sgn_a -- flip sign
	if sz_sgn_a >= 0 then
		local c = mpn.add_1(r, 0, a, 0, sz_a, 1) -- "subtract" 1
		if c ~= 0 then
			r[sz_a + 1] = c
			r[0] = r[0] - 1
		end
	else
		mpn.sub_1(r, 0, a, 0, sz_a, 1) -- subtract 1
	end
end

--- Computes the modular addition of two integers.
---
--- `r` MUST NOT alias `m`.
---
--- `r = (a + b) mod m`
---@param r mpz
---@param a mpz
---@param b mpz
---@param m mpz
function mpz.add_mod(r, a, b, m)
	assert(not rawequal(r, m), "mpz.add_mod: r and m must not alias")

	mpz.add(r, a, b)

	if mpz.sign(r) == -mpz.sign(m) then
		mpz.add(r, r, m)
	elseif mpz.cmpabs(r, m) >= 0 then
		mpz.sub(r, r, m)
	end

	if mpz.sign(r) == -mpz.sign(m) or mpz.cmpabs(r, m) >= 0 then
		mpz.mod_noalias(r, r, m)
	end
end

--- Computes the modular subtraction of two integers.
---
--- `r` MUST NOT alias `m`.
---
--- `r = (a + b) mod m`
---@param r mpz
---@param a mpz
---@param b mpz
---@param m mpz
function mpz.sub_mod(r, a, b, m)
	assert(not rawequal(r, m), "mpz.sub_mod: r and m must not alias")

	mpz.sub(r, a, b)

	if mpz.sign(r) == -mpz.sign(m) then
		mpz.add(r, r, m)
	elseif mpz.cmpabs(r, m) >= 0 then
		mpz.sub(r, r, m)
	end

	if mpz.sign(r) == -mpz.sign(m) or mpz.cmpabs(r, m) >= 0 then
		mpz.mod_noalias(r, r, m)
	end
end

--- Computes the modular multiplication of two integers.
---
--- `r` MUST NOT alias `m`.
---
--- `r = (a * b) mod m`
---@param r mpz
---@param a mpz
---@param b mpz
---@param m mpz
function mpz.mul_mod(r, a, b, m)
    assert(not rawequal(r, m), "mpz.mul_mod: r and m must not alias")

    mpz.mul(r, a, b)

    if mpz.sign(r) == -mpz.sign(m) then
        mpz.add(r, r, m)
    elseif mpz.cmpabs(r, m) >= 0 then
        mpz.sub(r, r, m)
    end

    if mpz.sign(r) == -mpz.sign(m) or mpz.cmpabs(r, m) >= 0 then
        mpz.mod_noalias(r, r, m)
    end
end


return mpz
