--- Multiple Precision Rational Arithmetic

local bit = require("bit")
local mpz = require("./mpz")

--- A multiple precision rational.
---
---@class mpq
---@field p mpz
---@field q mpz
local mpq = {}
mpq.__index = mpq

--- Create a duplicate of the given multiple precision rational.
---@param a mpq
---@return mpq
---@nodiscard
function mpq.dup(a)
	return setmetatable({ p = mpz.dup(a.p), q = mpz.dup(a.q) }, mpq)
end

--- Create a new multiple precision rational with the value of zero.
---@return mpq
---@nodiscard
function mpq.from_zero()
	return setmetatable({ p = mpz.from_zero(), q = mpz.from_one() }, mpq)
end

--- Create a new multiple precision integer with the value of positive one.
---@return mpq
---@nodiscard
function mpq.from_one()
	return setmetatable({ p = mpz.from_one(), q = mpz.from_one() }, mpq)
end

--- Create a duplicate of the given multiple precision rational.
---@param r mpq
---@param a mpq
function mpq.clone(r, a)
	mpz.clone(r.p, a.p)
	mpz.clone(r.q, a.q)
end

--- Create a new multiple precision rational with the value of `p / q`.
---@param p integer
---@param q integer
---@return mpq
---@nodiscard
function mpq.from_ratio(p, q)
	assert(q ~= 0, "denominator cannot be zero")
	if q < 0 then
		p = -p
		q = -q
	end

	return setmetatable({ p = mpz.from_number(p), q = mpz.from_number(q) }, mpq)
end

--- Create a new multiple precision rational with the value of `a`.
---@param a number
---@return mpq
---@nodiscard
function mpq.from_number(a)
	local p, q = a, 1
	while p % 1 ~= 0 do
		p = p * 2
		q = q * 2
	end

	return setmetatable({ p = mpz.from_number(p), q = mpz.from_number(q) }, mpq)
end

--- Returns an approximation of the given rational as a Lua number.
---@param a mpq
---@return number
---@nodiscard
function mpq.to_number(a)
	return mpz.to_number(a.p) / mpz.to_number(a.q)
end

--- Returns a string representation of the given rational in fraction notation.
---@param a mpq
---@param base? integer
---@return string
function mpq.to_string(a, base)
	return string.format("%s/%s", mpz.to_string(a.p, base), mpz.to_string(a.q, base))
end

--- Returns a string representation of the given rational in point notation.
---@param a mpq
---@param digits integer
---@param base? integer
function mpq.to_string_point(a, digits, base)
    base = base or 10

	local exp = mpz.from_number(base)
    mpz.pow_scalar(exp, exp, digits)

    local tmp = mpz.from_zero()
    mpz.mul(tmp, a.p, exp)

	local unused = mpz.from_zero()
	mpz.divrem(tmp, unused, tmp, a.q)

    local str = mpz.to_string(tmp, base)
	return str:sub(1, #str - digits) .. "." .. str:sub(#str - digits + 1)
end

--- Returns true if the given rational is zero, false otherwise.
---@param a mpq
---@return boolean
---@nodiscard
function mpq.is_zero(a)
	return mpz.is_zero(a.p)
end

--- Returns true if the given rational is one, false otherwise.
---@param a mpq
---@return boolean
---@nodiscard
function mpq.is_one(a)
	return mpz.cmp(a.p, a.q) == 0
end

--- Returns true if the given rational is positive, false otherwise.
---@param a mpq
---@return boolean
---@nodiscard
function mpq.is_positive(a)
	return mpz.is_positive(a.p)
end

--- Returns true if the given rational is negative, false otherwise.
---@param a mpq
---@return boolean
---@nodiscard
function mpq.is_negative(a)
	return mpz.is_negative(a.p)
end

--- Returns the sign of the given rational, -1 for negative, 0 for zero, and 1 for positive
---@param a mpq
---@return integer
---@nodiscard
function mpq.sign(a)
	return mpz.sign(a.p)
end

--- Negates the given rational.
---
--- `r = -a`
---@param r mpq
---@param a mpq
function mpq.neg(r, a)
	mpz.neg(r.p, a.p)
	mpz.clone(r.q, a.q)
end

--- Computes the absolute value of the given rational.
---
--- `r = |a|`
---@param r mpq
---@param a mpq
function mpq.abs(r, a)
	mpz.abs(r.p, a.p)
	mpz.abs(r.q, a.q)
end

--- Reduces the given rational to its simplest form.
---@param r mpq
function mpq.reduce(r)
	local gcd = mpz.from_zero()
	mpz.gcd(gcd, r.p, r.q)

	local one = mpz.from_one()
	if mpz.cmp(gcd, one) == 0 then
		return
	end

	mpz.divmod(r.p, one, r.p, gcd)
	mpz.divmod(r.q, one, r.q, gcd)
end

--- Computes the sum of an rational and a scalar.
---
--- `r = a + y`
---@param r mpq
---@param a mpq
---@param y integer
function mpq.add_scalar(r, a, y)
	local tmp = mpz.from_zero()
	mpz.mul_scalar(tmp, a.q, y)
	mpz.add(r.p, tmp, a.p)
	mpz.clone(r.q, a.q)
end

--- Computes the sum of two rationals.
---
--- `r = a + b`
---@param r mpq
---@param a mpq
---@param b mpq
function mpq.add(r, a, b)
	mpz.mul(r.p, a.p, b.q)
	mpz.mul(r.q, a.q, b.p)
	mpz.add(r.p, r.p, r.q)
	mpz.mul(r.q, a.q, b.q)
	mpq.reduce(r)
end

--- Computes the subtraction of an rational and a scalar.
---
--- `r = a - y`
---@param r mpq
---@param a mpq
---@param y integer
function mpq.sub_scalar(r, a, y)
	local tmp = mpz.from_zero()
	mpz.mul_scalar(tmp, a.q, y)
	mpz.neg(tmp, tmp)
	mpz.add(r.p, tmp, a.p)
	mpz.clone(r.q, a.q)
end

--- Computes the subtraction of a scalar and an rational.
---
--- `r = x - b`
---@param r mpq
---@param x integer
---@param b mpq
function mpq.scalar_sub(r, x, b)
	local tmp = mpz.from_zero()
	mpz.mul_scalar(tmp, b.q, x)
	mpz.sub(r.p, tmp, b.p)
	mpz.clone(r.q, b.q)
end

--- Computes the subtraction of two rationals.
---
--- `r = a - b`
---@param r mpq
---@param a mpq
---@param b mpq
function mpq.sub(r, a, b)
	mpz.mul(r.p, a.p, b.q)
	mpz.mul(r.q, a.q, b.p)
	mpz.add(r.p, r.p, r.q)
	mpz.mul(r.q, a.q, b.q)
	mpq.reduce(r)
end

--- Computes the product of an rational and a scalar.
---
--- `r = a * y`
---@param r mpq
---@param a mpq
---@param y integer
function mpq.mul_scalar(r, a, y)
	mpz.mul_scalar(r.p, a.p, y)
	mpz.clone(r.q, a.q)
end

--- Computes the product of two rationals.
---
--- `r = a * b`
---@param r mpq
---@param a mpq
---@param b mpq
function mpq.mul(r, a, b)
	mpz.mul(r.p, a.p, b.p)
	mpz.mul(r.q, a.q, b.q)
	mpq.reduce(r)
end

--- Computes the square of an rational.
---
--- `r = a * a`
---@param r mpq
---@param a mpq
function mpq.sqr(r, a)
	mpz.sqr(r.p, a.p)
	mpz.sqr(r.q, a.q)
	mpq.reduce(r)
end

--- Computes the division of two rationals.
---
--- `r = a / b`
---@param r mpq
---@param a mpq
---@param b mpq
function mpq.div(r, a, b)
	mpz.mul(r.p, a.p, b.q)
	mpz.mul(r.q, a.q, b.p)
	mpq.reduce(r)
end

--- Computes the exponentiation of a rational to a scalar power.
---
--- `r = a ^ y`
---@param r mpq
---@param a mpq
---@param y integer
function mpq.pow_scalar(r, a, y)
	mpz.pow_scalar(r.p, a.p, y)
	mpz.pow_scalar(r.q, a.q, y)
	mpq.reduce(r)
end

--- Computes the exponentiation of a rational to an integer power.
---
--- `r = a ^ b`
---@param r mpq
---@param a mpq
---@param b mpz
function mpq.pow(r, a, b)
	mpz.pow(r.p, a.p, b)
	mpz.pow(r.q, a.q, b)
	mpq.reduce(r)
end

return mpq