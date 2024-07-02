---@type Integer
local int = require("./init.lua").Integer

local bit = require('bit')

local MAX_PRECISION = 2 ^ 53

assert(MAX_PRECISION + 1 == MAX_PRECISION, 'loss of precision did not happen at MAX_PRECISION')
assert(MAX_PRECISION - 1 ~= MAX_PRECISION, 'loss of precision happenned before MAX_PRECISION')

local ZERO = int.zero()
local ONE = int.one()

local values_sum = {
    0, 1, -1, 2, -2, 3, -3, 4, -4, 5, 10000, -10000, 5000000, -5000000, MAX_PRECISION / 2, -MAX_PRECISION / 2
}

for _, scalar_a in ipairs(values_sum) do
    for _, scalar_b in ipairs(values_sum) do
        local a = int.new(scalar_a)
        local b = int.new(scalar_b)

        local r = int.zero()
        local tmp = int.zero()

        -- check equality
        assert(a == a, 'a == a failed')
        assert(b == b, 'b == b failed')

        assert(a == int.new(scalar_a), 'a == int.new(scalar_a) failed')
        assert(b == int.new(scalar_b), 'b == int.new(scalar_b) failed')

        assert(a == b == (scalar_a == scalar_b), 'a == b failed')
        assert(a ~= b == (scalar_a ~= scalar_b), 'a == b failed')

        -- check ordering
        assert(a < b == (scalar_a < scalar_b), 'a < b failed')
        assert(a <= b == (scalar_a <= scalar_b), 'a <= b failed')
        assert(a > b == (scalar_a > scalar_b), 'a > b failed')
        assert(a >= b == (scalar_a >= scalar_b), 'a >= b failed')

        -- check unary minus and negation
        assert((-a):tonumber() == -scalar_a, '-a failed')
        assert((-b):tonumber() == -scalar_b, '-b failed')

        assert(a:negate():tonumber() == -scalar_a, 'a:negate() failed')
        assert(b:negate():tonumber() == -scalar_b, 'b:negate() failed')

        assert(a:abs():tonumber() == math.abs(scalar_a), 'a:abs() failed')
        assert(b:abs():tonumber() == math.abs(scalar_b), 'b:abs() failed')

        -- check functions
        assert(a:isZero() == (scalar_a == 0), 'a:isZero() failed')
        assert(a:isEven() == (scalar_a % 2 == 0), 'a:isEven() failed')
        assert(a:isOdd() == (scalar_a % 2 == 1), 'a:isOdd() failed')

        assert(rawequal(a:clone(), a) == false, 'a:clone() failed')
        assert(a:clone() == a, 'a:clone() failed')

        assert(rawequal(r:copy(a), a) == false, 'r:copy(a) failed')
        assert(r:copy(a) == a, 'r:copy(a) failed')

        a:swap(b)
        assert(a:tonumber() == scalar_b, 'a:swap(b) failed')
        assert(b:tonumber() == scalar_a, 'a:swap(b) failed')

        b:swap(a)
        assert(a:tonumber() == scalar_a, 'a:swap(b) failed')
        assert(b:tonumber() == scalar_b, 'a:swap(b) failed')

        assert(tostring(a) == string.format('%i', scalar_a), 'tostring(a) failed')
        assert(a:tostring() == string.format('%i', scalar_a), 'a:tostring() failed')
        assert(a:tostring(10) == string.format('%i', scalar_a), 'a:tostring(10) failed')

        if scalar_a >= 0 then -- %x and %o use twos complement
            assert(a:tostring(16) == string.format('%x', scalar_a), 'a:tostring(16) failed')
            assert(a:tostring(8) == string.format('%o', scalar_a), 'a:tostring(8) failed')
        else
            assert(a:tostring(16) == string.format('-%x', -scalar_a), 'a:tostring(16) failed')
            assert(a:tostring(8) == string.format('-%o', -scalar_a), 'a:tostring(8) failed')
        end

        local log2_a = math.log(math.abs(scalar_a), 2)
        assert(a:isPowerOfTwo() == (scalar_a ~= 0 and math.abs(log2_a - math.ceil(log2_a)) < 0.0000000000001),
               'a:isPowerOfTwo() failed')

        -- check addition
        local sum = scalar_a + scalar_b

        assert((a + b):tonumber() == sum, 'a + b failed')
        assert((b + a):tonumber() == sum, 'b + a failed')

        assert((a + scalar_b):tonumber() == sum, 'a + scalar_b failed')
        assert((scalar_b + a):tonumber() == sum, 'scalar_b + a failed')

        assert((scalar_a + b):tonumber() == sum, 'scalar_a + b failed')
        assert((b + scalar_a):tonumber() == sum, 'b + scalar_a failed')

        assert(r:add(a, b):tonumber() == sum, 'r:add(a, b) failed')
        assert(r:add(b, a):tonumber() == sum, 'r:add(b, a) failed')

        assert(a:tonumber() == scalar_a, 'a was modified during addition')
        assert(b:tonumber() == scalar_b, 'b was modified during addition')

        -- check subtraction
        local diff = scalar_a - scalar_b

        assert((a - b):tonumber() == diff, 'a - b failed')
        assert((b - a):tonumber() == -diff, 'b - a failed')

        assert((a - scalar_b):tonumber() == diff, 'a - scalar_b failed')
        assert((scalar_b - a):tonumber() == -diff, 'scalar_b - a failed')

        assert((scalar_a - b):tonumber() == diff, 'scalar_a - b failed')
        assert((b - scalar_a):tonumber() == -diff, 'b - scalar_a failed')

        assert(r:sub(a, b):tonumber() == diff, 'r:sub(a, b) failed')
        assert(r:sub(b, a):tonumber() == -diff, 'r:sub(b, a) failed')

        assert(a:tonumber() == scalar_a, 'a was modified during subtraction')
        assert(b:tonumber() == scalar_b, 'b was modified during subtraction')

        -- check multiplication
        local product = scalar_a * scalar_b

        if product <= MAX_PRECISION then
            assert((a * b):tonumber() == product, 'a * b failed')
            assert((b * a):tonumber() == product, 'b * a failed')

            assert((a * scalar_b):tonumber() == product, 'a * scalar_b failed')
            assert((scalar_b * a):tonumber() == product, 'scalar_b * a failed')

            assert((scalar_a * b):tonumber() == product, 'scalar_a * b failed')
            assert((b * scalar_a):tonumber() == product, 'b * scalar_a failed')

            assert(r:mul(a, b):tonumber() == product, 'r:mul(a, b) failed')
            assert(r:mul(b, a):tonumber() == product, 'r:mul(b, a) failed')

            assert(r:mulNoAlias(a, b):tonumber() == product, 'r:mulNoAlias(a, b) failed')
            assert(r:mulNoAlias(b, a):tonumber() == product, 'r:mulNoAlias(b, a) failed')

            assert(r:mulNoAliasScalar(a, scalar_b):tonumber() == product, 'r:mulNoAliasScalar(a, scalar_b) failed')
            assert(r:mulNoAliasScalar(b, scalar_a):tonumber() == product, 'r:mulNoAliasScalar(b, scalar_a) failed')

            assert(a:tonumber() == scalar_a, 'a was modified during multiplication')
            assert(b:tonumber() == scalar_b, 'b was modified during multiplication')
        end

        -- check division
        local quotient = math.floor(scalar_a / scalar_b)
        local modulo = math.floor(scalar_a % scalar_b)

        if scalar_b ~= 0 then
            assert((a / b):tonumber() == quotient, 'a / b failed')
            assert((a % b):tonumber() == modulo, 'a % b failed')

            assert((a / scalar_b):tonumber() == quotient, 'a / scalar_b failed')
            assert((a % scalar_b):tonumber() == modulo, 'a % scalar_b failed')

            assert((scalar_a / b):tonumber() == quotient, 'scalar_a / b failed')
            assert((scalar_a % b):tonumber() == modulo, 'scalar_a % b failed')

            assert(r:divFloor(tmp, a, b):tonumber() == quotient, 'r:div(a, b) failed')
            assert(tmp:tonumber() == modulo, 'r:div(a, b) remainder failed')

            r:divTrunc(tmp, a, b)
            assert(r * b + tmp == a, 'r:divTrunc(a, b) failed to satisfy identity')

            r:divFloor(tmp, a, b)
            assert(r * b + tmp == a, 'r:divFloor(a, b) failed to satisfy identity')

            assert(a:tonumber() == scalar_a, 'a was modified during division')
            assert(b:tonumber() == scalar_b, 'b was modified during division')
        end

        -- check exponentiation
        local power = math.floor(scalar_a ^ scalar_b)

        if power <= MAX_PRECISION then
            assert((a ^ b):tonumber() == power, 'a ^ b failed')

            assert((a ^ scalar_b):tonumber() == power, 'a ^ scalar_b failed')
            assert((scalar_a ^ b):tonumber() == power, 'scalar_a ^ b failed')

            assert(r:pow(a, b):tonumber() == power, 'r:pow(a, b) failed')
            assert(r:powScalar(a, scalar_b):tonumber() == power, 'r:powScalar(a, scalar_b) failed')

            assert(a:tonumber() == scalar_a, 'a was modified during exponentiation')
            assert(b:tonumber() == scalar_b, 'b was modified during exponentiation')
        end
    end
end

local values_bitwise = {
    0, 1, -1, 2, -2, 0x12345678, 0x87654321, 0x33333333, 0x77777777, 0x55aa55aa, 0xaa55aa55, 0x7fffffff, 0x80000000,
    0xffffffff
}

for _, scalar_a in ipairs(values_bitwise) do
    for _, scalar_b in ipairs(values_bitwise) do
        local a = int.new(bit.tobit(scalar_a))
        local b = int.new(bit.tobit(scalar_b))

        local r = int.zero()

        -- check bitwise operations
        local and_result = bit.band(scalar_a, scalar_b)
        local or_result = bit.bor(scalar_a, scalar_b)
        local xor_result = bit.bxor(scalar_a, scalar_b)
        local not_result = bit.bnot(scalar_a)

        assert(r:bitAnd(a, b):tonumber() == and_result, 'r:bitAnd(a, b) failed')
        assert(r:bitOr(a, b):tonumber() == or_result, 'r:bitOr(a, b) failed')
        assert(r:bitXor(a, b):tonumber() == xor_result, 'r:bitXor(a, b) failed')
        assert(r:bitNot(a):tonumber() == not_result, 'r:bitXor(a, b) failed')
    end
end