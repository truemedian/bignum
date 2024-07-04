local fw = require('./framework.lua')
local Integer, all = fw.Integer, fw.all

local bit = require('bit')

local MAX_PRECISION = 2 ^ 53

assert(MAX_PRECISION + 1 == MAX_PRECISION, 'loss of precision did not happen at MAX_PRECISION')
assert(MAX_PRECISION - 1 ~= MAX_PRECISION, 'loss of precision happenned before MAX_PRECISION')

local values_normal = {0, 1, -1, 2, -2, 3, -3, 4, -4, 5, 10000, -10000, 5000000, -5000000, 2 ^ 26 - 1, 2 ^ 26, 2 ^ 40, MAX_PRECISION / 2, -MAX_PRECISION / 2}
local values_bitwise = {0, 1, -1, 2, -2, 0x12345678, 0x87654321, 0x33333333, 0x77777777, 0x55aa55aa, 0xaa55aa55, 0x7fffffff, 0x80000000, 0xffffffff}

local r = Integer.zero()
local tmp = Integer.zero()

local function b_ne_zero(a, b) return b ~= 0 end
local function a_positive(a, b) return a >= 0 end
local function a_negative(a, b) return a < 0 end
local function pow_precison(a, b) return math.abs(a ^ b) <= MAX_PRECISION end

fw.test(all, 'A == A', function(a, b, A, B) return true, A == A end)
fw.test(all, 'A ~= A', function(a, b, A, B) return false, A ~= A end)

fw.test(all, 'A == B', function(a, b, A, B) return a == b, A == B end)
fw.test(all, 'A ~= B', function(a, b, A, B) return a ~= b, A ~= B end)
fw.test(all, 'A <= B', function(a, b, A, B) return a <= b, A <= B end)
fw.test(all, 'A >= B', function(a, b, A, B) return a >= b, A >= B end)
fw.test(all, 'A < B', function(a, b, A, B) return a < b, A < B end)
fw.test(all, 'A > B', function(a, b, A, B) return a > b, A > B end)

fw.test(all, 'A:abs()', function(a, b, A, B) return math.abs(a), A:abs() end)
fw.test(all, 'A:isZero()', function(a, b, A, B) return a == 0, A:isZero() end)
fw.test(all, 'A:isEven()', function(a, b, A, B) return a % 2 == 0, A:isEven() end)
fw.test(all, 'A:isOdd()', function(a, b, A, B) return a % 2 == 1, A:isOdd() end)

fw.test(all, 'tostring(A)', function(a, b, A, B) return string.format('%i', a), tostring(A) end)
fw.test(all, 'A:tostring()', function(a, b, A, B) return string.format('%i', a), A:tostring() end)
fw.test(all, 'A:tostring(10)', function(a, b, A, B) return string.format('%i', a), A:tostring(10) end)
fw.test(a_positive, 'A:tostring(16), positive', function(a, b, A, B) return string.format('%x', a), A:tostring(16) end)
fw.test(a_positive, 'A:tostring(8), positive', function(a, b, A, B) return string.format('%o', a), A:tostring(8) end)
fw.test(a_negative, 'A:tostring(16), negative', function(a, b, A, B) return string.format('-%x', -a), A:tostring(16) end)
fw.test(a_negative, 'A:tostring(8), negative', function(a, b, A, B) return string.format('-%o', -a), A:tostring(8) end)

fw.test(a_positive, 'r:sqrt(A)', function(a, b, A, B) return math.floor(math.sqrt(math.abs(a))), r:sqrt(A) end)
fw.test(all, 'A:isPowerOfTwo()', function(a, b, A, B)
    local log2_a = math.log(math.abs(a), 2)
    return a ~= 0 and math.abs(log2_a - math.ceil(log2_a)) < 0.0000000000001, A:isPowerOfTwo()
end)

fw.run(values_normal, Integer.new)
fw.report()

fw.test(all, '-A', function(a, b, A, B) return -a, -A end)
fw.test(all, 'A:negate()', function(a, b, A, B) return -a, A:negate() end)

fw.test(all, 'A + B', function(a, b, A, B) return a + b, A + B end)
fw.test(all, 'A + b', function(a, b, A, B) return a + b, A + b end)
fw.test(all, 'a + B', function(a, b, A, B) return a + b, a + B end)
fw.test(all, 'r:add(A, B)', function(a, b, A, B) return a + b, r:add(A, B) end)

fw.test(all, 'A - B', function(a, b, A, B) return a - b, A - B end)
fw.test(all, 'A - b', function(a, b, A, B) return a - b, A - b end)
fw.test(all, 'a - B', function(a, b, A, B) return a - b, a - B end)
fw.test(all, 'r:sub(A, B)', function(a, b, A, B) return a - b, r:sub(A, B) end)

fw.test(all, 'A * B', function(a, b, A, B) return a * b, A * B end)
fw.test(all, 'A * b', function(a, b, A, B) return a * b, A * b end)
fw.test(all, 'a * B', function(a, b, A, B) return a * b, a * B end)
fw.test(all, 'r:mul(A, B)', function(a, b, A, B) return a * b, r:mul(A, B) end)
fw.test(all, 'r:mulNoAlias(A, B)', function(a, b, A, B) return a * b, r:mulNoAlias(A, B) end)
fw.test(all, 'r:mulNoAliasScalar(A, b)', function(a, b, A, B) return a * b, r:mulNoAliasScalar(A, b) end)

fw.test(b_ne_zero, 'A / B', function(a, b, A, B) return math.floor(a / b), A / B end)
fw.test(b_ne_zero, 'a / B', function(a, b, A, B) return math.floor(a / b), a / B end)
fw.test(b_ne_zero, 'A / b', function(a, b, A, B) return math.floor(a / b), A / b end)
fw.test(b_ne_zero, 'r:divTrunc(A, B), identity', function(a, b, A, B)
    r:divTrunc(tmp, A, B)
    return true, r * B + tmp == A
end)
fw.test(b_ne_zero, 'r:divFloor(A, B), identity', function(a, b, A, B)
    r:divFloor(tmp, A, B)
    return true, r * B + tmp == A
end)
fw.test(b_ne_zero, 'r:divFloor(A, B)', function(a, b, A, B) return math.floor(a / b), r:divFloor(tmp, A, B) end)
fw.test(b_ne_zero, 'r:divFloorScalar(A, b)', function(a, b, A, B) return math.floor(a / b), r:divFloorScalar(tmp, A, b) end)

fw.test(b_ne_zero, 'A % B', function(a, b, A, B) return math.floor(a % b), A % B end)
fw.test(b_ne_zero, 'a % B', function(a, b, A, B) return math.floor(a % b), a % B end)
fw.test(b_ne_zero, 'A % b', function(a, b, A, B) return math.floor(a % b), A % b end)
fw.test(b_ne_zero, 'r:divFloor(A, B), remainder', function(a, b, A, B) return math.floor(a % b), r:divFloor(tmp, A, B) and tmp end)
fw.test(b_ne_zero, 'r:divFloorScalar(A, B), remainder', function(a, b, A, B) return math.floor(a % b), r:divFloorScalar(tmp, A, b) and tmp end)

fw.test(pow_precison, 'A ^ B', function(a, b, A, B) return math.floor(a ^ b), A ^ B end)
fw.test(pow_precison, 'A ^ b', function(a, b, A, B) return math.floor(a ^ b), A ^ b end)
fw.test(pow_precison, 'a ^ B', function(a, b, A, B) return math.floor(a ^ b), a ^ B end)
fw.test(pow_precison, 'r:pow(A, B)', function(a, b, A, B) return math.floor(a ^ b), r:pow(A, B) end)
fw.test(pow_precison, 'r:powScalar(A, b)', function(a, b, A, B) return math.floor(a ^ b), r:powScalar(A, b) end)

fw.run(values_normal, Integer.new)
fw.report()

fw.test(all, 'r:bitAnd(A, B)', function(a, b, A, B) return bit.band(a, b), r:bitAnd(A, B) end)
fw.test(all, 'r:bitOr(A, B)', function(a, b, A, B) return bit.bor(a, b), r:bitOr(A, B) end)
fw.test(all, 'r:bitXor(A, B)', function(a, b, A, B) return bit.bxor(a, b), r:bitXor(A, B) end)
fw.test(all, 'r:bitNot(A)', function(a, b, A, B) return bit.bnot(a), r:bitNot(A) end)

fw.run(values_bitwise, function(a) return Integer.new(bit.tobit(a)) end)

fw.report()
