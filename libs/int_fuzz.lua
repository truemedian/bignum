local Integer = require("int")

local fuzzer = require("aflua")
local bit = require("bit")

local function check_from_scalar(buf)
	local value = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)
	local r = Integer.from_scalar(value)
	local actual = r:to_scalar()

	if actual ~= value then
		print("value", value)
		print("actual", actual)
		error("failed")
	end
end

local function check_from_string(buf)
	local base = fuzzer.consume_integer(2, 36)
	local input = fuzzer.consume_rest()

	if input:find("[^0-9a-zA-Z]") then
		return fuzzer.skip()
	end

	local expect = tonumber(input, base)
	if not expect or math.abs(expect) >= 2 ^ 50 then
		return fuzzer.skip()
	end

	local r = Integer.from_string(input, base)
	local actual = r:to_scalar()
	if actual ~= expect then
		print("input", input)
		print("base", base)
		print("expect", expect)
		print("actual", actual)
		error("failed")
	end
end

local function check_classification(buf)
	local value = fuzzer.consume_integer(-2 ^ 32, 2 ^ 32)
	local r = Integer.from_scalar(value)

	assert((value % 2 == 0) == r:is_even())
	assert((value % 2 ~= 0) == r:is_odd())
	assert((value == 0) == r:is_zero())
	assert((math.abs(value) == 1) == r:is_one())
	assert((value > 0) == r:is_positive())
	assert((value < 0) == r:is_negative())
	assert((value ~= 0 and bit.band(math.abs(value), math.abs(value) - 1) == 0) == r:is_power_of_two())

	if value >= 0 then
		local popcount = 0
		local ctz = -1

		for j = 31, 0, -1 do
			if bit.band(value, bit.lshift(1, j)) ~= 0 then
				popcount = popcount + 1
				ctz = j
			end
		end

		assert(popcount == r:count_set_bits())
		assert(ctz == r:count_trailing_zeros())
	end
end

local function check_compare(buf)
	local a = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)
	local b = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)

	local x = math.abs(a)
	local y = math.abs(b)

	local r = Integer.from_scalar(a)
	local s = Integer.from_scalar(b)

	local ucmp_rr = r:ucmp(r)
	local ucmp_rs = r:ucmp(s)
	local ucmp_ss = s:ucmp(s)
	local ucmp_sr = s:ucmp(r)
	local ucmp_rx = r:ucmp_scalar(x)
	local ucmp_ry = r:ucmp_scalar(y)
	local ucmp_sx = s:ucmp_scalar(x)
	local ucmp_sy = s:ucmp_scalar(y)

	assert((ucmp_rs < 0) == (ucmp_sr > 0))
	assert(ucmp_rx == 0)
	assert(ucmp_sy == 0)
	assert(ucmp_rr == 0)
	assert(ucmp_ss == 0)

	assert((x < y) == (ucmp_rs < 0))
	assert((x > y) == (ucmp_rs > 0))
	assert((x == y) == (ucmp_rs == 0))

	assert((x < y) == (ucmp_ry < 0))
	assert((x > y) == (ucmp_ry > 0))
	assert((x == y) == (ucmp_ry == 0))

	assert((y < x) == (ucmp_sr < 0))
	assert((y > x) == (ucmp_sr > 0))
	assert((y == x) == (ucmp_sr == 0))

	assert((y < x) == (ucmp_sx < 0))
	assert((y > x) == (ucmp_sx > 0))
	assert((y == x) == (ucmp_sx == 0))

	local cmp_rr = r:cmp(r)
	local cmp_rs = r:cmp(s)
	local cmp_ss = s:cmp(s)
	local cmp_sr = s:cmp(r)
	local cmp_ra = r:cmp_scalar(a)
	local cmp_rb = r:cmp_scalar(b)
	local cmp_sa = s:cmp_scalar(a)
	local cmp_sb = s:cmp_scalar(b)

	assert((cmp_rs < 0) == (cmp_sr > 0))
	assert(cmp_ra == 0)
	assert(cmp_sb == 0)
	assert(cmp_rr == 0)
	assert(cmp_ss == 0)

	assert((a < b) == (cmp_rs < 0))
	assert((a > b) == (cmp_rs > 0))
	assert((a == b) == (cmp_rs == 0))

	assert((a < b) == (cmp_rb < 0))
	assert((a > b) == (cmp_rb > 0))
	assert((a == b) == (cmp_rb == 0))

	assert((b < a) == (cmp_sr < 0))
	assert((b > a) == (cmp_sr > 0))
	assert((b == a) == (cmp_sr == 0))

	assert((b < a) == (cmp_sa < 0))
	assert((b > a) == (cmp_sa > 0))
	assert((b == a) == (cmp_sa == 0))
end

local function check_add(buf)
	local a = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)
	local b = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)

	local x = math.abs(a)
	local y = math.abs(b)

	local r = Integer.from_scalar(a)
	local s = Integer.from_scalar(b)
	local t = Integer.new_zero()

	t:uadd(r, r)
	assert(t:to_scalar() == x + x)

	t:uadd(t, r)
	assert(t:to_scalar() == x + x + x)

	t:uadd(r, s)
	assert(t:to_scalar() == x + y)

	t:uadd(s, r)
	assert(t:to_scalar() == x + y)

	t:uadd_scalar(r, y)
	assert(t:to_scalar() == x + y)

	t:uadd_scalar(s, x)
	assert(t:to_scalar() == x + y)

	t:add(r, s)
	assert(t:to_scalar() == a + b)

	t:add(r, r)
	assert(t:to_scalar() == a + a)

	t:add(t, r)
	assert(t:to_scalar() == a + a + a)

	t:add(s, r)
	assert(t:to_scalar() == a + b)

	t:add_scalar(r, b)
	assert(t:to_scalar() == a + b)

	t:add_scalar(s, a)
	assert(t:to_scalar() == a + b)
end

local function check_sub(buf)
	local a = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)
	local b = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)

	local x = math.abs(a)
	local y = math.abs(b)

	local r = Integer.from_scalar(a)
	local s = Integer.from_scalar(b)
	local t = Integer.new_zero()

	if y > x then
		r, s = s, r
        x, y = y, x

		t:usub(r, r)
		assert(t:to_scalar() == x - x)

		if x - x - x > 0 then
			t:usub(t, r)
			assert(t:to_scalar() == x - x - x)
		end

        t:usub(r, s)
		assert(t:to_scalar() == x - y)

		t:usub_scalar(r, y)
		assert(t:to_scalar() == x - y)

		r, s = s, r
        x, y = y, x
	end

	t:sub(r, s)
	assert(t:to_scalar() == a - b)

	t:sub(r, r)
	assert(t:to_scalar() == a - a)

	t:sub(t, r)
	assert(t:to_scalar() == a - a - a)

	t:sub(s, r)
	assert(t:to_scalar() == b - a)

	t:sub_scalar(r, b)
	assert(t:to_scalar() == a - b)

	t:sub_scalar(s, a)
	assert(t:to_scalar() == b - a)
end

local function check_mul(buf)
	local a = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)
	local b = fuzzer.consume_integer(-2 ^ 46, 2 ^ 46)

	local x = math.abs(a)
	local y = math.abs(b)

	local r = Integer.from_scalar(a)
	local s = Integer.from_scalar(b)
	local t = Integer.new_zero()

	if x * x < 2 ^ 52 then
		t:umul(r, r)
		assert(t:to_scalar() == x * x)

		if x * x * x < 2 ^ 52 then
			t:umul(t, r)
			assert(t:to_scalar() == x * x * x)
		end
	end

	if x * y > 2 ^ 52 then
		return fuzzer.skip()
	end

	t:umul(r, s)
	assert(t:to_scalar() == x * y)

	t:umul(s, r)
	assert(t:to_scalar() == x * y)

	t:umul_scalar(r, y)
	assert(t:to_scalar() == x * y)

	t:umul_scalar(s, x)
	assert(t:to_scalar() == x * y)

	t:mul(r, s)
	assert(t:to_scalar() == a * b)

	if x * x < 2 ^ 52 then
		t:mul(r, r)
		assert(t:to_scalar() == a * a)

		if x * x * x < 2 ^ 52 then
			t:mul(t, r)
			assert(t:to_scalar() == a * a * a)
		end
	end

	t:mul(s, r)
	assert(t:to_scalar() == a * b)

	t:mul_scalar(r, b)
	assert(t:to_scalar() == a * b)

	t:mul_scalar(s, a)
	assert(t:to_scalar() == a * b)
end

local function check_all(buf)
	local choice = fuzzer.consume_integer(0, 6)

	if choice == 0 then
		check_from_scalar(buf)
	elseif choice == 1 then
		check_from_string(buf)
	elseif choice == 2 then
		check_classification(buf)
	elseif choice == 3 then
		check_compare(buf)
	elseif choice == 4 then
		check_add(buf)
	elseif choice == 5 then
        check_sub(buf)
    elseif choice == 6 then
        check_mul(buf)
	end
end

fuzzer.init()
fuzzer.coverage_hook(true)
fuzzer.run(check_all, 10000, debug.traceback)
