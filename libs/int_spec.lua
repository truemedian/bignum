local Integer = require("int")

local bit = require("bit")

local LIMIT = 20
local function trunc(n)
	if n >= 0 then
		return math.floor(n)
	else
		return math.ceil(n)
	end
end

describe("integer creation", function()
	it("should create an Integer from a scalar", function()
		local int = Integer.from_scalar(500)
		assert.are.equal(500, int:to_scalar())
	end)

	it("should create an Integer from a negative scalar", function()
		local int = Integer.from_scalar(-300)
		assert.are.equal(-300, int:to_scalar())
	end)

	it("should create an Integer from zero", function()
		local int = Integer.from_scalar(0)
		assert.are.equal(0, int:to_scalar())
	end)

	it("should create an Integer as zero", function()
		local int = Integer.new_zero()
		assert.are.equal(0, int:to_scalar())
	end)

	it("should set an integer to a new scalar", function()
		local int = Integer.from_scalar(150)
		int:set_scalar(-10)
		assert.are.equal(-10, int:to_scalar())
		int:set_scalar(1000)
		assert.are.equal(1000, int:to_scalar())
	end)
end)

describe("integer classification", function()
	-- shared to help ensure that integers can be reused
	local int = Integer.new_zero()

	for i = -LIMIT, LIMIT do
		it("should classify " .. i .. " correctly", function()
			int:set_scalar(i)
			assert.equal(i % 2 == 0, int:is_even())
			assert.equal(i % 2 ~= 0, int:is_odd())
			assert.equal(i == 0, int:is_zero())
			assert.equal(math.abs(i) == 1, int:is_one())
			assert.equal(i > 0, int:is_positive())
			assert.equal(i < 0, int:is_negative())
			assert.equal(i ~= 0 and bit.band(math.abs(i), math.abs(i) - 1) == 0, int:is_power_of_two())

			if i >= 0 then
				local popcount = 0
				local ctz = -1

				for j = 31, 0, -1 do
					if bit.band(i, bit.lshift(1, j)) ~= 0 then
						popcount = popcount + 1
						ctz = j
					end
				end

				assert.equal(popcount, int:count_set_bits())
				assert.equal(ctz, int:count_trailing_zeros())
			end
		end)
	end
end)

describe("integer comparison", function()
	-- shared to help ensure that integers can be reused
	local a = Integer.new_zero()
	local b = Integer.new_zero()

	for i = 0, LIMIT do
		for j = 0, LIMIT do
			it("should unsigned compare " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				local ucmp_ab = a:ucmp(b)
				local ucmp_ba = b:ucmp(a)
				local ucmp_aj = a:ucmp_scalar(j)
				local ucmp_bi = b:ucmp_scalar(i)

				assert.equal(i < j, ucmp_ab < 0)
				assert.equal(i == j, ucmp_ab == 0)
				assert.equal(i > j, ucmp_ab > 0)

				assert.equal(true, (ucmp_ab < 0) == (ucmp_ba > 0))

				assert.equal(i < j, ucmp_aj < 0)
				assert.equal(i == j, ucmp_aj == 0)
				assert.equal(i > j, ucmp_aj > 0)

				assert.equal(i > j, ucmp_bi < 0)
				assert.equal(i == j, ucmp_bi == 0)
				assert.equal(i < j, ucmp_bi > 0)

				assert.equal(true, a:ucmp(a) == 0)
				assert.equal(true, b:ucmp(b) == 0)

				assert.equal(true, a:ucmp_scalar(i) == 0)
				assert.equal(true, b:ucmp_scalar(j) == 0)
			end)
		end
	end

	for i = -LIMIT, LIMIT do
		for j = -LIMIT, LIMIT do
			it("should compare " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				local cmp_ab = a:cmp(b)
				local cmp_ba = b:cmp(a)
				local cmp_aj = a:cmp_scalar(j)
				local cmp_bi = b:cmp_scalar(i)

				assert.equal(i < j, cmp_ab < 0)
				assert.equal(i == j, cmp_ab == 0)
				assert.equal(i > j, cmp_ab > 0)

				assert.equal(true, (cmp_ab < 0) == (cmp_ba > 0))

				assert.equal(i < j, cmp_aj < 0)
				assert.equal(i == j, cmp_aj == 0)
				assert.equal(i > j, cmp_aj > 0)

				assert.equal(i > j, cmp_bi < 0)
				assert.equal(i == j, cmp_bi == 0)
				assert.equal(i < j, cmp_bi > 0)

				assert.equal(true, a:cmp(a) == 0)
				assert.equal(true, b:cmp(b) == 0)

				assert.equal(true, a:cmp_scalar(i) == 0)
				assert.equal(true, b:cmp_scalar(j) == 0)
			end)
		end
	end
end)

describe("unsigned integer arithmetic", function()
	local r = Integer.new_zero()
	local a = Integer.new_zero()
	local b = Integer.new_zero()

	for i = 0, LIMIT do
		for j = 0, LIMIT do
			it("should unsigned add " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:uadd(a, b)
				assert.equal(i + j, r:to_scalar())

				r:uadd_scalar(a, j)
				assert.equal(i + j, r:to_scalar())

				r:uadd_scalar(b, i)
				assert.equal(i + j, r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)

			if i >= j then
				it("should unsigned subtract " .. i .. " and " .. j .. " correctly", function()
					a:set_scalar(i)
					b:set_scalar(j)

					r:usub(a, b)
					assert.equal(i - j, r:to_scalar())

					r:usub_scalar(a, j)
					assert.equal(i - j, r:to_scalar())

					assert.equal(i, a:to_scalar())
					assert.equal(j, b:to_scalar())
				end)
			end

			it("should unsigned multiply " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:umul(a, b)
				assert.equal(i * j, r:to_scalar())

				r:umul_scalar(a, j)
				assert.equal(i * j, r:to_scalar())

				r:umul_scalar(b, i)
				assert.equal(i * j, r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)

			if i ^ j < 2 ^ 52 then
				it("should unsigned pow " .. i .. " and " .. j .. " correctly", function()
					a:set_scalar(i)
					b:set_scalar(j)

					r:upow(a, b)
					assert.equal(i ^ j, r:to_scalar())

					r:upow_scalar(a, j)
					assert.equal(i ^ j, r:to_scalar())

					assert.equal(i, a:to_scalar())
					assert.equal(j, b:to_scalar())
				end)
			end

			it("should unsigned lshift " .. i .. " by " .. j .. " correctly", function()
				a:set_scalar(i)

				r:ulshift(a, j)
				assert.equal(i * 2 ^ j, r:to_scalar())

				assert.equal(i, a:to_scalar())
			end)

			it("should unsigned rshift " .. i .. " by " .. j .. " correctly", function()
				a:set_scalar(i)

				r:urshift(a, j)
				assert.equal(math.floor(i / 2 ^ j), r:to_scalar())

				assert.equal(i, a:to_scalar())
			end)

			it("should unsigned bitwise and " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:uband(a, b)
				assert.equal(bit.band(i, j), r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)

			it("should unsigned bitwise or " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:ubor(a, b)
				assert.equal(bit.bor(i, j), r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)

			it("should unsigned bitwise xor " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:ubxor(a, b)
				assert.equal(bit.bxor(i, j), r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)
		end
	end
end)

describe("signed integer arithmetic", function()
	local r = Integer.new_zero()
	local a = Integer.new_zero()
	local b = Integer.new_zero()

	for i = -LIMIT, LIMIT do
		for j = -LIMIT, LIMIT do
			it("should signed add " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:add(a, b)
				assert.equal(i + j, r:to_scalar())

				r:add_scalar(a, j)
				assert.equal(i + j, r:to_scalar())

				r:add_scalar(b, i)
				assert.equal(i + j, r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)

			it("should signed subtract " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:sub(a, b)
				assert.equal(i - j, r:to_scalar())

				r:sub_scalar(a, j)
				assert.equal(i - j, r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)

			it("should signed multiply " .. i .. " and " .. j .. " correctly", function()
				a:set_scalar(i)
				b:set_scalar(j)

				r:mul(a, b)
				assert.equal(i * j, r:to_scalar())

				r:mul_scalar(a, j)
				assert.equal(i * j, r:to_scalar())

				r:mul_scalar(b, i)
				assert.equal(i * j, r:to_scalar())

				assert.equal(i, a:to_scalar())
				assert.equal(j, b:to_scalar())
			end)

			if math.abs(i ^ j) < 2 ^ 32 then
				it("should signed pow " .. i .. " and " .. j .. " correctly", function()
					a:set_scalar(i)
					b:set_scalar(j)

					r:pow(a, b)
					assert.equal(trunc(i ^ j), r:to_scalar())

					r:pow_scalar(a, j)
					assert.equal(trunc(i ^ j), r:to_scalar())

					assert.equal(i, a:to_scalar())
					assert.equal(j, b:to_scalar())
				end)
			end

			it("should signed lshift " .. i .. " by " .. j .. " correctly", function()
				a:set_scalar(i)

				r:lshift(a, j)
				assert.equal(trunc(i * 2 ^ j), r:to_scalar())

				assert.equal(i, a:to_scalar())
			end)

			it("should signed rshift " .. i .. " by " .. j .. " correctly", function()
				a:set_scalar(i)

				r:rshift(a, j)
				assert.equal(trunc(i / 2 ^ j), r:to_scalar())

				assert.equal(i, a:to_scalar())
			end)
		end
	end
end)
