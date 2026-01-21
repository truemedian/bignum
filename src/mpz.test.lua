require("busted.runner")()

local bit = require("bit")
local mpz = require("mpz")
local mpn = require("mpn")

local LIMB_SIZE = mpn.LIMB_SIZE
local LIMB_RADIX = mpn.LIMB_RADIX
local LIMB_MAX = mpn.LIMB_MAX

local R = LIMB_RADIX ^ 2
--- Given a number, return the truncated integer value.
---@param x number
---@return integer
local function scalar(x)
	if x >= 0 then
		return math.floor(x)
	else
		return math.ceil(x)
	end
end

describe("mpz.from_zero", function()
	it("is zero", function()
		local a = mpz.from_zero()
		assert.are.equal(0, mpz.sign(a))
		assert.are.equal(0, mpz.to_number(a))
	end)
end)

describe("mpz.from_one", function()
	it("is one", function()
		local a = mpz.from_one()
		assert.are.equal(1, mpz.sign(a))
		assert.are.equal(1, mpz.to_number(a))
	end)
end)

describe("mpz.from_number", function()
	it("is correct #validate", function()
		for x = -R, R do
			local a = mpz.from_number(x)
			assert.are.equal(x, mpz.to_number(a))

			if x == 0 then
				assert.are.equal(0, mpz.sign(a))
			else
				assert.are.equal(x / math.abs(x), mpz.sign(a))
			end

			assert.are.equal(x == 0, mpz.is_zero(a))
			assert.are.equal(x > 0, mpz.is_positive(a))
			assert.are.equal(x < 0, mpz.is_negative(a))
			assert.are.equal(string.format("%i", x), mpz.to_string(a, 10))

			mpz.neg(a)
			assert.are.equal(-x, mpz.to_number(a))

			mpz.abs(a)
			assert.are.equal(math.abs(x), mpz.to_number(a))
		end
	end)
end)

describe("mpz.cmp", function()
	it("is correct #validate", function()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -R, R do
				local b = mpz.from_number(y)

				local c = mpz.cmp(a, b)
				local c_abs = mpz.cmpabs(a, b)

				assert.are.equal(math.abs(x) < math.abs(y), c_abs < 0)
				assert.are.equal(math.abs(x) == math.abs(y), c_abs == 0)
				assert.are.equal(math.abs(x) > math.abs(y), c_abs > 0)

				assert.are.equal(x < y, c < 0)
				assert.are.equal(x == y, c == 0)
				assert.are.equal(x > y, c > 0)
			end
		end
	end)
end)

describe("mpz.add_scalar", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -LIMB_MAX, LIMB_MAX do
				mpz.add_scalar(r, a, y)
				assert.are.equal(x + y, mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.add", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -R, R do
				local b = mpz.from_number(y)
				mpz.add(r, a, b)
				assert.are.equal(x + y, mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.sub_scalar", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -LIMB_MAX, LIMB_MAX do
				mpz.sub_scalar(r, a, y)
				assert.are.equal(x - y, mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.scalar_sub", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -LIMB_MAX, LIMB_MAX do
				mpz.scalar_sub(r, y, a)
				assert.are.equal(y - x, mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.sub", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -R, R do
				local b = mpz.from_number(y)
				mpz.sub(r, a, b)
				assert.are.equal(x - y, mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.mul_scalar", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -LIMB_MAX, LIMB_MAX do
				mpz.mul_scalar(r, a, y)
				assert.are.equal(x * y, mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.mul", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -R, R do
				local b = mpz.from_number(y)
				mpz.mul_noalias(r, a, b)
				assert.are.equal(x * y, mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.sqr_scalar", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -LIMB_MAX, LIMB_MAX do
			mpz.sqr_scalar(r, x)
			assert.are.equal(x * x, mpz.to_number(r))
		end
	end)
end)

describe("mpz.sqr", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			mpz.sqr_noalias(r, a)
			assert.are.equal(x * x, mpz.to_number(r))
		end
	end)
end)

describe("mpz.lshift", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = 0, 32 do
				mpz.lshift(r, a, y)
				assert.are.equal(scalar(x * 2 ^ y), mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.rshift", function()
	it("is correct #validate", function()
		local r = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = 0, 32 do
				mpz.rshift(r, a, y)
				assert.are.equal(scalar(x / 2 ^ y), mpz.to_number(r))
			end
		end
	end)
end)

describe("mpz.divrem_scalar", function()
	it("is correct #validate", function()
		local q = mpz.from_zero()
		for x = -R, R do
			local a = mpz.from_number(x)
			for y = -LIMB_MAX, LIMB_MAX do
				if y ~= 0 then
					local r = mpz.divrem_scalar(q, a, y)

					local nq = scalar(x / y)
					local nr = x - nq * y
					assert.are.equal(nq, mpz.to_number(q))
					assert.are.equal(nr, r)
				end
			end
		end
	end)
end)

describe("mpz.divrem & mpz.rem", function()
	it("is correct #validate", function()
		local q = mpz.from_zero()
		local r = mpz.from_zero()
		for x = -R, R do
			for y = -R, R do
				if y ~= 0 then
					local a0 = mpz.from_number(x) -- a is clobbered every time
					local a1 = mpz.dup(a0)

					local b = mpz.from_number(y)
					local nq = scalar(x / y)
					local nr = x - nq * y

					mpz.divrem_noalias(q, r, a0, b)
					assert.are.equal(nq, mpz.to_number(q))
					assert.are.equal(nr, mpz.to_number(r))

					mpz.rem_noalias(r, a1, b)
					assert.are.equal(nr, mpz.to_number(r))
				end
			end
		end
	end)
end)
