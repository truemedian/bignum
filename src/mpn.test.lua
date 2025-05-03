require("busted.runner")()

local mpn = require("mpn")

local LIMB_SIZE = mpn.LIMB_SIZE
local LIMB_RADIX = mpn.LIMB_RADIX
local LIMB_MAX = mpn.LIMB_MAX

local function scalar(a, a0, n)
	local r = 0
	for i = a0 + 1, a0 + n do
		r = r + a[i] * LIMB_RADIX ^ (i - a0 - 1)
	end
	return r
end

describe("mpn.copyi", function()
	it("copies", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyi(r, 0, a, 0, 3)
		assert.are.same({ 1, 2, 3 }, r)
	end)

	it("copies, offset input", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyi(r, 0, a, 1, 2)
		assert.are.same({ 2, 3, -1 }, r)
	end)

	it("copies, offset output", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyi(r, 1, a, 0, 3)
		assert.are.same({ -1, 1, 2, 3 }, r)
	end)

	it("copies, offset input and output", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyi(r, 1, a, 1, 2)
		assert.are.same({ -1, 2, 3 }, r)
	end)

	it("copies, forward overlap", function()
		local a = { 1, 2, 3, 4, 5 }

		mpn.copyi(a, 1, a, 2, 3)
		assert.are.same({ 1, 3, 4, 5, 5 }, a)
	end)

	it("copies, backwards overlap fails", function()
		local a = { 1, 2, 3, 4, 5 }

		mpn.copyi(a, 1, a, 0, 3)
		assert.are_not.same({ 1, 1, 2, 3, 5 }, a)
	end)
end)

describe("mpn.copyd", function()
	it("copies", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyd(r, 0, a, 0, 3)
		assert.are.same({ 1, 2, 3 }, r)
	end)

	it("copies, offset input", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyd(r, 0, a, 1, 2)
		assert.are.same({ 2, 3, -1 }, r)
	end)

	it("copies, offset output", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyd(r, 1, a, 0, 3)
		assert.are.same({ -1, 1, 2, 3 }, r)
	end)

	it("copies, offset input and output", function()
		local r = { -1, -1, -1 }
		local a = { 1, 2, 3 }

		mpn.copyd(r, 1, a, 1, 2)
		assert.are.same({ -1, 2, 3 }, r)
	end)

	it("copies, forward overlap fails", function()
		local a = { 1, 2, 3, 4, 5 }

		mpn.copyd(a, 1, a, 2, 3)
		assert.are_not.same({ 1, 3, 4, 5, 5 }, a)
	end)

	it("copies, backwards overlap", function()
		local a = { 1, 2, 3, 4, 5 }

		mpn.copyd(a, 1, a, 0, 3)
		assert.are.same({ 1, 1, 2, 3, 5 }, a)
	end)
end)

describe("mpn.cmp", function()
	it("compares equal", function()
		local a = { 1, 2, 3 }
		local b = { 1, 2, 3 }

		assert.equal(true, mpn.cmp(a, 0, 3, b, 0, 3) == 0)
	end)

	it("compares less than length", function()
		local a = { 1, 2 }
		local b = { 1, 2, 3 }

		assert.equal(true, mpn.cmp(a, 0, 2, b, 0, 3) < 0)
	end)

	it("compares less than values", function()
		local a = { 0, 2, 3 }
		local b = { 1, 2, 3 }

		assert.equal(true, mpn.cmp(a, 0, 3, b, 0, 3) < 0)
	end)

	it("compares greater than length", function()
		local a = { 1, 2, 3 }
		local b = { 1, 2 }

		assert.equal(true, mpn.cmp(a, 0, 3, b, 0, 2) > 0)
	end)

	it("compares greater than values", function()
		local a = { 1, 2, 3 }
		local b = { 0, 2, 3 }

		assert.equal(true, mpn.cmp(a, 0, 3, b, 0, 3) > 0)
	end)
end)

describe("mpn.cmp_n", function()
	it("compares equal", function()
		local a = { 1, 2, 3 }
		local b = { 1, 2, 3 }

		assert.equal(true, mpn.cmp_n(a, 0, b, 0, 3) == 0)
	end)

	it("compares less than values", function()
		local a = { 0, 2, 3 }
		local b = { 1, 2, 3 }

		assert.equal(true, mpn.cmp_n(a, 0, b, 0, 3) < 0)
	end)

	it("compares greater than values", function()
		local a = { 1, 2, 3 }
		local b = { 0, 2, 3 }

		assert.equal(true, mpn.cmp_n(a, 0, b, 0, 3) > 0)
	end)
end)

describe("mpn.normalized_size", function()
	it("no normalization", function()
		local a = { 1, 2, 3 }

		assert.are.same(3, mpn.normalized_size(a, 0, 3))
	end)

	it("some normalization", function()
		local a = { 1, 2, 0 }

		assert.are.same(2, mpn.normalized_size(a, 0, 3))
	end)

	it("zero", function()
		local a = { 0, 0, 0 }

		assert.are.same(0, mpn.normalized_size(a, 0, 3))
	end)
end)

describe("mpn.is_zero", function()
	it("not zero", function()
		local a = { 1, 2, 3 }

		assert.are.same(false, mpn.is_zero(a, 0, 3))
	end)

	it("zero", function()
		local a = { 0, 0, 0 }

		assert.are.same(true, mpn.is_zero(a, 0, 3))
	end)
end)

describe("mpn.zero", function()
	it("makes zero", function()
		local a = { 1, 2, 3 }

		mpn.zero(a, 0, 3)
		assert.are.same({ 0, 0, 0 }, a)
	end)
end)

describe("mpn.zero", function()
	it("makes zero", function()
		local a = { 1, 2, 3 }

		mpn.zero(a, 0, 3)
		assert.are.same({ 0, 0, 0 }, a)
	end)
end)

describe("mpn.add_1", function()
	it("increments without carry", function()
		local a = { 1, 2 }
		local r = {}

		local c = mpn.add_1(r, 0, a, 0, 2, 2)
		assert.are.same({ 3, 2 }, r)
		assert.are.same(0, c)
	end)

	it("increments with carry", function()
		local a = { LIMB_MAX, 2 }
		local r = {}

		local c = mpn.add_1(r, 0, a, 0, 2, 2)
		assert.are.same({ 1, 3 }, r)
		assert.are.same(0, c)
	end)

	it("increments with overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local r = {}

		local c = mpn.add_1(r, 0, a, 0, 2, 2)
		assert.are.same({ 1, 0 }, r)
		assert.are.same(1, c)
	end)
end)

describe("mpn.add_n", function()
	it("increments without carry", function()
		local a = { 1, 2 }
		local b = { 2, 1 }
		local r = {}

		local c = mpn.add_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ 3, 3 }, r)
		assert.are.same(0, c)
	end)

	it("increments with carry", function()
		local a = { LIMB_MAX, 1 }
		local b = { 2, 1 }
		local r = {}

		local c = mpn.add_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ 1, 3 }, r)
		assert.are.same(0, c)
	end)

	it("increments with overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local b = { 2, 1 }
		local r = {}

		local c = mpn.add_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ 1, 1 }, r)
		assert.are.same(1, c)
	end)
end)

describe("mpn.add", function()
	it("increments without carry", function()
		local a = { 1, 2 }
		local b = { 2 }
		local r = {}

		local c = mpn.add(r, 0, a, 0, 2, b, 0, 1)
		assert.are.same({ 3, 2 }, r)
		assert.are.same(0, c)
	end)

	it("increments with carry", function()
		local a = { LIMB_MAX, 1 }
		local b = { 2 }
		local r = {}

		local c = mpn.add(r, 0, a, 0, 2, b, 0, 1)
		assert.are.same({ 1, 2 }, r)
		assert.are.same(0, c)
	end)

	it("increments with overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local b = { 2 }
		local r = {}

		local c = mpn.add(r, 0, a, 0, 2, b, 0, 1)
		assert.are.same({ 1, 0 }, r)
		assert.are.same(1, c)
	end)
end)

describe("mpn.sub_1", function()
	it("decrements without carry", function()
		local a = { 2, 2 }
		local r = {}

		local c = mpn.sub_1(r, 0, a, 0, 2, 2)
		assert.are.same({ 0, 2 }, r)
		assert.are.same(0, c)
	end)

	it("decrements with carry", function()
		local a = { 1, 2 }
		local r = {}

		local c = mpn.sub_1(r, 0, a, 0, 2, 2)
		assert.are.same({ LIMB_MAX, 1 }, r)
		assert.are.same(0, c)
	end)

	it("decrements with overflow", function()
		local a = { 1, 0 }
		local r = {}

		local c = mpn.sub_1(r, 0, a, 0, 2, 2)
		assert.are.same({ LIMB_MAX, LIMB_MAX }, r)
		assert.are.same(1, c)
	end)
end)

describe("mpn.sub_n", function()
	it("decrements without carry", function()
		local a = { 2, 2 }
		local b = { 1, 1 }
		local r = {}

		local c = mpn.sub_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ 1, 1 }, r)
		assert.are.same(0, c)
	end)

	it("decrements with carry", function()
		local a = { 1, 2 }
		local b = { 2, 1 }
		local r = {}

		local c = mpn.sub_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ LIMB_MAX, 0 }, r)
		assert.are.same(0, c)
	end)

	it("decrements with overflow", function()
		local a = { 1, 1 }
		local b = { 2, 1 }
		local r = {}

		local c = mpn.sub_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ LIMB_MAX, LIMB_MAX }, r)
		assert.are.same(1, c)
	end)
end)

describe("mpn.sub", function()
	it("decrements without carry", function()
		local a = { 2, 2 }
		local b = { 1 }
		local r = {}

		local c = mpn.sub(r, 0, a, 0, 2, b, 0, 1)
		assert.are.same({ 1, 2 }, r)
		assert.are.same(0, c)
	end)

	it("decrements with carry", function()
		local a = { 2, 2 }
		local b = { 3 }
		local r = {}

		local c = mpn.sub(r, 0, a, 0, 2, b, 0, 1)
		assert.are.same({ LIMB_MAX, 1 }, r)
		assert.are.same(0, c)
	end)

	it("decrements with overflow", function()
		local a = { 1, 1 }
		local b = { 2, 1 }
		local r = {}

		local c = mpn.sub(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same({ LIMB_MAX, LIMB_MAX }, r)
		assert.are.same(1, c)
	end)
end)

describe("mpn.mul_1", function()
	it("multiplies", function()
		local a = { 1, 2 }
		local r = {}

		r[3] = mpn.mul_1(r, 0, a, 0, 2, 4)
		assert.are.same(((1 + 2 * LIMB_RADIX) * 4), scalar(r, 0, 3))
	end)

	it("multiplies with non-trivial overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local r = {}

		r[3] = mpn.mul_1(r, 0, a, 0, 2, LIMB_MAX)
		assert.are.same(((LIMB_MAX + LIMB_MAX * LIMB_RADIX) * LIMB_MAX), scalar(r, 0, 3))
	end)
end)

describe("mpn.addmul_1", function()
	it("multiplies with non-trivial overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local r = { 0, 0 }

		r[3] = mpn.addmul_1(r, 0, a, 0, 2, LIMB_MAX)
		assert.are.same(((LIMB_MAX + LIMB_MAX * LIMB_RADIX) * LIMB_MAX), scalar(r, 0, 3))
	end)

	it("increments and multiplies with non-trivial overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local r = { LIMB_MAX, LIMB_MAX }

		r[3] = mpn.addmul_1(r, 0, a, 0, 2, LIMB_MAX)
		assert.are.same(
			((LIMB_MAX + LIMB_MAX * LIMB_RADIX) + (LIMB_MAX + LIMB_MAX * LIMB_RADIX) * LIMB_MAX),
			scalar(r, 0, 3)
		)
	end)
end)

describe("mpn.submul_1", function()
	it("decrements and multiplies", function()
		local a = { 1, 1 }
		local r = { 5, 4 }

		r[3] = mpn.submul_1(r, 0, a, 0, 2, 4)
		assert.are.same(1, scalar(r, 0, 3))
	end)
end)

describe("mpn.mul", function()
	it("multiplies", function()
		local a = { 1, 2 }
		local b = { 1, 2 }
		local r = {}

		mpn.mul(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same({ 1, 4, 4, 0 }, r)
	end)
end)

describe("mpn.addmul", function()
	it("multiplies and adds", function()
		local a = { 1, 2 }
		local b = { 1, 2 }
		local r = { 1, 1, 1, 1 }

		mpn.addmul(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same({ 2, 5, 5, 1, 0 }, r)
	end)

	it("multiplies with large overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local b = { LIMB_MAX, LIMB_MAX }
		local r = { LIMB_MAX, LIMB_MAX, LIMB_MAX, LIMB_MAX }

		mpn.addmul(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same({ 0, 0, LIMB_MAX - 1, LIMB_MAX, 1 }, r)
	end)
end)

describe("mpn.submul", function()
	it("multiplies and subtracts", function()
		local a = { 1, 2 }
		local b = { 1, 2 }
		local r = { 1, 1, 1, 1 }

		mpn.submul(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same({ 0, LIMB_MAX - 2, LIMB_MAX - 3, 0 }, r)
	end)
end)

describe("mpn.sqr", function() end)

describe("mpn.lshift", function() end)

describe("mpn.rshift", function() end)

describe("mpn.divmod", function() end)

describe("mpn.mod", function() end)

describe("mpn.divmod_1", function() end)

describe("mpn.mod_1", function() end)

describe("mpn.gcd_11", function() end)

describe("mpn.gcd_1", function() end)

describe("mpn.gcd", function() end)

describe("mpn.pow_1", function() end)

describe("mpn.pow", function() end)

describe("mpn.sqrtrem", function() end)

describe("mpn.is_perfect_square", function() end)

describe("mpn.is_power_of_two", function() end)

describe("mpn.popcount", function() end)

describe("mpn.log2_floor", function() end)

describe("mpn.log2_ceil", function() end)

describe("mpn.bextract", function() end)

describe("mpn.band_n", function() end)

describe("mpn.bior_n", function() end)

describe("mpn.bxor_n", function() end)

describe("mpn.bandn_n", function() end)

describe("mpn.biorn_n", function() end)

describe("mpn.bnand_n", function() end)

describe("mpn.binor_n", function() end)

describe("mpn.bxnor_n", function() end)

describe("mpn.bnot_n", function() end)

describe("mpn.bscan0", function() end)

describe("mpn.bscan1", function() end)
