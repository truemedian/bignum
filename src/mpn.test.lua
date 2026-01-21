require("busted.runner")()

local bit = require("bit")
local mpn = require("mpn")

local LIMB_SIZE = mpn.LIMB_SIZE
local LIMB_RADIX = mpn.LIMB_RADIX
local LIMB_MAX = mpn.LIMB_MAX

local function scalar(a, a0, n)
	local result = 0
	for i = 1, n do
		result = result + a[a0 + i] * LIMB_RADIX ^ (i - 1)
	end
	return result
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
	it("is correct #validate", function()
		local a = {}
		local r = {}

		for i = 0, LIMB_MAX do
			for x = 0, LIMB_MAX do
				a[1] = i
				local c = mpn.add_1(r, 0, a, 0, 1, x)

				assert.are.same(scalar(a, 0, 1) + x, scalar(r, 0, 1) + c * LIMB_RADIX)
			end
		end

		for i = 0, LIMB_MAX do
			for j = 0, LIMB_MAX do
				for x = 0, LIMB_MAX do
					a[1] = i
					a[2] = j
					local c = mpn.add_1(r, 0, a, 0, 2, x)

					assert.are.same(scalar(a, 0, 2) + x, scalar(r, 0, 2) + c * LIMB_RADIX ^ 2)
				end
			end
		end

		for i = 0, LIMB_MAX do
			for j = 0, LIMB_MAX do
				for k = 0, LIMB_MAX do
					for x = 0, LIMB_MAX do
						a[1] = i
						a[2] = j
						a[3] = k
						local c = mpn.add_1(r, 0, a, 0, 3, x)

						assert.are.same(scalar(a, 0, 3) + x, scalar(r, 0, 3) + c * LIMB_RADIX ^ 3)
					end
				end
			end
		end
	end)

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
	it("is correct #validate", function()
		local a = {}
		local r = {}

		for i = 0, LIMB_MAX do
			for x = 0, LIMB_MAX do
				a[1] = i
				local c = mpn.sub_1(r, 0, a, 0, 1, x)

				assert.are.same(scalar(a, 0, 1) - x, scalar(r, 0, 1) - c * LIMB_RADIX)
			end
		end

		for i = 0, LIMB_MAX do
			for j = 0, LIMB_MAX do
				for x = 0, LIMB_MAX do
					a[1] = i
					a[2] = j
					local c = mpn.sub_1(r, 0, a, 0, 2, x)

					assert.are.same(scalar(a, 0, 2) - x, scalar(r, 0, 2) - c * LIMB_RADIX ^ 2)
				end
			end
		end

		for i = 0, LIMB_MAX do
			for j = 0, LIMB_MAX do
				for k = 0, LIMB_MAX do
					for x = 0, LIMB_MAX do
						a[1] = i
						a[2] = j
						a[3] = k
						local c = mpn.sub_1(r, 0, a, 0, 3, x)

						assert.are.same(scalar(a, 0, 3) - x, scalar(r, 0, 3) - c * LIMB_RADIX ^ 3)
					end
				end
			end
		end
	end)

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

		r[3] = mpn.addmul_1(r, 0, 2, a, 0, 2, LIMB_MAX)
		assert.are.same(((LIMB_MAX + LIMB_MAX * LIMB_RADIX) * LIMB_MAX), scalar(r, 0, 3))
	end)

	it("increments and multiplies with non-trivial overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local r = { LIMB_MAX, LIMB_MAX }

		r[3] = mpn.addmul_1(r, 0, 2, a, 0, 2, LIMB_MAX)
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

		r[3] = mpn.submul_1(r, 0, 2, a, 0, 2, 4)
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

		local c = mpn.addmul(r, 0, 4, a, 0, 2, b, 0, 2)
		assert.are.same({ 2, 5, 5, 1 }, r)
		assert.are.same(0, c)
	end)

	it("multiplies with large overflow", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local b = { LIMB_MAX, LIMB_MAX }
		local r = { LIMB_MAX, LIMB_MAX, LIMB_MAX, LIMB_MAX }

		local c = mpn.addmul(r, 0, 4, a, 0, 2, b, 0, 2)
		assert.are.same({ 0, 0, LIMB_MAX - 1, LIMB_MAX }, r)
		assert.are.same(1, c)
	end)
end)

describe("mpn.submul", function()
	it("multiplies and subtracts", function()
		local a = { 1, 2 }
		local b = { 1, 2 }
		local r = { 1, 1, 1, 1 }

		local c = mpn.submul(r, 0, 4, a, 0, 2, b, 0, 2)
		assert.are.same({ 0, LIMB_MAX - 2, LIMB_MAX - 3, 0 }, r)
	end)
end)

describe("mpn.sqr", function()
	it("squares a number", function()
		local a = { 2, 3 }
		local r = {}
		mpn.sqr(r, 0, a, 0, 2)
		assert.are.same(scalar(a, 0, 2) ^ 2, scalar(r, 0, 4))
	end)
end)

describe("mpn.lshift", function()
	it("left shifts a number", function()
		local a = { 1, 2 }
		local r = {}
		mpn.lshift(r, 0, a, 0, 2, 1)
		assert.are.same(scalar(a, 0, 2) * 2, scalar(r, 0, 2))
	end)
end)

describe("mpn.rshift", function()
	it("right shifts a number", function()
		local a = { 2, 4 }
		local r = {}
		mpn.rshift(r, 0, a, 0, 2, 1)
		assert.are.same(math.floor(scalar(a, 0, 2) / 2), scalar(r, 0, 2))
	end)
end)

describe("mpn.divmod", function()
	it("divides and returns remainder", function()
		local a = { 5, 1 }
		local b = { 3 }
		local q = {}
		local r = {}
		local sa, sb = scalar(a, 0, 2), scalar(b, 0, 1)
        mpn.divmod(q, 0, r, 0, a, 0, 2, b, 0, 1)
		assert.are.same(math.floor(sa / sb), scalar(q, 0, 1))
		assert.are.same(sa % sb, scalar(r, 0, 1))
	end)
end)

describe("mpn.mod", function()
	it("returns remainder", function()
		local a = { 5, 1 }
		local b = { 3 }
		local r = {}
		local sa, sb = scalar(a, 0, 2), scalar(b, 0, 1)
		mpn.mod(r, 0, a, 0, 2, b, 0, 1)
		assert.are.same(sa % sb, scalar(r, 0, 1))
	end)
end)

describe("mpn.divmod_1", function()
	it("divides by single limb and returns remainder", function()
		local a = { 5, 0 }
		local q = {}
		local r = mpn.divmod_1(q, 0, a, 0, 2, 2)
		assert.are.same(math.floor(scalar(a, 0, 2) / 2), scalar(q, 0, 2))
		assert.are.same(scalar(a, 0, 2) % 2, r)
	end)
end)

describe("mpn.mod_1", function()
	it("returns remainder for single limb", function()
		local a = { 5, 0 }
		local r = mpn.mod_1(a, 0, 2, 2)
		assert.are.same(scalar(a, 0, 2) % 2, r)
	end)
end)

describe("mpn.gcd_11", function()
	it("gcd of two limbs", function()
		assert.are.same(2, mpn.gcd_11(6, 4))
	end)

	it("gcd of coprime limbs", function()
		assert.are.same(1, mpn.gcd_11(7, 4))
	end)

	it("gcd with zero", function()
		assert.are.same(7, mpn.gcd_11(7, 0))
	end)
end)

describe("mpn.gcd_1", function()
	it("gcd of array and limb", function()
		local a = { 6, 1 }
		assert.are.same(2, mpn.gcd_1(a, 0, 2, 4))
	end)

	it("gcd of array and coprime limb", function()
		local a = { 7, 1 }
		assert.are.same(1, mpn.gcd_1(a, 0, 2, 4))
	end)

	it("gcd with zero limb", function()
		local a = { 0, 0 }
		assert.are.same(5, mpn.gcd_1(a, 0, 2, 5))
	end)
end)

describe("mpn.gcd", function()
	it("gcd of two numbers", function()
		local a = { 6, 1 }
		local b = { 4, 1 }
		local r = {}
		local rn = mpn.gcd(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same(2, scalar(r, 0, rn))
	end)

	it("gcd of coprime arrays", function()
		local a = { 7, 1 }
		local b = { 3, 1 }
		local r = {}
		local rn = mpn.gcd(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same(1, scalar(r, 0, rn))
	end)

	it("gcd with zero array", function()
		local a = { 0, 0 }
		local b = { 5, 1 }
		local r = {}
		local rn = mpn.gcd(r, 0, a, 0, 2, b, 0, 2)
		assert.are.same(scalar(b, 0, 2), scalar(r, 0, rn))
	end)
end)

pending("mpn.sqrtrem", function()
	it("computes square root and remainder", function()
		local a = { 4, 0 }
		local r = {}
		local e = {}
		local en = mpn.sqrtrem(r, 0, e, 0, a, 0, 2)
		assert.are.same(2, scalar(r, 0, 2))
		assert.are.same(0, scalar(e, 0, en))
	end)

	it("computes square root with non-zero remainder", function()
		local a = { 5, 0 }
		local r = {}
		local e = {}
		local en = mpn.sqrtrem(r, 0, e, 0, a, 0, 2)
		assert.are.same(2, scalar(r, 0, 2))
		assert.are.same(1, scalar(e, 0, en))
	end)

	it("edge case: zero", function()
		local a = { 0 }
		local r = {}
		local e = {}
		local en = mpn.sqrtrem(r, 0, e, 0, a, 0, 1)
		assert.are.same(0, scalar(r, 0, 1))
		assert.are.same(0, scalar(e, 0, en))
	end)
end)

pending("mpn.is_perfect_square", function()
	it("detects perfect square", function()
		local a = { 4, 0 }
		assert.is_true(mpn.is_perfect_square(a, 0, 2))
	end)

	it("detects non-perfect square", function()
		local a = { 5, 0 }
		assert.is_false(mpn.is_perfect_square(a, 0, 2))
	end)

	it("zero is not a perfect square", function()
		local a = { 0 }
		assert.is_false(mpn.is_perfect_square(a, 0, 1))
	end)
end)

describe("mpn.is_power_of_two", function()
	it("detects power of two", function()
		local a = { 0, 1 }
		assert.is_true(mpn.is_power_of_two(a, 0, 2))
	end)

	it("detects non-power of two", function()
		local a = { 3, 0 }
		assert.is_false(mpn.is_power_of_two(a, 0, 2))
	end)

	it("zero is not a power of two", function()
		local a = { 0 }
		assert.is_false(mpn.is_power_of_two(a, 0, 1))
	end)
end)

describe("mpn.popcount", function()
	it("counts set bits in a single limb", function()
		local a = { 7 }
		assert.are.same(3, mpn.popcount(a, 0, 1))
	end)

	it("counts set bits in multiple limbs", function()
		local a = { 7, 1 }
		assert.are.same(4, mpn.popcount(a, 0, 2))
	end)

	it("edge case: zero", function()
		local a = { 0 }
		assert.are.same(0, mpn.popcount(a, 0, 1))
	end)
end)

describe("mpn.log2_floor", function()
	it("computes log2_floor for power of two", function()
		local a = { 0, 1 }
		assert.are.same(LIMB_SIZE, mpn.log2_floor(a, 0, 2))
	end)

	it("computes log2_floor for non-power of two", function()
		local a = { 1, 1 }
		assert.are.same(LIMB_SIZE, mpn.log2_floor(a, 0, 2))
	end)
end)

describe("mpn.log2_ceil", function()
	it("computes log2_ceil for power of two", function()
		local a = { 0, 1 }
		assert.are.same(LIMB_SIZE, mpn.log2_ceil(a, 0, 2))
	end)

	it("computes log2_ceil for non-power of two", function()
		local a = { 1, 1 }
		assert.are.same(LIMB_SIZE + 1, mpn.log2_ceil(a, 0, 2))
	end)
end)

describe("mpn.bextract", function()
	it("extracts bits from a single limb", function()
		local a = { LIMB_MAX }
		local r = {}
		mpn.bextract(r, 0, a, 0, 1, 0, LIMB_SIZE - 1)
		assert.are.same(math.floor(LIMB_MAX / 2), scalar(r, 0, 1))
	end)

	it("extracts bits with offset", function()
		local a = { LIMB_MAX, LIMB_MAX }
		local r = {}
		mpn.bextract(r, 0, a, 0, 2, 2, LIMB_SIZE)
		assert.are.same(math.floor(LIMB_MAX), scalar(r, 0, 1))
	end)
end)

describe("mpn.band_n", function()
	local function expected(a, b)
		return bit.band(a, b)
	end

	it("bitwise and with full intersection", function()
		local a = { 7, 3 }
		local b = { 3, 2 }
		local r = {}
		mpn.band_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ expected(7, 3), expected(3, 2) }, r)
	end)

	it("bitwise and with partial intersection", function()
		local a = { 1, 0 }
		local b = { 3, 2 }
		local r = {}
		mpn.band_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ expected(1, 3), expected(0, 2) }, r)
	end)

	it("bitwise and with no intersection", function()
		local a = { 4 }
		local b = { 1 }
		local r = {}
		mpn.band_n(r, 0, a, 0, b, 0, 1)
		assert.are.same({ expected(4, 1) }, r)
	end)
end)

describe("mpn.bior_n", function()
	local function expected(a, b)
		return bit.bor(a, b)
	end

	it("bitwise or with full intersection", function()
		local a = { 7, 3 }
		local b = { 3, 2 }
		local r = {}
		mpn.bior_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ expected(7, 3), expected(3, 2) }, r)
	end)

	it("bitwise or with partial intersection", function()
		local a = { 1, 0 }
		local b = { 3, 2 }
		local r = {}
		mpn.bior_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ expected(1, 3), expected(0, 2) }, r)
	end)

	it("bitwise or with no intersection", function()
		local a = { 4 }
		local b = { 1 }
		local r = {}
		mpn.bior_n(r, 0, a, 0, b, 0, 1)
		assert.are.same({ expected(4, 1) }, r)
	end)
end)

describe("mpn.bxor_n", function()
	local function expected(a, b)
		return bit.bxor(a, b)
	end

	it("bitwise xor with full intersection", function()
		local a = { 7, 3 }
		local b = { 3, 2 }
		local r = {}
		mpn.bxor_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ expected(7, 3), expected(3, 2) }, r)
	end)

	it("bitwise xor with zeros", function()
		local a = { 1, 0 }
		local b = { 3, 2 }
		local r = {}
		mpn.bxor_n(r, 0, a, 0, b, 0, 2)
		assert.are.same({ expected(1, 3), expected(0, 2) }, r)
	end)

	it("bitwise xor with no intersection", function()
		local a = { 4 }
		local b = { 1 }
		local r = {}
		mpn.bxor_n(r, 0, a, 0, b, 0, 1)
		assert.are.same({ expected(4, 1) }, r)
	end)
end)

describe("mpn.bscan0", function()
	it("finds lowest zero bit in all-ones limb", function()
		local a = { LIMB_MAX }
		assert.are.same(LIMB_SIZE, mpn.bscan0(a, 0, 1))
	end)

	it("finds lowest zero bit in mixed limb", function()
		local a = { 7 }
		assert.are.same(3, mpn.bscan0(a, 0, 1))
	end)

	it("finds first zero zeros", function()
		local a = { 0 }
		assert.are.same(0, mpn.bscan0(a, 0, 1))
	end)
end)

describe("mpn.bscan1", function()
	it("finds lowest one bit in a limb", function()
		local a = { 2 }
		assert.are.same(1, mpn.bscan1(a, 0, 1))
	end)

	it("finds lowest one bit in a multi-limb array", function()
		local a = { 0, 4 }
		assert.are.same(LIMB_SIZE + 2, mpn.bscan1(a, 0, 2))
	end)

	it("edge case: all zeros returns infinity", function()
		local a = { 0, 0 }
		assert.are.same(math.huge, mpn.bscan1(a, 0, 2))
	end)
end)
