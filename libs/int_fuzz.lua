local luzer = require("luzer")
local Integer = require("int")

local function check(buf)
	local a = Integer.new_zero()
	local b = Integer.new_zero()
	local r = Integer.new_zero()

	local fdp = luzer.FuzzedDataProvider(buf)
	a.positive = fdp:consume_boolean()
	b.positive = fdp:consume_boolean()

	a.n = fdp:consume_integer(4, 256)
	b.n = fdp:consume_integer(4, 256)

	for i = 1, a.n do
		a.limbs[i] = fdp:consume_integer(0, 255)
	end

	for i = 1, b.n do
		b.limbs[i] = fdp:consume_integer(0, 255)
	end

	a:normalize()
	b:normalize()

	r:add(a, b)
	r:sub(a, b)
	r:mul(a, b)
end

luzer.Fuzz(function(buf)
	check(buf)
end, nil, { })

