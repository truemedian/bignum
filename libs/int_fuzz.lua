local Integer = require("int")
local fuzzer = require("aflua")

local function check(buf)
	if buf:find("[^0-9a-zA-Z]") then
		fuzzer.skip()
		return
	end

	local r = Integer.new_zero()
    for base = 2, 36 do
        local expect = tonumber(buf, base)
        if expect and math.abs(expect) < 2 ^ 50 then
            r:set_string(buf, base)
            local actual = r:to_scalar()

            if actual ~= expect then
                print("buf", buf)
                print("base", base)
                print("expect", expect)
                print("actual", actual)
                error('failed')
            end
        end
    end

	local expect = tonumber(buf)
    if expect and math.abs(expect) < 2 ^ 50 then
		r:set_string(buf)
		local actual = r:to_scalar()

		if actual ~= expect then
			print("buf", buf)
			print("expect", expect)
			print("actual", actual)
			error('failed')
		end
	end
end

fuzzer.init()
fuzzer.coverage_hook(true)
fuzzer.run(check)
