---@type Integer
local Integer = require("../init.lua").Integer

local function all(a, b) return true end

local tests = {}
local passed, skipped, failed = {}, {}, {}

local function test(filter, name, fn) tests[name] = {filter = filter, fn = fn} end

local function run(values, construct)
    for _, a in ipairs(values) do
        for _, b in ipairs(values) do
            local A, B = construct(a), construct(b)

            for name, data in pairs(tests) do
                if data.filter == all or data.filter(a, b) then
                    local ok, expected, result = pcall(data.fn, a, b, A, B)
                    if ok then
                        if getmetatable(result) == Integer then result = result:tonumber() end

                        if expected == result then
                            passed[name] = (passed[name] or 0) + 1
                        else
                            print('fail ' .. name .. '(' .. a .. ', ' .. b .. '): expected ' .. string.format('%i', expected) .. ', got ' .. string.format('%i', result))
                            failed[name] = (failed[name] or 0) + 1
                        end
                    else
                        print('fail ' .. name .. '(' .. a .. ', ' .. b .. '): error ' .. expected)
                        failed[name] = (failed[name] or 0) + 1
                    end
                else
                    skipped[name] = (skipped[name] or 0) + 1
                end
            end
        end
    end
end

local function report()
    local names = {}
    local name_col_width = 0
    for name, _ in pairs(tests) do
        name_col_width = math.max(name_col_width, #name)
        table.insert(names, name)
    end

    table.sort(names)

    local total_failed = 0
    for _, name in ipairs(names) do
        local pass = passed[name] or 0
        local skip = skipped[name] or 0
        local fail = failed[name] or 0
        local total = pass + skip + fail
        total_failed = total_failed + fail

        print(('%-' .. name_col_width .. 's %d/%d passed, %d skipped, %d failed'):format(name, pass, total, skip, fail))
    end

    print('overall failed: ' .. total_failed)
    print()

    tests = {}
end

return {all = all, test = test, run = run, report = report, Integer = Integer}
