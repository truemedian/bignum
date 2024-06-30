-- Arbitrary precision integer
-- Limbs are stored little endian, with the radix provided below
local bit = require('bit')

local LIMB_BITS = 26
local RADIX = 2 ^ LIMB_BITS
local LIMB_MASK = RADIX - 1

local MAX_U32 = 2 ^ 32 - 1

assert(RADIX * RADIX ~= RADIX * RADIX + 1, 'radix overflow')
assert(RADIX * RADIX ~= RADIX * RADIX + 2, 'radix overflow')

--- computes r + a * b + carry
local function addMulWithCarry(r, a, b, carry)
    local ab = a * b + r + carry -- double wide multiplication
    local r2 = bit.band(ab, LIMB_MASK)
    local c2 = bit.band(math.floor(ab / RADIX), LIMB_MASK)

    return r2, c2
end

--- Knuth 4.3.1, Algorithm A.
--- Performs addition the limbs `a[a_n]...a[1]` by `b[b_n]...b[1]` and stores the result in `r`. Returns the carry bit.
local function limbwiseAddWithCarry(r, a, b, a_n, b_n)
    assert(a_n >= b_n)

    local i = 1
    local carry = 0

    -- add the common limbs
    while i <= b_n do
        local ov = a[i] + b[i] + carry
        r[i] = bit.band(ov, LIMB_MASK)
        carry = bit.rshift(ov, LIMB_BITS)
        i = i + 1
    end

    -- perform the carry on the remaining limbs
    while i <= a_n do
        local ov = a[i] + carry
        r[i] = bit.band(ov, LIMB_MASK)
        carry = bit.rshift(ov, LIMB_BITS)
        i = i + 1
    end

    return carry
end

--- Knuth 4.3.1, Algorithm S.
--- Performs subtraction the limbs `a[a_n]...a[1]` by `b[b_n]...b[1]` and stores the result in `r`. Returns the borrow bit.
local function limbwiseSubtractWithBorrow(r, a, b, a_n, b_n)
    assert(a_n >= b_n)

    local i = 1
    local borrow = 0

    -- subtract the common limbs
    while i <= b_n do
        local ov = a[i] - b[i] - borrow
        r[i] = bit.band(ov, LIMB_MASK)
        borrow = ov < 0 and 1 or 0
        i = i + 1
    end

    -- perform the borrow on the remaining limbs
    while i <= a_n do
        local ov = a[i] - borrow
        r[i] = bit.band(ov, LIMB_MASK)
        borrow = ov < 0 and 1 or 0
        i = i + 1
    end

    return borrow
end

--- Performs multiplication the limbs `a[a_n]...a[1]` by a scalar `b_i` and stores the result in `r`.
local function limbwiseAddMulScalar(r, i, a, b_i, a_n)
    if b_i == 0 then
        return
    end

    local carry = 0
    for j = 1, a_n do
        r[i + j - 1], carry = addMulWithCarry(r[i + j - 1], a[j], b_i, carry)
    end

    while carry ~= 0 do
        local ov = r[i + a_n] + carry
        r[i + a_n] = bit.band(ov, LIMB_MASK)
        carry = bit.rshift(ov, LIMB_BITS)

        i = i + 1
    end

    return carry ~= 0
end

--- Performs multiplication the limbs `a[a_n]...a[1]` by `b[b_n]...b[1]` and stores the result in `r`.
local function limbwiseMultiply(r, a, b, a_n, b_n)
    if a_n < b_n then
        a, b = b, a
        a_n, b_n = b_n, a_n
    end

    -- TODO: karatsuba

    -- long multiplication
    for i = 1, b_n do
        limbwiseAddMulScalar(r, i, a, b[i], a_n)
    end
end

--- Performs a logical left shift on the limbs `a[a_n]...a[1]` by `shift` bits and stores the result in `r`.
local function limbwiseShiftLeft(r, a, shift, a_n)
    local interior_shift = shift % LIMB_BITS
    local limb_shift = math.floor(shift / LIMB_BITS)

    if interior_shift == 0 then
        -- optimization for whole limb shifts
        for i = a_n, 1, -1 do
            r[i + limb_shift] = a[i]
        end
    else
        local carry = 0
        for src_i = a_n, 1, -1 do
            local src_digit = a[src_i]

            r[src_i + limb_shift + 1] = bit.bor(bit.rshift(src_digit, LIMB_BITS - interior_shift), carry)
            carry = bit.band(bit.lshift(src_digit, interior_shift), LIMB_MASK)
        end

        r[limb_shift + 1] = carry
    end

    for i = 1, limb_shift do
        r[i] = 0
    end
end

--- Performs a logical right shift on the limbs `a[a_n]...a[1]` by `shift` bits and stores the result in `r`.
local function limbwiseShiftRight(r, a, shift, a_n)
    local interior_shift = shift % LIMB_BITS
    local limb_shift = math.floor(shift / LIMB_BITS)

    if interior_shift == 0 then
        -- optimization for whole limb shifts
        for i = 1, a_n - limb_shift do
            r[i] = a[i + limb_shift]
        end
    else
        for dst_i = 1, a_n - limb_shift do
            local src_i = dst_i + limb_shift

            local src_digit = a[src_i] or 0
            local src_digit_next = a[src_i + 1] or 0
            local carry = bit.band(bit.lshift(src_digit_next, LIMB_BITS - interior_shift), LIMB_MASK)
            r[dst_i] = bit.bor(bit.rshift(src_digit, interior_shift), carry)
        end
    end

    for i = a_n - limb_shift + 1, a_n do
        r[i] = 0
    end
end

--- Performs normalization on the limbs `a[a_n]...a[1]` by removing leading zero limbs and returns the new length of the limbs.
local function limbwiseNormalize(a, a_n)
    local j = a_n

    -- find the last non-zero limb
    while j > 1 and (a[j] == 0 or a[j] == nil) do
        j = j - 1
    end

    for i = j + 1, math.max(a_n, #a) do
        a[i] = nil
    end

    return j
end

----------------------------------------

---@class Integer
---@field limbs table<number>
---@field n number
---@field neg boolean
local Integer = {}
Integer.__index = Integer

--- Constructs a new Integer from a number or string.
---@param num number|string
---@return Integer
function Integer.new(num)
    local self = setmetatable({n = 0, limbs = {}, neg = false}, Integer)

    return Integer.set(self, num)
end

--- Constructs a new Integer with the value of zero.
---@return Integer
function Integer.zero()
    return setmetatable({n = 1, limbs = {0}, neg = false}, Integer)
end

--- Constructs a new Integer with the value of one.
---@return Integer
function Integer.one()
    return setmetatable({n = 1, limbs = {1}, neg = false}, Integer)
end

--- Returns true if the given Integer is zero.
---@param num Integer
---@return boolean
function Integer.isZero(num)
    local d = 0
    for i = 1, num.n do
        d = bit.bor(d, num.limbs[i])
    end
    return d == 0
end

--- Sets the value of the Integer to the given number or string.
---@param r Integer result location
---@param num number|string
function Integer.set(r, num)
    if type(num) == 'string' then
        return Integer.setString(r, num)
    end

    if num < 0 then
        r.neg = true
        num = -num
    elseif num > 0 then
        r.neg = false
    else -- set to zero
        for i = 2, r.n do
            r.limbs[i] = nil
        end

        r.neg = false
        r.n = 1
        r.limbs[1] = 0
        return r
    end

    for i = 2, r.n do
        r.limbs[i] = nil
    end

    r.n = 0
    while num >= RADIX do
        r.n = r.n + 1
        r.limbs[r.n] = num % RADIX
        num = math.floor(num / RADIX)
    end

    if num > 0 then
        r.n = r.n + 1
        r.limbs[r.n] = num
    end

    return r
end

local hex_digits = {}
for i = 0, 15 do
    hex_digits[i] = Integer.new(i)
end

--- Sets the value of the Integer to the given string.
---@param r Integer result location
---@param str string
---@return Integer
function Integer.setString(r, str)
    local i = 1
    local neg = false
    local base = 10

    if str:sub(i, i) == '-' then
        neg = true
        i = 2
    end

    if str:sub(i, i + 1) == '0x' then
        base = 16
        i = i + 2
    elseif str:sub(i, i + 1) == '0b' then
        base = 2
        i = i + 2
    elseif str:sub(i, i + 1) == '0o' then
        base = 8
        i = i + 2
    end

    if i == #str then
        error('invalid numeric string')
    end

    Integer.set(r, 0)

    local tmp = Integer.zero()
    for j = i, #str do
        local digit = tonumber(str:sub(j, j), base) or error('invalid numeric string')

        Integer.mulNoAliasScalar(tmp, r, base)
        Integer.add(r, tmp, hex_digits[digit])
    end

    r.neg = neg

    return r
end

--- Constructs an Integer with the hexadecimal value of `hex`.
---@param hex string
---@return Integer
function Integer.fromHex(hex)
    local self = setmetatable({n = 0, limbs = {}, neg = false}, Integer)

    for i = 1, #hex do
        local digit = tonumber(hex:sub(i, i), 16) or error('invalid hex string')

        Integer.shiftLeft(self, self, 4)
        Integer.add(self, self, hex_digits[digit])
    end

    return self
end

--- Returns a hexadecimal representation of the given Integer.
---@param num Integer
---@return string
function Integer.toHexString(num)
    if Integer.isZero(num) then
        return '0'
    end

    local parts = {}
    for i = num.n, 1, -1 do
        table.insert(parts, string.format('%06x', num.limbs[i]))
    end

    return (num.neg and '-' or '') .. table.concat(parts)
end

--- Returns a decimal representation of the given Integer.
---@param num Integer
---@return string
function Integer.toDecString(num)
    if Integer.isZero(num) then
        return '0'
    end

    local tmp = Integer.zero()
    Integer.copy(tmp, num)

    local parts = {}
    local r = Integer.zero()

    local big_base = 10 ^ math.floor(math.log(RADIX, 10))
    while not Integer.isZero(tmp) do
        Integer.divFloorScalar(tmp, r, tmp, big_base)
        assert(r.n == 1)

        local part = string.format('%07d', r.limbs[1])
        table.insert(parts, part)
    end

    for i = 1, #parts / 2 do
        parts[i], parts[#parts - i + 1] = parts[#parts - i + 1], parts[i]
    end

    parts[1] = parts[1]:match('^0+(.*)$')
    return (num.neg and '-' or '') .. table.concat(parts)
end

--- Copies the value of `a` into `r` and returns `r`.
--- @param r Integer
--- @param a Integer
--- @return Integer
function Integer.copy(r, a)
    for i = 1, a.n do
        r.limbs[i] = a.limbs[i]
    end
    for j = a.n + 1, r.n do
        r.limbs[j] = nil
    end

    r.n = a.n
    r.neg = a.neg
    return r
end

--- Efficiently swaps the values of `a` and `b`.
--- @param a Integer
--- @param b Integer
function Integer.swap(a, b)
    a.n, b.n = b.n, a.n
    a.limbs, b.limbs = b.limbs, a.limbs
    a.neg, b.neg = b.neg, a.neg
end

--- returns a clone of `a`
--- @param a Integer
--- @return Integer
function Integer.clone(a)
    local self = setmetatable({n = a.n, limbs = {}, neg = a.neg}, Integer)

    for i = 1, a.n do
        self.limbs[i] = a.limbs[i]
    end

    return self
end

--- Returns true if `a` is even.
--- @param a Integer
--- @return boolean
function Integer.isEven(a)
    return a.limbs[a.n] % 2 == 0
end

--- Returns true if `a` is odd.
--- @param a Integer
--- @return boolean
function Integer.IsOdd(a)
    return a.limbs[a.n] % 2 == 1
end

--- Returns true if `a` is a power of two.
--- @param a Integer
--- @return boolean
function Integer.isPowerOfTwo(a)
    local n = 0

    for i = 1, a.n do
        local x = a.limbs[i]
        if x ~= 0 and bit.band(x, x - 1) == 0 then
            n = n + 1
        end
    end

    return n == 1
end

-------------------------------------
---                               ---
---   Begin Arithmetic Operations ---
---                               ---
-------------------------------------

--- returns `|a|`
--- The result is a mutation of `a`, not a new integer. This mutation shares the same limbs as `a`.
--- @param a Integer
--- @return Integer
function Integer.abs(a)
    local self = setmetatable({n = a.n, limbs = a.limbs, neg = false}, Integer)

    return self
end

--- returns `-a`
--- The result is a mutation of `a`, not a new integer. This mutation shares the same limbs as `a`.
--- @param a Integer
--- @return Integer
function Integer.negate(a)
    local self = setmetatable({n = a.n, limbs = a.limbs, neg = not a.neg}, Integer)

    return self
end

--- returns -1 if a < b, 0 if a == b, 1 if a > b
--- The result satisfies the equivalence `a cmp b := order(a, b) cmp 0` where `cmp` is a logical comparison operator.
--- @param a Integer
--- @param b Integer
--- @return number
function Integer.order(a, b)
    if a.neg ~= b.neg then
        return a.neg and -1 or 1
    elseif a.n ~= b.n then
        return a.n < b.n and -1 or 1
    else
        for i = a.n, 1, -1 do
            if a.limbs[i] ~= b.limbs[i] then
                return a.limbs[i] < b.limbs[i] and -1 or 1
            end
        end
    end

    return 0
end

--- returns `r = a + b`
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer
function Integer.add(r, a, b)
    local carry

    local msl = math.max(a.n, b.n)
    if Integer.isZero(a) then
        return Integer.copy(r, b)
    elseif Integer.isZero(b) then
        return Integer.copy(r, a)
    elseif a.neg ~= b.neg then
        -- subtraction
        if a.neg then
            -- (-a) + b = b - a
            a, b = b, Integer.abs(a)
        else
            -- a + (-b) = a - b
            b = Integer.abs(b)
        end

        if a >= b then
            r.neg = false
            carry = limbwiseSubtractWithBorrow(r.limbs, a.limbs, b.limbs, a.n, b.n)
            r.n = limbwiseNormalize(r.limbs, a.n)
        else
            r.neg = true
            carry = limbwiseSubtractWithBorrow(r.limbs, b.limbs, a.limbs, b.n, a.n)
            r.n = limbwiseNormalize(r.limbs, b.n)
        end
    else
        r.neg = a.neg

        if a.n >= b.n then
            carry = limbwiseAddWithCarry(r.limbs, a.limbs, b.limbs, a.n, b.n)
            r.n = limbwiseNormalize(r.limbs, a.n)
        else
            carry = limbwiseAddWithCarry(r.limbs, b.limbs, a.limbs, b.n, a.n)
            r.n = limbwiseNormalize(r.limbs, b.n)
        end
    end

    if carry ~= 0 then
        for i = r.n + 1, msl do
            r.limbs[i] = 0
        end
        r.n = msl + 1
        r.limbs[msl + 1] = 1
    end

    return r
end

--- returns `r = a - b`
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer
function Integer.sub(r, a, b)
    return Integer.add(r, a, Integer.negate(b))
end

--- returns `r = a * b`
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer
function Integer.mul(r, a, b)
    if r == a then
        a = Integer.copy(Integer.zero(), a)
    end

    if r == b then
        b = Integer.copy(Integer.zero(), b)
    end

    return Integer.mulNoAlias(r, a, b)
end

-- returns `r = a * b`, where `b` is a scalar
--- @param r Integer
--- @param a Integer
--- @param b number
--- @return Integer
function Integer.mulNoAliasScalar(r, a, b)
    assert(not rawequal(r, a), 'r must not alias a')

    if b == 0 then
        return Integer.set(r, 0)
    end

    local c = math.abs(b)

    -- simplify multiplication by a power of 2 to a left shift
    if c <= MAX_U32 and bit.band(c, c - 1) == 0 then
        local shift = math.log(c, 2)

        Integer.shiftLeft(r, a, shift)
    else
        for i = 1, a.n + 1 do
            r.limbs[i] = 0
        end

        limbwiseAddMulScalar(r.limbs, 1, a.limbs, b, a.n)
        r.n = limbwiseNormalize(r.limbs, a.n + 1)
    end

    r.neg = a.neg ~= (b < 0)
    return r
end

--- returns `r = a * b`, where `r` must not alias `a` or `b`
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer
function Integer.mulNoAlias(r, a, b)
    assert(not rawequal(r, a), 'r must not alias a')
    assert(not rawequal(r, b), 'r must not alias b')

    if a.n == 1 and b.n == 1 then
        Integer.set(r, a.limbs[1] * b.limbs[1])
        return r
    end

    if a.n < b.n then
        a, b = b, a
    end

    if Integer.isPowerOfTwo(b) then
        local shift = Integer.log2floor(b)

        Integer.shiftLeft(r, a, shift)
    elseif b.n == 1 then
        Integer.mulNoAliasScalar(r, a, b.limbs[1])
    else
        for i = 1, a.n + b.n do
            r.limbs[i] = 0
        end

        limbwiseMultiply(r.limbs, a.limbs, b.limbs, a.n, b.n)
        r.n = limbwiseNormalize(r.limbs, a.n + b.n)
    end

    r.neg = a.neg ~= b.neg
    return r
end

--- returns `q rem r = a / b`, where `b` is a scalar
--- The results `q` and `r` satisfy the equation `a = b * q + r`
--- @param q Integer
--- @param r Integer
--- @param a Integer
--- @param b number
--- @return Integer, Integer
function Integer.divTruncScalar(q, r, a, b)
    assert(b ~= 0, 'division by zero')
    assert(not rawequal(q, r), 'q must not alias r')

    if Integer.abs(a) < Integer.new(math.abs(b)) then
        Integer.copy(r, a)
        Integer.set(q, 0)
        return q, r
    end

    local c = math.abs(b)

    -- simplify division by a power of 2 to a right shift
    if c <= MAX_U32 and bit.band(c, c - 1) == 0 then
        local shift = math.log(c, 2)

        Integer.shiftRight(q, a, shift)
        local tmp = Integer.clone(q)
        Integer.shiftLeft(tmp, tmp, shift)

        Integer.sub(r, a, tmp)
        return q, r
    end

    assert(c < RADIX, 'b must be less than ' .. RADIX)

    local remainder = 0
    for i = a.n, 1, -1 do
        local pdiv = remainder * RADIX + a.limbs[i] -- double wide multiplication
        assert(pdiv >= 0)
        if pdiv == 0 then
            q.limbs[i] = 0
            remainder = 0
        elseif pdiv < c then
            q.limbs[i] = 0
            remainder = bit.band(pdiv, LIMB_MASK)
        elseif pdiv == c then
            q.limbs[i] = 1
            remainder = 0
        else -- TODO: assert this is always correct
            q.limbs[i] = bit.band(math.floor(pdiv / c), LIMB_MASK)
            remainder = pdiv % c
        end
    end

    q.n = limbwiseNormalize(q.limbs, a.n)
    Integer.set(r, remainder)

    q.neg = a.neg ~= (b < 0)
    r.neg = a.neg

    return q, r
end

--- returns `q rem r = a / b`. Truncates towards zero.
--- The results `q` and `r` satisfy the equation `a = b * q + r`
--- @param q Integer
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer, Integer
function Integer.divTrunc(q, r, a, b)
    assert(not Integer.isZero(b), 'division by zero')
    assert(not rawequal(q, r), 'q must not alias r')

    if Integer.abs(a) < Integer.abs(b) then
        Integer.copy(r, a)
        Integer.set(q, 0)
        return q, r
    end

    local a_trailing = 0
    while a.limbs[a_trailing + 1] == 0 do
        a_trailing = a_trailing + 1
    end

    local b_trailing = 0
    while b.limbs[b_trailing + 1] == 0 do
        b_trailing = b_trailing + 1
    end

    local ab_trailing = math.min(a_trailing, b_trailing)
    Integer.shiftRight(a, a, ab_trailing * LIMB_BITS)
    Integer.shiftRight(b, b, ab_trailing * LIMB_BITS)

    local a_neg = a.neg
    local b_neg = b.neg

    a.neg = false
    b.neg = false

    if Integer.isPowerOfTwo(b) then
        local shift = Integer.log2floor(b)

        Integer.shiftRight(q, a, shift)
        local tmp = Integer.clone(q)
        Integer.shiftLeft(tmp, tmp, shift)

        Integer.sub(r, a, tmp)
    elseif b.n == 1 then
        Integer.divTruncScalar(q, r, a, b.limbs[1])
    else
        -- TODO: optimize

        -- find candiate for q by simplifying to division by a single limb
        local numerator = Integer.zero()
        Integer.copy(numerator, a)

        Integer.set(q, 0)
        local q_hat = Integer.zero()
        local r_hat = Integer.zero()

        local msd_shift = (b.n - 1) * LIMB_BITS
        while true do -- iterate until numerator < b
            Integer.shiftRight(numerator, numerator, msd_shift)
            Integer.divTruncScalar(q_hat, r_hat, numerator, b.limbs[b.n])
            if Integer.isZero(q_hat) then
                break
            end

            Integer.add(q, q, q_hat)

            Integer.mulNoAlias(r_hat, b, q)
            Integer.sub(numerator, a, r_hat)
        end

        -- if for whatever reason the numerator is negative, fix it
        if numerator < Integer.zero() then
            local radix = Integer.new(RADIX)

            Integer.sub(q, q, Integer.one())
            Integer.add(numerator, numerator, radix)
        end

        Integer.copy(r, numerator)
    end

    q.neg = a_neg ~= b_neg
    r.neg = a_neg

    a.neg = a_neg
    b.neg = b_neg

    Integer.shiftLeft(r, r, ab_trailing * LIMB_BITS)
    Integer.shiftLeft(a, a, ab_trailing * LIMB_BITS)
    Integer.shiftLeft(b, b, ab_trailing * LIMB_BITS)

    return q, r
end

--- returns `q rem r = a / b`, where `b` is a scalar. Truncates towards negative infinity.
--- The results `q` and `r` satisfy the equation `a = b * q + r`
--- @param q Integer
--- @param r Integer
--- @param a Integer
--- @param b number
--- @return Integer, Integer
function Integer.divFloorScalar(q, r, a, b)
    Integer.divTruncScalar(q, r, a, b)

    -- adjust the truncated result to match floor behavior
    b_n = Integer.new(b)
    if not a.neg and b < 0 and not Integer.isZero(r) then
        Integer.sub(q, q, Integer.one())
        r.neg = true
        Integer.add(r, r, b_n)
    elseif a.neg and b >= 0 and not Integer.isZero(r) then
        Integer.sub(q, q, Integer.one())
        r.neg = false
        Integer.sub(r, r, b_n)
    elseif a.neg and b < 0 then
        r.neg = false
    end

    return q, r
end

--- returns `q rem r = a / b`. Truncates towards negative infinity.
--- The results `q` and `r` satisfy the equation `a = b * q + r`
--- @param q Integer
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer, Integer
function Integer.divFloor(q, r, a, b)
    Integer.divTrunc(q, r, a, b)

    -- adjust the truncated result to match floor behavior
    if b.neg and not a.neg and not Integer.isZero(r) then
        Integer.sub(q, q, Integer.one())
        r.neg = false
        Integer.sub(r, r, b)
    elseif a.neg and not b.neg and not Integer.isZero(r) then
        Integer.sub(q, q, Integer.one())
        r.neg = true
        Integer.add(r, r, b)
    elseif a.neg and b.neg then
        r.neg = false
    end

    return q, r
end

--- returns `r = a ^ b`
---@param r Integer
---@param a Integer
---@param b Integer
---@return Integer
function Integer.pow(r, a, b)
    if b.neg then
        return Integer.set(r, 0)
    elseif Integer.isZero(b) then
        return Integer.set(r, 1)
    elseif b.n == 1 then
        return Integer.powScalar(r, a, b.limbs[1])
    elseif Integer.isZero(a) then
        return Integer.set(r, 0)
    end

    local count = Integer.clone(b)
    local tmp = Integer.zero()

    -- handle the non-trivial cases
    -- TODO: optimize
    while not Integer.isZero(count) do
        Integer.mulNoAlias(tmp, r, a)
        Integer.swap(r, tmp)
        Integer.sub(count, count, Integer.one())
    end

    return r
end

--- returns `r = a ^ b`, where `b` is a scalar
---@param r Integer
---@param a Integer
---@param b number
---@return Integer
function Integer.powScalar(r, a, b)
    if b < 0 then
        return Integer.set(r, 0)
    elseif b == 0 then
        return Integer.set(r, 1)
    elseif b == 1 then
        return Integer.copy(r, a)
    elseif b == 2 then
        return Integer.mulNoAlias(r, a, a)
    end

    -- handle the non-trivial cases
    -- TODO: optimize
    local tmp = Integer.one()
    for i = 1, b do
        Integer.mulNoAlias(r, tmp, a)
        Integer.swap(r, tmp)
    end

    return r
end

-------------------------------------
---                               ---
---   Begin Bitwise Operations    ---
---                               ---
-------------------------------------

--- Returns true if the `n`-th bit of `a` is set. Bits are 0-indexed.
--- @param a Integer
--- @param n integer
--- @return boolean
function Integer.bitTest(a, n)
    local n_limb = math.floor(n / LIMB_BITS) + 1
    local n_bit = n % LIMB_BITS

    if n_limb > a.n then
        return false
    end

    return bit.band(a.limbs[n_limb], bit.lshift(1, n_bit)) ~= 0
end

--- returns `r = a | b`
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer
function Integer.bitOr(r, a, b)
    if Integer.isZero(a) then
        return Integer.copy(r, b)
    elseif Integer.isZero(b) then
        return Integer.copy(r, a)
    end

    if a.n < b.n then
        a, b = b, a
    end

    if not a.neg and not b.neg then
        for i = 1, b.n do
            r.limbs[i] = bit.bor(a.limbs[i], b.limbs[i])
        end

        for i = b.n + 1, a.n do
            r.limbs[i] = a.limbs[i]
        end

        r.n = limbwiseNormalize(r.limbs, a.n)
        r.neg = false
    elseif a.neg and not b.neg then
        local a_borrow = 1
        local r_carry = 1

        for i = 1, b.n do
            local ov1 = a.limbs[i] - a_borrow
            a_borrow = ov1 < 0 and 1 or 0
            local ov2 = bit.band(bit.band(ov1, LIMB_MASK), bit.bnot(b.limbs[i])) + r_carry
            r.limbs[i] = bit.band(ov2, LIMB_MASK)
            r_carry = ov2 < 0 and 1 or 0
        end

        assert(r_carry == 0)

        for i = b.n + 1, a.n do
            local ov1 = a.limbs[i] - a_borrow
            r.limbs[i] = bit.band(ov1, LIMB_MASK)

            if ov1 >= 0 then
                break
            end

            a_borrow = 1
        end

        assert(a_borrow == 0)

        r.n = limbwiseNormalize(r.limbs, a.n)
        r.neg = true
    elseif not a.neg and b.neg then
        local b_borrow = 1
        local r_carry = 1

        for i = 1, b.n do
            local ov1 = b.limbs[i] - b_borrow
            b_borrow = ov1 < 0 and 1 or 0
            local ov2 = bit.band(bit.band(ov1, LIMB_MASK), bit.bnot(a.limbs[i])) + r_carry
            r.limbs[i] = bit.band(ov2, LIMB_MASK)
            r_carry = ov2 < 0 and 1 or 0
        end

        assert(r_carry == 0)
        assert(b_borrow == 0)

        r.n = limbwiseNormalize(r.limbs, a.n)
        r.neg = true
    else -- a.neg and b.neg
        local a_borrow = 1
        local b_borrow = 1
        local r_carry = 1

        for i = 1, b.n do
            local ov1 = a.limbs[i] - a_borrow
            a_borrow = ov1 < 0 and 1 or 0
            local ov2 = b.limbs[i] - b_borrow
            b_borrow = ov2 < 0 and 1 or 0
            local ov3 = bit.band(bit.band(ov1, LIMB_MASK), bit.band(ov2, LIMB_MASK)) + r_carry
            r.limbs[i] = bit.band(ov3, LIMB_MASK)
            r_carry = ov3 < 0 and 1 or 0
        end

        assert(r_carry == 0)
        assert(a_borrow == 0)

        r.n = limbwiseNormalize(r.limbs, a.n)
        r.neg = true
    end

    return r
end

--- returns `r = a & b`
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer
function Integer.bitAnd(r, a, b)
    if Integer.isZero(a) then
        return Integer.copy(r, b)
    elseif Integer.isZero(b) then
        return Integer.copy(r, a)
    end

    if a.n < b.n then
        a, b = b, a
    end

    if not a.neg and not b.neg then
        for i = 1, b.n do
            r.limbs[i] = bit.band(a.limbs[i], b.limbs[i])
        end

        r.n = limbwiseNormalize(r.limbs, b.n)
        r.neg = false
    elseif a.neg and not b.neg then
        local a_borrow = 1

        for i = 1, b.n do
            local ov = a.limbs[i] - a_borrow
            a_borrow = ov < 0 and 1 or 0
            r.limbs[i] = bit.band(bit.bnot(bit.band(ov, LIMB_MASK)), b.limbs[i])
        end

        r.n = limbwiseNormalize(r.limbs, b.n)
        r.neg = false
    elseif not a.neg and b.neg then
        local b_borrow = 1

        for i = 1, b.n do
            local ov = b.limbs[i] - b_borrow
            b_borrow = ov < 0 and 1 or 0
            r.limbs[i] = bit.band(bit.bnot(bit.band(ov, LIMB_MASK)), a.limbs[i])
        end

        for i = b.n + 1, a.n do
            r.limbs[i] = a.limbs[i]
        end

        r.n = limbwiseNormalize(r.limbs, a.n)
        r.neg = false
    else -- a.neg and b.neg
        local a_borrow = 1
        local b_borrow = 1
        local r_carry = 1

        for i = 1, b.n do
            local ov1 = a.limbs[i] - a_borrow
            a_borrow = ov1 < 0 and 1 or 0
            local ov2 = b.limbs[i] - b_borrow
            b_borrow = ov2 < 0 and 1 or 0
            local ov3 = bit.bor(bit.band(ov1, LIMB_MASK), bit.band(ov2, LIMB_MASK)) + r_carry
            r.limbs[i] = bit.band(ov3, LIMB_MASK)
            r_carry = ov3 < 0 and 1 or 0
        end

        assert(b_borrow == 0)

        for i = b.n + 1, a.n do
            local ov1 = a.limbs[i] - a_borrow
            a_borrow = ov1 < 0 and 1 or 0
            local ov2 = bit.bnot(bit.band(ov1, LIMB_MASK)) + r_carry
            r.limbs[i] = bit.band(ov2, LIMB_MASK)
            r_carry = ov2 < 0 and 1 or 0
        end

        assert(a_borrow == 0)
        r[a.n + 1] = r_carry

        r.n = limbwiseNormalize(r.limbs, a.n + 1)
        r.neg = true
    end

    return r
end

--- returns `r = a ~ b`
--- @param r Integer
--- @param a Integer
--- @param b Integer
--- @return Integer
function Integer.bitXor(r, a, b)
    if Integer.isZero(a) then
        return Integer.copy(r, b)
    elseif Integer.isZero(b) then
        return Integer.copy(r, a)
    end

    if a.n < b.n then
        a, b = b, a
    end

    local a_borrow = a.neg and 1 or 0
    local b_borrow = b.neg and 1 or 0
    local r_carry = (a.neg ~= b.neg) and 1 or 0

    for i = 1, b.n do
        local ov1 = a.limbs[i] - a_borrow
        a_borrow = ov1 < 0 and 1 or 0
        local ov2 = b.limbs[i] - b_borrow
        b_borrow = ov2 < 0 and 1 or 0
        local ov3 = bit.bxor(bit.band(ov1, LIMB_MASK), bit.band(ov2, LIMB_MASK)) + r_carry
        r.limbs[i] = bit.band(ov3, LIMB_MASK)
        r_carry = ov3 < 0 and 1 or 0
    end

    for i = b.n + 1, a.n do
        local ov1 = a.limbs[i] - a_borrow
        a_borrow = ov1 < 0 and 1 or 0
        local ov2 = bit.band(ov1, LIMB_MASK) + r_carry
        r.limbs[i] = bit.band(ov2, LIMB_MASK)
        r_carry = ov2 < 0 and 1 or 0
    end

    if a.neg ~= b.neg then
        r[a.n + 1] = r_carry

        r.n = limbwiseNormalize(r.limbs, a.n + 1)
    else
        assert(r_carry == 0)

        r.n = limbwiseNormalize(r.limbs, a.n)
    end

    assert(a_borrow == 0)
    assert(b_borrow == 0)

    r.neg = a.neg ~= b.neg

    return r
end

--- returns `r = a << shift`
--- @param r Integer
--- @param a Integer
--- @param shift number
--- @return Integer
function Integer.shiftLeft(r, a, shift)
    if shift == 0 then
        return Integer.copy(r, a)
    end
    if shift < 0 then
        return Integer.shiftRight(r, a, -shift)
    end

    limbwiseShiftLeft(r.limbs, a.limbs, shift, a.n)
    r.n = limbwiseNormalize(r.limbs, a.n + math.floor(shift / LIMB_BITS) + 1)
    r.neg = a.neg

    return r
end

--- returns `r = a >> shift`. The shift is arithmetic, negative numbers converge to -1.
--- @param r Integer
--- @param a Integer
--- @param shift number
--- @return Integer
function Integer.shiftRight(r, a, shift)
    if shift == 0 then
        return Integer.copy(r, a)
    end
    if shift < 0 then
        return Integer.shiftLeft(r, a, -shift)
    end

    if a.n <= shift / LIMB_BITS then
        if a.neg then
            return Integer.set(r, -1)
        end

        return Integer.set(r, 0)
    end

    limbwiseShiftRight(r.limbs, a.limbs, shift, a.n)
    r.n = limbwiseNormalize(r.limbs, a.n - math.floor(shift / LIMB_BITS))
    r.neg = a.neg

    if r.neg and r.n == 1 and r.limbs[1] == 0 then
        r.limbs[1] = 1
    end

    return r
end

--------------------------------------
---                                ---
---   Begin Mathematical Functions ---
---                                ---
--------------------------------------

--- returns `floor(log2(|a|))`
--- @param a Integer
--- @return integer
function Integer.log2floor(a)
    return (a.n - 1) * LIMB_BITS + math.floor(math.log(a.limbs[a.n], 2))
end

function Integer.__add(a, b)
    a = getmetatable(a) == Integer and a or Integer.new(a)
    b = getmetatable(b) == Integer and b or Integer.new(b)

    local r = Integer.zero()
    Integer.add(r, a, b)
    return r
end

function Integer.__sub(a, b)
    a = getmetatable(a) == Integer and a or Integer.new(a)
    b = getmetatable(b) == Integer and b or Integer.new(b)

    local r = Integer.zero()
    Integer.sub(r, a, b)
    return r
end

function Integer.__mul(a, b)
    local r = Integer.zero()

    if type(b) == 'number' then
        -- a must be an Integer
        Integer.mulNoAliasScalar(r, a, b)
    elseif type(a) == 'number' then
        -- b must be an Integer
        Integer.mulNoAliasScalar(r, b, a)
    else
        a = getmetatable(a) == Integer and a or Integer.new(a)
        b = getmetatable(b) == Integer and b or Integer.new(b)

        Integer.mulNoAlias(r, a, b)
    end

    return r
end

function Integer.__div(a, b)
    local q = Integer.zero()
    local r = Integer.zero()

    if type(b) == 'number' then
        -- a must be an Integer
        Integer.divFloorScalar(q, r, a, b)
    else
        a = getmetatable(a) == Integer and a or Integer.new(a)
        b = getmetatable(b) == Integer and b or Integer.new(b)

        Integer.divFloor(q, r, a, b)
    end

    return q
end
Integer.__idiv = Integer.__div

function Integer.__mod(a, b)
    local q = Integer.zero()
    local r = Integer.zero()

    if type(b) == 'number' then
        -- a must be an Integer
        Integer.divFloorScalar(q, r, a, b)
    else
        a = getmetatable(a) == Integer and a or Integer.new(a)
        b = getmetatable(b) == Integer and b or Integer.new(b)

        Integer.divFloor(q, r, a, b)
    end

    return r
end

function Integer.__pow(a, b)
    a = getmetatable(a) == Integer and a or Integer.new(a)
    b = getmetatable(b) == Integer and b or Integer.new(b)

    local r = Integer.zero()
    Integer.pow(r, a, b)
    return r
end

function Integer.__unm(a)
    return Integer.negate(Integer.clone(a))
end

function Integer.__shl(a, shift)
    shift = math.floor(shift)

    local r = Integer.zero()
    Integer.shiftLeft(r, a, shift)
    return r
end

function Integer.__shr(a, shift)
    shift = math.floor(shift)

    local r = Integer.zero()
    Integer.shiftRight(r, a, shift)
    return r
end

function Integer.__eq(a, b)
    return Integer.order(a, b) == 0
end

function Integer.__lt(a, b)
    return Integer.order(a, b) == -1
end

function Integer.__le(a, b)
    return Integer.order(a, b) <= 0
end

Integer.__tostring = Integer.toDecString

--- sanity checks

do
    local a = Integer.new(0x123456123456)
    local b = Integer.new(0x123456)
    local sum = Integer.new(0x1234562468AC)
    local sub = Integer.new(0x123456000000)
    local prod = Integer.fromHex('14b66cc584acb0ce4')

    assert(a + b == sum, 'addition failed')
    assert(a - b == sub, 'subtraction failed')
    assert(a * b == prod, 'multiplication failed')
    assert(a / b == Integer.new(0x1000001), 'division failed')
    assert(a % b == Integer.zero(), 'modulo failed')
end

return Integer
