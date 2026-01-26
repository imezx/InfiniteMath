--!native
-- forked by @EternityDev
-- originally created by @KdudeDev

--[=[
	@class InfiniteMath

	InfiniteMath is module that allows you to surpass the limit of -10^308 to 10^308, with a new limit of -10^^308 to 10^^308 (1 with 10^308 zeros)

	InfiniteMath has many of the functions from the math library, as well as metamethods for arithmatic and comparison.
	
	Datastores and OrderedDataStores are supported, with special functions for OrderedDataStores.
]=]

--[=[
	An InfiniteMath constructed number that has a limit of -10^^308 to 10^^308.

	@class Number
]=]

--[=[
	@prop DECIMALPOINTS number
	@within InfiniteMath

	How many decimal points are displayed. 1 = 1.0, 2 = 1.00, 3 = 1.000, etc.
]=]

--[=[
	@prop AALENGTHMAX number
	@within InfiniteMath

	The maximum length for suffixes generated for aaNotation conversions. Exceeding this length results in a scientific number instead.
]=]

local InfiniteMath = {
	DECIMALPOINTS = 2,
	AALENGTHMAX = 3,
}

local Number = {}
Number.__index = Number

export type Number = typeof(setmetatable({
	first = 0 :: number,
	second = 0 :: number
}, Number))

--[[ Private variables ]]--

local THRESHOLD = 16
local LEADERBOARDPRECISION, LEADERBOARDPOINT = 10000, 5
local NaN = 0/0
local POW10 = table.create(617)
local SMALL_POW10 = table.create(2*THRESHOLD + 1)

-- pre-compute powers with offset
for i = -308, 308 do
	POW10[i + 309] = 10 ^ i
end
for d = -THRESHOLD, THRESHOLD do
	SMALL_POW10[d + THRESHOLD + 1] = 10 ^ d
end

local suffixes = require("@self/Values/Suffixes")
local full_names = require("@self/Values/FullNames")
local int = require("@self/Int")

--[[ Private functions ]]--
local function fastNew(first: number, second: number): Number
	return setmetatable({ first = first, second = second }, Number)
end

local function pow10(e: number): number
	-- e must be integer here
	return POW10[e + 309] or (10 ^ e)
end

local function smallPow10(e: number): number
	-- e must be integer here
	return SMALL_POW10[e + THRESHOLD + 1] or (10 ^ e)
end

local function normalize(first: number, second: number): (number, number)
	if first == 0 then
		return 0, 0
	end
	local sign = if first < 0 then -1 else 1
	local m = math.abs(first)

	-- m is always a finite double here. cuz log10(m) is in [-308..308]
	local k = math.floor(math.log10(m))
	if k ~= 0 then
		m /= pow10(k)
		second += k
	end
	if m >= 10 then
		m /= 10
		second += 1
	elseif m < 1 then
		m *= 10
		second -= 1
	end
	return m * sign, second
end

local function coerce(x: any): Number
	if type(x) == "table" and getmetatable(x) == Number then
		return x
	elseif type(x) == "number" then
		return fastNew(x, 0)
	elseif type(x) == "string" then
		return InfiniteMath.new(x)
	end
	local f = x.first or x[1]
	local e = x.second or x[2]
	f, e = normalize(f, e)
	return fastNew(f, e)
end

local function convert(number: number): (number, number)
	if type(number) ~= "number" then
		error('Type is not a "number".')
	end

	if number ~= number then
		error("NaN is not supported.")
	end
	if number == math.huge or number == -math.huge then
		error('INF is not supported as a number input. Use "1,1000" or "1e+1000".')
	end

	if number == 0 then
		return 0, 0
	end

	local sign = if number < 0 then -1 else 1
	number = math.abs(number)

	-- exponent guess
	local e = math.floor(math.log10(number))
	-- scale into ~[1,10)
	local m = number / (10 ^ e)

	if m >= 10 then
		m /= 10
		e += 1
	elseif m < 1 then
		m *= 10
		e -= 1
	end
	return m * sign, e
end

local function isNumberObject(x: any): boolean
	return type(x) == "table" and getmetatable(x) == Number
end

local function isFieldNaN(v: any): boolean
	return v == "nan" or (type(v) == "number" and v ~= v)
end

local function isFieldInf(v: any): boolean
	return v == "inf" or v == "-inf"
		or (type(v) == "number" and (v == math.huge or v == -math.huge))
end

local function checkNumber(a): Number
	if type(a) == "table" and getmetatable(a) == Number then
		return a
	end
	return coerce(a)
end

local function cmp(a: Number, b: Number): number
	local f1, e1 = a.first, a.second
	local f2, e2 = b.first, b.second

	local s1, s2 = math.sign(f1), math.sign(f2)
	if s1 ~= s2 then
		return (s1 < s2) and -1 or 1
	end
	if s1 == 0 then return 0 end

	-- magnitude
	local af1, af2 = math.abs(f1), math.abs(f2)
	if e1 ~= e2 then
		if s1 > 0 then
			return (e1 < e2) and -1 or 1
		end
		return (e1 > e2) and -1 or 1 -- inverted for negatives
	end

	if af1 ~= af2 then
		if s1 > 0 then
			return (af1 < af2) and -1 or 1
		end
		return (af1 > af2) and -1 or 1
	end
	return 0
end

local function parseExpString(s: string): (number?, number?)
	local m, e = s:match("^%s*([+-]?%d*%.?%d+)%s*,%s*([+-]?%d+)%s*$")
	if not m then
	  m, e = s:match("^%s*([+-]?%d*%.?%d+)%s*[eE]%s*([+-]?%d+)%s*$")
	end
	if not m then return nil end
	return tonumber(m), tonumber(e)
  end

-- math metamethods:
function Number.__add(a, b)
	a, b = coerce(a), coerce(b)

	local first1, second1 = a.first, a.second
	local first2, second2 = b.first, b.second
	local difference = second1 - second2

	if math.abs(difference) > THRESHOLD then -- Check if difference in exponents is greater than threshold
		if math.max(second1, second2) == second1 then
			return fastNew(first1, second1)
		end
		return fastNew(first2, second2)
	end

	first2 *= smallPow10(-difference)
	first1, second1 = normalize(first1 + first2, second1)

	return fastNew(first1 , second1)
end

function Number.__sub(a, b)
	a, b = coerce(a), coerce(b)

	local first1, second1 = a.first, a.second
	local first2, second2 = b.first, b.second
	local difference = second1 - second2

	if math.abs(difference) > THRESHOLD then -- Check if difference in exponents is greater than threshold
		if math.max(second1, second2) == second1 then
			return fastNew(first1 ,second1)
		end
		return fastNew(first2, second2)
	end

	first2 *= smallPow10(-difference)
	first1, second1 = normalize(first1 - first2, second1)

	return fastNew(first1 , second1)
end

function Number.__mul(a, b)
	a = coerce(a); b = coerce(b)
	local rf, re = normalize(a.first * b.first, a.second + b.second)
	return fastNew(rf, re)
end

function Number.__div(a, b)
	a = coerce(a); b = coerce(b)
	local rf, re = normalize(a.first / b.first, a.second - b.second)
	return fastNew(rf, re)
end

function Number.__pow(a, power)
	a = coerce(a)

	if type(power) == "string" then
		power = tonumber(power)
	elseif type(power) == "table" and getmetatable(power) == Number then
		power = power:Reverse()
	end

	if power == math.huge or power ~= power or type(power) ~= "number" then
		error(`'{power}' is not a valid power. If power is 'inf' you must keep it below 10^308.`)
		return
	end

	local sign = InfiniteMath.sign(a)
	a *= sign

	local first, second = normalize(a.first, a.second)
	local n, n2 = first^power, second * power

	if n == math.huge or n2 == math.huge then
		if type(power) ~= "number" then
			power = power:Reverse()
		end

		local answer = fastNew(1, 0)

		local firstAnswer, secondAnswer

		if power > 1 then
			while power > 0 do
				local lastBit = (bit32.band(power, 1) == 1)

				if lastBit then
					answer *= a
				end

				a *= a

				power = bit32.rshift(power, 1)
			end

			firstAnswer, secondAnswer = normalize(answer.first, answer.second)
		elseif power == 0 then
			firstAnswer, secondAnswer = 1, 0
		else
			firstAnswer, secondAnswer = first, second
		end
		return fastNew(firstAnswer, secondAnswer)
	end
	return fastNew(n, n2) * sign
end

function Number.__mod(a, b)
	a, b = coerce(a), coerce(b)
	local sign = InfiniteMath.sign(a)

	local divided

	if sign == 1 then
		divided = InfiniteMath.floor(a / b)
	else
		divided = InfiniteMath.round(a / b)
	end
	local nextNum = b * divided

	return a - nextNum
end

function Number.__eq(a, b)
	a, b = coerce(a), coerce(b)
	local c = cmp(a, b)
	return (c == c) and (c == 0)
end

function Number.__lt(a, b)
	a, b = coerce(a), coerce(b)
	local c = cmp(a, b)
	if c ~= c then
		return false
	end
	return c < 0
end

function Number.__le(a, b)
	a, b = coerce(a), coerce(b)
	local c = cmp(a, b)
	if c ~= c then
		return false
	end
	return c <= 0
end

function Number.__unm(a)
	a = coerce(a)
	return fastNew(-a.first, a.second) -- much faster than a * -1
end

function Number.__tostring(self)
	return self:GetSuffix(true)
end

function Number.__concat(self, value)
	return `{self}{value}`
end

--[[ Class methods ]]--

--[=[
	@within InfiniteMath

	Returns a new InfiniteMath constructed number

	You can use numbers `1`, correctly formatted strings `"1,0"`, tables `{1, 0}`, and other constructed numbers `InfiniteMath.new(1)`.

	```lua
		print(InfiniteMath.new(1)) -- 1
	```

	To create a number above 1e+308, we can use strings or tables.

	```lua
		print(InfiniteMath.new("1,1000")) -- 10DTL
		print(InfiniteMath.new({1, 1000})) -- 10DTL
	```

	@param val number | string | table | Number
	@return Number
]=]
function InfiniteMath.new(val : number | string | {} | Number) : Number
	local first, second

	if type(val) == "table" then
		if val.first ~= nil and val.second ~= nil then 
			if getmetatable(val) ~= Number then
				return setmetatable(val, Number)
			end

			return val
		end

		first = val[1]
		second = val[2]
	elseif type(val) == "string" then
		local mantStr, expStr = parseExpString(val)
		if mantStr and expStr then
			first, second = normalize(mantStr, expStr)
		else
			local n = tonumber(val)
			if n == nil then
				error('string is not a valid number format. Use "1,0" or "1e+3" etc.')
			end
			if n == math.huge or n == -math.huge then
				error('String overflows to INF. Use explicit exponent like "1e+1000" (supported) or "1,1000".')
			end
			first, second = convert(n)
		end
	elseif type(val) == 'number' then
		if val ~= val then
			error("NaN is not allowed.")
		end
		if val == math.huge or val == -math.huge then
			error('INF number is not allowed. Please use "string" or "table" instead of "number" to go above INF (e.g. "1,1000" or "1e+1000").')
		end

		first, second = convert(val)
	else
		error(`'{type(val)}' is not a valid type. Please only use "number", "string", "table", or constructed numbers.`)
		return
	end

	return setmetatable({
		first = first,
		second = second
	}, Number)
end

--[=[
	@within Number

	Sets the value of the constructed number without creating a new Number metatable. If you want to set the value of a constructed number it is better to use this than setting it to a new `.new()`.

	`SetValue` takes a new `first` and `second` to set the value to, if you want to set the value to `100` you must pass `1, 3`.

	```lua
		local Number = InfiniteMath.new(1000)
		print(Number) -- 1000
		Number:SetValue(5, 4)
		print(Number) -- 5000
	```

	@method SetValue
	@param newFirst number
	@param newSecond number
]=]
function Number:SetValue(newFirst: number, newSecond: number)
	if type(newFirst) ~= "number" or type(newSecond) ~= "number" then
		error('Both parameters of SetValue must be "number"')
	end

	newFirst, newSecond = normalize(newFirst, newSecond)

	self.first = newFirst
	self.second = newSecond
end

--[=[
	@within Number

	Attempts to return the constructed number converted into a regular number. If the constructed number is above 1e+308 it will instead return INF.

	```lua
		print(InfiniteMath.new("1, 3"):Reverse()) -- 1000
	```

	@method Reverse
	@return number
]=]
function Number:Reverse(): number
	local first, second = normalize(self.first, self.second)

	return first * 10^second
end

--[=[
	@within Number

	Returns a string with the number and a suffix at the end, these suffixes will go up to 1e+12000. After, it will default to returning scientific notation.

	By default, it will return an abbreviated suffix (1K). Using true will use the default behavior. Using false will return the full suffix (1 Thousand).

	```lua
		print(InfiniteMath.new(1000):GetSuffix()) -- 1K
		print(InfiniteMath.new(1000):GetSuffix(true)) -- 1K
		print(InfiniteMath.new(1000):GetSuffix(false)) -- 1 Thousand
	```

	@method GetSuffix
	@param abbreviation boolean | nil
	@return string
]=]
function Number:GetSuffix(abbreviation: boolean?): string
	if type(abbreviation) ~= "boolean" then
		abbreviation = true
	end
	
	local first, second = normalize(self.first, self.second)

	if second < 3 then 
		local result = `{self:Reverse()}`
		local Length = 2
		if math.sign(first) == -1 then Length = 3 end

		if math.abs(first) >= 1 then
			if InfiniteMath.DECIMALPOINTS > 0 then
				result = result:sub(1, second + Length + InfiniteMath.DECIMALPOINTS)
				local decimal = result:split(".")[2]
				if decimal == nil then return result end

				if tonumber(decimal) == 0 then
					result = result:split(".")[1]
				elseif decimal == string.rep(9 :: any, InfiniteMath.DECIMALPOINTS) then
					result = tonumber(result:split(".")[1]) + 1
				end
			else
				result = result:split(".")[1]
			end
		else
			if math.abs(first) <= .01 then return "0" end
			result = result:sub(1, second + Length + InfiniteMath.DECIMALPOINTS)
			local decimal = result:split(".")[2]

			if decimal == string.rep(9 :: any, InfiniteMath.DECIMALPOINTS) then
				result = tonumber(result:split(".")[1]) + 1
			end
		end

		return result
	end

	local secondRemainder = second % 3
	first *= 10^secondRemainder

	local suffixIndex = math.floor(second/3)
	local str = math.floor(first * 10^InfiniteMath.DECIMALPOINTS)/10^InfiniteMath.DECIMALPOINTS -- The * 10 / 10 controls decimal precision, more zeros = more decimals

	local suffix = if abbreviation then suffixes[suffixIndex] else (full_names[suffixIndex] and " " .. full_names[suffixIndex] or nil)

	if suffixIndex > 0 then
		if suffix ~= nil then
			str ..= suffix
		else
			str = self:ScientificNotation(abbreviation)
		end
	end

	return str
end

--[=[
	@within Number

	Returns a string with the number formatted in scientific notation.

	```lua
		print(InfiniteMath.new(1000):ScientificNotation()) -- 1e+3
	```
	
	When a number reaches `1e+1000000` you can choose an abbreviation mode for the amount of zeros in the scientific notation. By default, it will use GetSuffix on the exponent `1e+1M`, but you can also choose to have it use scientific notation `1e+1e+6`.

	```lua
		print(InfiniteMath.new("1, 1e+6"):ScientificNotation()) -- 1e+1M
		print(InfiniteMath.new("1, 1e+6"):ScientificNotation(true)) -- 1e+1M
		print(InfiniteMath.new("1, 1e+6"):ScientificNotation(false)) -- 1e+1e+6
	```

	You can also use nil and false to stop the functionality and instead just display `1e+1000000`.
	
	```lua
		print(InfiniteMath.new("1, 1e+6"):ScientificNotation(nil, false)) -- 1e+1000000
	```

	@method ScientificNotation
	@param abbreviation boolean | nil
	@param secondAbbreviation boolean | nil
	@return string
]=]
function Number:ScientificNotation(abbreviation: boolean?, secondAbbreviation: boolean?): string
	local first, second = normalize(self.first, self.second)

	first, second = `{first}`, `{second}`


	local str = math.floor(first * 10^InfiniteMath.DECIMALPOINTS)/10^InfiniteMath.DECIMALPOINTS -- The * 10 / 10 controls decimal precision, more zeros = more decimals
	local n = tonumber(second)

	if secondAbbreviation == false then
		second = tostring(second)
	elseif n > 1e+6 then
		second = fastNew(n, 0)
		if abbreviation ~= false then
			second = second:GetSuffix(true)
		else
			second = second:ScientificNotation(nil, false)
		end
	end

	return `{str}e+{second}`
end

--[=[
	@within Number

	Returns a string with the number formatted in logarithmic notation.

	```lua
		print(InfiniteMath.new(1000):ScientificNotation()) -- e3.0
	```

	@method LogarithmNotation
	@return string
]=]
function Number:LogarithmNotation(): string
	local first, second = normalize(self.first, self.second)
	first, second = `{first}`, `{second}`

	local suffixIndex = math.floor(second/3)

	if suffixIndex == 0 then
		local secondRemainder = second % 3
		first *= 10^secondRemainder

		return math.floor(first * 10^InfiniteMath.DECIMALPOINTS)/10^InfiniteMath.DECIMALPOINTS
	end

	local log = `{math.log10(first :: any)}`

	if string.match(log, "%.") then
		log = string.split(log, ".")
		log = log[2]:sub(1, 3)
	end

	return `e{second}.{log}`
end

local Alphabet = {"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"}

--[=[
	@within Number

	Returns a string with the number formatted in double letter notation. Use the AALENGTHMAX property to adjust the max letters possible. 
	
	```lua
		print(InfiniteMath.new(1e+15):aaNotation()) -- 1a
	```

	@method aaNotation
	@return string
]=]
function Number:aaNotation(): string
	local first, second = normalize(self.first, self.second)

	local secondRemainder = second % 3
	first *= 10^secondRemainder
	local suffixIndex = math.floor(second / 3) - 4

	if suffixIndex <= 0 then
		return self:GetSuffix()
	end

	local suffix = ""
	while suffixIndex > 0 do
		local remainder = suffixIndex % #Alphabet
		remainder = if remainder == 0 then #Alphabet else remainder
		suffix = `{Alphabet[remainder]}{suffix}`
		suffixIndex = math.floor((suffixIndex - remainder) / #Alphabet)
	end

	if #suffix > InfiniteMath.AALENGTHMAX then
		return self:ScientificNotation()
	end

	local str = math.floor(first * 10^InfiniteMath.DECIMALPOINTS) / 10^InfiniteMath.DECIMALPOINTS
	return `{str}{suffix}`
end

--[=[
	@within Number

	Returns a number that you can use for OrderedDataStores in order to create global leaderboards that support InfiniteMath constructed numbers.

	```lua
		print(InfiniteMath.new(1000):ConvertForLeaderboards()) -- 31000
	```

	@method ConvertForLeaderboards
	@return number
]=]
function Number:ConvertForLeaderboards(): number
	local first, second = normalize(self.first, self.second)
	first, second = `{first}`, `{second}`

	first = first:gsub("%.", "")

	return math.floor(tonumber(`{second}.{first:sub(1, LEADERBOARDPOINT)}`) * LEADERBOARDPRECISION)
end

--[=[
	@within InfiniteMath

	Returns a constructed number, and should be given a number created by `Number:ConvertForLeaderboards`. This is what you will display on global leaderboards using OrderedDataStores.

	```lua
		local ValueFromStore = InfiniteMath.new(1000):ConvertForLeaderboards()
		print(InfiniteMath:ConvertFromLeaderboards(ValueFromStore)) -- 1K
	```

	@method ConvertFromLeaderboards
	@param GivenNumber number
	@return Number
]=]
function InfiniteMath:ConvertFromLeaderboards(GivenNumber: number): Number
	--return 0
	local num = GivenNumber
	if num == 0 then
		return fastNew(0, 0)
	end

	num /= LEADERBOARDPRECISION
	num = `{num}`

	local numbers = num:split('.')
	local second, first = numbers[1], numbers[2]
	first, second = `{first}`, `{second}`

	local firstFirst = first:sub(1, 1)
	local firstSecond = first:sub(2)

	first = `{firstFirst}.{firstSecond}`

	return fastNew(tonumber(first), tonumber(second))
end

--[[ Math methods ]]--

--[=[
	@within InfiniteMath

	Rounds a number down to the nearest integer

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.floor(Num): Number
	Num = checkNumber(Num)

	local _first, second = normalize(Num.first, Num.second)
	if second >= 300 then return Num end -- Rounding after 1e+300 would be pointless, so don't do it.

	return InfiniteMath.new(math.floor(Num:Reverse()))
end

--[=[
	@within InfiniteMath

	Rounds a number to the nearest integer

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.round(Num): Number
	Num = checkNumber(Num)

	local _, second = normalize(Num.first, Num.second)
	if second >= 300 then return Num end -- Rounding after 1e+300 would be pointless, so don't do it.

	local r = Num:Reverse() -- finite here due to second < 300
	local rounded = if r >= 0 then math.floor(r + 0.5) else math.ceil(r - 0.5)

	return fastNew(rounded, 0)
end

--[=[
	@within InfiniteMath

	Rounds a number up to the nearest integer

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.ceil(Num): Number
	Num = checkNumber(Num)

	local _first, second = normalize(Num.first, Num.second)
	if second >= 300 then return Num end -- Rounding after 1e+300 would be pointless, so don't do it.

	return fastNew(math.ceil(Num:Reverse()))
end

--[=[
	@within InfiniteMath

	Returns the absolute value (distance from 0)

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.abs(Num): Number
	Num = checkNumber(Num)
	local first, second = normalize(Num.first, Num.second)

	return fastNew(math.abs(first), second)
end

--[=[
	@within InfiniteMath

	Clamps a number between a minimum and maximum value

	@param Num number | string | table | Number
	@param Min number | string | table | Number
	@param Max number | string | table | Number
	@return Number
]=]
function InfiniteMath.clamp<T, A, B>(Num: T, Min: A, Max: B): T
	Num = checkNumber(Num)
	local first, second = normalize(Num.first, Num.second)
	Num = fastNew(first, second)

	if Min ~= nil then
		Min = checkNumber(Min)
		local firstMin, secondMin = normalize(Min.first, Min.second)
		Min = fastNew(firstMin, secondMin)
	else
		Min = fastNew(0, 0)
	end

	if Max ~= nil then
		Max = checkNumber(Max)
		local firstMax, secondMax = normalize(Max.first, Max.second)
		Max = fastNew(firstMax, secondMax)
	else
		Max = fastNew(1, 1e+308)
	end

	Num = if Num < Min then Min elseif Num > Max then Max else Num

	return Num
end

--[=[
	@within InfiniteMath

	Returns the smallest number among the given arguments 

	@param ... number | string | table | Number
	@return Number
]=]
function InfiniteMath.min(...): Number
	local Numbers = {...}
	if Numbers[1] == nil then
		error("InfiniteMath.min requires at least 1 argument.")
	end

	for Index, Num in Numbers do
		Numbers[Index] = checkNumber(Num)
	end

	local Min = Numbers[1]

	for _, Num in Numbers do
		if Num < Min then
			Min = Num
		end
	end

	return Min
end

--[=[
	@within InfiniteMath

	Returns the largest number among the given arguments

	@param ... number | string | table | Number
	@return Number
]=]
function InfiniteMath.max(...): Number
	local Numbers = {...}
	if Numbers[1] == nil then
		error("InfiniteMath.max requires at least 1 argument.")
	end

	for Index, Num in Numbers do
		Numbers[Index] = checkNumber(Num)
	end

	local Max = Numbers[1]

	for _, Num in Numbers do
		if Num > Max then
			Max = Num
		end
	end

	return Max
end


--[=[
	@within InfiniteMath

	Returns the sign of the number. Negative numbers return -1, positive numbers return 1, 0 returns 0.
	
	@param Num number | string | table | Number
	@return number
]=]
function InfiniteMath.sign(Num): number
	Num = checkNumber(Num)
	local first = normalize(Num.first, Num.second)
	first = tonumber(first)

	return if first > 0 then 1 elseif first < 0 then -1 else 0
end

--[=[
	@within InfiniteMath

	Returns the square root of a number

	@param Num number | string | table | Number
	@return Number
]=]

function InfiniteMath.sqrt(Num): Number
	return Num^.5
end

--[=[
	@within InfiniteMath

	Returns the remainder of the division of a by b that rounds the quotient towards zero.

	@param a number | string | table | Number
	@param b number | string | table | Number
	@return Number
]=]
function InfiniteMath.fmod(a, b): Number
	a, b = checkNumber(a), checkNumber(b)
	local q = a / b
	local qi = (InfiniteMath.sign(q) >= 0) and InfiniteMath.floor(q) or InfiniteMath.ceil(q)
	return a - b * qi
end

--[=[
	@within InfiniteMath

	Returns both the integral part of n and the fractional part (if there is one). 

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.modf(Num): (Number, number?)
	Num = checkNumber(Num)
	local sign = InfiniteMath.sign(Num)
	Num *= sign

	local first, second = normalize(Num.first, Num.second)
	local firstSplit = tostring(first):split(".")

	if firstSplit[2] ~= nil then
		first = firstSplit[2]:sub(1, second)
		first = firstSplit[1].."."..first

		local power = if second == 0 then 2 else second
		local decimal

		if second > 0 then
			decimal = firstSplit[2]:sub(power + 1) / 10^#firstSplit[2]:sub(power + 1)
		else
			decimal = firstSplit[2] / 10^#firstSplit[2]
		end

		return fastNew(first, second) * sign, decimal
	end

	return Num
end

--[=[
	@within InfiniteMath
	
	Returns the logarithm of x with the given base. Default base is constant e (2.7182818)

	@param Num number | string | table | Number
	@param Base number
	@return Number
]=]
function InfiniteMath.log(Num, Base): Number
	Num = checkNumber(Num)

	if InfiniteMath.sign(Num) == -1 then 
		return NaN  -- log of a negative number is always nan
	end

	if Base == nil then
		Base = 2.7182818
	end

	local f, e = normalize(Num.first, Num.second)

	-- log_base(Num) = log_base(f) + e * log_base(10)
	local term1 = InfiniteMath.new(e) * math.log(10, Base)
	local term2 = InfiniteMath.new(math.log(f, Base))
	return term1 + term2
end

--[=[
	@within InfiniteMath

	Returns the base-10 logarithm of x.

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.log10(Num): Number
	return InfiniteMath.log(Num, 10)
end

--[=[
	@within InfiniteMath

	Checks if a value is nil (or an invalid constructed number).

	This is meant as a "safe check" for external inputs / user data.

	Returns true if:
	- `x == nil`, OR
	- `x` is a constructed `Number` but has missing fields (`first` or `second` is nil).

	@param x any
	@return boolean
]=]
function InfiniteMath.isNil(x: any): boolean
	if x == nil then
		return true
	end
	if isNumberObject(x) then
		return x.first == nil or x.second == nil
	end
	return false
end

--[=[
	@within InfiniteMath

	Checks if a value is NaN.

	Supported inputs:
	- `number`: true if `x ~= x`
	- constructed `Number`: true if either internal field is NaN-like
	- `string`: true if it contains "nan"
	- anything else: false

	This function does NOT throw.

	@param x any
	@return boolean
]=]
function InfiniteMath.isNaN(x: any): boolean
	if x == nil then
		return false
	end
	if type(x) == "number" then
		return x ~= x
	end
	if isNumberObject(x) then
		return isFieldNaN(x.first) or isFieldNaN(x.second)
	end
	if type(x) == "string" then
		return x == "nan"
	end
	return false
end

--[=[
	@within InfiniteMath

	Checks if a value is positive or negative infinity.

	Supported inputs:
	- `number`: true if `x == math.huge` or `x == -math.huge`
	- constructed `Number`: true if either internal field is inf-like
	- `string`: true if it equals "inf", "-inf"
	- anything else: false

	This function does NOT throw.

	@param x any
	@return boolean
]=]
function InfiniteMath.isInf(x: any): boolean
	if x == nil then
		return false
	end
	if type(x) == "number" then
		return x == math.huge or x == -math.huge
	end
	if isNumberObject(x) then
		return isFieldInf(x.first) or isFieldInf(x.second)
	end
	if type(x) == "string" then
		return x == "inf" or x == "-inf"
	end
	return false
end

--[=[
	@within InfiniteMath

	Checks if a value represents exactly zero.

	Note:
	- For constructed `Number`s, it normalizes using `fixNumber`, so values like `{0, 1000}` are treated as zero.

	Supported inputs:
	- `number`
	- constructed `Number`
	- `string` (tries `tonumber`, and also supports `"0,123"` style)

	This function does NOT throw.

	@param x any
	@return boolean
]=]
function InfiniteMath.isZero(x: any): boolean
	if x == nil then
		return false
	end
	if type(x) == "number" then
		return x == 0
	end
	if isNumberObject(x) then
		local f, e = normalize(x.first, x.second)
		return f == 0 and e == 0
	end
	if type(x) == "string" then
		local n = tonumber(x)
		if n ~= nil then
			return n == 0
		end
		-- "0,1234" style
		local a = x:match("^%s*([+-]?%d*%.?%d+)%s*,")
		return a ~= nil and tonumber(a) == 0
	end
	return false
end

InfiniteMath.Int = int(InfiniteMath)

return InfiniteMath
