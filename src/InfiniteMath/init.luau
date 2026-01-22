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
local POW10 = {}

-- pre-compute powers of 10 to avoid recalculating them every time
for i = -THRESHOLD, THRESHOLD do
	POW10[i] = 10^i
end

local suffixes = require("@self/Values/Suffixes")
local full_names = require("@self/Values/FullNames")
local int = require("@self/Int")

--[[ Private functions ]]--
local function fixNumber(first, second): (number, number)
	if type(first) ~= "number" then
		first = tonumber(first)
	end
	if type(second) ~= "number" then
		second = tonumber(second)
	end

	if second % 1 > 0 then
		first *= 10^(second % 1)
	end

	second = math.floor(second)

	local sign = math.sign(first)
	local x

	if first == 0 or (second == 0 and first < 1) then
		return first, 0
	elseif second == 0 and first == 0 then
		return 0,0
	elseif first < 1 * sign then
		x = math.abs(first)
		local log10 = math.abs(math.floor(math.log10(x)))

		if log10 ~= 0 then -- Check if exponent is 0 then
			second -= log10
			x *= 10^log10
		end

	elseif first >= 1 * sign then
		x = math.abs(first)
		local e = math.floor(math.log10(x))
		if e ~= 0 then -- Check if exponent is 0 then
			second += e
			x /= 10^e
		end
	end

	if x == nil then
		return NaN, NaN
	end

	if second < 0 then
		local Pow = math.abs(second)

		x /= 10^Pow
		second += Pow
	end

	return x*sign, second
end

local function convert(number: number): (string, string)
	if type(number) ~= "number" then
		error('Type is not a "number".')
	end

	local sign = math.sign(number)
	number = math.abs(number)

	-- get string representation
	local numberStr = tostring(number)
	local removed = 0

	if string.match(numberStr, "%.") and not string.match(numberStr, "e") then
		local dot = numberStr:find(".", 1, true)
		if dot then
			local frac = numberStr:sub(dot + 1)
			numberStr = `{numberStr:sub(1, dot - 1)}{frac}`
			removed = #frac
		end
	end

	local first
	local second = #numberStr - 1 - removed

	if string.match(numberStr, "e") then
		if string.match(numberStr, "+") then
			second = numberStr:split("+")[2]
		elseif string.match(numberStr, "-") then
			second = numberStr:split("e")[2]
		end
		first = numberStr:split("e")[1]
	elseif string.match(numberStr, "inf") then
		second = "inf"
		first = "inf"
	elseif string.match(numberStr, "nan") then
		second = "nan"
		first = "nan"
	else
		if #numberStr == 1 then
			first = number
		else
			local firstZ = numberStr:sub(1, 1)
			local secondZ = numberStr:sub(2)

			if tonumber(secondZ) > 0 then
				first = `{firstZ}.{secondZ}`
			else
				first = firstZ
			end
		end
	end

	return first * sign, second
end

local function checkNumber<T>(a: T): T
	if type(a) == "table" and getmetatable(a) == Number then
		return a
	end
	if type(a) ~= "number" and type(a) ~= "string" and type(a) ~= "table" then
		error(`{type(a)} is not a valid type. Please only use "number", "string", or constructed numbers.`)
	end

	a = InfiniteMath.new(a)

	if a.first == nil and a.second == nil then
		error('"string" is not correctly formatted. Correctly formatted strings look like "1,0".')
	end

	return a
end

local function cmp(a: Number, b: Number): number
	local f1, e1 = fixNumber(a.first, a.second)
	local f2, e2 = fixNumber(b.first, b.second)

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

-- math metamethods:
function Number.__add(a, b)
	a, b = checkNumber(a), checkNumber(b)

	local first1, second1 = fixNumber(a.first, a.second)
	local first2, second2 = fixNumber(b.first, b.second)
	if math.abs(second1 - second2) > THRESHOLD then -- Check if difference in exponents is greater than threshold
		if math.max(second1, second2) == second1 then
			return InfiniteMath.new({first1, second1})
		end

		return InfiniteMath.new({first2, second2})
	end

	local difference = second1 - second2
	first2 *= POW10[-difference]

	first1, second1 = fixNumber(first1 + first2, second1)

	return InfiniteMath.new({first1 , second1})
end

function Number.__sub(a, b)
	a, b = checkNumber(a), checkNumber(b)

	local first1, second1 = fixNumber(a.first, a.second)
	local first2, second2 = fixNumber(b.first, b.second)
	if math.abs(second1 - second2) > THRESHOLD then -- Check if difference in exponents is greater than threshold
		if math.max(second1, second2) == second1 then
			return InfiniteMath.new({first1 ,second1})
		end

		return InfiniteMath.new({first2, second2})
	end

	local difference = second1 - second2
	first2 *= POW10[-difference]

	first1, second1 = fixNumber(first1 - first2, second1)

	return InfiniteMath.new({first1 , second1})
end

function Number.__mul(a, b)
	a, b = checkNumber(a), checkNumber(b)

	local first1, second1 = fixNumber(a.first, a.second)
	local first2, second2 = fixNumber(b.first, b.second)

	first1, second1 = fixNumber(first1 * first2, second1 + second2)

	return InfiniteMath.new({first1 , second1})
end

function Number.__div(a, b)
	a, b = checkNumber(a), checkNumber(b)

	local first1, second1 = fixNumber(a.first, a.second)
	local first2, second2 = fixNumber(b.first, b.second)

	first1, second1 = fixNumber(first1/first2, second1 - second2)

	return InfiniteMath.new({first1 , second1})
end

function Number.__pow(a, power)
	a = checkNumber(a)

	if type(power) ~= "number" then
		power = power:Reverse()
	end

	if power == math.huge or power ~= power or type(power) ~= "number" then
		error(`'{power}' is not a valid power. If power is 'inf' you must keep it below 10^308.`)
	end

	local sign = InfiniteMath.sign(a)
	a *= sign

	local first, second = fixNumber(a.first, a.second)
	local n, n2 = first^power, second * power

	if n == math.huge or n2 == math.huge then
		if type(power) ~= "number" then
			power = power:Reverse()
		end

		local answer = InfiniteMath.new(1)

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

			firstAnswer, secondAnswer = fixNumber(answer.first, answer.second)
		elseif power == 0 then
			firstAnswer, secondAnswer = 1, 0
		else
			firstAnswer, secondAnswer = first, second
		end
		return InfiniteMath.new({firstAnswer, secondAnswer})
	end
	return InfiniteMath.new({n, n2}) * sign
end

function Number.__mod(a, b)
	a, b = checkNumber(a), checkNumber(b)
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
	a, b = checkNumber(a), checkNumber(b)
	local c = cmp(a, b)
	return (c == c) and (c == 0)
end

function Number.__lt(a, b)
	a, b = checkNumber(a), checkNumber(b)
	local c = cmp(a, b)
	if c ~= c then
		return false
	end
	return c < 0
end

function Number.__le(a, b)
	a, b = checkNumber(a), checkNumber(b)
	local c = cmp(a, b)
	if c ~= c then
		return false
	end
	return c <= 0
end

function Number.__unm(a)
	a = checkNumber(a)

	return a * -1
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
function InfiniteMath.new(val) : Number
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
		local mantStr, expStr = val:match("^%s*([+-]?%d*%.?%d+)%s*[eE]%s*([+-]?%d+)%s*$")
		if mantStr and expStr then
			first, second = fixNumber(tonumber(mantStr), tonumber(expStr))

		elseif val:find(",", 1, true) then
			first, second = fixNumber(table.unpack(val:split(",")))

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
		if val == 1e+999 then
			error('INF number is not allowed. Please use "string" or "table" instead of "number" to go above INF.')
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

	newFirst, newSecond = fixNumber(newFirst, newSecond)

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
	local first, second = fixNumber(self.first, self.second)

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

	local first, second = fixNumber(self.first, self.second)

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
	local first, second = fixNumber(self.first, self.second)
	
	first, second = `{first}`, `{second}`


	local str = math.floor(first * 10^InfiniteMath.DECIMALPOINTS)/10^InfiniteMath.DECIMALPOINTS -- The * 10 / 10 controls decimal precision, more zeros = more decimals
	local n = tonumber(second)
	
	if n > 1e+6 and secondAbbreviation ~= false then
		second = InfiniteMath.new(n)
		if abbreviation ~= false then
			second:GetSuffix(true)
		else
			second:ScientificNotation(nil, false)
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
	local first, second = fixNumber(self.first, self.second)
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
	local first, second = fixNumber(self.first, self.second)

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
	local first, second = fixNumber(self.first, self.second)
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
		return InfiniteMath.new(0)
	end

	num /= LEADERBOARDPRECISION
	num = `{num}`

	local numbers = num:split('.')
	local second, first = numbers[1], numbers[2]
	first, second = `{first}`, `{second}`

	local firstFirst = first:sub(1, 1)
	local firstSecond = first:sub(2)

	first = `{firstFirst}.{firstSecond}`

	return InfiniteMath.new({tonumber(first), tonumber(second)})
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

	local _first, second = fixNumber(Num.first, Num.second)
	if second >= 300 then return Num end -- Rounding after 1e+300 would be pointless, so don't do it.

	return InfiniteMath.new(math.floor(Num:Reverse()))
end

--[=[
	@within InfiniteMath

	Rounds a number to the nearest integer

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.round<T>(Num: T): T
	Num = checkNumber(Num)

	local first, second = fixNumber(Num.first, Num.second)
	if second >= 300 then return Num end -- Rounding after 1e+300 would be pointless, so don't do it.
	first = `{first}`

	local decimal: string = first:sub(3 + second)

	if decimal ~= "" then
		local firstSplit = tonumber(decimal) / 10^#decimal
		local reverse = Num:Reverse()

		if firstSplit >= .5 then
			return InfiniteMath.new(math.ceil(reverse))
		end
		return InfiniteMath.new(math.floor(reverse))
	end

	return Num
end

--[=[
	@within InfiniteMath

	Rounds a number up to the nearest integer

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.ceil(Num): Number
	Num = checkNumber(Num)

	local _first, second = fixNumber(Num.first, Num.second)
	if second >= 300 then return Num end -- Rounding after 1e+300 would be pointless, so don't do it.

	return InfiniteMath.new(math.ceil(Num:Reverse()))
end

--[=[
	@within InfiniteMath

	Returns the absolute value (distance from 0)

	@param Num number | string | table | Number
	@return Number
]=]
function InfiniteMath.abs(Num): Number
	Num = checkNumber(Num)
	local first, second = fixNumber(Num.first, Num.second)

	return InfiniteMath.new({math.abs(first), second})
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
	local first, second = fixNumber(Num.first, Num.second)
	Num = InfiniteMath.new({first, second})

	if Min ~= nil then
		Min = checkNumber(Min)
		local firstMin, secondMin = fixNumber(Min.first, Min.second)
		Min = InfiniteMath.new({firstMin, secondMin})
	else
		Min = InfiniteMath.new(0)
	end

	if Max ~= nil then
		Max = checkNumber(Max)
		local firstMax, secondMax = fixNumber(Max.first, Max.second)
		Max = InfiniteMath.new({firstMax, secondMax})
	else
		Max = InfiniteMath.new({1, 1e+308})
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
	local first = fixNumber(Num.first, Num.second)
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
function InfiniteMath.modf(Num): Number
	Num = checkNumber(Num)
	local sign = InfiniteMath.sign(Num)
	Num *= sign

	local first, second = fixNumber(Num.first, Num.second)
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

		return InfiniteMath.new({first, second}) * sign, decimal
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

	local first, second = fixNumber(Num.first, Num.second)

	return InfiniteMath.new(math.log(first, Base) + second * math.log(10, Base))
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

InfiniteMath.Int = int(InfiniteMath)

return InfiniteMath