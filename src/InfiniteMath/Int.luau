--!native
local Int = {}
Int.__index = Int

export type Int = typeof(setmetatable({
	sign = 0 :: number, -- -1, 0, +1
	limbs = {} :: { number }, -- little-endian uint32 limbs (base 2^32)
}, Int))

local function trimLimbs(limbs: { number })
	while #limbs > 0 and limbs[#limbs] == 0 do
		table.remove(limbs)
	end
end

local function cloneArray(t: { number }): { number }
	local out = table.create(#t)
	for i = 1, #t do
		out[i] = t[i]
	end
	return out
end

local function assertEndian(endian: string)
	if endian ~= "le" and endian ~= "be" then
		error(("Invalid endian '%s'. Use 'le' or 'be'."):format(endian))
	end
end

local function assertBytes(bytes: { number })
	if type(bytes) ~= "table" then
		error("bytes must be an array/table of integers 0..255")
	end
	for i = 1, #bytes do
		local b = bytes[i]
		if type(b) ~= "number" or b % 1 ~= 0 or b < 0 or b > 255 then
			error(("bytes[%d] is not a valid byte (0..255 integer). Got: %s"):format(i, `{b}`))
		end
	end
end

local function toLEBytes(endian: string, bytes: { number }): { number }
	if endian == "le" then
		return cloneArray(bytes)
	end
	local out = table.create(#bytes)
	for i = 1, #bytes do
		out[i] = bytes[#bytes - i + 1]
	end
	return out
end

local function fromLEBytes(endian: string, leBytes: { number }): { number }
	if endian == "le" then
		return leBytes
	end
	local out = table.create(#leBytes)
	for i = 1, #leBytes do
		out[i] = leBytes[#leBytes - i + 1]
	end
	return out
end

local function twosComplementToMagnitudeLE(leBytes: { number }): { number }
	local n = #leBytes
	local out = table.create(n)
	for i = 1, n do
		out[i] = 255 - leBytes[i]
	end
	-- +1
	local carry = 1
	for i = 1, n do
		local v = out[i] + carry
		if v >= 256 then
			out[i] = v - 256
			carry = 1
		else
			out[i] = v
			carry = 0
			break
		end
	end
	return out
end

local function magnitudeToTwosComplementLE(magLE: { number }, length: number): { number }
	local out = table.create(length, 0)
	for i = 1, length do
		out[i] = (i <= #magLE) and magLE[i] or 0
	end
	for i = 1, length do
		out[i] = 255 - out[i]
	end
	-- +1
	local carry = 1
	for i = 1, length do
		local v = out[i] + carry
		if v >= 256 then
			out[i] = v - 256
			carry = 1
		else
			out[i] = v
			carry = 0
			break
		end
	end
	return out
end

local function limbsFromLEBytes(leBytes: { number }): { number }
	local limbs = {}
	local limbIndex = 1
	local i = 1
	while i <= #leBytes do
		local b0 = leBytes[i] or 0
		local b1 = leBytes[i + 1] or 0
		local b2 = leBytes[i + 2] or 0
		local b3 = leBytes[i + 3] or 0

		local limb = b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
		limbs[limbIndex] = limb

		limbIndex += 1
		i += 4
	end
	trimLimbs(limbs)
	return limbs
end

local function leBytesFromLimbs(limbs: { number }): { number }
	if #limbs == 0 then
		return { 0 }
	end
	local out = table.create(#limbs * 4)
	local k = 1
	for i = 1, #limbs do
		local limb = limbs[i]
		for _ = 1, 4 do
			out[k] = limb % 256
			limb = math.floor(limb / 256)
			k += 1
		end
	end
	while #out > 1 and out[#out] == 0 do
		table.remove(out)
	end
	return out
end

return function(InfiniteMath): typeof(Int)
	function Int.is(value: any): boolean
		return typeof(value) == "table" and getmetatable(value) == Int
	end

	function Int.zero(): Int
		return setmetatable({ sign = 0, limbs = {} }, Int)
	end

	function Int.FromRawBytes(endian: string, bytes: { number }, signed: boolean?): Int
		assertEndian(endian)
		assertBytes(bytes)

		if #bytes == 0 then
			return Int.zero()
		end

		local le = toLEBytes(endian, bytes)
		local sign = 1

		if signed then
			local msb = le[#le]
			if msb >= 128 then
				sign = -1
				le = twosComplementToMagnitudeLE(le)
			end
		end

		local limbs = limbsFromLEBytes(le)
		if #limbs == 0 then
			return Int.zero()
		end

		return setmetatable({
			sign = sign,
			limbs = limbs,
		}, Int)
	end

	function Int:ToRawBytes(endian: string, minBytes: number?, signed: boolean?): { number }
		assertEndian(endian)

		if minBytes ~= nil then
			if type(minBytes) ~= "number" or minBytes % 1 ~= 0 or minBytes < 0 then
				error("minBytes must be a non-negative integer")
			end
		end

		if signed ~= true and self.sign < 0 then
			error("ToRawBytes(unsigned) cannot serialize a negative Int. Pass signed=true.")
		end

		local magLE = leBytesFromLimbs(self.limbs)

		if signed then
			if self.sign >= 0 then
				-- ensure sign bit 0
				if magLE[#magLE] >= 128 then
					magLE[#magLE + 1] = 0
				end
				if minBytes ~= nil then
					while #magLE < minBytes do
						magLE[#magLE + 1] = 0
					end
				end
				return fromLEBytes(endian, magLE)
			end
			local length = minBytes or #magLE
			if length < #magLE then
				error("minBytes too small to represent this value")
			end
			while #magLE < length do
				magLE[#magLE + 1] = 0
			end
			local twosLE = magnitudeToTwosComplementLE(magLE, length)
			return fromLEBytes(endian, twosLE)
		end
		if minBytes ~= nil then
			if minBytes < #magLE then
				error("minBytes too small to represent this value")
			end
			while #magLE < minBytes do
				magLE[#magLE + 1] = 0
			end
		end
		return fromLEBytes(endian, magLE)
	end

	function Int:IterRawBytes(endian: string, minBytes: number?, signed: boolean?)
		return ipairs(self:ToRawBytes(endian, minBytes, signed))
	end

	function Int:ToNumber()
		if self.sign == 0 or #self.limbs == 0 then
			return InfiniteMath.new(0)
		end

		local n: number = #self.limbs
		local msw: number = self.limbs[n]
		if msw == 0 then
			return InfiniteMath.new(0)
		end

		-- log10(value) ~= ((n-1)*32 + log2(msw)) * log10(2)
		local LOG10_2 = math.log(2) / math.log(10)
		local log2 = (n - 1) * 32 + (math.log(msw) / math.log(2))
		local log10 = log2 * LOG10_2

		local exp10 = math.floor(log10)
		local frac = log10 - exp10
		local mant = 10 ^ frac -- [1,10)

		return InfiniteMath.new({ mant * self.sign, exp10 })
	end

	function Int:ScientificNotation(abbrev: boolean?, secondAbbrev: boolean?): string
		return self:ToNumber():ScientificNotation(abbrev, secondAbbrev)
	end

	function Int:__tostring()
		return self:ScientificNotation()
	end

	return Int
end