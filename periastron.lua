

-- // Load

local startupArgs = ({...})[1] or {}

if getgenv().library ~= nil and type(getgenv().library.Unload) == 'function' then
    pcall(function()
        getgenv().library:Unload();
    end)
end

if not game:IsLoaded() then
    game.Loaded:Wait()
end

local function gs(a)
    return game:GetService(a)
end

-- // Variables
local players, http, runservice, inputservice, tweenService, stats, actionservice = gs('Players'), gs('HttpService'), gs('RunService'), gs('UserInputService'), gs('TweenService'), gs('Stats'), gs('ContextActionService')
local localplayer = players.LocalPlayer

local setByConfig = false
local floor, ceil, huge, pi, clamp = math.floor, math.ceil, math.huge, math.pi, math.clamp
local c3new, fromrgb, fromhsv = Color3.new, Color3.fromRGB, Color3.fromHSV
local next, newInstance, newUDim2, newVector2 = next, Instance.new, UDim2.new, Vector2.new
local isexecutorclosure = isexecutorclosure or is_synapse_function or is_sirhurt_closure or iskrnlclosure;
local executor = (
    syn and 'syn' or
    (identifyexecutor and identifyexecutor()) or
    (getexecutorname and getexecutorname()) or
    'unknown'
)

-- // Executor compatibility helpers
-- The original lib relied on Synapse-only globals (syn.request, syn.crypt, syn.protect_gui, printconsole)
-- which error on every other executor. These fall back gracefully.

-- size + position of a slider's fill bar. ranges that cross 0 (like -50..50) fill from the 0 point
-- towards the value, so the bar never gets a negative width (that's what made it spill past the end)
local function sliderFill(min, max, value)
    local range = max - min
    if range <= 0 then
        return UDim2.new(1, 0, 1, 0), UDim2.new(0, 0, 0, 0)
    end
    local zero = math.clamp((0 - min) / range, 0, 1)
    local point = math.clamp((value - min) / range, 0, 1)
    local left = math.min(zero, point)
    return UDim2.new(math.abs(point - zero), 0, 1, 0), UDim2.new(left, 0, 0, 0)
end

-- snaps a value to the nearest increment (the old floor() turned 0.5 with increment 0.1 into 0.4)
local function snapToIncrement(value, increment, min, max)
    increment = (typeof(increment) == 'number' and increment > 0) and increment or 1
    local snapped = math.floor(value / increment + 0.5) * increment
    -- strip float noise like 0.30000000000000004
    snapped = tonumber(string.format('%.10f', snapped)) or snapped
    return math.clamp(snapped, min, max)
end

local function log(msg)
    if printconsole then
        pcall(printconsole, tostring(msg), 255, 0, 0)
    else
        warn('[ui] ' .. tostring(msg))
    end
end

-- note: the local `http` above is HttpService, so the executor `http` table is read from getgenv
local genvHttp = getgenv and rawget(getgenv(), 'http')
local httpRequest = (syn and syn.request) or (type(genvHttp) == 'table' and genvHttp.request) or http_request or (fluxus and fluxus.request) or request

local nativeSetClipboard = setclipboard or toclipboard or set_clipboard or (Clipboard and Clipboard.set)
local function setclip(str)
    if nativeSetClipboard then
        pcall(nativeSetClipboard, tostring(str))
        return true
    end
    log('setclipboard is not supported by this executor')
    return false
end

local function safeMakeFolder(path)
    if makefolder and not (isfolder and isfolder(path)) then
        pcall(makefolder, path)
    end
end

local base64decode
do
    local native = (crypt and (crypt.base64decode or (crypt.base64 and crypt.base64.decode)))
        or (syn and syn.crypt and syn.crypt.base64 and syn.crypt.base64.decode)
        or base64_decode
        or (base64 and base64.decode)

    local chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
    local lookup = {}
    for i = 1, #chars do
        lookup[chars:sub(i, i)] = i - 1
    end

    -- pure lua fallback
    local function luaDecode(data)
        data = data:gsub('[^%w%+/=]', '')
        local out = {}
        local bits, bitCount = 0, 0
        for i = 1, #data do
            local ch = data:sub(i, i)
            if ch == '=' then break end
            local v = lookup[ch]
            if v then
                bits = bits * 64 + v
                bitCount = bitCount + 6
                if bitCount >= 8 then
                    bitCount = bitCount - 8
                    local byte = math.floor(bits / (2 ^ bitCount)) % 256
                    out[#out + 1] = string.char(byte)
                    bits = bits % (2 ^ bitCount)
                end
            end
        end
        return table.concat(out)
    end

    base64decode = function(data)
        if native then
            local ok, res = pcall(native, data)
            if ok and type(res) == 'string' and #res > 0 then
                return res
            end
        end
        return luaDecode(data)
    end
end

-- // Signal
-- The original loaded Quenty's Nevermore Signal.lua from GitHub. That file now calls
-- require(script.Parent.loader), which errors under loadstring, so the whole lib failed to load.
-- This is a small self-contained replacement with the same API (new/Connect/Fire/Wait/Once/DisconnectAll).
local Signal = {}
Signal.__index = Signal
do
    local Connection = {}
    Connection.__index = Connection

    function Connection:Disconnect()
        if not self.Connected then return end
        self.Connected = false
        local handlers = self._signal._handlers
        local idx = table.find(handlers, self)
        if idx then
            table.remove(handlers, idx)
        end
    end
    Connection.Destroy = Connection.Disconnect

    function Signal.new()
        return setmetatable({_handlers = {}}, Signal)
    end

    function Signal:Connect(fn)
        assert(type(fn) == 'function', 'Signal:Connect expects a function')
        local conn = setmetatable({_signal = self, _fn = fn, Connected = true}, Connection)
        table.insert(self._handlers, conn)
        return conn
    end

    function Signal:Once(fn)
        local conn
        conn = self:Connect(function(...)
            conn:Disconnect()
            fn(...)
        end)
        return conn
    end

    -- handlers run in a reused coroutine (GoodSignal style) instead of a brand new thread per handler per fire.
    -- a handler that yields simply keeps that coroutine, and a new one is made for the next handler.
    local freeRunner = nil
    local function acquireRunnerAndCall(fn, ...)
        local runner = freeRunner
        freeRunner = nil
        fn(...)
        freeRunner = runner
    end
    local function runEventHandlerInFreeThread()
        while true do
            acquireRunnerAndCall(coroutine.yield())
        end
    end

    function Signal:Fire(...)
        local handlers = self._handlers
        if #handlers == 0 then return end
        -- copy so handlers can disconnect while firing
        for _, conn in ipairs(table.clone(handlers)) do
            if conn.Connected then
                if not freeRunner then
                    freeRunner = coroutine.create(runEventHandlerInFreeThread)
                    coroutine.resume(freeRunner)
                end
                task.spawn(freeRunner, conn._fn, ...)
            end
        end
    end

    function Signal:Wait()
        local thread = coroutine.running()
        self:Once(function(...)
            task.spawn(thread, ...)
        end)
        return coroutine.yield()
    end

    function Signal:DisconnectAll()
        for _, conn in ipairs(table.clone(self._handlers)) do
            conn:Disconnect()
        end
    end
    Signal.Destroy = Signal.DisconnectAll
end

local library = {
    windows = {};
    indicators = {};
    flags = {};
    options = {};
    connections = {};
    drawings = {};
    instances = {};
    utility = {};
    notifications = {};
    tweens = {};
    activeTweens = {};
    hitboxes = {}; -- visible-or-not Squares that can be hovered/clicked (drawing data -> true)
    theme = {};
    zindexOrder = {
        ['indicator'] = 950;
        ['window'] = 1000;
        ['dropdown'] = 1200;
        ['colorpicker'] = 1100;
        ['watermark'] = 1300;
        ['notification'] = 1400;
        ['cursor'] = 1500;
    },
    stats = {
        ['fps'] = 0;
        ['ping'] = 0;
    };
    images = {
        ['gradientp90'] = 'https://raw.githubusercontent.com/portallol/luna/main/modules/gradient90.png';
        ['gradientp45'] = 'https://raw.githubusercontent.com/portallol/luna/main/modules/gradient45.png';
        ['colorhue'] = 'https://raw.githubusercontent.com/portallol/luna/main/modules/lgbtqshit.png';
        ['colortrans'] = 'https://raw.githubusercontent.com/portallol/luna/main/modules/trans.png';
    };
    -- keys accepted when ctrl+clicking a slider to type a number (numpad, minus and decimal point included)
    numberStrings = {
        ['Zero'] = 0, ['One'] = 1, ['Two'] = 2, ['Three'] = 3, ['Four'] = 4, ['Five'] = 5, ['Six'] = 6, ['Seven'] = 7, ['Eight'] = 8, ['Nine'] = 9,
        ['KeypadZero'] = 0, ['KeypadOne'] = 1, ['KeypadTwo'] = 2, ['KeypadThree'] = 3, ['KeypadFour'] = 4,
        ['KeypadFive'] = 5, ['KeypadSix'] = 6, ['KeypadSeven'] = 7, ['KeypadEight'] = 8, ['KeypadNine'] = 9,
        ['Minus'] = '-', ['KeypadMinus'] = '-', ['Period'] = '.', ['KeypadPeriod'] = '.',
    };
    signal = Signal;
    open = false;
    opening = false;
    hasInit = false;
    cheatname = startupArgs.cheatname or 'periastron';
    gamename = startupArgs.gamename or 'universal';
    fileext = startupArgs.fileext or '.txt';
}

-- animation timings (seconds). set any of these to 0 to turn that animation off
library.animations = {
    enabled = true;   -- master switch
    color = .12;      -- hover / toggle / tab color easing
    tab = .22;        -- tab switch fade + rise
    tabOffset = 6;    -- how many pixels sections rise when switching tabs
    popup = .16;      -- dropdown / color picker open
    popupOffset = 4;
    window = .22;     -- menu open rise
    windowOffset = 8;
    indicator = .25;  -- sliding tab underline
}

-- window decorations (can be changed at runtime)
library.decorations = {
    enabled = true;     -- master switch
    vines = true;       -- vines growing from the top-left and bottom-right corners
    shadow = true;      -- soft drop shadow under the window
    palette = 'nature'; -- 'nature' = green vines with accent blossoms, 'theme' = everything in accent shades
    sway = true;        -- gentle swaying while the menu is open
    growTime = .8;      -- seconds for the vines to grow in when the menu opens (0 = instant)
    density = 1;        -- leaf amount multiplier (0.5 = sparse, 2 = lush)
    fps = 30;           -- how often the sway animation updates (lower = cheaper)
}

library.themes = {
    {
        name = 'Default',
        theme = {
            ['Accent']                    = fromrgb(255,135,255);
            ['Background']                = fromrgb(18,18,18);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(60,60,60);
            ['Border 2']                  = fromrgb(35,35,35);
            ['Border 3']                  = fromrgb(10,10,10);
            ['Primary Text']              = fromrgb(235,235,235);
            ['Group Background']          = fromrgb(35,35,35);
            ['Selected Tab Background']   = fromrgb(35,35,35);
            ['Unselected Tab Background'] = fromrgb(18,18,18);
            ['Selected Tab Text']         = fromrgb(245,245,245);
            ['Unselected Tab Text']       = fromrgb(145,145,145);
            ['Section Background']        = fromrgb(18,18,18);
            ['Option Text 1']             = fromrgb(245,245,245);
            ['Option Text 2']             = fromrgb(195,195,195);
            ['Option Text 3']             = fromrgb(145,145,145);
            ['Option Border 1']           = fromrgb(50,50,50);
            ['Option Border 2']           = fromrgb(0,0,0);
            ['Option Background']         = fromrgb(35,35,35);
            ["Risky Text"]                = fromrgb(175, 21, 21);
            ["Risky Text Enabled"]        = fromrgb(255, 41, 41);
        }
    },
    {
        name = 'Tokyo Night',
        theme = {
            ['Accent']                    = fromrgb(103,89,179);
            ['Background']                = fromrgb(22,22,31);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(50,50,50);
            ['Border 2']                  = fromrgb(24,25,37);
            ['Border 3']                  = fromrgb(10,10,10);
            ['Primary Text']              = fromrgb(235,235,235);
            ['Group Background']          = fromrgb(24,25,37);
            ['Selected Tab Background']   = fromrgb(24,25,37);
            ['Unselected Tab Background'] = fromrgb(22,22,31);
            ['Selected Tab Text']         = fromrgb(245,245,245);
            ['Unselected Tab Text']       = fromrgb(145,145,145);
            ['Section Background']        = fromrgb(22,22,31);
            ['Option Text 1']             = fromrgb(245,245,245);
            ['Option Text 2']             = fromrgb(195,195,195);
            ['Option Text 3']             = fromrgb(145,145,145);
            ['Option Border 1']           = fromrgb(50,50,50);
            ['Option Border 2']           = fromrgb(0,0,0);
            ['Option Background']         = fromrgb(24,25,37);
            ["Risky Text"]                = fromrgb(175, 21, 21);
            ["Risky Text Enabled"]        = fromrgb(255, 41, 41);
        }
    },
    {
        name = 'Nekocheat',
        theme = {
            ["Accent"]                    = fromrgb(226, 30, 112);
            ["Background"]                = fromrgb(18,18,18);
            ["Border"]                    = fromrgb(0,0,0);
            ["Border 1"]                  = fromrgb(60,60,60);
            ["Border 2"]                  = fromrgb(18,18,18);
            ["Border 3"]                  = fromrgb(10,10,10);
            ["Primary Text"]              = fromrgb(255,255,255);
            ["Group Background"]          = fromrgb(18,18,18);
            ["Selected Tab Background"]   = fromrgb(18,18,18);
            ["Unselected Tab Background"] = fromrgb(18,18,18);
            ["Selected Tab Text"]         = fromrgb(245,245,245);
            ["Unselected Tab Text"]       = fromrgb(145,145,145);
            ["Section Background"]        = fromrgb(18,18,18);
            ["Option Text 1"]             = fromrgb(255,255,255);
            ["Option Text 2"]             = fromrgb(255,255,255);
            ["Option Text 3"]             = fromrgb(255,255,255);
            ["Option Border 1"]           = fromrgb(50,50,50);
            ["Option Border 2"]           = fromrgb(0,0,0);
            ["Option Background"]         = fromrgb(23,23,23);
            ["Risky Text"]                = fromrgb(175, 21, 21);
            ["Risky Text Enabled"]        = fromrgb(255, 41, 41);
        }
    },
    {
        name = 'Nekocheat Blue',
        theme = {
            ["Accent"]                    = fromrgb(0, 247, 255);
            ["Background"]                = fromrgb(18,18,18);
            ["Border"]                    = fromrgb(0,0,0);
            ["Border 1"]                  = fromrgb(60,60,60);
            ["Border 2"]                  = fromrgb(18,18,18);
            ["Border 3"]                  = fromrgb(10,10,10);
            ["Primary Text"]              = fromrgb(255,255,255);
            ["Group Background"]          = fromrgb(18,18,18);
            ["Selected Tab Background"]   = fromrgb(18,18,18);
            ["Unselected Tab Background"] = fromrgb(18,18,18);
            ["Selected Tab Text"]         = fromrgb(245,245,245);
            ["Unselected Tab Text"]       = fromrgb(145,145,145);
            ["Section Background"]        = fromrgb(18,18,18);
            ["Option Text 1"]             = fromrgb(255,255,255);
            ["Option Text 2"]             = fromrgb(255,255,255);
            ["Option Text 3"]             = fromrgb(255,255,255);
            ["Option Border 1"]           = fromrgb(50,50,50);
            ["Option Border 2"]           = fromrgb(0,0,0);
            ["Option Background"]         = fromrgb(23,23,23);
            ["Risky Text"]                = fromrgb(175, 21, 21);
            ["Risky Text Enabled"]        = fromrgb(255, 41, 41);
        }
    },
    {
        name = 'Fatality',
        theme = {
            ['Accent']                    = fromrgb(197,7,83);
            ['Background']                = fromrgb(25,19,53);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(60,53,93);
            ['Border 2']                  = fromrgb(29,23,66);
            ['Border 3']                  = fromrgb(10,10,10);
            ['Primary Text']              = fromrgb(235,235,235);
            ['Group Background']          = fromrgb(29,23,66);
            ['Selected Tab Background']   = fromrgb(29,23,66);
            ['Unselected Tab Background'] = fromrgb(25,19,53);
            ['Selected Tab Text']         = fromrgb(245,245,245);
            ['Unselected Tab Text']       = fromrgb(145,145,145);
            ['Section Background']        = fromrgb(25,19,53);
            ['Option Text 1']             = fromrgb(245,245,245);
            ['Option Text 2']             = fromrgb(195,195,195);
            ['Option Text 3']             = fromrgb(145,145,145);
            ['Option Border 1']           = fromrgb(60,53,93);
            ['Option Border 2']           = fromrgb(0,0,0);
            ['Option Background']         = fromrgb(29,23,66);
            ["Risky Text"]                = fromrgb(175, 21, 21);
            ["Risky Text Enabled"]        = fromrgb(255, 41, 41);
        }
    },
    {
        name = 'Gamesense',
        theme = {
            ['Accent']                    = fromrgb(147,184,26);
            ['Background']                = fromrgb(17,17,17);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(47,47,47);
            ['Border 2']                  = fromrgb(17,17,17);
            ['Border 3']                  = fromrgb(10,10,10);
            ['Primary Text']              = fromrgb(235,235,235);
            ['Group Background']          = fromrgb(17,17,17);
            ['Selected Tab Background']   = fromrgb(17,17,17);
            ['Unselected Tab Background'] = fromrgb(17,17,17);
            ['Selected Tab Text']         = fromrgb(245,245,245);
            ['Unselected Tab Text']       = fromrgb(145,145,145);
            ['Section Background']        = fromrgb(17,17,17);
            ['Option Text 1']             = fromrgb(245,245,245);
            ['Option Text 2']             = fromrgb(195,195,195);
            ['Option Text 3']             = fromrgb(145,145,145);
            ['Option Border 1']           = fromrgb(47,47,47);
            ['Option Border 2']           = fromrgb(0,0,0);
            ['Option Background']         = fromrgb(35,35,35);
            ["Risky Text"]                = fromrgb(175, 21, 21);
            ["Risky Text Enabled"]        = fromrgb(255, 41, 41);
        }
    },
    {
        name = 'Twitch',
        theme = {
            ['Accent']                    = fromrgb(169,112,255);
            ['Background']                = fromrgb(14,14,14);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(45,45,45);
            ['Border 2']                  = fromrgb(31,31,35);
            ['Border 3']                  = fromrgb(10,10,10);
            ['Primary Text']              = fromrgb(235,235,235);
            ['Group Background']          = fromrgb(31,31,35);
            ['Selected Tab Background']   = fromrgb(31,31,35);
            ['Unselected Tab Background'] = fromrgb(17,17,17);
            ['Selected Tab Text']         = fromrgb(225,225,225);
            ['Unselected Tab Text']       = fromrgb(160,170,175);
            ['Section Background']        = fromrgb(17,17,17);
            ['Option Text 1']             = fromrgb(245,245,245);
            ['Option Text 2']             = fromrgb(195,195,195);
            ['Option Text 3']             = fromrgb(145,145,145);
            ['Option Border 1']           = fromrgb(45,45,45);
            ['Option Border 2']           = fromrgb(0,0,0);
            ['Option Background']         = fromrgb(24,24,27);
            ["Risky Text"]                = fromrgb(175, 21, 21);
            ["Risky Text Enabled"]        = fromrgb(255, 41, 41);
        }
    }
}

local blacklistedKeys = {
    Enum.KeyCode.Unknown,
    Enum.KeyCode.W,
    Enum.KeyCode.A,
    Enum.KeyCode.S,
    Enum.KeyCode.D,
    Enum.KeyCode.Slash,
    Enum.KeyCode.Tab,
    Enum.KeyCode.Escape
}

local whitelistedBoxKeys = {
    Enum.KeyCode.Zero,
    Enum.KeyCode.One,
    Enum.KeyCode.Two,
    Enum.KeyCode.Three,
    Enum.KeyCode.Four,
    Enum.KeyCode.Five,
    Enum.KeyCode.Six,
    Enum.KeyCode.Seven,
    Enum.KeyCode.Eight,
    Enum.KeyCode.Nine
}

local keyNames = {
    [Enum.KeyCode.LeftControl] = 'LCTRL';
    [Enum.KeyCode.RightControl] = 'RCTRL';
    [Enum.KeyCode.LeftShift] = 'LSHIFT';
    [Enum.KeyCode.RightShift] = 'RSHIFT';
    [Enum.UserInputType.MouseButton1] = 'MB1';
    [Enum.UserInputType.MouseButton2] = 'MB2';
    [Enum.UserInputType.MouseButton3] = 'MB3';
}

-- display name for a bind ('none' / nil / false -> 'none')
local function getKeyName(key)
    if typeof(key) == 'EnumItem' then
        return keyNames[key] or key.Name
    end
    return 'none'
end

-- turns an InputObject into a bind value; returns false for blacklisted keys (= cancel)
local function getInputKey(inp, nomouse)
    local mouseButtons = {Enum.UserInputType.MouseButton1, Enum.UserInputType.MouseButton2, Enum.UserInputType.MouseButton3}
    if table.find(mouseButtons, inp.UserInputType) then
        return (not nomouse) and inp.UserInputType or false
    end
    if inp.UserInputType == Enum.UserInputType.Keyboard then
        if inp.KeyCode == Enum.KeyCode.Backspace then
            return 'none'
        end
        if not table.find(blacklistedKeys, inp.KeyCode) then
            return inp.KeyCode
        end
    end
    return false
end

library.button1down = library.signal.new()
library.button1up   = library.signal.new()
library.mousemove   = library.signal.new()
library.unloaded    = library.signal.new();

local button1down, button1up, mousemove = library.button1down, library.button1up, library.mousemove
local mb1down = false;

local utility = library.utility
do

    function utility:Connection(signal, func)
        local c = signal:Connect(func)
        table.insert(library.connections, c)
        return c
    end

    function utility:Instance(class, properties)
        local inst = newInstance(class)
        for prop, val in next, properties or {} do
            local s,e = pcall(function()
                inst[prop] = val
            end)
            if not s then
                log(e)
            end
        end
        return inst
    end

    function utility:HasProperty(obj, prop)
        return ({(pcall(function() local a = obj[prop] end))})[1]
    end

    function utility:ToRGB(c3)
        return c3.R*255,c3.G*255,c3.B*255
    end

    function utility:AddRGB(a,b)
        local r1,g1,b1 = self:ToRGB(a);
        local r2,g2,b2 = self:ToRGB(b);
        return fromrgb(clamp(r1+r2,0,255),clamp(g1+g2,0,255),clamp(b1+b2,0,255))
    end

    function utility:ConvertNumberRange(val,oldmin,oldmax,newmin,newmax)
        return (((val - oldmin) * (newmax - newmin)) / (oldmax - oldmin)) + newmin
    end

    function utility:UDim2ToVector2(udim2, vector2)
        local x,y
        x = udim2.X.Offset + self:ConvertNumberRange(udim2.X.Scale,0,1,0,vector2.X)
        y = udim2.Y.Offset + self:ConvertNumberRange(udim2.Y.Scale,0,1,0,vector2.Y)
        return newVector2(x,y)
    end

    function utility:Lerp(a,b,c)
        return a + (b-a) * c
    end

    function utility:Tween(obj, prop, val, time, direction, style)
        if self:HasProperty(obj, prop) then
            if library.tweens[obj] then
                if library.tweens[obj][prop] then
                    library.tweens[obj][prop]:Cancel()
                end
            end

            local startVal = obj[prop];
            local a = 0;
            local tween = {
                Completed = library.signal.new();
            };

            library.tweens[obj] = library.tweens[obj] or {};
            library.tweens[obj][prop] = tween;

            local finished = false
            local isNumber = typeof(startVal) == 'number'
            style = style or Enum.EasingStyle.Linear
            direction = direction or Enum.EasingDirection.In

            function tween:Cancel()
                if finished then return end
                finished = true
                library.activeTweens[tween] = nil
                local completed = tween.Completed
                if library.tweens[obj] and library.tweens[obj][prop] == tween then
                    library.tweens[obj][prop] = nil;
                end
                completed:Fire();
            end

            -- called by the shared tween loop (see utility:StepTweens)
            function tween:Step(dt)
                if finished then return end
                a = (time and time > 0) and (a + (dt / time)) or 1;
                local alpha = a < 1 and a or 1
                local progress = tweenService:GetValue(alpha, style, direction)
                local ok = pcall(function()
                    if isNumber then
                        obj[prop] = startVal + (val - startVal) * progress;
                    else
                        obj[prop] = startVal:Lerp(val, progress);
                    end
                end)
                if a >= 1 or not ok then
                    tween:Cancel();
                end
            end

            library.activeTweens[tween] = true
            return tween;
        else
            log('unable to tween: invalid property '..tostring(prop)..' for object '..tostring(obj))
        end
    end

    -- one RenderStepped connection drives every running tween (connected in library:init)
    function utility:StepTweens(dt)
        if next(library.activeTweens) == nil then return end
        local list = {}
        for tween in next, library.activeTweens do
            list[#list + 1] = tween
        end
        for i = 1, #list do
            list[i]:Step(dt)
        end
    end

    function utility:DetectTableChange(indexcallback,newindexcallback)
        if indexcallback == nil then
            warn('DetectTableChange: Argument #1 (indexcallback) is nil, function may not work as expected.')
        elseif newindexcallback == nil then
            warn('DetectTableChange: Argument #2 (newindexcallback) is nil, function may not work as expected.')
        end
        local proxy = newproxy(true);
        local mt = getmetatable(proxy);
        mt.__index = indexcallback
        mt.__newindex = newindexcallback
        return proxy
    end

    -- animTime > 0 eases the color (used for hover / toggle / tab changes); theme changes stay instant
    function utility:ApplyThemeColor(v, animTime)
        if v == nil or v.Object == nil then return end
        local offset = tonumber(v.ThemeColorOffset) or 0
        local outlineOffset = tonumber(v.OutlineThemeColorOffset) or 0
        if v.ThemeColor and v.ThemeColor ~= '' and library.theme[v.ThemeColor] then
            local target = utility:AddRGB(library.theme[v.ThemeColor], fromrgb(offset, offset, offset))
            local running = library.tweens[v.Object] and library.tweens[v.Object].Color
            local animate = library.animations.enabled and typeof(animTime) == 'number' and animTime > 0 and v.AbsVisible

            if animate then
                utility:Tween(v.Object, 'Color', target, animTime, Enum.EasingDirection.Out, Enum.EasingStyle.Quad)
            else
                if running then
                    running:Cancel()
                end
                pcall(function()
                    v.Object.Color = target
                end)
            end
        end
        if v.OutlineThemeColor and v.OutlineThemeColor ~= '' and library.theme[v.OutlineThemeColor] then
            pcall(function()
                v.Object.OutlineColor = utility:AddRGB(library.theme[v.OutlineThemeColor], fromrgb(outlineOffset, outlineOffset, outlineOffset))
            end)
        end
    end

    -- // Animation helpers

    -- the "real" transparency of an object, even if a fade is currently running on it
    local restingTransparency = setmetatable({}, {__mode = 'k'})
    function utility:GetRestingTransparency(obj)
        local running = library.tweens[obj] and library.tweens[obj].Transparency
        if running and restingTransparency[obj] ~= nil then
            return restingTransparency[obj]
        end
        return obj.Transparency
    end

    -- call right after starting a Transparency tween on obj, so other animations know its real value
    function utility:SetRestingTransparency(obj, value)
        restingTransparency[obj] = value
    end

    -- fades a drawing and all its descendants in from invisible to their normal transparency
    function utility:FadeIn(root, duration)
        if not library.animations.enabled or not duration or duration <= 0 then return end
        local rootData = root and root.Object and library.drawings[root.Object]
        if not rootData then return end

        local list = rootData:GetDescendants()
        table.insert(list, rootData)

        for _, d in next, list do
            local obj = d.Object
            if obj ~= nil then
                local target = utility:GetRestingTransparency(obj)
                if target ~= 0 then -- 0 = invisible hit areas, leave them alone
                    obj.Transparency = 0
                    utility:Tween(obj, 'Transparency', target, duration, Enum.EasingDirection.Out, Enum.EasingStyle.Quad)
                    restingTransparency[obj] = target -- set after Tween() so the cancelled tween can't clear it
                end
            end
        end
    end

    -- eases a drawing's Position from (target + offset) to target
    function utility:SlideIn(drawing, target, offset, duration)
        if not library.animations.enabled or not duration or duration <= 0 then
            drawing.Position = target
            return
        end
        drawing.Position = target + offset
        return utility:Tween(drawing, 'Position', target, duration, Enum.EasingDirection.Out, Enum.EasingStyle.Quint)
    end

    -- makes drawings draggable while the menu is open.
    -- getPos/setPos work in screen pixels (Vector2); onDrop runs when the mouse is released.
    function utility:MakeDraggable(handles, getPos, setPos, onDrop)
        local state = {dragging = false}

        local function begin(mouse)
            state.dragging = true
            state.mouseStart = mouse
            state.objStart = getPos()
        end

        function state:AddHandle(handle)
            utility:Connection(handle.MouseButton1Down, begin)
        end

        for _, handle in ipairs(handles) do
            state:AddHandle(handle)
        end

        utility:Connection(library.mousemove, function(mouse)
            if state.dragging then
                local screen = workspace.CurrentCamera.ViewportSize
                local p = state.objStart + (mouse - state.mouseStart)
                -- keep it on screen
                setPos(newVector2(clamp(p.X, 0, math.max(screen.X - 20, 0)), clamp(p.Y, 0, math.max(screen.Y - 10, 0))))
            end
        end)

        utility:Connection(library.button1up, function()
            if state.dragging then
                state.dragging = false
                if onDrop then
                    onDrop()
                end
            end
        end)

        return state
    end

    function utility:MouseOver(obj)
        local mousePos = inputservice:GetMouseLocation();
        local x1 = obj.Position.X
        local y1 = obj.Position.Y
        local x2 = x1 + obj.Size.X
        local y2 = y1 + obj.Size.Y
        return (mousePos.X >= x1 and mousePos.Y >= y1 and mousePos.X <= x2 and mousePos.Y <= y2)
    end

    -- topmost visible Square under the mouse. uses the screen rects cached in drawing:Update,
    -- so it never has to read properties back from the Drawing objects
    function utility:GetHoverObject()
        local mouse = inputservice:GetMouseLocation()
        local mx, my = mouse.X, mouse.Y
        local best, bestZ = nil, -math.huge
        for v in next, library.hitboxes do
            if v.AbsVisible and not v.NoHit then
                local p, s = v.AbsolutePosition, v.AbsoluteSize
                if mx >= p.X and my >= p.Y and mx <= p.X + s.X and my <= p.Y + s.Y then
                    local zi = v.ZIndexCache or 0
                    if zi > bestZ then
                        best, bestZ = v.Object, zi
                    end
                end
            end
        end
        return best
    end

    -- maps the mouse X over a slider's bar to a value (uses the cached rect, no Drawing reads)
    function utility:SliderDragTo(slider, mousePos)
        local bar = slider.objects and slider.objects.background
        local data = bar and bar.Object and library.drawings[bar.Object]
        if not data then return end
        local width = math.max(data.AbsoluteSize.X, 1)
        local rel = clamp((mousePos.X - data.AbsolutePosition.X) / width, 0, 1)
        local value = slider.min + (slider.max - slider.min) * rel
        -- only update (and fire the callback) when the snapped value actually changes
        if snapToIncrement(value, slider.increment, slider.min, slider.max) ~= slider.value then
            slider:SetValue(value)
        end
    end

    -- is drawing data `data` the drawing `root` (a proxy) or somewhere inside it?
    function utility:IsInside(data, root)
        if data == nil or root == nil or root.Object == nil then return false end
        local target = root.Object
        local cur = data
        while cur do
            if cur.Object == target then
                return true
            end
            cur = cur.Parent and library.drawings[cur.Parent.Object] or nil
        end
        return false
    end

    local blacklistedLookup = {Object = true, Children = true, Class = true}
    -- keys that only exist on the wrapper table (writing them to a Drawing just throws an error)
    local customKeys = {
        ThemeColor = true, OutlineThemeColor = true, ThemeColorOffset = true, OutlineThemeColorOffset = true,
        Parent = true, Hover = true, ColorTween = true, Ready = true, NoHit = true,
        Visible = true, -- resolved against the parent's visibility in Update()
        AbsoluteSize = true, AbsolutePosition = true, AbsVisible = true,
    }
    local themeKeys = {ThemeColor = true, OutlineThemeColor = true, ThemeColorOffset = true, OutlineThemeColorOffset = true}
    local function setRaw(obj, key, value)
        obj[key] = value
    end
    local function getRaw(obj, key)
        return obj[key]
    end

    function utility:Draw(class, properties)
        local drawing = {
            Object = Drawing.new(class);
            Children = {};
            ThemeColor = '';
            OutlineThemeColor = '';
            ThemeColorOffset = 0;
            OutlineThemeColorOffset = 0;
            Parent = nil;
            Size = newUDim2(0,0,0,0);
            Position = newUDim2(0,0,0,0);
            AbsoluteSize = newVector2(0,0);
            AbsolutePosition = newVector2(0,0);
            Hover = false;
            Visible = true;
            ColorTween = library.animations and library.animations.color or .12; -- seconds to ease ThemeColor changes (0 = instant)
            Ready = false; -- becomes true after creation, so initial colors never animate
            NoHit = false; -- true = purely decorative, ignored by hover/click detection
            MouseButton1Down = library.signal.new();
            MouseButton2Down = library.signal.new();
            MouseButton1Up = library.signal.new();
            MouseButton2Up = library.signal.new();
            MouseEnter = library.signal.new();
            MouseLeave = library.signal.new();
            Class = class;
        }

        local hasSize = class == 'Square' or class == 'Image'
        local hasPosition = hasSize or class == 'Circle' or class == 'Text'

        -- recomputes the screen rect from the parent's cached rect and only writes to the
        -- Drawing object when something actually changed (writes are the expensive part)
        function drawing:Update()
            local obj = drawing.Object
            if obj == nil then return end

            local parent = drawing.Parent ~= nil and library.drawings[drawing.Parent.Object] or nil
            local parentSize, parentPos, parentVis
            if parent ~= nil then
                parentPos = parent.AbsolutePosition
                parentVis = parent.AbsVisible
                if parent.Class == 'Square' or parent.Class == 'Image' then
                    parentSize = parent.AbsoluteSize
                elseif parent.Class == 'Text' then
                    parentSize = parent.Object.TextBounds
                else
                    parentSize = workspace.CurrentCamera.ViewportSize
                end
            else
                parentSize, parentPos, parentVis = workspace.CurrentCamera.ViewportSize, newVector2(0, 0), true
            end

            if hasSize then
                local size = drawing.Size
                local abs = typeof(size) == 'Vector2' and size or utility:UDim2ToVector2(size, parentSize)
                if abs ~= drawing.AbsoluteSize or not drawing.SizeWritten then
                    drawing.AbsoluteSize = abs
                    drawing.SizeWritten = true
                    obj.Size = abs
                end
            end

            if hasPosition then
                local pos = drawing.Position
                local abs = parentPos + (typeof(pos) == 'Vector2' and pos or utility:UDim2ToVector2(pos, parentSize))
                if abs ~= drawing.AbsolutePosition or not drawing.PositionWritten then
                    drawing.AbsolutePosition = abs
                    drawing.PositionWritten = true
                    obj.Position = abs
                end
            end

            local visible = (parentVis and drawing.Visible) and true or false
            if visible ~= drawing.AbsVisible then
                drawing.AbsVisible = visible
                obj.Visible = visible
            end

            drawing:UpdateChildren()
        end

        function drawing:UpdateChildren()
            for i,v in next, drawing.Children do
                v:Update()
            end
        end

        function drawing:GetDescendants()
            local descendants = {};
            local function a(t)
                for _,v in next, t.Children do
                    table.insert(descendants, v);
                    a(v)
                end
            end
            a(self)
            return descendants;
        end

        library.drawings[drawing.Object] = drawing
        if class == 'Square' then
            library.hitboxes[drawing] = true
        end

        -- this is really stupid lol
        local proxy = utility:DetectTableChange(
        function(obj,i)
            if drawing[i] ~= nil then
                return drawing[i]
            end
            if drawing.Object == nil then
                return nil -- drawing was removed
            end
            local ok, res = pcall(getRaw, drawing.Object, i)
            if ok then
                return res
            end
            return nil
        end,
        function(obj,i,v)
            if drawing.Object == nil then
                return -- drawing was removed
            end
            if not blacklistedLookup[i] then

                local lastval = drawing[i]

                -- layout props are resolved by Update(), never written raw
                if (i == 'Size' and hasSize) or (i == 'Position' and hasPosition) then
                    if lastval ~= v then
                        drawing[i] = v
                        drawing:Update()
                    end
                    return
                end

                if i == 'ZIndex' then
                    drawing.ZIndexCache = v
                end

                if i == 'Parent' then
                    -- Children is an array, so remove by index (the old code did Children[drawing] = nil which never removed anything)
                    if drawing.Parent ~= nil then
                        local siblings = drawing.Parent.Children
                        local idx = siblings and table.find(siblings, drawing)
                        if idx then
                            table.remove(siblings, idx)
                        end
                    end
                    if v ~= nil and not table.find(v.Children, drawing) then
                        table.insert(v.Children,drawing)
                    end
                elseif i == 'Transparency' then
                    -- an explicit set wins over any fade that's running on this object
                    local running = library.tweens[drawing.Object] and library.tweens[drawing.Object].Transparency
                    if running then
                        running:Cancel()
                    end
                elseif i == 'Visible' then
                    drawing.Visible = v
                elseif i == 'Font' and v == 2 and executor == 'ScriptWare' then
                    v = 1
                end

                -- custom keys only live on the wrapper; everything else goes to the Drawing object
                if not customKeys[i] then
                    pcall(setRaw, drawing.Object, i, v)
                end
                if drawing[i] ~= nil or i == 'Parent' then
                    drawing[i] = v
                end

                if i == 'Visible' or i == 'Parent' then
                    drawing:Update()
                end
                if themeKeys[i] and lastval ~= v then
                    -- only recolor this drawing instead of every drawing in the library (eased once it exists)
                    utility:ApplyThemeColor(drawing, drawing.Ready and drawing.ColorTween or 0)
                end

            end
        end)

        function drawing:Remove()
            if drawing.Object == nil then
                return
            end

            -- iterate a copy, children remove themselves from this list
            for _,v in next, table.clone(drawing.Children) do
                v:Remove();
            end

            if drawing.Parent then
                local siblings = drawing.Parent.Children
                local idx = siblings and table.find(siblings, drawing)
                if idx then
                    table.remove(siblings, idx)
                end
            end

            library.drawings[drawing.Object] = nil;
            library.hitboxes[drawing] = nil;
            if library.hoverData == drawing then
                library.hoverData = nil;
            end
            pcall(function()
                drawing.Object:Remove();
            end)
            table.clear(drawing);

        end

        properties = typeof(properties) == 'table' and properties or {}

        if class == 'Square' and properties.Filled == nil then
            properties.Filled = true;
        end

        if properties.Visible == nil then
            properties.Visible = true;
        end

        for i,v in next, properties do
            proxy[i] = v
        end

        drawing:Update()
        drawing.Ready = true
        return proxy
    end
end

library.utility = utility

-- true while a ui text box is capturing keys (or was closed this same input)
function library:IsTyping()
    return self.focusedBox ~= nil or (self.boxReleasedAt ~= nil and os.clock() - self.boxReleasedAt < 0.05)
end

function library:Unload()
    -- switch every toggle off first (with callbacks), so features stop when the menu goes away.
    -- otherwise re-running the script leaves the old features running while the new menu shows them off
    for _, toggle in ipairs(self.allToggles or {}) do
        if toggle.state == true then
            pcall(toggle.SetState, toggle, false);
        end
    end
    library.unloaded:Fire();
    for _,c in next, self.connections do
        pcall(function()
            c:Disconnect()
        end)
    end
    table.clear(self.connections)
    for obj in next, self.drawings do
        pcall(function()
            obj:Remove()
        end)
    end
    table.clear(self.drawings)
    pcall(function()
        actionservice:UnbindAction('FreezeMovement');
    end)
    self.open = false
    self.hasInit = false
    if getgenv().library == library then
        getgenv().library = nil
    end
end

function library:init()
    if self.hasInit then
        return
    end

    local tooltipObjects = {};

    safeMakeFolder(self.cheatname)
    safeMakeFolder(self.cheatname..'/assets')
    safeMakeFolder(self.cheatname..'/'..self.gamename)
    safeMakeFolder(self.cheatname..'/'..self.gamename..'/configs');

    -- start with the Default theme so colors work even without CreateSettingsTab
    if next(self.theme) == nil then
        for i,v in next, self.themes[1].theme do
            self.theme[i] = v;
        end
    end

    function self:SetTheme(theme)
        for i,v in next, theme do
            self.theme[i] = v;
        end
        self.UpdateThemeColors();
    end

    function self:GetConfig(name)
        if typeof(name) ~= 'string' or name == '' or not isfile then
            return nil
        end
        if isfile(self.cheatname..'/'..self.gamename..'/configs/'..name..self.fileext) then
            return readfile(self.cheatname..'/'..self.gamename..'/configs/'..name..self.fileext);
        end
    end

    function self:LoadConfig(name)
        local cfg = self:GetConfig(name)
        if not cfg then
            self:SendNotification('Error loading config: Config does not exist. ('..tostring(name)..')', 5, c3new(1,0,0));
            return
        end

        local s,e = pcall(function()
            setByConfig = true
            for flag,value in next, http:JSONDecode(cfg) do
                local option = library.options[flag]
                if option ~= nil then
                    if option.class == 'toggle' then
                        option:SetState(value == nil and false or (value == 1 and true or false));
                    elseif option.class == 'slider' then
                        option:SetValue(value == nil and 0 or value)
                    elseif option.class == 'bind' then
                        local key = 'none'
                        if typeof(value) == 'string' and value:lower() ~= 'none' then
                            local okKey, keyCode = pcall(function() return Enum.KeyCode[value] end)
                            local okInput, inputType = pcall(function() return Enum.UserInputType[value] end)
                            key = (okKey and keyCode) or (okInput and inputType) or 'none'
                        end
                        option:SetBind(key);
                    elseif option.class == 'color' then
                        option:SetColor(value == nil and c3new(1,1,1) or c3new(value[1], value[2], value[3]));
                        option:SetTrans(value == nil and 1 or value[4]);
                    elseif option.class == 'list' then
                        option:Select(value == nil and '' or value);
                    elseif option.class == 'box' then
                        option:SetInput(value == nil and '' or value)
                    end
                end
            end
        end)
        setByConfig = false

        if s then
            self:SendNotification('Successfully loaded config: '..name, 5, c3new(0,1,0));
        else
            self:SendNotification('Error loading config: '..tostring(e)..'. ('..tostring(name)..')', 5, c3new(1,0,0));
        end
    end

    function self:SaveConfig(name)
        if not self:GetConfig(name) then
            self:SendNotification('Error saving config: Config does not exist. ('..tostring(name)..')', 5, c3new(1,0,0));
            return
        end

        local s,e = pcall(function()
            local cfg = {};
            for flag,option in next, self.options do
                if option.class == 'toggle' then
                    cfg[flag] = option.state and 1 or 0;
                elseif option.class == 'slider' then
                    cfg[flag] = option.value;
                elseif option.class == 'bind' then
                    cfg[flag] = typeof(option.bind) == 'EnumItem' and option.bind.Name or 'none';
                elseif option.class == 'color' then
                    cfg[flag] = {
                        option.color.r,
                        option.color.g,
                        option.color.b,
                        option.trans,
                    }
                elseif option.class == 'list' then
                    cfg[flag] = option.selected;
                elseif option.class == 'box' then
                    cfg[flag] = option.input
                end
            end
            writefile(self.cheatname..'/'..self.gamename..'/configs/'..name..self.fileext, http:JSONEncode(cfg));
        end)

        if s then
            self:SendNotification('Successfully saved config: '..name, 5, c3new(0,1,0));
        else
            self:SendNotification('Error saving config: '..tostring(e)..'. ('..tostring(name)..')', 5, c3new(1,0,0));
        end
    end

    -- download + cache images; a failed download no longer kills the whole lib
    local function isPng(data)
        return typeof(data) == 'string' and data:sub(1, 4) == '\137PNG'
    end
    for i,v in next, self.images do
        if typeof(v) == 'string' and not isPng(v) then
            local path = self.cheatname..'/assets/'..i..'.oh'
            local data

            if isfile and readfile and isfile(path) then
                local ok, cached = pcall(readfile, path)
                if ok and isPng(cached) then
                    data = cached
                end
            end

            if data == nil then
                local ok, downloaded = pcall(function()
                    return game:HttpGet(v)
                end)
                if ok and isPng(downloaded) then
                    data = downloaded
                    if writefile then
                        pcall(writefile, path, downloaded)
                    end
                else
                    log('failed to download image "'..i..'"')
                end
            end

            self.images[i] = data
        end
    end

    -- // Cursor
    -- accent-filled arrow with a dark outline, drawn every frame so it never lags behind the real mouse
    self.cursorFill = utility:Draw('Triangle', {Filled = true, ThemeColor = 'Accent', Visible = false, ZIndex = self.zindexOrder.cursor});
    self.cursorOutline = utility:Draw('Triangle', {Filled = false, Thickness = 1.5, Color = fromrgb(10,10,10), Visible = false, ZIndex = self.zindexOrder.cursor+1});
    -- kept for scripts that referenced the old names
    self.cursor1, self.cursor2 = self.cursorFill, self.cursorOutline

    local function updateCursor()
        local show = self.open
        self.cursorFill.Visible = show
        self.cursorOutline.Visible = show
        if show then
            local pos = inputservice:GetMouseLocation();
            local a, b, c = pos, pos + newVector2(14, 5), pos + newVector2(5, 14)
            self.cursorFill.PointA, self.cursorFill.PointB, self.cursorFill.PointC = a, b, c
            self.cursorOutline.PointA, self.cursorOutline.PointB, self.cursorOutline.PointC = a, b, c
        end
    end

    -- // Real mouse icon
    -- hidden while the menu is open (games love to turn it back on, so it's enforced every frame)
    local savedMouseIcon = inputservice.MouseIconEnabled
    local function setRealMouseHidden(hidden)
        pcall(function()
            if hidden then
                inputservice.MouseIconEnabled = false
            else
                inputservice.MouseIconEnabled = savedMouseIcon
            end
        end)
    end

    -- // Input passthrough
    -- modalButton: tiny button with Modal = true, frees the mouse in first person / shift lock while the menu is open
    -- inputBlocker: only covers the screen while the mouse is over the menu, so clicks elsewhere reach the game
    local screenGui = Instance.new('ScreenGui');
    screenGui.Name = http:GenerateGUID(false);
    screenGui.ResetOnSpawn = false;
    screenGui.IgnoreGuiInset = true;
    screenGui.DisplayOrder = 999999;
    pcall(function()
        if syn and syn.protect_gui then syn.protect_gui(screenGui) end
    end)
    local guiParentOk = pcall(function()
        screenGui.Parent = (gethui and gethui()) or game:GetService('CoreGui');
    end)
    if not guiParentOk then
        screenGui.Parent = localplayer:WaitForChild('PlayerGui');
    end
    screenGui.Enabled = false;

    local modalButton = utility:Instance('TextButton', {
        Parent = screenGui,
        Visible = true,
        Modal = true,
        Text = '',
        Size = UDim2.new(0,0,0,0),
        BackgroundTransparency = 1;
        AutoButtonColor = false;
    })

    local inputBlocker = utility:Instance('ImageButton', {
        Parent = screenGui,
        Visible = false,
        Size = UDim2.new(1,0,1,0),
        ZIndex = 99999,
        BackgroundTransparency = 1;
        ImageTransparency = 1;
        AutoButtonColor = false;
    })

    -- hidden real TextBox used by every text box option (see box:CaptureFocus).
    -- it sits above the input blocker so clicking inside the box you're typing in moves the caret natively.
    library.inputBox = utility:Instance('TextBox', {
        Parent = screenGui,
        Name = 'input',
        Visible = true,
        Position = UDim2.fromOffset(-10000, -10000),
        Size = UDim2.fromOffset(200, 16),
        BackgroundTransparency = 1,
        TextTransparency = 1,
        TextStrokeTransparency = 1,
        Text = '',
        PlaceholderText = '',
        ClearTextOnFocus = false,
        MultiLine = false,
        TextEditable = true,
        TextXAlignment = Enum.TextXAlignment.Left,
        ZIndex = 100000,
    })

    -- holding right click outside the menu temporarily locks the mouse again so you can look around
    local lookingAround = false
    local function setMouseOverUI(over)
        library.mouseOverUI = over
        inputBlocker.Visible = over and self.open and not lookingAround
    end

    utility:Connection(library.unloaded, function()
        setRealMouseHidden(false)
        screenGui:Destroy()
    end)

    local lastCursorPos = nil
    utility:Connection(runservice.RenderStepped, function()
        if self.open then
            local pos = inputservice:GetMouseLocation()
            if pos ~= lastCursorPos then
                lastCursorPos = pos
                updateCursor()
            end
            if inputservice.MouseIconEnabled then
                setRealMouseHidden(true)
            end
        else
            lastCursorPos = nil
        end
    end)

    utility:Connection(inputservice.InputBegan, function(input)
        if self.open and input.UserInputType == Enum.UserInputType.MouseButton2 and not library.mouseOverUI then
            lookingAround = true
            modalButton.Modal = false
            inputBlocker.Visible = false
        end
    end)

    utility:Connection(inputservice.InputEnded, function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton2 and lookingAround then
            lookingAround = false
            modalButton.Modal = true
            setMouseOverUI(utility:GetHoverObject() ~= nil)
        end
    end)

    utility:Connection(inputservice.InputBegan, function(input, gpe)
        if self.hasInit then
            if input.KeyCode == self.toggleKey and not library.opening and not gpe then
                self:SetOpen(not self.open)
                task.spawn(function()
                    library.opening = true;
                    task.wait(.15);
                    library.opening = false;
                end)
            end
            if library.open then
                local hoverObj = utility:GetHoverObject();
                local hoverObjData = library.drawings[hoverObj];
                if input.UserInputType == Enum.UserInputType.MouseButton1 then
                    mb1down = true;
                    library.pressStartedOverUI = hoverObj ~= nil;
                    button1down:Fire()
                    if hoverObj and hoverObjData then
                        hoverObjData.MouseButton1Down:Fire(inputservice:GetMouseLocation())
                    end

                    -- // Update Sliders Click
                    if library.draggingSlider ~= nil then
                        utility:SliderDragTo(library.draggingSlider, inputservice:GetMouseLocation())
                    end

                elseif input.UserInputType == Enum.UserInputType.MouseButton2 then
                    if hoverObj and hoverObjData then
                        hoverObjData.MouseButton2Down:Fire(inputservice:GetMouseLocation())
                    end
                end
            end
        end
    end)

    utility:Connection(inputservice.InputEnded, function(input, gpe)
        -- always release mouse state, otherwise sliders/drags get stuck if the menu closes mid-drag
        if input.UserInputType == Enum.UserInputType.MouseButton1 and (not library.open or not self.hasInit) then
            if mb1down then
                mb1down = false;
                button1up:Fire();
            end
            return
        end

        if self.hasInit and library.open then
            local hoverObj = utility:GetHoverObject();
            local hoverObjData = library.drawings[hoverObj];

            if input.UserInputType == Enum.UserInputType.MouseButton1 then
                mb1down = false;
                button1up:Fire();
                if hoverObj and hoverObjData then
                    hoverObjData.MouseButton1Up:Fire(inputservice:GetMouseLocation())
                end
            elseif input.UserInputType == Enum.UserInputType.MouseButton2 then
                if hoverObj and hoverObjData then
                    hoverObjData.MouseButton2Up:Fire(inputservice:GetMouseLocation())
                end
            end
        end
    end)

    -- // Mouse movement
    -- processed once per frame (instead of once per input event) and only when the mouse actually moved.
    -- hover only fires enter/leave on the previous and new hovered object instead of looping every drawing.
    local function setHover(data, mousePos)
        local previous = library.hoverData
        if previous == data then return end
        library.hoverData = data
        if previous and previous.Object then
            previous.Hover = false
            previous.MouseLeave:Fire(mousePos)
        end
        if data then
            data.Hover = true
            data.MouseEnter:Fire(mousePos)
        end
    end

    local lastMouse = nil
    local function processMouse()
        if not library.open then
            if library.hoverData then
                setHover(nil, inputservice:GetMouseLocation())
            end
            lastMouse = nil
            return
        end

        local mousePos = inputservice:GetMouseLocation()
        if mousePos == lastMouse and not library.hoverDirty then
            return
        end
        local moved = mousePos ~= lastMouse
        lastMouse = mousePos
        library.hoverDirty = false

        if moved then
            mousemove:Fire(mousePos);

            if library.CurrentTooltip ~= nil then
                tooltipObjects.background.Position = UDim2.new(0,mousePos.X + 15,0,mousePos.Y + 15)
                tooltipObjects.background.Size = UDim2.new(0,tooltipObjects.text.TextBounds.X + 6 + (library.CurrentTooltip.risky and 60 or 0),0,tooltipObjects.text.TextBounds.Y + 2)
            end
        end

        local hoverObj = utility:GetHoverObject();
        -- keep blocking while dragging something that started on the menu (sliders, window drag)
        setMouseOverUI(hoverObj ~= nil or (mb1down and library.pressStartedOverUI == true))
        setHover(hoverObj and library.drawings[hoverObj] or nil, mousePos)

        -- // Update Sliders Drag
        if moved and mb1down and library.draggingSlider ~= nil then
            utility:SliderDragTo(library.draggingSlider, mousePos)
        end
    end

    utility:Connection(runservice.RenderStepped, function(dt)
        utility:StepTweens(dt)
        processMouse()
    end)
    
    function self:SetOpen(bool)
        local wasOpen = self.open
        self.open = bool;
        screenGui.Enabled = bool;

        if bool then
            if not wasOpen then
                -- remember the game's own setting so closing the menu restores it
                savedMouseIcon = inputservice.MouseIconEnabled
            end
            setRealMouseHidden(true)
            setMouseOverUI(utility:GetHoverObject() ~= nil)
        else
            lookingAround = false
            modalButton.Modal = true
            setMouseOverUI(false)
            setRealMouseHidden(false)
            -- closing the menu finishes whatever you were typing
            if library.activeBox then
                library.activeBox:ReleaseFocus(true)
            end
        end

        if bool and library.flags.disablemenumovement then
            actionservice:BindAction(
                'FreezeMovement',
                function()
                    return Enum.ContextActionResult.Sink
                end,
                false,
                unpack(Enum.PlayerActions:GetEnumItems())
            )
        else
            actionservice:UnbindAction('FreezeMovement');
        end

        updateCursor();
        for _,window in next, self.windows do
            window:SetOpen(bool);
        end

        library.CurrentTooltip = nil;
        tooltipObjects.background.Visible = false
    end

    function self.UpdateThemeColors()
        for _,v in next, library.drawings do
            utility:ApplyThemeColor(v)
        end
    end

    function self:SendNotification(message, time, color)
        time = time or 5
        if typeof(message) ~= 'string' then
            return error(string.format('invalid message type, got %s, expected string', typeof(message)))
        elseif typeof(time) ~= 'number' then
            return error(string.format('invalid time type, got %s, expected number', typeof(time)))
        elseif color ~= nil and typeof(color) ~= 'Color3' then
            return error(string.format('invalid color type, got %s, expected color3', typeof(color)))
        end

        -- // Notification card
        -- slides + fades in from the left, shows a countdown bar, then slides + fades out.
        -- Cards stack top-down (newest at the bottom) and the stack eases into place when one leaves.
        local notifSettings = self.notificationSettings
        local z = self.zindexOrder.notification
        local height = notifSettings.height
        local accentColor = color

        local notification = {
            objects = {};
            targets = {};   -- final transparency of each drawing, used for the fade in/out
            width = 0;
            removing = false;
        };
        local objs = notification.objects

        -- new cards spawn directly in the next free slot
        local slot = 0
        for _, v in ipairs(self.notifications) do
            if not v.removing then
                slot += 1
            end
        end

        objs.holder = utility:Draw('Square', {
            Size = newUDim2(0, 0, 0, height);
            Position = newUDim2(0, notifSettings.x, 0, notifSettings.y + slot * (height + notifSettings.spacing));
            Transparency = 0;
            ZIndex = z;
        })

        objs.background = utility:Draw('Square', {
            Size = newUDim2(0, 200, 0, height);
            ThemeColor = 'Background';
            ZIndex = z;
            Parent = objs.holder;
        })

        objs.border1 = utility:Draw('Square', {
            Size = newUDim2(1,2,1,2);
            Position = newUDim2(0,-1,0,-1);
            ThemeColor = 'Border 1';
            ZIndex = z-1;
            Parent = objs.background;
        })

        objs.border2 = utility:Draw('Square', {
            Size = newUDim2(1,2,1,2);
            Position = newUDim2(0,-1,0,-1);
            ThemeColor = 'Border 3';
            ZIndex = z-2;
            Parent = objs.border1;
        })

        objs.gradient = utility:Draw('Image', {
            Size = newUDim2(1,0,1,0);
            Data = self.images.gradientp90;
            Transparency = .35;
            ZIndex = z+1;
            Parent = objs.background;
        })

        objs.accentBar = utility:Draw('Square', {
            Size = newUDim2(0,2,1,0);
            ThemeColor = accentColor == nil and 'Accent' or '';
            ZIndex = z+3;
            Parent = objs.background;
        })

        objs.text = utility:Draw('Text', {
            Position = newUDim2(0,10,.5,-7);
            ThemeColor = 'Primary Text';
            Text = message;
            Outline = true;
            Font = 2;
            Size = 13;
            ZIndex = z+4;
            Parent = objs.background;
        })

        objs.progressTrack = utility:Draw('Square', {
            Size = newUDim2(1,-2,0,1);
            Position = newUDim2(0,2,1,-1);
            ThemeColor = 'Border 2';
            ZIndex = z+2;
            Parent = objs.background;
        })

        objs.progress = utility:Draw('Square', {
            Size = newUDim2(1,-2,0,1);
            Position = newUDim2(0,2,1,-1);
            ThemeColor = accentColor == nil and 'Accent' or '';
            ZIndex = z+3;
            Parent = objs.background;
        })

        if accentColor then
            objs.accentBar.Color = accentColor;
            objs.progress.Color = accentColor;
        end

        -- size the card to the text, then park it off-screen to the left
        notification.width = math.max(objs.text.TextBounds.X + 22, notifSettings.minWidth)
        objs.background.Size = newUDim2(0, notification.width, 0, height)
        objs.background.Position = newUDim2(0, -(notification.width + notifSettings.x + 10), 0, 0)

        -- start fully transparent and remember where each piece should fade to
        for name, obj in next, objs do
            if name ~= 'holder' then
                notification.targets[obj] = obj.Transparency
                obj.Transparency = 0
            end
        end

        local function fade(visible, duration, direction)
            for obj, target in next, notification.targets do
                utility:Tween(obj, 'Transparency', visible and target or 0, duration, direction, Enum.EasingStyle.Quad)
            end
        end

        function notification:Remove()
            local idx = table.find(library.notifications, notification)
            if idx then
                table.remove(library.notifications, idx)
            end
            if objs.holder then
                objs.holder:Remove()
            end
            library:UpdateNotifications()
        end

        function notification:Dismiss()
            if self.removing then return end
            self.removing = true

            fade(false, notifSettings.outTime * .9, Enum.EasingDirection.In)
            local outTween = utility:Tween(objs.background, 'Position', newUDim2(0, -(self.width + notifSettings.x + 10), 0, 0), notifSettings.outTime, Enum.EasingDirection.In, Enum.EasingStyle.Quint)

            if outTween then
                outTween.Completed:Once(function()
                    notification:Remove()
                end)
            else
                notification:Remove()
            end
        end

        table.insert(self.notifications, notification)

        -- too many on screen: push the oldest out early
        local active = {}
        for _, v in ipairs(self.notifications) do
            if not v.removing then
                table.insert(active, v)
            end
        end
        for i = 1, #active - notifSettings.maxVisible do
            active[i]:Dismiss()
        end

        self:UpdateNotifications()

        -- in
        fade(true, notifSettings.inTime, Enum.EasingDirection.Out)
        utility:Tween(objs.background, 'Position', newUDim2(0, 0, 0, 0), notifSettings.inTime, Enum.EasingDirection.Out, Enum.EasingStyle.Quint)

        -- countdown bar shrinks over the lifetime of the notification
        utility:Tween(objs.progress, 'Size', newUDim2(0, 0, 0, 1), time, Enum.EasingDirection.InOut, Enum.EasingStyle.Linear)

        task.delay(time, function()
            if objs.background and objs.background.Object then
                notification:Dismiss()
            end
        end)

        return notification
    end

    self.notificationSettings = {
        x = 14;          -- left margin
        y = 60;          -- top of the stack
        height = 24;     -- card height
        spacing = 6;     -- gap between cards
        minWidth = 140;
        maxVisible = 7;
        inTime = .45;
        outTime = .35;
    }

    function self:UpdateNotifications()
        local settings = self.notificationSettings
        local slot = 0
        for _, v in ipairs(self.notifications) do
            if not v.removing then
                local target = newUDim2(0, settings.x, 0, settings.y + slot * (settings.height + settings.spacing))
                utility:Tween(v.objects.holder, 'Position', target, .3, Enum.EasingDirection.Out, Enum.EasingStyle.Quint)
                slot += 1
            end
        end
    end

    -- // Alerts
    -- centered boxes near the top middle of the screen, styled like the menu (accent top line, borders,
    -- countdown bar). they drop + fade in, stack downwards and rise + fade out.
    --   library:SendAlert('Target locked', 3)
    --   library:SendAlert('Low health!', 5, Color3.fromRGB(255, 60, 60))
    --   local a = library:SendAlert('Loading...', 999); a:SetText('Done'); a:Dismiss()
    self.alerts = {}
    self.alertSettings = {
        y = 34;          -- top of the stack (just under the default watermark spot)
        height = 22;
        spacing = 5;
        minWidth = 160;
        padding = 28;    -- horizontal space around the text
        maxVisible = 4;
        inTime = .35;
        outTime = .3;
        offset = 10;     -- how far it drops in from / rises out to
    }

    function self:UpdateAlerts()
        local settings = self.alertSettings
        local screen = workspace.CurrentCamera.ViewportSize
        local slot = 0
        for _, a in ipairs(self.alerts) do
            if not a.removing then
                local target = newUDim2(0, floor(screen.X / 2 - a.width / 2), 0, settings.y + slot * (settings.height + settings.spacing))
                if a.placed then
                    utility:Tween(a.objects.holder, 'Position', target, .3, Enum.EasingDirection.Out, Enum.EasingStyle.Quint)
                else
                    a.objects.holder.Position = target
                    a.placed = true
                end
                slot += 1
            end
        end
    end

    function self:SendAlert(message, time, color)
        time = time or 4
        if typeof(message) ~= 'string' then
            return error(string.format('invalid message type, got %s, expected string', typeof(message)))
        elseif typeof(time) ~= 'number' then
            return error(string.format('invalid time type, got %s, expected number', typeof(time)))
        elseif color ~= nil and typeof(color) ~= 'Color3' then
            return error(string.format('invalid color type, got %s, expected color3', typeof(color)))
        end

        local settings = self.alertSettings
        local z = self.zindexOrder.notification
        local height = settings.height

        local alert = {
            objects = {};
            targets = {};
            width = 0;
            removing = false;
            placed = false;
        }
        local objs = alert.objects

        objs.holder = utility:Draw('Square', {
            Size = newUDim2(0, 0, 0, height);
            Transparency = 0;
            ZIndex = z;
            NoHit = true;
        })

        objs.background = utility:Draw('Square', {
            Size = newUDim2(0, 200, 0, height);
            ThemeColor = 'Background';
            ZIndex = z;
            NoHit = true;
            Parent = objs.holder;
        })

        objs.border1 = utility:Draw('Square', {
            Size = newUDim2(1,2,1,2);
            Position = newUDim2(0,-1,0,-1);
            ThemeColor = 'Border 1';
            ZIndex = z-1;
            NoHit = true;
            Parent = objs.background;
        })

        objs.border2 = utility:Draw('Square', {
            Size = newUDim2(1,2,1,2);
            Position = newUDim2(0,-1,0,-1);
            ThemeColor = 'Border 3';
            ZIndex = z-2;
            NoHit = true;
            Parent = objs.border1;
        })

        objs.gradient = utility:Draw('Image', {
            Size = newUDim2(1,0,1,0);
            Data = self.images.gradientp90;
            Transparency = .35;
            ZIndex = z+1;
            Parent = objs.background;
        })

        objs.topBar = utility:Draw('Square', {
            Size = newUDim2(1,0,0,1);
            ThemeColor = color == nil and 'Accent' or '';
            ZIndex = z+3;
            NoHit = true;
            Parent = objs.background;
        })

        objs.text = utility:Draw('Text', {
            Position = newUDim2(.5,0,.5,-7);
            ThemeColor = 'Primary Text';
            Text = message;
            Center = true;
            Outline = true;
            Font = 2;
            Size = 13;
            ZIndex = z+4;
            Parent = objs.background;
        })

        objs.progress = utility:Draw('Square', {
            Size = newUDim2(1,0,0,1);
            Position = newUDim2(0,0,1,-1);
            ThemeColor = color == nil and 'Accent' or '';
            ThemeColorOffset = color == nil and -60 or 0;
            ZIndex = z+3;
            NoHit = true;
            Parent = objs.background;
        })

        if color then
            objs.topBar.Color = color
            objs.progress.Color = color
        end

        local function resize()
            alert.width = math.max(objs.text.TextBounds.X + settings.padding, settings.minWidth)
            objs.background.Size = newUDim2(0, alert.width, 0, height)
        end
        resize()

        -- start invisible, a little above its spot
        for name, obj in next, objs do
            if name ~= 'holder' then
                alert.targets[obj] = obj.Transparency
                obj.Transparency = 0
            end
        end
        objs.background.Position = newUDim2(0, 0, 0, -settings.offset)

        local function fade(visible, duration, direction)
            for obj, target in next, alert.targets do
                utility:Tween(obj, 'Transparency', visible and target or 0, duration, direction, Enum.EasingStyle.Quad)
            end
        end

        function alert:SetText(str)
            if typeof(str) == 'string' and objs.text.Object then
                objs.text.Text = str
                resize()
                library:UpdateAlerts()
            end
        end

        function alert:Remove()
            local idx = table.find(library.alerts, alert)
            if idx then
                table.remove(library.alerts, idx)
            end
            if objs.holder and objs.holder.Object then
                objs.holder:Remove()
            end
            library:UpdateAlerts()
        end

        function alert:Dismiss()
            if self.removing then return end
            self.removing = true
            library:UpdateAlerts()
            fade(false, settings.outTime * .9, Enum.EasingDirection.In)
            local outTween = utility:Tween(objs.background, 'Position', newUDim2(0, 0, 0, -settings.offset), settings.outTime, Enum.EasingDirection.In, Enum.EasingStyle.Quad)
            if outTween then
                outTween.Completed:Once(function()
                    alert:Remove()
                end)
            else
                alert:Remove()
            end
        end

        table.insert(self.alerts, alert)

        -- too many: push the oldest out early
        local active = {}
        for _, a in ipairs(self.alerts) do
            if not a.removing then
                table.insert(active, a)
            end
        end
        for i = 1, #active - settings.maxVisible do
            active[i]:Dismiss()
        end

        self:UpdateAlerts()

        -- in
        fade(true, settings.inTime, Enum.EasingDirection.Out)
        utility:Tween(objs.background, 'Position', newUDim2(0, 0, 0, 0), settings.inTime, Enum.EasingDirection.Out, Enum.EasingStyle.Quint)
        -- countdown bar shrinks towards the middle
        utility:Tween(objs.progress, 'Size', newUDim2(0, 0, 0, 1), time, Enum.EasingDirection.InOut, Enum.EasingStyle.Linear)
        utility:Tween(objs.progress, 'Position', newUDim2(.5, 0, 1, -1), time, Enum.EasingDirection.InOut, Enum.EasingStyle.Linear)

        task.delay(time, function()
            if objs.background and objs.background.Object then
                alert:Dismiss()
            end
        end)

        return alert
    end

    function self.NewIndicator(data)
        local indicator = {
            title = data.title or 'indicator',
            enabled = data.enabled or false,
            position = data.position or newUDim2(0,15,0,300),
            values = {},
            objects = {valueObjects = {}},
            spacing = '   ',
        };

        table.insert(self.indicators, indicator)

        -- Create Objects --
        do
            local z = self.zindexOrder.indicator;
            local objs = indicator.objects;

            objs.background = utility:Draw('Square', {
                Size = newUDim2(0, 200, 0, 16);
                Position = indicator.position;
                ThemeColor = 'Background';
                ZIndex = z;
            })

            objs.border1 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 2';
                Parent = objs.background;
                ZIndex = z-1;
            })

            objs.border2 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 3';
                Parent = objs.border1;
                ZIndex = z-2;
            })

            objs.topborder = utility:Draw('Square', {
                Size = newUDim2(1,0,0,1);
                ThemeColor = 'Accent';
                Parent = objs.background;
                ZIndex = z+1;
            })

            objs.textlabel = utility:Draw('Text', {
                Position = newUDim2(.5,0,0,1);
                ThemeColor = 'Primary Text';
                Text = indicator.title;
                Size = 13;
                Font = 2;
                ZIndex = z+2;
                Center = true;
                Outline = true;
                Parent = objs.background;
            });

        end
        --------------------

        -- drag it around while the menu is open (value rows are added as handles in AddValue)
        indicator.drag = utility:MakeDraggable({indicator.objects.background, indicator.objects.topborder}, function()
            return indicator.objects.background.Object.Position
        end, function(p)
            indicator:SetPosition(newUDim2(0, p.X, 0, p.Y))
        end, function()
            if indicator.onMoved then
                indicator.onMoved(indicator.position)
            end
        end)

        function indicator:Update()
            local xSize  = 125
            local yPos  = 0
            table.sort(self.values, function(a,b)
                return a.order < b.order;
            end)

            for _,v in next, self.values do
                v.objects.keyLabel.Text = tostring(v.key);
                v.objects.valueLabel.Text = tostring(v.value);
            
                v.objects.valueLabel.Position = newUDim2(1,-(v.objects.valueLabel.TextBounds.X + 3),0,0)
                v.objects.background.Position = newUDim2(0,0,1,3 + yPos)
                v.objects.background.Visible = v.enabled

                if v.enabled then
                    yPos = yPos + 16 + 3
                    local x = (v.objects.keyLabel.TextBounds.X + 10 + v.objects.valueLabel.TextBounds.X)
                    if x > xSize then
                        xSize = x
                    end
                end
            end

            self.objects.background.Size = newUDim2(0,xSize + 8,0,16)
            self.objects.background.Position = self.position
        end

        function indicator:AddValue(data)
            local value = {
                key = data.key or '',
                value = data.value or '',
                order = data.order or #self.values+1,
                enabled = data.enabled == nil and true or data.enabled,
                objects = {},
            }

            table.insert(self.values, value);

            -- Create Objects --
            do
                local z = library.zindexOrder.indicator;
                local objs = value.objects;

                objs.background = utility:Draw('Square', {
                    Size = newUDim2(1, 0, 0, 16);
                    ThemeColor = 'Background';
                    ZIndex = z;
                    Parent = indicator.objects.background;
                })
                indicator.drag:AddHandle(objs.background) -- rows drag the whole indicator too
    
                objs.border1 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border 2';
                    Parent = objs.background;
                    ZIndex = z-1;
                })
    
                objs.border2 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border 3';
                    Parent = objs.border1;
                    ZIndex = z-2;
                })
    
                objs.keyLabel = utility:Draw('Text', {
                    Position = newUDim2(0,3,0,1);
                    ThemeColor = 'Option Text 2';
                    Size = 13;
                    Font = 2;
                    ZIndex = z+2;
                    Outline = true;
                    Parent = objs.background;
                });

                objs.valueLabel = utility:Draw('Text', {
                    Position = newUDim2(0,0,0,1);
                    ThemeColor = 'Option Text 2';
                    Size = 13;
                    Font = 2;
                    ZIndex = z+2;
                    Outline = true;
                    Parent = objs.background;
                });

            end
            --------------------

            function value:Remove()
                table.remove(indicator.values, table.find(indicator.values, value))
                self.objects.background:Remove()
                table.clear(self)
                indicator:Update();
            end

            function value:SetEnabled(bool)
                if typeof(bool) == 'boolean' then
                    self.enabled = bool
                    indicator:Update()
                end
            end

            function value:SetValue(str)
                if typeof(str) == 'string' then
                    self.value = str
                    indicator:Update()
                end
            end

            function value:SetKey(str)
                if typeof(str) == 'string' then
                    self.key = str
                    indicator:Update()
                end
            end

            self:Update()
            return value
        end

        function indicator:GetValue(idx)
            if typeof(idx) == 'number' then
                return self.values[idx]
            else
                for i,v in next, self.values do
                    if v.key == idx then
                        return v
                    end
                end
            end
        end

        function indicator:SetEnabled(bool)
            if typeof(bool) == 'boolean' then
                self.enabled = bool;
                self.objects.background.Visible = bool;
                self:Update();
            end
        end

        function indicator:SetPosition(udim2)
            if typeof(udim2) == 'UDim2' then
                self.position = udim2
                self.objects.background.Position = udim2;
            end
        end

        for i,v in next, data.values or {} do
            indicator:AddValue({key = tostring(i), value = tostring(v)})
        end

        indicator:SetEnabled(indicator.enabled);
        return indicator
    end

    function self.NewWindow(data)
        local window = {
            title = data.title or '',
            selectedTab = nil;
            tabs = {},
            objects = {},
            colorpicker = {
                objects = {};
                color = c3new(1,0,0);
                trans = 0;
            };
            dropdown = {
                objects = {
                    values = {};
                };
                max = data.maxDropdownItems or 8; -- rows visible before the list scrolls
            }
        };

        table.insert(library.windows, window);

        ----- Create Objects ----
        do
            local size = data.size or newUDim2(0, 525, 0, 650);
            local position = data.position or newUDim2(0, 250, 0, 150);
            local objs = window.objects;
            local z = library.zindexOrder.window;

            objs.background = utility:Draw('Square', {
                Size = size;
                Position = position;
                ThemeColor = 'Background';
                ZIndex = z;
            })

            objs.innerBorder1 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 3';
                ZIndex = z-1;
                Parent = objs.background;
            })

            objs.innerBorder2 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 1';
                ZIndex = z-2;
                Parent = objs.innerBorder1;
            })

            objs.midBorder = utility:Draw('Square', {
                Size = newUDim2(1,10,1,25);
                Position = newUDim2(0,-5,0,-20);
                ThemeColor = 'Border 2';
                ZIndex = z-3;
                Parent = objs.innerBorder2;
            })

            objs.outerBorder1 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 1';
                ZIndex = z-4;
                Parent = objs.midBorder;
            })

            objs.outerBorder2 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 3';
                ZIndex = z-5;
                Parent = objs.outerBorder1;
            })

            objs.topBorder = utility:Draw('Square', {
                Size = newUDim2(1,0,0,1);
                ThemeColor = 'Accent';
                ZIndex = z+1;
                Parent = objs.background;
            })

            objs.title = utility:Draw('Text', {
                Position = newUDim2(0,7,0,2);
                ThemeColor = 'Primary Text';
                Text = window.title;
                Font = 2;
                Size = 13;
                ZIndex = z+1;
                Outline = true;
                Parent = objs.midBorder;
            })

            objs.groupBackground = utility:Draw('Square', {
                Size = newUDim2(1,-16,1,-(16+23));
                Position = newUDim2(0,8,0,8+23);
                ThemeColor = 'Group Background';
                ZIndex = z+5;
                Parent = objs.background;
            })

            objs.groupInnerBorder = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 1';
                ZIndex = z+4;
                Parent = objs.groupBackground;
            })

            objs.groupOuterBorder = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 3';
                ZIndex = z+3;
                Parent = objs.groupInnerBorder;
            })

            objs.tabHolder = utility:Draw('Square', {
                Size = newUDim2(1,0,0,20);
                Position = newUDim2(0,0,0,-21);
                Parent = objs.groupBackground;
                Transparency = 0;
                ZIndex = z+1;
            })

            objs.columnholder1 = utility:Draw('Square', {
                Size = newUDim2(.48, 0, .96, 0);
                Position = newUDim2(.01, 0, .02, 0);
                Transparency = 0;
                ZIndex = z+6;
                Parent = objs.groupBackground;
            })

            objs.columnholder2 = utility:Draw('Square', {
                Size = newUDim2(.48, 0, .96, 0);
                Position = newUDim2(1 - (.48 + .01), 0, .02, 0);
                Transparency = 0;
                ZIndex = z+6;
                Parent = objs.groupBackground;
            })

            -- accent line that slides under the selected tab
            objs.tabIndicator = utility:Draw('Square', {
                Size = newUDim2(0,0,0,1);
                ThemeColor = 'Accent';
                ZIndex = z+8;
                Parent = objs.tabHolder;
            })


            objs.dragdetector = utility:Draw('Square',{
                Size = newUDim2(1,0,1,0);
                Parent = objs.midBorder;
                Transparency = 0;
                ZIndex = z+2;
            })

            local dragging, mouseStart, objStart;

            utility:Connection(objs.dragdetector.MouseButton1Down, function(pos)
                -- stop the open animation so it doesn't fight the drag
                local running = library.tweens[objs.background] and library.tweens[objs.background].Position
                if running then
                    running:Cancel();
                    if window.restPosition then
                        objs.background.Position = window.restPosition;
                    end
                end
                dragging = true;
                mouseStart = newUDim2(0, pos.X, 0, pos.Y);
                objStart = objs.background.Position;
            end)

            utility:Connection(button1up, function()
                dragging = false;
            end)

            utility:Connection(mousemove, function(pos)
                if dragging then
                    if window.open then
                        objs.background.Position = objStart + newUDim2(0, pos.X, 0, pos.Y) - mouseStart;
                        window.restPosition = objs.background.Position;
                    else
                        dragging = false
                    end
                end
            end)

        end
        -------------------------

        ---- Decorations ----
        -- Everything is parented to the window so it moves, fades and hides with it,
        -- and flagged NoHit so it never blocks clicks. Wrapped in pcall so a Drawing
        -- limitation on some executor can never break the window itself.
        local decoOk, decoErr = pcall(function()
            local deco = library.decorations
            local objs = window.objects
            local z = library.zindexOrder.window
            local frame = objs.outerBorder2 -- outermost window border

            -- soft drop shadow: a few stacked, very transparent black squares, slightly offset down
            local shadowLayers = {}
            for i = 1, 4 do
                shadowLayers[i] = utility:Draw('Square', {
                    Size = newUDim2(1, i * 4, 1, i * 4);
                    Position = newUDim2(0, -i * 2, 0, -i * 2 + 3);
                    Color = c3new(0, 0, 0);
                    Transparency = .14 - i * .03;
                    ZIndex = z - 6 - i;
                    NoHit = true;
                    Parent = frame;
                })
            end

            -- // Vines
            -- a stem is a wavy line that grows from a window corner along one edge, sitting just outside the frame.
            -- leaves are small diamond quads along the stem, blossoms are accent circles.
            local palettes = {
                nature = {
                    stem = {color = fromrgb(52, 98, 48)},
                    leaf1 = {color = fromrgb(78, 140, 64)},
                    leaf2 = {color = fromrgb(104, 168, 80)},
                },
                theme = {
                    stem = {theme = 'Accent', offset = -110},
                    leaf1 = {theme = 'Accent', offset = -70},
                    leaf2 = {theme = 'Accent', offset = -35},
                },
            }

            local function paint(drawing, style)
                if style.theme then
                    drawing.ThemeColorOffset = style.offset or 0
                    drawing.ThemeColor = style.theme
                else
                    drawing.ThemeColor = ''
                    drawing.Color = style.color
                end
            end

            local SEGMENTS = 22
            local stems = {}

            -- corner: 'tl' or 'br'; dir/normal are unit vectors (along the edge / pointing away from the window)
            local function newStem(corner, dir, normal, edge, fraction, phase)
                local stem = {
                    corner = corner, dir = dir, normal = normal, edge = edge,
                    fraction = fraction, phase = phase,
                    lines = {}, leaves = {}, blossoms = {},
                }

                for i = 1, SEGMENTS do
                    stem.lines[i] = utility:Draw('Line', {
                        Thickness = 1,
                        Transparency = 1,
                        ZIndex = z + 3,
                        Visible = false,
                        Parent = objs.background,
                    })
                end

                local leafEvery = math.max(1, math.floor(3 / math.max(deco.density, .1) + .5))
                local side = 1
                for i = 2, SEGMENTS - 1, leafEvery do
                    -- a leaf is a diamond made of two triangles (Quad isn't supported everywhere)
                    local function half()
                        return utility:Draw('Triangle', {
                            Filled = true,
                            Thickness = 1,
                            Transparency = .95,
                            ZIndex = z + 4,
                            Visible = false,
                            Parent = objs.background,
                        })
                    end
                    local leaf = {
                        segment = i,
                        side = side, -- 1 = outward, -1 = small leaf hugging the frame
                        halves = {half(), half()},
                    }
                    side = -side
                    table.insert(stem.leaves, leaf)
                end

                -- blossoms at the base and the tip
                for _, at in ipairs({0.04, 1}) do
                    local blossom = {
                        at = at,
                        petal = utility:Draw('Circle', {
                            Filled = true, NumSides = 12, Radius = 2.6, Transparency = 1,
                            ThemeColor = 'Accent', ZIndex = z + 5, Visible = false, Parent = objs.background,
                        }),
                        center = utility:Draw('Circle', {
                            Filled = true, NumSides = 8, Radius = 1, Transparency = 1,
                            Color = fromrgb(255, 240, 200), ZIndex = z + 6, Visible = false, Parent = objs.background,
                        }),
                    }
                    table.insert(stem.blossoms, blossom)
                end

                table.insert(stems, stem)
                return stem
            end

            newStem('tl', newVector2(1, 0), newVector2(0, -1), 'x', .38, 0)    -- along the top
            newStem('tl', newVector2(0, 1), newVector2(-1, 0), 'y', .32, 1.7)  -- down the left side
            newStem('br', newVector2(-1, 0), newVector2(0, 1), 'x', .30, 3.1)  -- along the bottom
            newStem('br', newVector2(0, -1), newVector2(1, 0), 'y', .26, 4.4)  -- up the right side

            local currentPalette
            local function applyPalette()
                local palette = palettes[deco.palette] or palettes.nature
                if palette == currentPalette then return end
                currentPalette = palette
                for _, stem in ipairs(stems) do
                    for _, line in ipairs(stem.lines) do
                        paint(line, palette.stem)
                    end
                    for i, leaf in ipairs(stem.leaves) do
                        local style = i % 2 == 0 and palette.leaf2 or palette.leaf1
                        paint(leaf.halves[1], style)
                        paint(leaf.halves[2], style)
                    end
                end
            end
            applyPalette()

            -- only touch Visible when it actually changes (each change re-runs the drawing's Update)
            local function setShown(drawing, shown)
                if drawing.Visible ~= shown then
                    drawing.Visible = shown
                end
            end

            local wasOpen, openedAt = false, 0
            local shadowShown = true
            local broken = false

            local function updateDecorations()
                local frameObj = frame.Object
                if frameObj == nil then return end -- unloaded

                -- shadow toggle
                local wantShadow = deco.enabled and deco.shadow
                if wantShadow ~= shadowShown then
                    shadowShown = wantShadow
                    for _, layer in ipairs(shadowLayers) do
                        setShown(layer, wantShadow)
                    end
                end

                if not window.open then
                    wasOpen = false
                    return
                end
                if not wasOpen then
                    wasOpen = true
                    openedAt = os.clock()
                end

                local active = deco.enabled and deco.vines
                applyPalette()

                local now = os.clock()
                local grown = (deco.growTime and deco.growTime > 0) and clamp((now - openedAt) / deco.growTime, 0, 1) or 1
                grown = 1 - (1 - grown) ^ 3 -- ease out
                local swayTime = deco.sway and now or 0

                local origin = frameObj.Position
                local size = frameObj.Size
                local bgPos = objs.background.Object.Position

                for _, stem in ipairs(stems) do
                    local corner = stem.corner == 'tl' and origin or (origin + size)
                    local length = (stem.edge == 'x' and size.X or size.Y) * stem.fraction
                    local step = length / SEGMENTS

                    -- point on the stem at distance s (wave grows towards the tip, and sways over time)
                    local function pointAt(s)
                        local t = s / math.max(length, 1)
                        local wave = math.sin(s * .16 + stem.phase) * (1.2 + 1.6 * t)
                        local sway = math.sin(swayTime * 1.4 + stem.phase + s * .05) * .9 * t
                        return corner + stem.dir * s + stem.normal * (1.5 + wave + sway)
                    end

                    local visibleSegments = active and math.floor(SEGMENTS * grown + .5) or 0

                    for i, line in ipairs(stem.lines) do
                        local shown = i <= visibleSegments
                        setShown(line, shown)
                        if shown then
                            local a, b = pointAt((i - 1) * step), pointAt(i * step)
                            local raw = line.Object
                            raw.From = a
                            raw.To = b
                            raw.Thickness = 2.2 - 1.2 * (i / SEGMENTS) -- taper towards the tip
                        end
                    end

                    for _, leaf in ipairs(stem.leaves) do
                        local shown = leaf.segment <= visibleSegments
                        setShown(leaf.halves[1], shown)
                        setShown(leaf.halves[2], shown)
                        if shown then
                            local s = leaf.segment * step
                            local base = pointAt(s)
                            local tangent = (pointAt(s + 1) - base).Unit
                            local flutter = math.sin(swayTime * 2.1 + leaf.segment) * .25
                            local outward = stem.normal * leaf.side
                            local dir = (tangent * (.7 + flutter) + outward).Unit
                            local perp = newVector2(-dir.Y, dir.X)
                            local leafLength = (leaf.side > 0 and 7.5 or 4.5) * (1 - .35 * (leaf.segment / SEGMENTS))
                            local width = leafLength * .32
                            local tip = base + dir * leafLength
                            local mid = base + dir * (leafLength * .45)
                            local left, right = mid + perp * width, mid - perp * width
                            local a, b = leaf.halves[1].Object, leaf.halves[2].Object
                            a.PointA, a.PointB, a.PointC = base, left, tip
                            b.PointA, b.PointB, b.PointC = base, right, tip
                        end
                    end

                    for _, blossom in ipairs(stem.blossoms) do
                        -- the tip blossom only appears once the vine has finished growing
                        local shown = active and (blossom.at < 1 or grown >= .98)
                        setShown(blossom.petal, shown)
                        setShown(blossom.center, shown)
                        if shown then
                            local p = pointAt(length * blossom.at) - bgPos
                            local pos = newUDim2(0, p.X, 0, p.Y)
                            blossom.petal.Position = pos
                            blossom.center.Position = pos
                        end
                    end
                end
            end

            -- the vines only need ~30 updates a second (sway is slow), and none at all while
            -- the menu is closed or nothing about them changes
            local lastDecoUpdate, lastFramePos, lastFrameSize, lastSettingsKey = 0, nil, nil, nil
            utility:Connection(runservice.RenderStepped, function()
                if broken then return end
                local frameData = frame.Object and library.drawings[frame.Object]
                if not frameData then return end
                local now = os.clock()
                local moved = frameData.AbsolutePosition ~= lastFramePos or frameData.AbsoluteSize ~= lastFrameSize
                local growTime = tonumber(deco.growTime) or 0
                local growing = window.open and growTime > 0 and (now - openedAt) < growTime + .1
                local animating = window.open and deco.enabled and deco.vines and (deco.sway or growing)
                local interval = 1 / math.max(tonumber(deco.fps) or 30, 1)
                local settingsKey = tostring(deco.enabled)..tostring(deco.vines)..tostring(deco.shadow)..tostring(deco.palette)..tostring(deco.sway)
                local changed = moved or wasOpen ~= window.open or settingsKey ~= lastSettingsKey
                if not changed and not (animating and now - lastDecoUpdate >= interval) then
                    return
                end
                lastSettingsKey = settingsKey
                lastDecoUpdate = now
                lastFramePos, lastFrameSize = frameData.AbsolutePosition, frameData.AbsoluteSize
                local ok, err = pcall(updateDecorations)
                if not ok then
                    broken = true
                    log('window decorations stopped: '..tostring(err))
                end
            end)
        end)
        if not decoOk then
            log('window decorations disabled: '..tostring(decoErr))
        end
        -------------------------

        -- Create Color Picker --
        do
            -- Objects
            do
                local objs = window.colorpicker.objects;
                local z = library.zindexOrder.colorpicker;

                objs.background = utility:Draw('Square', {
                    Visible = false;
                    Size = newUDim2(0,200,0,242);
                    Position = newUDim2(1,-200,1,10);
                    ThemeColor = 'Background';
                    ZIndex = z;
                    Parent = window.objects.background;
                })

                objs.border1 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border';
                    ZIndex = z-1;
                    Parent = objs.background;
                })

                objs.border2 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border 1';
                    ZIndex = z-2;
                    Parent = objs.border1;
                })

                objs.border3 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border';
                    ZIndex = z-3;
                    Parent = objs.border2;
                })

                objs.statusText = utility:Draw('Text', {
                    Position = newUDim2(0,5,0,4);
                    Text = 'colorpicker_status_text';
                    ThemeColor = 'Option Text 1';
                    Size = 13;
                    Font = 2;
                    Outline = true;
                    ZIndex = z+1;
                    Parent = objs.background;
                })

                objs.mainColor = utility:Draw('Square', {
                    Size = newUDim2(0, 175, 0, 175);
                    Position = newUDim2(0, 5, 0, 25);
                    Color = c3new(1,0,0);
                    ZIndex = z+2;
                    Parent = objs.background;
                })

                objs.sat1 = utility:Draw('Image', {
                    Size = newUDim2(1,0,1,0);
                    Data = base64decode"iVBORw0KGgoAAAANSUhEUgAAAaQAAAGkCAQAAADURZm+AAAABGdBTUEAALGPC/xhBQAAACBjSFJNAAB6JQAAgIMAAPn/AACA6QAAdTAAAOpgAAA6mAAAF2+SX8VGAAAAAmJLR0QA/4ePzL8AAAAJcEhZcwAACxMAAAsTAQCanBgAAAAHdElNRQflBwwSLzK3wl3KAAADrElEQVR42u3TORLCMBBFwT+6/50hMqXSZgonBN0BWCDGYPwqeSWVZPWYVHd0Pc5H86v9areu4Sz9u7XZXT/vvtZtu6dtJtYw525iGya05afnWW17ltPE8fzfTZy/yf3vmCes59xf0Sf/42l3lnvGOyyH+y/bo/X689wCPCYkEBIICYQECAmEBEICIQFCAiGBkEBIgJBASCAkEBIgJBASCAmEBAgJhARCAiEBQgIhgZAAIYGQQEggJEBIICQQEggJEBIICYQEQgKEBEICIYGQACGBkEBIICRASCAkEBIICRASCAmEBAgJhARCAiEBQgIhgZBASICQQEggJBASICQQEggJhAQICYQEQgIhAUICIYGQQEguAQgJhARCAoQEQgIhgZAAIYGQQEggJEBIICQQEggJEBIICYQEQgKEBEICIYGQACGBkEBIgJBASCAkEBIgJBASCAmEBAgJhARCAiEBQgIhgZBASICQQEggJBASICQQEggJhAQICYQEQgKEBEICIYGQACGBkEBIICRASCAkEBIICRASCAmEBEIChARCAiGBkAAhgZBASCAkQEggJBASICQQEggJhAQICYQEQgIhAUICIYGQQEiAkEBIICQQEiAkEBIICYQECAmEBEIChARCAiGBkAAhgZBASCAkQEggJBASCAkQEggJhARCAoQEQgIhgZAAIYGQQEggJEBIICQQEiAkEBIICYQECAmEBEICIQFCAiGBkEBIgJBASCAkEBIgJBASCAmEBAgJhARCAiEBQgIhgZAAIYGQQEggJEBIICQQEggJEBIICYQEQgKEBEICIYGQACGBkEBIICRASCAkEBIgJBASCAmEBAgJhARCAiEBQgIhgZBASICQQEggJBASICQQEggJhAQICYQEQgIhAUICIYGQACGBkEBIICRASCAkEBIICRASCAmEBEIChARCAiGBkAAhgZBASCAkQEggJBASCAkQEggJhAQICYQEQgIhAUICIYGQQEiAkEBIICQQEiAkEBIICYQECAmEBEICIQFCAiGBkEBILgEICYQEQgKEBEICIYGQACGBkEBIICRASCAkEBIICRASCAmEBEIChARCAiGBkAAhgZBASICQQEggJBASICQQEggJhAQICYQEQgIhAUICIYGQQEiAkEBIICQQEiAkEBIICYQECAmEBEIChARCAiGBkAAhgZBASCAkQEggJBASCAkQEggJhARCAoQEQgIhgZAAIYGQQEggJEBIICQQEiAkEBL8lzft9AVFFzN+ywAAACV0RVh0ZGF0ZTpjcmVhdGUAMjAyMS0wNy0xMlQxODo0Nzo1MCswMDowMIxlM90AAAAldEVYdGRhdGU6bW9kaWZ5ADIwMjEtMDctMTJUMTg6NDc6NTArMDA6MDD9OIthAAAAAElFTkSuQmCC";
                    ZIndex = z+3;
                    Parent = objs.mainColor;
                })

                objs.sat2 = utility:Draw('Image', {
                    Size = newUDim2(1,0,1,0);
                    Data = base64decode"iVBORw0KGgoAAAANSUhEUgAAAaQAAAGkCAQAAADURZm+AAAABGdBTUEAALGPC/xhBQAAACBjSFJNAAB6JQAAgIMAAPn/AACA6QAAdTAAAOpgAAA6mAAAF2+SX8VGAAAAAmJLR0QA/4ePzL8AAAAJcEhZcwAACxMAAAsTAQCanBgAAAAHdElNRQflBwwSLyBEeyyCAAAD4klEQVR42u3YwQnAQAhFQTek/5pz9eBtEYzMlBD4PDcRADDBieMjwK3HJwBDghFepx0oEhgSOO0ARQJDAqcdKBJgSGBI4I0EhgQ47cCQwJDAGwlQJDAkcNqBIgGKBIoEhgROO0CRQJFAkQBDAqcdGBI47QBFAkUCQwKnHaBIoEigSKBIgCKBIYHTDhQJUCQwJHDagSIBigSGBE47UCRAkcCQwGkHKBIoEigSGBLgtANDAkMCbyTAkMBpB4oEigQoEhgSOO1AkQBDAqcdKBIoEqBIYEjgtANFUiRQJFAkMCTAaQeKBIoEigQYEjjtQJFAkQBFAkMCpx0oEmBI4LQDRQJFAhQJDAmcdqBIgCKBIoEhAU47UCRQJFAkwJDAaQeKBIYEOO1AkUCRYHuRTAmcduC0A0UCFAkUCQwJnHaAIoEigSKBIQFOO2gvkimBIoE3EhgS4LQDRQJDAqcdoEigSKBIYEiAIYEhwXx+NoAigSGB0w5QJDAkMCQwJKDiZwMoEhgSOO0ARQJFgnlFMiVw2oHTDhQJUCRQJDAkcNoBVZFMCRQJvJHAkACnHSgSKBIoElANSZPAaQdOOzAkwGkHigSGBIYEGBK08LMBFAkUCRQJMCQwJDAkWMjPBlAkMCRw2gG5SKYEigTeSGBIgNMOFAkMCQwJMCRo4WcDKBIYEjjtgFwkUwJFAm8kMCTAaQeKBIoEigRUQ9IkcNqB0w4MCXDagSKBIsHCIpkSOO3AaQeKBCgSKBIYEhgSYEjQws8GUCQwJHDaAblIpgSKBN5IYEiA0w4UCQwJDAkwJGjhZwMoEhgSOO0ARQJDAkMCQwIqfjaAIoEigSIBhgROO5hXJFMCpx047UCRAEUCRQJDAqcdUBXJlECRwBsJDAlw2oEigSKBIgGGBIYEhgSL+dkAigSGBE47QJHAkMBpB4oEGBIYEhgSrOZnAygSKBIoEmBI4LQDRQJFAhQJDAmcdrC8SKYEigTeSGBIgNMOFAkMCZx2gCKBIoEigSEBTjtQJFAkUCTAkMBpB4oEigQoEhgSOO1AkQBDAqcdKBKgSKBIYEjgtAMUCRQJFAkMCXDagSKBIoEiAYYETjtQJFAkQJHAkMBpB4oEGBI47UCRQJEARQJDAqcdoEigSGBI4LQDFAkUCRQJFAkwJHDagSKBIQFOOzAkMCTwRgIMCZx2oEigSIAigSKBIYHTzkcARQJFAkMCnHZgSGBI4I0EGBI47UCRQJEAQwKnHSgSKBKgSGBI4LQDRQIUCRQJDAmcdoAigSGB0w5QJFAkUCQwJMBpB4oEhgROO0CRwJDAkMAbCVAkMCT4gw/reQYigE05fAAAACV0RVh0ZGF0ZTpjcmVhdGUAMjAyMS0wNy0xMlQxODo0NzozMiswMDowMN2VK3MAAAAldEVYdGRhdGU6bW9kaWZ5ADIwMjEtMDctMTJUMTg6NDc6MzIrMDA6MDCsyJPPAAAAAElFTkSuQmCC";
                    ZIndex = z+4;
                    Parent = objs.mainColor;
                })

                objs.colorBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border';
                    ZIndex = z+1;
                    Parent = objs.mainColor;
                })

                objs.mainDetector = utility:Draw('Square',{
                    Size = newUDim2(1,0,1,0);
                    Transparency = 0;
                    ZIndex = z+10;
                    Parent = objs.mainColor;
                })

                objs.hue = utility:Draw('Image', {
                    Size = newUDim2(0,175,0,10);
                    Position = newUDim2(0,5,0,205);
                    Data = library.images.colorhue;
                    ZIndex = z+2;
                    Parent = objs.background;
                })

                objs.hueBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border';
                    ZIndex = z+1;
                    Parent = objs.hue;
                })

                objs.hueDetector = utility:Draw('Square',{
                    Size = newUDim2(1,0,1,0);
                    Transparency = 0;
                    ZIndex = z+10;
                    Parent = objs.hue;
                })

                objs.transColor = utility:Draw('Square', {
                    Size = newUDim2(0,10,0,175);
                    Position = newUDim2(0,185,0,25);
                    Color = c3new(1,0,0);
                    ZIndex = z+2;
                    Parent = objs.background;
                })

                objs.trans = utility:Draw('Image', {
                    Size = newUDim2(1,0,1,0);
                    Data = library.images.colortrans;
                    ZIndex = z+3;
                    Parent = objs.transColor;
                })

                objs.transBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border';
                    ZIndex = z+1;
                    Parent = objs.transColor;
                })

                objs.transDetector = utility:Draw('Square',{
                    Size = newUDim2(1,0,1,0);
                    Transparency = 0;
                    ZIndex = z+10;
                    Parent = objs.transColor;
                })

                objs.pointer = utility:Draw('Square', {
                    Size = newUDim2(0,2,0,2);
                    Position = newUDim2(0,0,0,0);
                    Color = c3new(1,1,1);
                    ZIndex = z+6;
                    Parent = objs.mainColor;
                })

                objs.pointerBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    Color = c3new(0,0,0);
                    ZIndex = z+5;
                    Parent = objs.pointer;
                })

                objs.hueSlider = utility:Draw('Square', {
                    Size = newUDim2(0,1,1,0);
                    Color = c3new(1,1,1);
                    ZIndex = z+4;
                    Parent = objs.hue;
                })

                objs.hueSliderBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    Color = c3new(0,0,0);
                    ZIndex = z+3;
                    Parent = objs.hueSlider;
                })

                objs.transSlider = utility:Draw('Square', {
                    Size = newUDim2(1,0,0,1);
                    Color = c3new(1,1,1);
                    ZIndex = z+5;
                    Parent = objs.trans;
                })

                objs.transSliderBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    Color = c3new(0,0,0);
                    ZIndex = z+4;
                    Parent = objs.transSlider;
                })

                objs.rBackground = utility:Draw('Square', {
                    Size = newUDim2(0, 60, 0, 15);
                    Position = newUDim2(0, 5, 1, - 20);
                    ThemeColor = 'Option Background';
                    Parent = objs.background;
                    ZIndex = z+5;
                })

                objs.rBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    Color = c3new(0,0,0);
                    ZIndex = z+4;
                    Parent = objs.rBackground;
                })

                objs.rText = utility:Draw('Text', {
                    Position = newUDim2(.5,0,0,0);
                    Color = c3new(1,.1,.1);
                    Text = 'R';
                    Size = 13;
                    Font = 2;
                    Outline = true;
                    Center = true;
                    ZIndex = z+6;
                    Parent = objs.rBackground;
                })

                objs.gBackground = utility:Draw('Square', {
                    Size = newUDim2(0, 60, 0, 15);
                    Position = newUDim2(0, 70, 1, - 20);
                    ThemeColor = 'Option Background';
                    Parent = objs.background;
                    ZIndex = z+5;
                })

                objs.gBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    Color = c3new(0,0,0);
                    ZIndex = z+4;
                    Parent = objs.gBackground;
                })

                objs.gText = utility:Draw('Text', {
                    Position = newUDim2(.5,0,0,0);
                    Color = c3new(.1,1,.1);
                    Text = 'G';
                    Size = 13;
                    Font = 2;
                    Outline = true;
                    Center = true;
                    ZIndex = z+6;
                    Parent = objs.gBackground;
                })

                objs.bBackground = utility:Draw('Square', {
                    Size = newUDim2(0, 60, 0, 15);
                    Position = newUDim2(0, 135, 1, - 20);
                    ThemeColor = 'Option Background';
                    Parent = objs.background;
                    ZIndex = z+5;
                })

                objs.bBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    Color = c3new(0,0,0);
                    ZIndex = z+4;
                    Parent = objs.bBackground;
                })

                objs.bText = utility:Draw('Text', {
                    Position = newUDim2(.5,0,0,0);
                    Color = c3new(.1,.1,1);
                    Text = 'B';
                    Size = 13;
                    Font = 2;
                    Outline = true;
                    Center = true;
                    ZIndex = z+6;
                    Parent = objs.bBackground;
                })

                local draggingHue, draggingSat, draggingTrans = false, false, false;

                local function updateSatVal(pos)
                    if window.colorpicker.selected ~= nil then
                        local hue, sat, val = window.colorpicker.selected.color:ToHSV()
                        local mainPos, mainSize = objs.mainColor.Object.Position, objs.mainColor.Object.Size
                        local X = math.clamp((pos.X - mainPos.X) / math.max(mainSize.X, 1), 0, 0.995)
                        local Y = math.clamp((pos.Y - mainPos.Y) / math.max(mainSize.Y, 1), 0, 0.995)
                        sat, val = 1 - X, 1 - Y;
                        window.colorpicker.selected:SetColor(fromhsv(hue,sat,val));
                        window.colorpicker:Visualize(fromhsv(hue, sat, val), window.colorpicker.selected.trans);
                    end
                end

                local function updateHue(pos)
                    if window.colorpicker.selected ~= nil then
                        local hue, sat, val = window.colorpicker.selected.color:ToHSV()
                        local huePos, hueSize = objs.hue.Object.Position, objs.hue.Object.Size
                        local X = math.clamp((pos.X - huePos.X) / math.max(hueSize.X, 1), 0, 0.995)
                        hue = 1 - X
                        window.colorpicker.selected:SetColor(fromhsv(hue,sat,val));
                        window.colorpicker:Visualize(fromhsv(hue, sat, val), window.colorpicker.selected.trans);
                    end
                end

                local function updateTrans(pos)
                    if window.colorpicker.selected ~= nil then
                        local transPos, transSize = objs.transColor.Object.Position, objs.transColor.Object.Size
                        local Y = math.clamp((pos.Y - transPos.Y) / math.max(transSize.Y, 1), 0, 0.995)
                        window.colorpicker.selected:SetTrans(Y);
                        window.colorpicker:Visualize(window.colorpicker.selected.color, Y);
                    end
                end

                utility:Connection(objs.mainDetector.MouseButton1Down, function(pos)
                    draggingSat = true;
                    updateSatVal(pos)
                end)

                utility:Connection(objs.hueDetector.MouseButton1Down, function(pos)
                    draggingHue = true;
                    updateHue(pos)
                end)

                utility:Connection(objs.transDetector.MouseButton1Down, function(pos)
                    draggingTrans = true;
                    updateTrans(pos)
                end)

                utility:Connection(mousemove, function(pos)
                    if library.open then
                        if draggingSat then
                            updateSatVal(pos)
                        elseif draggingHue then
                            updateHue(pos)
                        elseif draggingTrans then
                            updateTrans(pos)
                        end
                    end
                end)

                utility:Connection(button1up, function()
                    draggingSat = false;
                    draggingHue = false;
                    draggingTrans = false;
                end)

            end

            function window.colorpicker:Visualize(c3, a)
                if typeof(c3) ~= 'Color3' then return end
                if typeof(a) ~= 'number' then return end
                local h,s,v = c3:ToHSV();
                h = h == 0 and 1 or h;
                self.color = c3;
                self.trans = a;
                self.objects.mainColor.Color = fromhsv(h,1,1);
                self.objects.transColor.Color = fromhsv(h,s,v);
                self.objects.hueSlider.Position = newUDim2(1 - h, 0,0,0);
                self.objects.transSlider.Position = newUDim2(0,0,a,0);
                self.objects.pointer.Position = newUDim2(1 - s, 0, 1 - v, 0);
                self.objects.statusText.Text = 'Editing : Unknown';
                if self.selected ~= nil then
                    local txt = 'Editing : Unknown';
                    if self.selected.text ~= nil and self.selected.text ~= '' then
                        txt = tostring(self.selected.text)
                    elseif self.selected.flag ~= nil and self.selected.flag ~= '' then
                        txt = tostring(self.selected.flag)
                    end
                    self.objects.statusText.Text = tostring(txt);
                end
            end
            
            window.colorpicker:Visualize(window.colorpicker.color, window.colorpicker.trans)

        end
        -------------------------

        ---- Create Dropdown ----
        do
            -- Default Objects
            do
                local objs = window.dropdown.objects;
                local z = library.zindexOrder.dropdown;

                objs.background = utility:Draw('Square', {
                    Visible = false;
                    Size = newUDim2(1,-3,0,50);
                    Position = newUDim2(0,3,1,0);
                    ThemeColor = 'Background';
                    ZIndex = z;
                    Parent = window.objects.background;
                })

                objs.border1 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border';
                    ZIndex = z-1;
                    Parent = objs.background;
                })

                objs.border2 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border 1';
                    ZIndex = z-2;
                    Parent = objs.border1;
                })

                objs.border3 = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border';
                    ZIndex = z-3;
                    Parent = objs.border2;
                })

            end

            -- // Scrollable list
            -- only `max` rows exist (a small reused pool); scrolling just changes which values they show.
            -- scroll with the mouse wheel, or drag the scrollbar on the right.
            local dropdown = window.dropdown
            local ROW, PAD = 18, 2
            local z = library.zindexOrder.dropdown
            dropdown.scroll = 0

            dropdown.objects.scrollTrack = utility:Draw('Square', {
                Size = newUDim2(0,4,1,-4);
                Position = newUDim2(1,-7,0,2);
                ThemeColor = 'Option Background';
                ZIndex = z+3;
                Visible = false;
                Parent = dropdown.objects.background;
            })

            dropdown.objects.scrollThumb = utility:Draw('Square', {
                Size = newUDim2(1,0,0,10);
                ThemeColor = 'Accent';
                ZIndex = z+4;
                Parent = dropdown.objects.scrollTrack;
            })

            local function isSelected(list, val)
                if typeof(list.selected) == 'table' then
                    return table.find(list.selected, val) ~= nil
                end
                return list.selected == val
            end

            function dropdown:GetMax()
                local list = self.selected
                return math.max(1, floor((list and list.maxVisible) or self.max or 8))
            end

            function dropdown:ClampScroll()
                local list = self.selected
                local count = list and #list.values or 0
                self.scroll = clamp(floor(self.scroll or 0), 0, math.max(count - self:GetMax(), 0))
            end

            function dropdown:Scroll(delta)
                local before = self.scroll
                self.scroll = (self.scroll or 0) + delta
                self:ClampScroll()
                if self.scroll ~= before then
                    self:Refresh()
                end
            end

            -- scrolls so the selected value sits in the middle of the list
            function dropdown:ScrollToSelected()
                local list = self.selected
                if not list then return end
                local target = typeof(list.selected) == 'table' and list.selected[1] or list.selected
                local idx = table.find(list.values, target)
                self.scroll = idx and (idx - math.ceil(self:GetMax() / 2)) or 0
                self:ClampScroll()
            end

            function dropdown:Close()
                local list = self.selected
                if list then
                    list.open = false
                    list.objects.openText.Text = '+'
                end
                self.selected = nil
                self.draggingScroll = false
                self.objects.background.Visible = false
            end

            function dropdown:GetRow(slot)
                local row = self.objects.values[slot]
                if row then return row end

                row = {}
                row.background = utility:Draw('Square', {
                    Size = newUDim2(1,-4,0,ROW);
                    Color = Color3.new(.25,.25,.25);
                    Transparency = 0;
                    ZIndex = z+1;
                    Parent = self.objects.background;
                })
                row.text = utility:Draw('Text', {
                    Position = newUDim2(0,3,0,1);
                    ThemeColor = 'Option Text 2';
                    Size = 13;
                    Font = 2;
                    ZIndex = z+2;
                    Parent = row.background;
                })

                utility:Connection(row.background.MouseEnter, function()
                    local list = self.selected
                    if list and row.value ~= nil and not isSelected(list, row.value) then
                        row.text.ThemeColor = 'Accent'
                    end
                end)

                utility:Connection(row.background.MouseLeave, function()
                    local list = self.selected
                    row.text.ThemeColor = (list and row.value ~= nil and isSelected(list, row.value)) and 'Option Text 1' or 'Option Text 2'
                end)

                utility:Connection(row.background.MouseButton1Down, function()
                    local list = self.selected
                    if not list then return end
                    local val = list.values[(self.scroll or 0) + slot]
                    if val == nil then return end

                    local newSelected = list.multi and {} or val
                    if list.multi then
                        for _, v in next, (typeof(list.selected) == 'table' and list.selected or {}) do
                            if v ~= 'none' then
                                table.insert(newSelected, v)
                            end
                        end
                        local found = table.find(newSelected, val)
                        if found then
                            table.remove(newSelected, found)
                        else
                            table.insert(newSelected, val)
                        end
                    end

                    list:Select(newSelected)
                    if list.multi then
                        self:Refresh()
                    else
                        self:Close()
                    end
                end)

                self.objects.values[slot] = row
                return row
            end

            function dropdown:Refresh()
                local list = self.selected
                if list == nil then return end
                self:ClampScroll()

                local max = self:GetMax()
                local count = #list.values
                local shown = math.min(count, max)
                local scrollable = count > max
                local rowWidth = scrollable and -12 or -4

                for slot = 1, math.max(shown, #self.objects.values) do
                    local val = slot <= shown and list.values[self.scroll + slot] or nil
                    local row = val ~= nil and self:GetRow(slot) or self.objects.values[slot]
                    if row then
                        row.value = val
                        row.background.Visible = val ~= nil
                        if val ~= nil then
                            local selected = isSelected(list, val)
                            row.background.Position = newUDim2(0,2,0,2 + (slot - 1) * (ROW + PAD))
                            row.background.Size = newUDim2(1,rowWidth,0,ROW)
                            row.background.Transparency = selected and 1 or 0
                            row.text.Text = tostring(val)
                            row.text.ThemeColor = selected and 'Option Text 1' or (row.background.Hover and 'Accent' or 'Option Text 2')
                        end
                    end
                end

                local height = math.max(2 + shown * (ROW + PAD), 4)
                self.objects.background.Size = newUDim2(1,-6,0,height)

                local track, thumb = self.objects.scrollTrack, self.objects.scrollThumb
                track.Visible = scrollable
                if scrollable then
                    local trackHeight = height - 4
                    local thumbHeight = math.max(floor(trackHeight * max / count), 12)
                    local y = floor((trackHeight - thumbHeight) * (self.scroll / (count - max)))
                    thumb.Size = newUDim2(1,0,0,thumbHeight)
                    thumb.Position = newUDim2(0,0,0,y)
                end

                library.hoverDirty = true
            end

            -- scrollbar dragging: thumb follows the mouse
            local function scrollToMouse(pos)
                local list = dropdown.selected
                if not list then return end
                local trackData = library.drawings[dropdown.objects.scrollTrack.Object]
                local thumbData = library.drawings[dropdown.objects.scrollThumb.Object]
                if not trackData or not thumbData then return end
                local trackHeight = trackData.AbsoluteSize.Y
                local thumbHeight = thumbData.AbsoluteSize.Y
                local maxScroll = #list.values - dropdown:GetMax()
                if maxScroll <= 0 or trackHeight <= thumbHeight then return end
                local rel = clamp((pos.Y - trackData.AbsolutePosition.Y - thumbHeight / 2) / (trackHeight - thumbHeight), 0, 1)
                local target = floor(rel * maxScroll + .5)
                if target ~= dropdown.scroll then
                    dropdown.scroll = target
                    dropdown:Refresh()
                end
            end

            for _, handle in ipairs({dropdown.objects.scrollTrack, dropdown.objects.scrollThumb}) do
                utility:Connection(handle.MouseButton1Down, function(pos)
                    dropdown.draggingScroll = true
                    scrollToMouse(pos)
                end)
            end

            utility:Connection(mousemove, function(pos)
                if dropdown.draggingScroll then
                    scrollToMouse(pos)
                end
            end)

            utility:Connection(button1up, function()
                dropdown.draggingScroll = false
            end)

            -- is the mouse over the open dropdown? (checks its cached screen rect directly)
            local function mouseOverDropdown()
                if not library.open or dropdown.selected == nil then return false end
                local data = library.drawings[dropdown.objects.background.Object]
                if not data or not data.AbsVisible then return false end
                local m = inputservice:GetMouseLocation()
                local p, s = data.AbsolutePosition, data.AbsoluteSize
                return m.X >= p.X and m.Y >= p.Y and m.X <= p.X + s.X and m.Y <= p.Y + s.Y
            end

            -- mouse wheel scrolling. UserInputService still fires when a GUI (like the menu's input blocker)
            -- has already processed the wheel, unlike ContextActionService, which never saw it.
            utility:Connection(inputservice.InputChanged, function(input)
                if input.UserInputType == Enum.UserInputType.MouseWheel and mouseOverDropdown() then
                    local z = input.Position.Z
                    if z ~= 0 then
                        dropdown:Scroll(z > 0 and -1 or 1)
                    end
                end
            end)

            -- only sinks the wheel (so the camera doesn't zoom) while scrolling the dropdown; never scrolls by itself
            local wheelAction = 'UIDropdownScroll_'..http:GenerateGUID(false)
            pcall(function()
                actionservice:BindActionAtPriority(wheelAction, function()
                    if mouseOverDropdown() then
                        return Enum.ContextActionResult.Sink
                    end
                    return Enum.ContextActionResult.Pass
                end, false, Enum.ContextActionPriority.High.Value + 100, Enum.UserInputType.MouseWheel)
            end)
            utility:Connection(library.unloaded, function()
                pcall(function()
                    actionservice:UnbindAction(wheelAction)
                end)
            end)

            -- clicking anywhere outside an open dropdown / color picker closes it
            utility:Connection(button1down, function()
                local hoverObj = utility:GetHoverObject()
                local hoverData = hoverObj and library.drawings[hoverObj] or nil
                local list = dropdown.selected
                if list and not utility:IsInside(hoverData, list.objects.holder) then
                    dropdown:Close()
                end
                local color = window.colorpicker.selected
                if color and not utility:IsInside(hoverData, color.objects.holder) then
                    color:SetOpen(false)
                end
            end)

            dropdown:Refresh();

            -- drops down a few pixels while fading in (and jumps to the selected value)
            function window.dropdown:AnimateOpen()
                local anim = library.animations
                self:ScrollToSelected()
                self:Refresh()
                utility:SlideIn(self.objects.background, newUDim2(0,3,1,0), newUDim2(0,0,0,-anim.popupOffset), anim.popup)
                utility:FadeIn(self.objects.background, anim.popup)
            end

            function window.colorpicker:AnimateOpen()
                local anim = library.animations
                utility:SlideIn(self.objects.background, newUDim2(1,-200,1,10), newUDim2(0,0,0,-anim.popupOffset), anim.popup)
                utility:FadeIn(self.objects.background, anim.popup)
            end
        end
        -------------------------

        local function tooltip(option)
            utility:Connection(option.objects.holder.MouseEnter, function()
                tooltipObjects.background.Visible = (not (option.tooltip == '' or option.tooltip == nil)) and true or false;
                tooltipObjects.riskytext.Visible = option.risky;
                tooltipObjects.text.Position = option.risky and newUDim2(0,60,0,0) or newUDim2(0,3,0,0)
                tooltipObjects.text.Text = tostring(option.tooltip);
                library.CurrentTooltip = option;
            end)
            utility:Connection(option.objects.holder.MouseLeave, function()
                if library.CurrentTooltip == option then
                    library.CurrentTooltip = nil;
                    tooltipObjects.background.Visible = false
                end
            end)
        end


        local visValues = {};

        local fadeTime = .18;
        local openGeneration = 0;

        function window:SetOpen(bool)
            if typeof(bool) == 'boolean' then
                self.open = bool;
                openGeneration += 1;
                local generation = openGeneration;

                local objs = self.objects.background:GetDescendants()
                table.insert(objs, self.objects.background)

                if bool then
                    self.objects.background.Visible = true;
                    -- rise into place (restPosition is the dragged position, so spamming the key can't drift the window)
                    local anim = library.animations
                    local running = library.tweens[self.objects.background] and library.tweens[self.objects.background].Position
                    if not running then
                        self.restPosition = self.objects.background.Position
                    end
                    if self.restPosition then
                        utility:SlideIn(self.objects.background, self.restPosition, newUDim2(0, 0, 0, anim.windowOffset), anim.window)
                    end
                else
                    -- hide after the fade, unless the menu was reopened in the meantime
                    task.delay(fadeTime, function()
                        if generation == openGeneration and not window.open then
                            window.objects.background.Visible = false;
                        end
                    end)
                end

                for _,v in next, objs do
                    local obj = v.Object
                    if obj ~= nil then
                        if bool then
                            -- only restore things we faded out (fresh objects already have the right value)
                            if visValues[v] ~= nil then
                                utility:Tween(obj, 'Transparency', visValues[v], fadeTime, Enum.EasingDirection.Out, Enum.EasingStyle.Quad);
                                utility:SetRestingTransparency(obj, visValues[v]);
                                visValues[v] = nil;
                            end
                        elseif obj.Transparency ~= 0 then
                            -- remember the real value once, so spamming the keybind can't "lose" it mid-fade
                            if visValues[v] == nil then
                                visValues[v] = utility:GetRestingTransparency(obj);
                            end
                            utility:Tween(obj, 'Transparency', 0, fadeTime, Enum.EasingDirection.Out, Enum.EasingStyle.Quad);
                            utility:SetRestingTransparency(obj, visValues[v]);
                        end
                    end
                end
            end
        end

        function window:AddTab(text, order)
            local tab = {
                text = text;
                order = order or #self.tabs+1;
                callback = function() end;
                objects = {};
                sections = {};
            }

            table.insert(self.tabs, tab);

            --- Create Objects ---
            do
                local objs = tab.objects;
                local z = library.zindexOrder.window + 5;

                objs.background = utility:Draw('Square', {
                    Size = newUDim2(0,50,1,0);
                    Parent = self.objects.tabHolder;
                    ThemeColor = 'Unselected Tab Background';
                    ZIndex = z;
                })

                objs.innerBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border 1';
                    ZIndex = z-1;
                    Parent = objs.background;
                })
    
                objs.outerBorder = utility:Draw('Square', {
                    Size = newUDim2(1,2,1,2);
                    Position = newUDim2(0,-1,0,-1);
                    ThemeColor = 'Border 3';
                    ZIndex = z-2;
                    Parent = objs.innerBorder;
                })

                objs.topBorder = utility:Draw('Square', {
                    Size = newUDim2(1,0,0,1);
                    ThemeColor = 'Unselected Tab Background';
                    ZIndex = z+1;
                    Parent = objs.background;
                })

                objs.text = utility:Draw('Text', {
                    ThemeColor = 'Unselected Tab Text';
                    Text = text;
                    Size = 13;
                    Font = 2;
                    ZIndex = z+1;
                    Outline = true;
                    Center = true;
                    Parent = objs.background;
                })

                utility:Connection(objs.background.MouseButton1Down, function()
                    tab:Select();
                end)

            end
            ----------------------

            function tab:AddSection(text, side, order)
                local section = {
                    text = tostring(text);
                    side = side == nil and 1 or clamp(side,1,2);
                    order = order or #self.sections+1;
                    enabled = true;
                    objects = {};
                    options = {};
                };

                table.insert(self.sections, section);

                --- Create Objects ---
                do
                    local objs = section.objects;
                    local z = library.zindexOrder.window+15;

                    objs.background = utility:Draw('Square', {
                        ThemeColor = 'Section Background';
                        ZIndex = z;
                        Parent = window.objects['columnholder'..(section.side)];
                    })

                    objs.innerBorder = utility:Draw('Square', {
                        Size = newUDim2(1,2,1,1);
                        Position = newUDim2(0,-1,0,0);
                        ThemeColor = 'Border 3';
                        ZIndex = z-1;
                        Parent = objs.background;
                    })

                    objs.outerBorder = utility:Draw('Square', {
                        Size = newUDim2(1,2,1,1);
                        Position = newUDim2(0,-1,0,0);
                        ThemeColor = 'Border 1';
                        ZIndex = z-2;
                        Parent = objs.innerBorder;
                    })

                    objs.topBorder1 = utility:Draw('Square', {
                        Size = newUDim2(.025,1,0,1);
                        Position = newUDim2(0,-1,0,0);
                        ThemeColor = 'Accent';
                        ZIndex = z+1;
                        Parent = objs.background;
                    })

                    objs.topBorder2 = utility:Draw('Square', {
                        ThemeColor = 'Accent';
                        ZIndex = z+1;
                        Parent = objs.background;
                    })

                    objs.textlabel = utility:Draw('Text', {
                        Position = newUDim2(.0425,0,0,-7);
                        ThemeColor = 'Primary Text';
                        Size = 13;
                        Font = 2;
                        ZIndex = z+1;
                        Parent = objs.background;
                    })

                    objs.optionholder = utility:Draw('Square',{
                        Size = newUDim2(1-.03,0,1,-15);
                        Position = newUDim2(.015,0,0,13);
                        Transparency = 0;
                        ZIndex = z+1;
                        Parent = objs.background;
                    })
                    
                end
                ----------------------

                function section:SetText(text)
                    self.text = tostring(text);
                    self.objects.textlabel.Text = self.text;
                    local x = self.objects.background.Object.Size.X - self.objects.textlabel.TextBounds.X - 13
                    self.objects.topBorder2.Size = newUDim2(0, x, 0, 1)
                    self.objects.topBorder2.Position = newUDim2(1, 1 + -x, 0, 0)
                end

                function section:UpdateOptions()
                    table.sort(self.options, function(a,b)
                        return a.order < b.order
                    end)

                    local ySize, padding = 15, 0;
                    for i,option in next, self.options do
                        option.objects.holder.Visible = option.enabled
                        if option.enabled then
                            option.objects.holder.Position = newUDim2(0,0,0,ySize-15);
                            ySize += option.objects.holder.Object.Size.Y + padding;
                        end
                    end

                    self.objects.background.Size = newUDim2(1,0,0,ySize);

                end

                function section:SetEnabled(bool)
                    if typeof(bool) == 'boolean' then
                        section.enabled = bool;
                        tab:UpdateSections();
                    end
                end

                ------- Options -------

                -- // Toggle
                function section:AddToggle(data)
                    local toggle = {
                        class = 'toggle';
                        flag = data.flag;
                        text = '';
                        tooltip = '';
                        order = #self.options+1;
                        state = false;
                        risky = false;
                        keybind = false; -- true = adds a [NONE] keybind that flips this toggle
                        callback = function() end;
                        enabled = true;
                        options = {};
                        objects = {};
                    };

                    local blacklist = {'objects'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and toggle[i] ~= nil then
                            toggle[i] = v
                        end
                    end

                    -- accept the names other ui libs use for the starting state (default / value / toggled)
                    if typeof(data.state) ~= 'boolean' then
                        for _, alias in ipairs({'default', 'value', 'toggled'}) do
                            if typeof(data[alias]) == 'boolean' then
                                toggle.state = data[alias]
                                break
                            end
                        end
                    end

                    table.insert(self.options, toggle)

                    if toggle.flag then
                        library.flags[toggle.flag] = toggle.state;
                        library.options[toggle.flag] = toggle;
                    end

                    --- Create Objects ---
                    do
                        local objs = toggle.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,17);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(0,8,0,8);
                            Position = newUDim2(0,2,0,4);
                            ThemeColor = 'Option Background';
                            ZIndex = z+3;
                            Parent = objs.holder;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp45;
                            Transparency = .25;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.border1 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 1';
                            ZIndex = z+2;
                            Parent = objs.background;
                        })

                        objs.border2 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z+1;
                            Parent = objs.border1;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,19,0,1);
                            ThemeColor = 'Option Text 3';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        utility:Connection(objs.holder.MouseEnter, function()
                            objs.border1.ThemeColor = 'Accent';
                        end)

                        utility:Connection(objs.holder.MouseLeave, function()
                            objs.border1.ThemeColor = toggle.state and 'Accent' or 'Option Border 1';
                        end)

                        utility:Connection(objs.holder.MouseButton1Down, function()
                            toggle:SetState(not toggle.state);
                        end)

                    end
                    ----------------------

                    function toggle:SetState(bool, nocallback)
                        if typeof(bool) == 'boolean' then
                            self.state = bool;
                            if self.flag then
                                library.flags[self.flag] = bool;
                            end

                            self.objects.border1.ThemeColor = bool and 'Accent' or (self.objects.holder.Hover and 'Accent' or 'Option Border 1');
                            self.objects.text.ThemeColor = bool and (self.risky and 'Risky Text Enabled' or 'Option Text 1') or (self.risky and 'Risky Text' or 'Option Text 3');
                            self.objects.background.ThemeColor = bool and 'Accent' or 'Option Background';
                            self.objects.background.ThemeColorOffset = bool and -55 or 0

                            if not nocallback then
                                self.callback(bool);
                            end

                            if self.linkedBind then
                                self.linkedBind:RefreshIndicator();
                            end

                        end
                    end

                    function toggle:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                        end
                    end

                    function toggle:UpdateOptions()
                        table.sort(self.options, function(a,b)
                            return a.order < b.order
                        end)

                        local x, y = 0, 0
                        for i,option in next, self.options do
                            option.objects.holder.Visible = option.enabled
                            if option.enabled then
                                if option.class == 'color' or option.class == 'bind' then
                                    option.objects.holder.Position = newUDim2(1,-option.objects.holder.Object.Size.X-x,0,0);
                                    x = x + option.objects.holder.Object.Size.X;
                                elseif option.class == 'slider' or option.class == 'list' then
                                    option.objects.holder.Position = newUDim2(0,0,1,-option.objects.holder.Object.Size.Y-y);
                                    y = y + option.objects.holder.Object.Size.Y;
                                end
                            end
                        end

                        self.objects.holder.Size = newUDim2(1,0,0,17 + y);
                        section:UpdateOptions()

                    end

                    -- // Toggle Addons
                    function toggle:AddColor(data)
                        local color = {
                            class = 'color';
                            flag = data.flag;
                            text = '';
                            tooltip = '';
                            order = #self.options+1;
                            callback = function() end;
                            color = Color3.new(1,1,1);
                            trans = 0;
                            open = false;
                            enabled = true;
                            objects = {};
                        };
    
                        local blacklist = {'objects'};
                        for i,v in next, data do
                            if not table.find(blacklist, i) and color[i] ~= nil then
                                color[i] = v
                            end
                        end
                        
                        table.insert(self.options, color)
    
                        if color.flag then
                            library.flags[color.flag] = color.color;
                            library.options[color.flag] = color;
                        end
    
                        --- Create Objects ---
                        do
                            local objs = color.objects;
                            local z = library.zindexOrder.window+25;
    
                            objs.holder = utility:Draw('Square', {
                                Size = newUDim2(0,21,0,17);
                                Transparency = 0;
                                ZIndex = z+6;
                                Parent = self.objects.holder;
                            })
    
                            objs.background = utility:Draw('Square', {
                                Size = newUDim2(0,15,0,8);
                                Position = newUDim2(0,4,0,5);
                                ZIndex = z+3;
                                Parent = objs.holder;
                            })
    
                            objs.gradient = utility:Draw('Image', {
                                Size = newUDim2(1,0,1,0);
                                Data = library.images.gradientp45;
                                Transparency = .25;
                                ZIndex = z+4;
                                Parent = objs.background;
                            })
    
                            objs.border1 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 1';
                                ZIndex = z+2;
                                Parent = objs.background;
                            })
    
                            objs.border2 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 2';
                                ZIndex = z+1;
                                Parent = objs.border1;
                            })
    
                            utility:Connection(objs.holder.MouseEnter, function()
                                objs.border1.ThemeColor = 'Accent';
                            end)
    
                            utility:Connection(objs.holder.MouseLeave, function()
                                objs.border1.ThemeColor = color.open and 'Accent' or 'Option Border 1';
                            end)
    
                            utility:Connection(objs.holder.MouseButton1Down, function()
                                color:SetOpen(not color.open);
                            end)
    
                        end
                        ----------------------

    
                        function color:SetColor(c3, nocallback)
                            if typeof(c3) == 'Color3' then
                                local h,s,v = c3:ToHSV(); c3 = fromhsv(h, clamp(s,.005,.995), clamp(v,.005,.995))
                                self.color = c3;
                                self.objects.background.Color = c3;
                                if not nocallback then
                                    self.callback(c3, self.trans);
                                end
                                if self.open then
                                    window.colorpicker:Visualize(self.color, self.trans);
                                end
                                if self.flag then
                                    library.flags[self.flag] = c3;
                                end
                            end
                        end
    
                        function color:SetTrans(trans, nocallback)
                            if typeof(trans) == 'number' then
                                self.trans = trans;
                                if not nocallback then
                                    self.callback(self.color, trans);
                                end
                                if self.open then
                                    window.colorpicker:Visualize(self.color, self.trans);
                                end
                            end
                        end
    
                        function color:SetOpen(bool)
                            if typeof(bool) == 'boolean' then
                                self.open = bool
                                if bool then
                                    if window.colorpicker.selected then
                                        window.colorpicker.selected.open = false;
                                    end
                                    window.colorpicker.selected = color
                                    window.colorpicker.objects.background.Parent = self.objects.background;
                                    window.colorpicker.objects.background.Visible = true;
                                    window.colorpicker:Visualize(color.color, color.trans)
                                    window.colorpicker:AnimateOpen()
                                elseif window.colorpicker.selected == color then
                                    window.colorpicker.selected = nil;
                                    window.colorpicker.objects.background.Parent = window.objects.background;
                                    window.colorpicker.objects.background.Visible = false;
                                end
                            end
                        end
    
                        tooltip(color);
                        color:SetColor(color.color, true);
                        color:SetTrans(color.trans, true);
                        self:UpdateOptions();
                        return color
                    end

                    function toggle:AddBind(data)
                        local bind = {
                            class = 'bind';
                            flag = data.flag;
                            text = '';
                            tooltip = '';
                            bind = 'none';
                            mode = 'toggle';
                            order = #self.options+1;
                            callback = function() end;
                            keycallback = function() end;
                            indicatorValue = library.keyIndicator:AddValue({value = 'value', key = 'key', enabled = false});
                            noindicator = false;
                            invertindicator = false;
                            state = false;
                            nomouse = false;
                            enabled = true;
                            binding = false;
                            linked = false; -- true = the key flips this toggle, 'none' = unbound (see toggle:AddKeybind)
                            objects = {};
                        };
    
                        local blacklist = {'objects'};
                        for i,v in next, data do
                            if not table.find(blacklist, i) and bind[i] ~= nil then
                                bind[i] = v
                            end
                        end
                        
                        table.insert(self.options, bind)
    
                        if bind.flag then
                            library.options[bind.flag] = bind;
                        end

                        if bind.bind == 'none' and not bind.linked then
                            bind.state = true
                            if bind.flag then
                                library.flags[bind.flag] = bind.state;
                            end
                            bind.callback(true)
                            local display = bind.state; if bind.invertindicator then display = not bind.state; end
                            bind.indicatorValue:SetEnabled(display and not bind.noindicator);
                            bind.indicatorValue:SetKey((bind.text == nil or bind.text == '') and (bind.flag == nil and 'unknown' or bind.flag) or bind.text); -- this is so dumb
                            bind.indicatorValue:SetValue('[Always]');
                        end
    
                        --- Create Objects ---
                        do
                            local objs = bind.objects;
                            local z = library.zindexOrder.window+25;
    
                            objs.holder = utility:Draw('Square', {
                                Size = newUDim2(0,0,0,17);
                                Transparency = 0;
                                ZIndex = z+6;
                                Parent = self.objects.holder;
                            })
    
                            objs.keyText = utility:Draw('Text', {
                                ThemeColor = 'Option Text 3';
                                Size = 13;
                                Font = 2;
                                ZIndex = z+1;
                                Parent = objs.holder;
                            })
    
                            utility:Connection(objs.holder.MouseEnter, function()
                                objs.keyText.ThemeColor = 'Accent';
                            end)
    
                            utility:Connection(objs.holder.MouseLeave, function()
                                objs.keyText.ThemeColor = bind.binding and 'Accent' or 'Option Text 3';
                            end)
    
                            utility:Connection(objs.holder.MouseButton1Down, function()
                                if not bind.binding then
                                    bind:SetKeyText('...');
                                    bind.bindingStarted = os.clock();
                                    bind.binding = true;
                                end
                            end)
    
                        end
                        ----------------------
    
                        local c
                        function bind:SetBind(keybind)
                            if c then
                                c:Disconnect();
                                c = nil;
                                if bind.flag then
                                    library.flags[bind.flag] = false;
                                end
                                bind.callback(false);
                            end
                            local keyName = 'NONE'
                            -- false/nil means "cancelled" (blacklisted key), keep the previous bind
                            if keybind == 'none' or typeof(keybind) == 'EnumItem' then
                                self.bind = keybind
                            end
                            if self.bind == Enum.KeyCode.Backspace or self.bind == 'none' then
                                self.bind = 'none';
                                if not bind.linked then
                                    bind.state = true
                                    if bind.flag then
                                        library.flags[bind.flag] = bind.state;
                                    end
                                    self.callback(true)
                                    local display = bind.state; if bind.invertindicator then display = not bind.state; end
                                    bind.indicatorValue:SetEnabled(display and not bind.noindicator);
                                end
                            else
                                keyName = getKeyName(self.bind)
                            end
                            if self.bind ~= 'none' and not bind.linked then
                                bind.state = false
                                if bind.flag then
                                    library.flags[bind.flag] = bind.state;
                                end
                                self.callback(false)
                                local display = bind.state; if bind.invertindicator then display = not bind.state; end
                                bind.indicatorValue:SetEnabled(display and not bind.noindicator);
                            end
                            self.keycallback(self.bind);
                            self:SetKeyText(keyName:upper());
                            self.indicatorValue:SetKey((self.text == nil or self.text == '') and (self.flag == nil and 'unknown' or self.flag) or self.text); -- this is so dumb
                            self.indicatorValue:SetValue('['..keyName:upper()..']');
                            if self.bind == 'none' then
                                self.indicatorValue:SetValue('[Always]');
                            end
                            self.objects.keyText.ThemeColor = self.objects.holder.Hover and 'Accent' or 'Option Text 3';
                            self:RefreshIndicator();
                        end

                        -- linked binds show in the keybind list while their toggle is on and a key is set
                        function bind:RefreshIndicator()
                            if not self.linked then return end
                            self.indicatorValue:SetKey((toggle.text ~= nil and toggle.text ~= '') and toggle.text or (toggle.flag or 'unknown'));
                            self.indicatorValue:SetValue('['..getKeyName(self.bind):upper()..']');
                            self.indicatorValue:SetEnabled(toggle.state == true and self.bind ~= 'none' and not self.noindicator);
                        end
    
                        function bind:SetKeyText(str)
                            str = tostring(str);
                            self.objects.keyText.Text = '['..str..']';
                            self.objects.keyText.Position = newUDim2(0, 2, 0, 2);
                            self.objects.holder.Size = newUDim2(0,self.objects.keyText.TextBounds.X+2,0,17)
                            toggle:UpdateOptions();
                        end
    
                        utility:Connection(inputservice.InputBegan, function(inp)
                            if inputservice:GetFocusedTextBox() or library:IsTyping() then
                                return
                            elseif bind.binding then
                                -- ignore the same click that started binding
                                if inp.UserInputType == Enum.UserInputType.MouseButton1 and os.clock() - (bind.bindingStarted or 0) < 0.05 then
                                    return
                                end
                                local key = getInputKey(inp, bind.nomouse)
                                -- for toggle keybinds, left click cancels instead of binding (it would flip the toggle on every click)
                                if bind.linked and inp.UserInputType == Enum.UserInputType.MouseButton1 then
                                    key = false
                                end
                                bind:SetBind(key)
                                bind.binding = false
                            elseif bind.linked then
                                -- bound key flips the toggle it belongs to
                                if bind.bind ~= 'none' and (inp.KeyCode == bind.bind or inp.UserInputType == bind.bind) then
                                    toggle:SetState(not toggle.state);
                                end
                            elseif not bind.binding and bind.bind == 'none' then
                                bind.state = true
                                if bind.flag then
                                    library.flags[bind.flag] = bind.state
                                end
                                local display = bind.state; if bind.invertindicator then display = not bind.state; end
                                bind.indicatorValue:SetEnabled(display and not bind.noindicator)
                            elseif (inp.KeyCode == bind.bind or inp.UserInputType == bind.bind) and not bind.binding then
                                if bind.mode == 'toggle' then
                                    bind.state = not bind.state
                                    if bind.flag then
                                        library.flags[bind.flag] = bind.state;
                                    end
                                    bind.callback(bind.state)
                                    local display = bind.state; if bind.invertindicator then display = not bind.state; end
                                    bind.indicatorValue:SetEnabled(display and not bind.noindicator);
                                elseif bind.mode == 'hold' then
                                    if bind.flag then
                                        library.flags[bind.flag] = true;
                                    end
                                    bind.indicatorValue:SetEnabled((not bind.invertindicator and true or false) and not bind.noindicator);
                                    c = utility:Connection(runservice.RenderStepped, function()
                                        if bind.callback then
                                            bind.callback(true);
                                        end
                                    end)
                                end
                            end
                        end)
    
                        utility:Connection(inputservice.InputEnded, function(inp)
                            if bind.bind ~= 'none' then
                                if inp.KeyCode == bind.bind or inp.UserInputType == bind.bind then
                                    if c then
                                        c:Disconnect();
                                        c = nil;
                                        if bind.flag then
                                            library.flags[bind.flag] = false;
                                        end
                                        if bind.callback then
                                            bind.callback(false);
                                        end
                                        bind.indicatorValue:SetEnabled((bind.invertindicator and true or false) and not bind.noindicator);
                                    end
                                end
                            end
                        end)
    
                        tooltip(bind);
                        bind:SetBind(bind.bind);
                        self:UpdateOptions();
                        return bind
                    end

                    function toggle:AddSlider(data)
                        local slider = {
                            class = 'slider';
                            flag = data.flag;
                            suffix = '';
                            tooltip = '';
                            order = #self.options+1;
                            value = 0;
                            min = 0;
                            max = 100;
                            increment = 1;
                            callback = function() end;
                            enabled = true;
                            dragging = false;
                            focused = false;
                            objects = {};
                        };
    
                        local blacklist = {'objects', 'dragging'};
                        for i,v in next, data do
                            if not table.find(blacklist, i) and (slider[i] ~= nil and typeof(slider[i]) == typeof(v)) then
                                slider[i] = v;
                            end
                        end
                
                        table.insert(self.options, slider)

                        if slider.flag then
                            library.flags[slider.flag] = slider.value;
                            library.options[slider.flag] = slider;
                        end

                        --- Create Objects ---
                        do
                            local objs = slider.objects;
                            local z = library.zindexOrder.window+25;

                            objs.holder = utility:Draw('Square', {
                                Size = newUDim2(1,0,0,20);
                                Transparency = 0;
                                ZIndex = z+6;
                                Parent = toggle.objects.holder;
                            })

                            objs.background = utility:Draw('Square', {
                                Size = newUDim2(1,-4,1,-8);
                                Position = newUDim2(0,2,0,4);
                                ThemeColor = 'Option Background';
                                ZIndex = z+2;
                                Parent = objs.holder;
                            })

                            objs.slider = utility:Draw('Square', {
                                Size = newUDim2(0,0,1,0);
                                ThemeColor = 'Accent';
                                ZIndex = z+3;
                                Parent = objs.background;
                            })

                            objs.border1 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 1';
                                ZIndex = z+1;
                                Parent = objs.background;
                            })

                            objs.border2 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 2';
                                ZIndex = z;
                                Parent = objs.border1;
                            })
    
                            objs.gradient = utility:Draw('Image', {
                                Size = newUDim2(1,0,1,0);
                                Data = library.images.gradientp90;
                                Transparency = .65;
                                ZIndex = z+4;
                                Parent = objs.background;
                            })
    
                            objs.text = utility:Draw('Text', {
                                Position = newUDim2(.5,0,0,-1);
                                ThemeColor = 'Option Text 3';
                                Size = 13;
                                Font = 2;
                                ZIndex = z+5;
                                Outline = true;
                                Center = true;
                                Parent = objs.background;
                            })

                            utility:Connection(objs.holder.MouseEnter, function()
                                objs.border1.ThemeColor = 'Accent';
                            end)
    
                            utility:Connection(objs.holder.MouseLeave, function()
                                objs.border1.ThemeColor = slider.dragging and 'Accent' or 'Option Border 1';
                            end)
    
                            local c;
                            local inputNumber = '';
                            utility:Connection(slider.objects.holder.MouseButton1Down, function()
                                if inputservice:IsKeyDown(Enum.KeyCode.LeftControl) then
                                    if slider.focused then
                                        slider.focused = false;
                                        c:Disconnect();
                                    else
                                        objs.text.Text = tostring(slider.value)..tostring(slider.suffix)..'/'..tostring(slider.max)..tostring(slider.suffix)..' []';
                                        slider.focused = true;
                                        inputNumber = '';
                                        c = utility:Connection(inputservice.InputBegan, function(inp)
                                            if library.numberStrings[inp.KeyCode.Name] then
                                                local number = library.numberStrings[inp.KeyCode.Name];
                                                inputNumber = inputNumber..tostring(number);
                                                objs.text.Text = string.format("%.14g", slider.value) .. tostring(slider.suffix) .. "/" .. slider.max .. tostring(slider.suffix) .. " [" .. inputNumber .. "]";
                                            elseif inp.KeyCode == Enum.KeyCode.Backspace then
                                                inputNumber = inputNumber:sub(1,-2);
                                                objs.text.Text = string.format("%.14g", slider.value)..tostring(slider.suffix)..'/'..slider.max..tostring(slider.suffix)..' ['..inputNumber..']';
                                            elseif inp.KeyCode == Enum.KeyCode.Return then
                                                slider:SetValue(tonumber(inputNumber))
                                                slider.focused = false;
                                                c:Disconnect();
                                            elseif inp.KeyCode == Enum.KeyCode.Escape then
                                                slider:SetValue(slider.value, true)
                                                slider.focused = false;
                                                c:Disconnect();
                                            end
                                        end)
                                    end
                                else
                                    slider.dragging = true;
                                    library.draggingSlider = slider;
                                end
                            end)
    
                            utility:Connection(button1up, function()
                                objs.border1.ThemeColor = objs.holder.Hover and 'Accent' or 'Option Border 1';
                                slider.dragging = false;
                                library.draggingSlider = nil;
                            end)
    
                        end
                        ----------------------
    
                        function slider:SetValue(value, nocallback)
                            if typeof(value) == 'number' then
                                local newValue = snapToIncrement(value, self.increment, self.min, self.max);
                                local size, pos = self.objects.slider.Size, self.objects.slider.Position;
    
                                if self.min >= 0 then
                                    size, pos = sliderFill(self.min, self.max, newValue);
                                else
                                    size, pos = sliderFill(self.min, self.max, newValue);
                                    -- negative ranges fill outwards from 0 (handled in sliderFill)
                                end
    
                                utility:Tween(self.objects.slider, 'Size', size, .05, Enum.EasingDirection.Out, Enum.EasingStyle.Quad);
                                utility:Tween(self.objects.slider, 'Position', pos, .05, Enum.EasingDirection.Out, Enum.EasingStyle.Quad);
    
                                self.value = newValue;
                                if self.flag then
                                    library.flags[self.flag] = newValue;
                                end
                                self.objects.text.Text = string.format("%.14g",newValue)..tostring(self.suffix)..'/'..self.max..tostring(self.suffix);
                                self.objects.text.ThemeColor = (self.min < 0 and newValue == 0 or newValue == self.min)  and (self.risky and 'Risky Text' or 'Option Text 3') or (self.risky and 'Risky Text Enabled' or 'Option Text 1');
    
                                if not nocallback then
                                    self.callback(newValue);
                                end
    
                            end
                        end

                        tooltip(slider);
                        slider:SetValue(slider.value, true);
                        self:UpdateOptions();
                        return slider
                    end

                    function toggle:AddList(data)
                        local list = {
                            class = 'list';
                            flag = data.flag;
                            text = '';
                            selected = '';
                            tooltip = '';
                            order = #self.options+1;
                            callback = function() end;
                            enabled = true;
                            multi = false;
                            maxVisible = false; -- rows shown before scrolling (false = window default)
                            open = false;
                            values = {};
                            objects = {};
                        }
    
                        table.insert(self.options, list);
    
                        local blacklist = {'objects'};
                        for i,v in next, data do
                            if not table.find(blacklist, i) and list[i] ~= nil then
                                list[i] = v
                            end
                        end
    
                        if list.flag then
                            library.flags[list.flag] = list.selected;
                            library.options[list.flag] = list;
                        end
    
                        -- Create Objects --
                        do
                            local objs = list.objects;
                            local z = library.zindexOrder.window+25;
    
                            objs.holder = utility:Draw('Square', {
                                Size = newUDim2(1,0,0,22);
                                Transparency = 0;
                                ZIndex = z+6;
                                Parent = toggle.objects.holder;
                            })
    
                            objs.background = utility:Draw('Square', {
                                Size = newUDim2(1,-4,1,-8);
                                Position = newUDim2(0,2,0,4);
                                ThemeColor = 'Option Background';
                                ZIndex = z+2;
                                Parent = objs.holder;
                            })
    
                            objs.border1 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 1';
                                ZIndex = z+1;
                                Parent = objs.background;
                            })
    
                            objs.border2 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 2';
                                ZIndex = z;
                                Parent = objs.border1;
                            })
    
                            objs.gradient = utility:Draw('Image', {
                                Size = newUDim2(1,0,1,0);
                                Data = library.images.gradientp90;
                                Transparency = .65;
                                ZIndex = z+4;
                                Parent = objs.background;
                            })
    
                            objs.inputText = utility:Draw('Text', {
                                Position = newUDim2(0,4,0,0);
                                ThemeColor = 'Option Text 2';
                                Text = 'none',
                                Size = 13;
                                Font = 2;
                                ZIndex = z+5;
                                Outline = true;
                                Parent = objs.background;
                            })
    
                            objs.openText = utility:Draw('Text', {
                                Position = newUDim2(1,-10,0,0);
                                ThemeColor = 'Option Text 3';
                                Text = '+';
                                Size = 13;
                                Font = 2;
                                ZIndex = z+5;
                                Outline = true;
                                Parent = objs.background;
                            })
    
                            utility:Connection(objs.holder.MouseEnter, function()
                                objs.border1.ThemeColor = 'Accent';
                            end)
    
                            utility:Connection(objs.holder.MouseLeave, function()
                                objs.border1.ThemeColor = 'Option Border 1';
                            end)
    
                            utility:Connection(objs.holder.MouseButton1Down, function()
                                if list.open then
                                    list.open = false;
                                    objs.openText.Text = '+';
                                    if window.dropdown.selected == list then
                                        window.dropdown.selected = nil;
                                        window.dropdown.objects.background.Visible = false;
                                    end
                                else
                                    if window.dropdown.selected ~= nil then
                                        window.dropdown.selected.open = false
                                    end
                                    list.open = true;
                                    objs.openText.Text = '-';
                                    window.dropdown.selected = list;
                                    window.dropdown.objects.background.Visible = true;
                                    window.dropdown.objects.background.Parent = objs.holder;
                                    window.dropdown:Refresh();
                                    window.dropdown:AnimateOpen();
                                end
                            end)
    
    
                        end
                        --------------------
    
                        function list:Select(option, nocallback)
                            option = typeof(option) == 'table' and (self.multi == true and option or (#option == 0 and nil or option[1])) or self.multi == true and {option} or option;
                            if option ~= nil then
                                self.selected = option;
                                local text = typeof(option) == 'table' and (#option == 0 and "none" or table.concat(option, ', ')) or tostring(option);
                                local label = self.objects.inputText
                                label.Text = text;
                                if label.TextBounds.X > self.objects.background.Object.Size.X - 10 then
                                    local split = text:split('');
                                    for i = 1,#split do
                                        label.Text = table.concat(split, '', 1, i)
                                        if label.TextBounds.X > self.objects.background.Object.Size.X - 10 then
                                            label.Text = label.Text:sub(1,-6)..'...';
                                            break
                                        end
                                    end
                                end
                                if self.flag then
                                    library.flags[self.flag] = self.selected
                                end
                                if not nocallback then
                                    self.callback(self.selected);
                                end
                            end
                        end
    
                        function list:AddValue(value)
                            table.insert(list.values, tostring(value));
                            if window.dropdown.selected == list then
                                window.dropdown:Refresh()
                            end
                        end
    
                        function list:RemoveValue(value)
                            if table.find(list.values, value) then
                                table.remove(list.values, table.find(list.values, value));
                                if window.dropdown.selected == list then
                                    window.dropdown:Refresh()
                                end
                            end
                        end
    
                        function list:ClearValues()
                            table.clear(list.values);
                            if window.dropdown.selected == list then
                                window.dropdown:Refresh()
                            end
                        end
    
                        tooltip(list);
                        list:Select((data.value or data.selected) or (list.multi and 'none' or list.values[1]), true);
                        self:UpdateOptions();
                        return list
                    end

                    -- keybind that flips the toggle. starts as [NONE]; click it, press a key, Backspace clears it.
                    -- the bind is saved in configs as '<flag>_bind'
                    function toggle:AddKeybind(bindData)
                        if self.linkedBind then
                            return self.linkedBind
                        end
                        bindData = typeof(bindData) == 'table' and bindData or {}
                        self.linkedBind = self:AddBind({
                            linked = true,
                            bind = bindData.bind or 'none',
                            flag = bindData.flag or (self.flag and self.flag..'_bind') or nil,
                            nomouse = bindData.nomouse == true,
                            noindicator = bindData.noindicator == true,
                            tooltip = bindData.tooltip or '',
                        })
                        return self.linkedBind
                    end

                    tooltip(toggle);
                    toggle:SetText(toggle.text);
                    -- starting look is applied instantly (no color easing), so a default-on toggle
                    -- always shows its checkmark even if another animation interrupts
                    do
                        local objs = toggle.objects
                        local animated = {objs.background, objs.border1, objs.text}
                        for _, d in ipairs(animated) do d.ColorTween = 0 end
                        toggle:SetState(toggle.state, true);
                        for _, d in ipairs(animated) do d.ColorTween = library.animations.color end
                    end
                    if toggle.keybind then
                        toggle:AddKeybind(typeof(data.keybind) == 'table' and data.keybind or nil);
                    end

                    -- tracked so Unload can switch everything off (see library:Unload)
                    library.allToggles = library.allToggles or {};
                    table.insert(library.allToggles, toggle);

                    -- a toggle that starts on actually runs its callback, so the feature matches the checkmark.
                    -- deferred so the rest of the script (other options, variables) exists first
                    if toggle.state == true then
                        task.defer(function()
                            if toggle.state == true and library.hasInit and not toggle.startupFired then
                                toggle.startupFired = true;
                                local ok, err = pcall(toggle.callback, true);
                                if not ok then
                                    log('toggle callback error ('..tostring(toggle.text)..'): '..tostring(err));
                                end
                            end
                        end)
                    end

                    self:UpdateOptions();
                    return toggle
                end

                -- // Slider
                function section:AddSlider(data)
                    local slider = {
                        class = 'slider';
                        flag = data.flag;
                        text = '';
                        tooltip = '';
                        suffix = '';
                        order = #self.options+1;
                        value = 0;
                        min = 0;
                        max = 100;
                        increment = 1;
                        callback = function() end;
                        enabled = true;
                        dragging = false;
                        focused = false;
                        risky = false;
                        objects = {};
                    };

                    local blacklist = {'objects', 'dragging'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and (slider[i] ~= nil and typeof(slider[i]) == typeof(v)) then
                            slider[i] = v;
                        end
                    end
                    
                    table.insert(self.options, slider)

                    if slider.flag then
                        library.flags[slider.flag] = slider.value;
                        library.options[slider.flag] = slider;
                    end

                    --- Create Objects ---
                    do
                        local objs = slider.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,32);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-4,0,11);
                            Position = newUDim2(0,2,1,-14);
                            ThemeColor = 'Option Background';
                            ZIndex = z+2;
                            Parent = objs.holder;
                        })

                        objs.slider = utility:Draw('Square', {
                            Size = newUDim2(0,0,1,0);
                            ThemeColor = 'Accent';
                            ZIndex = z+3;
                            Parent = objs.background;
                        })

                        objs.border1 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 1';
                            ZIndex = z+1;
                            Parent = objs.background;
                        })

                        objs.border2 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z;
                            Parent = objs.border1;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp90;
                            Transparency = .65;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,2,0,1);
                            ThemeColor = 'Option Text 3';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        objs.plusDetector = utility:Draw('Square', {
                            Size = newUDim2(0,14,0,14);
                            Position = newUDim2(1,-28,0,1);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = objs.holder;
                        })

                        objs.minusDetector = utility:Draw('Square', {
                            Size = newUDim2(0,14,0,14);
                            Position = newUDim2(1,-14,0,1);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = objs.holder;
                        })

                        objs.plusText = utility:Draw('Text', {
                            Position = newUDim2(.5,0,0,-1);
                            ThemeColor = 'Option Text 3';
                            Text = '+';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+4;
                            Center = true;
                            Outline = true;
                            Parent = objs.plusDetector;
                        })

                        objs.minusText = utility:Draw('Text', {
                            Position = newUDim2(.5,0,0,-1);
                            ThemeColor = 'Option Text 3';
                            Text = '-';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+4;
                            Center = true;
                            Outline = true;
                            Parent = objs.minusDetector;
                        })

                        utility:Connection(objs.holder.MouseEnter, function()
                            objs.border1.ThemeColor = 'Accent';
                        end)

                        utility:Connection(objs.holder.MouseLeave, function()
                            objs.border1.ThemeColor = slider.dragging and 'Accent' or 'Option Border 1';
                        end)

                        utility:Connection(slider.objects.plusDetector.MouseButton1Down,function()
                            slider:SetValue(slider.value + (inputservice:IsKeyDown(Enum.KeyCode.LeftShift) and 10 or slider.increment))
                        end)
    
                        utility:Connection(slider.objects.minusDetector.MouseButton1Down,function()
                            slider:SetValue(slider.value - (inputservice:IsKeyDown(Enum.KeyCode.LeftShift) and 10 or slider.increment))
                        end)


                        local c;
                        local inputNumber = '';
                        utility:Connection(slider.objects.holder.MouseButton1Down, function()
                            if inputservice:IsKeyDown(Enum.KeyCode.LeftControl) then
                                if slider.focused then
                                    slider.focused = false;
                                    c:Disconnect();
                                else
                                    objs.text.Text = slider.text..': '..tostring(slider.value)..tostring(slider.suffix)..' []';
                                    slider.focused = true;
                                    inputNumber = '';
                                    c = utility:Connection(inputservice.InputBegan, function(inp)
                                        if library.numberStrings[inp.KeyCode.Name] then
                                            local number = library.numberStrings[inp.KeyCode.Name];
                                            inputNumber = inputNumber..tostring(number);
                                            objs.text.Text = slider.text..': '..string.format("%.14g",slider.value)..tostring(slider.suffix)..' ['..inputNumber..']';
                                        elseif inp.KeyCode == Enum.KeyCode.Backspace then
                                            inputNumber = inputNumber:sub(1,-2);
                                            objs.text.Text = slider.text..': '..string.format("%.14g",slider.value)..tostring(slider.suffix)..' ['..inputNumber..']';
                                        elseif inp.KeyCode == Enum.KeyCode.Return then
                                            slider:SetValue(tonumber(inputNumber))
                                            slider.focused = false;
                                            c:Disconnect();
                                        elseif inp.KeyCode == Enum.KeyCode.Escape then
                                            slider:SetValue(slider.value, true)
                                            slider.focused = false;
                                            c:Disconnect();
                                        end
                                    end)

                                end


                            else
                                slider.dragging = true;
                                library.draggingSlider = slider;
                            end
                        end)

                        utility:Connection(button1up, function()
                            objs.border1.ThemeColor = objs.holder.Hover and 'Accent' or 'Option Border 1';
                            slider.dragging = false;
                            library.draggingSlider = nil;
                        end)

                    end
                    ----------------------

                    function slider:SetValue(value, nocallback)
                        if typeof(value) == 'number' then
                            local newValue = snapToIncrement(value, self.increment, self.min, self.max);
                            local size, pos = self.objects.slider.Size, self.objects.slider.Position;

                            if self.min >= 0 then
                                size, pos = sliderFill(self.min, self.max, newValue);
                            else
                                size, pos = sliderFill(self.min, self.max, newValue);
                                -- negative ranges fill outwards from 0 (handled in sliderFill)
                            end

                            utility:Tween(self.objects.slider, 'Size', size, .05, Enum.EasingDirection.Out, Enum.EasingStyle.Quad);
                            utility:Tween(self.objects.slider, 'Position', pos, .05, Enum.EasingDirection.Out, Enum.EasingStyle.Quad);

                            self.value = newValue;
                            if self.flag then
                                library.flags[self.flag] = newValue;
                            end
                            self.objects.text.Text = slider.text..': '..string.format("%.14g",newValue)..tostring(self.suffix);
                            self.objects.text.ThemeColor = (self.min < 0 and newValue == 0 or newValue == self.min)  and (self.risky and 'Risky Text' or 'Option Text 3') or (self.risky and 'Risky Text Enabled' or 'Option Text 1');

                            if not nocallback then
                                self.callback(newValue);
                            end

                        end
                    end

                    function slider:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str..': '..tostring(self.value)..tostring(self.suffix);
                        end
                    end

                    tooltip(slider);
                    slider:SetText(slider.text);
                    slider:SetValue(slider.value, true);
                    self:UpdateOptions();
                    return slider
                end

                -- // Button
                function section:AddButton(data)
                    local button = {
                        class = 'button';
                        flag = data.flag;
                        text = '';
                        suffix = '';
                        tooltip = '';
                        order = #self.options+1;
                        callback = function() end;
                        confirm = false;
                        enabled = true;
                        risky = false;
                        objects = {};
                        subbuttons = {};
                    };

                    local blacklist = {'objects'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and button[i] ~= nil then
                            button[i] = v;
                        end
                    end
        
                    table.insert(self.options, button)

                    if button.flag then
                        library.options[button.flag] = button;
                    end

                    --- Create Objects ---
                    do
                        local objs = button.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,22);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-4,0,14);
                            Position = newUDim2(0,2,0,4);
                            ThemeColor = 'Option Background';
                            ZIndex = z+2;
                            Parent = objs.holder;
                        })

                        objs.border1 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 1';
                            ZIndex = z+1;
                            Parent = objs.background;
                        })

                        objs.border2 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z;
                            Parent = objs.border1;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp90;
                            Transparency = .65;
                            ZIndex = z+3;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(.5,0,0,0);
                            ThemeColor = 'Option Text 3';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+4;
                            Outline = true;
                            Center = true;
                            Parent = objs.background;
                        })

                        utility:Connection(objs.holder.MouseEnter, function()
                            objs.border1.ThemeColor = 'Accent';
                        end)

                        utility:Connection(objs.holder.MouseLeave, function()
                            objs.border1.ThemeColor = 'Option Border 1';
                            objs.text.ThemeColor = button.risky and 'Risky Text' or 'Option Text 3';
                            objs.background.ThemeColor = 'Option Background';
                            objs.background.ThemeColorOffset = 0;
                        end)

                        utility:Connection(objs.holder.MouseButton1Up, function()
                            objs.text.ThemeColor = button.risky and 'Risky Text' or  'Option Text 3';
                            objs.background.ThemeColor = 'Option Background';
                            objs.background.ThemeColorOffset = 0;
                        end)

                        local clicked, counting = false, false
                        utility:Connection(objs.holder.MouseButton1Down, function()
                            objs.text.ThemeColor = button.risky and 'Risky Text Enabled' or 'Option Text 2';
                            objs.background.ThemeColor = 'Accent';
                            objs.background.ThemeColorOffset = -95;

                            task.spawn(function() -- this is ugly and i do not care :)
                                if button.confirm then
                                    if clicked then
                                        clicked = false
                                        counting = false
                                        objs.text.Text = button.text
                                        button.callback()
                                    else
                                        clicked = true
                                        counting = true
                                        for i = 3,1,-1 do
                                            if not counting then
                                                break
                                            end
                                            objs.text.Text = 'Confirm '..button.text..'? '..tostring(i)
                                            task.wait(1)
                                        end
                                        clicked = false
                                        counting = false
                                        objs.text.Text = button.text
                                    end
                                else
                                    button.callback()
                                end
                            end)

                        end)

                    end
                    ----------------------
                    function button:AddButton(data)
                        local button = {
                            class = 'button';
                            flag = data.flag;
                            text = '';
                            suffix = '';
                            tooltip = '';
                            order = #self.subbuttons+1;
                            callback = function() end;
                            confirm = false;
                            enabled = true;
                            objects = {};
                        };
    
                        local blacklist = {'objects'};
                        for i,v in next, data do
                            if not table.find(blacklist, i) and button[i] ~= nil then
                                button[i] = v;
                            end
                        end
            
                        table.insert(self.subbuttons, button)
    
                        if button.flag then
                            library.options[button.flag] = button;
                        end
    
                        --- Create Objects ---
                        do
                            local objs = button.objects;
                            local z = library.zindexOrder.window+25;
    
                            objs.holder = utility:Draw('Square', {
                                Size = newUDim2(1,0,1,0);
                                Transparency = 0;
                                ZIndex = z+5;
                                Parent = self.objects.holder;
                            })
    
                            objs.background = utility:Draw('Square', {
                                Size = newUDim2(1,-4,1,-8);
                                Position = newUDim2(0,2,0,4);
                                ThemeColor = 'Option Background';
                                ZIndex = z+2;
                                Parent = objs.holder;
                            })
    
                            objs.border1 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 1';
                                ZIndex = z+1;
                                Parent = objs.background;
                            })
    
                            objs.border2 = utility:Draw('Square', {
                                Size = newUDim2(1,2,1,2);
                                Position = newUDim2(0,-1,0,-1);
                                ThemeColor = 'Option Border 2';
                                ZIndex = z;
                                Parent = objs.border1;
                            })
    
                            objs.gradient = utility:Draw('Image', {
                                Size = newUDim2(1,0,1,0);
                                Data = library.images.gradientp90;
                                Transparency = .65;
                                ZIndex = z+3;
                                Parent = objs.background;
                            })
    
                            objs.text = utility:Draw('Text', {
                                Position = newUDim2(.5,0,0,0);
                                ThemeColor = 'Option Text 3';
                                Size = 13;
                                Font = 2;
                                ZIndex = z+4;
                                Outline = true;
                                Center = true;
                                Parent = objs.background;
                            })
    
                            utility:Connection(objs.holder.MouseEnter, function()
                                objs.border1.ThemeColor = 'Accent';
                            end)
    
                            utility:Connection(objs.holder.MouseLeave, function()
                                objs.border1.ThemeColor = 'Option Border 1';
                                objs.text.ThemeColor = button.risky and 'Risky Text' or 'Option Text 3';
                                objs.background.ThemeColor = 'Option Background';
                                objs.background.ThemeColorOffset = 0;
                            end)
    
                            utility:Connection(objs.holder.MouseButton1Up, function()
                                objs.text.ThemeColor = button.risky and 'Risky Text' or 'Option Text 3';
                                objs.background.ThemeColor = 'Option Background';
                                objs.background.ThemeColorOffset = 0;
                            end)
    
                            local clicked, counting = false, false
                            utility:Connection(objs.holder.MouseButton1Down, function()
                                objs.text.ThemeColor = button.risky and 'Risky Text Enabled' or 'Option Text 2';
                                objs.background.ThemeColor = 'Accent';
                                objs.background.ThemeColorOffset = -95;
    
                                task.spawn(function() -- this is ugly and i do not care :)
                                    if button.confirm then
                                        if clicked then
                                            clicked = false
                                            counting = false
                                            objs.text.Text = button.text
                                            button.callback()
                                        else
                                            clicked = true
                                            counting = true
                                            for i = 3,1,-1 do
                                                if not counting then
                                                    break
                                                end
                                                objs.text.Text = 'Confirm '..button.text..'? '..tostring(i)
                                                task.wait(1)
                                            end
                                            clicked = false
                                            counting = false
                                            objs.text.Text = button.text
                                        end
                                    else
                                        button.callback()
                                    end
                                end)
    
                            end)
    
                        end
                        ----------------------
    
                        function button:SetText(str)
                            if typeof(str) == 'string' then
                                self.text = str;
                                self.objects.text.Text = str;
                            end
                        end
    
                        tooltip(button);
                        button:SetText(button.text);
                        self:UpdateOptions();
                        return button
                    end
                    ----------------------

                    function button:UpdateOptions() -- this so dumb XD
                        local buttons = 1 + #self.subbuttons;
                        local buttonSize = (1 / buttons) - .005;
                        self.objects.background.Size = newUDim2(buttonSize,-4,0,14);
                        for i,v in next, self.subbuttons do
                            v.objects.holder.Size = newUDim2(buttonSize,0,1,0);
                            v.objects.holder.Position = newUDim2(i * buttonSize + .01, 0, 0, 0)
                        end
                    end

                    function button:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                        end
                    end

                    tooltip(button);
                    button:SetText(button.text);
                    self:UpdateOptions();
                    return button
                end

                -- // Separator
                function section:AddSeparator(data)
                    local separator = {
                        class = 'separator';
                        flag = data.flag;
                        text = '';
                        order = #self.options+1;
                        enabled = true;
                        objects = {};
                    };

                    local blacklist = {'objects', 'dragging'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and (separator[i] ~= nil and typeof(separator[i]) == typeof(v)) then
                            separator[i] = v;
                        end
                    end
        
                    table.insert(self.options, separator)

                    --- Create Objects ---
                    do
                        local objs = separator.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,18);
                            Transparency = 0;
                            ZIndex = z;
                            Parent = section.objects.optionholder;
                        })

                        objs.line1 = utility:Draw('Square', {
                            Position = newUDim2(0,0,0,1);
                            ThemeColor = 'Option Background';
                            ZIndex = z+1;
                            Parent = objs.holder;
                        })

                        objs.line2 = utility:Draw('Square', {
                            Position = newUDim2(0,0,0,1);
                            ThemeColor = 'Option Background';
                            ZIndex = z+1;
                            Parent = objs.holder;
                        })

                        objs.border1 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z;
                            Parent = objs.line1;
                        })

                        objs.border2 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z;
                            Parent = objs.line2;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(.5,0,0,1);
                            ThemeColor = 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z;
                            Outline = true;
                            Center = true;
                            Parent = objs.holder;
                        })

                    end
                    ----------------------

                    function separator:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                            local xScale = ( 1- utility:ConvertNumberRange(self.objects.text.TextBounds.X, 0, self.objects.holder.Object.Size.X, 0, 1)) / 2 - (str == '' and 0 or .04)
                            self.objects.line1.Size = newUDim2(xScale, 0, 0, 1)
                            self.objects.line2.Size = newUDim2(xScale, 0, 0, 1)
                            self.objects.line1.Position = newUDim2(0,1,.5,-1)
                            self.objects.line2.Position = newUDim2(1 - self.objects.line2.Size.X.Scale,-1,.5,-1)
                        end
                    end

                    separator:SetText(separator.text);
                    self:UpdateOptions();
                    return separator
                end

                -- // Color Picker
                function section:AddColor(data)
                    local color = {
                        class = 'color';
                        flag = data.flag;
                        text = '';
                        tooltip = '';
                        order = #self.options+1;
                        callback = function() end;
                        color = Color3.new(1,1,1);
                        trans = 0;
                        open = false;
                        enabled = true;
                        risky = false;
                        objects = {};
                    };

                    local blacklist = {'objects'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and color[i] ~= nil then
                            color[i] = v
                        end
                    end
                    
                    table.insert(self.options, color)

                    if color.flag then
                        library.flags[color.flag] = color.color;
                        library.options[color.flag] = color;
                    end

                    --- Create Objects ---
                    do
                        local objs = color.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,19);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(0,15,0,8);
                            Position = newUDim2(1,-16,0,5);
                            ZIndex = z+3;
                            Parent = objs.holder;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp45;
                            Transparency = .25;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.border1 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 1';
                            ZIndex = z+2;
                            Parent = objs.background;
                        })

                        objs.border2 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z+1;
                            Parent = objs.border1;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,2,0,2);
                            ThemeColor = color.risky and 'Risky Text Enabled' or 'Option Text 3';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        utility:Connection(objs.holder.MouseEnter, function()
                            objs.border1.ThemeColor = 'Accent';
                        end)

                        utility:Connection(objs.holder.MouseLeave, function()
                            objs.border1.ThemeColor = color.open and 'Accent' or 'Option Border 1';
                        end)

                        utility:Connection(objs.holder.MouseButton1Down, function()
                            color:SetOpen(not color.open);
                        end)

                    end
                    ----------------------

                    function color:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                        end
                    end

                    function color:SetColor(c3, nocallback)
                        if typeof(c3) == 'Color3' then
                            local h,s,v = c3:ToHSV(); c3 = fromhsv(h, clamp(s,.005,.995), clamp(v,.005,.995));
                            self.color = c3;
                            self.objects.background.Color = c3;
                            if not nocallback then
                                self.callback(c3, self.trans);
                            end
                            if self.open then
                                window.colorpicker:Visualize(self.color, self.trans);
                            end
                            if self.flag then
                                library.flags[self.flag] = c3;
                            end
                        end
                    end

                    function color:SetTrans(trans, nocallback)
                        if typeof(trans) == 'number' then
                            self.trans = trans;
                            if not nocallback then
                                self.callback(self.color, trans);
                            end
                            if self.open then
                                window.colorpicker:Visualize(self.color, self.trans);
                            end
                        end
                    end

                    function color:SetOpen(bool)
                        if typeof(bool) == 'boolean' then
                            self.open = bool
                            if bool then
                                if window.colorpicker.selected then
                                    window.colorpicker.selected.open = false;
                                end
                                window.colorpicker.selected = color
                                window.colorpicker.objects.background.Parent = self.objects.background;
                                window.colorpicker.objects.background.Visible = true;
                                window.colorpicker:Visualize(color.color, color.trans)
                                window.colorpicker:AnimateOpen()
                            elseif window.colorpicker.selected == color then
                                window.colorpicker.selected = nil;
                                window.colorpicker.objects.background.Parent = window.objects.background;
                                window.colorpicker.objects.background.Visible = false;
                            end
                        end
                    end

                    tooltip(color);
                    color:SetText(color.text);
                    color:SetColor(color.color, true);
                    color:SetTrans(color.trans, true);
                    self:UpdateOptions();
                    return color
                end

                -- // Text Box
                function section:AddBox(data)
                    local box = {
                        class = 'box';
                        flag = data.flag;
                        text = '';
                        input = '';
                        order = #self.options+1;
                        callback = function() end;
                        enabled = true;
                        focused = false;
                        risky = false;
                        objects = {};
                    };

                    local blacklist = {'objects', 'dragging'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and box[i] ~= nil then
                            box[i] = v;
                        end
                    end
                    
                    table.insert(self.options, box)

                    if box.flag then
                        library.flags[box.flag] = box.input;
                        library.options[box.flag] = box;
                    end

                    --- Create Objects ---
                    do
                        local objs = box.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,37);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-4,0,15);
                            Position = newUDim2(0,2,1,-17);
                            ThemeColor = 'Option Background';
                            ZIndex = z+2;
                            Parent = objs.holder;
                        })

                        objs.border1 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 1';
                            ZIndex = z+1;
                            Parent = objs.background;
                        })

                        objs.border2 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z;
                            Parent = objs.border1;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp90;
                            Transparency = .65;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,2,0,2);
                            ThemeColor = box.risky and 'Risky Text Enabled' or 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        objs.inputText = utility:Draw('Text', {
                            Position = newUDim2(0,2,0,0);
                            ThemeColor = 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+5;
                            Outline = true;
                            Parent = objs.background;
                        })

                        utility:Connection(objs.holder.MouseEnter, function()
                            objs.border1.ThemeColor = 'Accent';
                        end)

                        utility:Connection(objs.holder.MouseLeave, function()
                            objs.border1.ThemeColor = 'Option Border 1';
                        end)

                        -- click to type (ctrl + click starts with an empty box). clicking it again while typing keeps typing.
                        utility:Connection(objs.holder.MouseButton1Down, function()
                            if not box.focused then
                                box:CaptureFocus(inputservice:IsKeyDown(Enum.KeyCode.LeftControl));
                            end
                        end)

                    end
                    ----------------------

                    function box:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                        end
                    end

                    -- draws `str` in the box; long text shows its end so what you're typing stays visible.
                    -- caret (1-based like TextBox.CursorPosition) draws a | at that spot
                    local function render(str, caret)
                        local label = box.objects.inputText
                        local shown = str
                        if caret and caret >= 1 then
                            caret = math.clamp(caret, 1, #str + 1)
                            shown = str:sub(1, caret - 1)..'|'..str:sub(caret)
                        end
                        local maxWidth = box.objects.background.Object.Size.X - 6
                        label.Text = shown
                        if label.TextBounds.X > maxWidth then
                            -- too long: split into whole characters (so emoji / accents never get cut in half),
                            -- cut from the right while the caret stays visible, then from the left
                            local chars, caretChar = {}, nil
                            local bytePos = 1
                            for ch in shown:gmatch(utf8.charpattern) do
                                table.insert(chars, ch)
                                if caret and bytePos == caret then
                                    caretChar = #chars
                                end
                                bytePos += #ch
                            end
                            local first, last = 1, #chars
                            local keep = caretChar or #chars
                            local function fits()
                                label.Text = table.concat(chars, '', first, last)
                                return label.TextBounds.X <= maxWidth
                            end
                            while not fits() and last > keep do
                                last -= 1
                            end
                            while not fits() and first < last do
                                first += 1
                            end
                        end
                    end

                    function box:SetInput(str, nocallback)
                        if typeof(str) == 'string' then
                            self.input = str;
                            render(str);
                            if not nocallback then
                                self.callback(str);
                            end
                            if self.flag then
                                library.flags[self.flag] = str;
                            end
                        end
                    end

                    -- // Typing
                    -- a hidden real Roblox TextBox (library.inputBox) does the typing, so every character, shift,
                    -- keyboard layouts, arrow keys, Ctrl+A / Ctrl+C / Ctrl+V and Ctrl+Backspace all work natively.
                    -- the drawing just mirrors its text with a | caret.
                    -- Enter or clicking away = apply, Escape = cancel.
                    local conns = {}
                    local input = box.input;

                    local function disconnectAll()
                        for _, conn in ipairs(conns) do
                            conn:Disconnect()
                        end
                        table.clear(conns)
                    end

                    function box:CaptureFocus(clear)
                        local tb = library.inputBox
                        if tb == nil then return end

                        -- only one box types at a time
                        if library.activeBox and library.activeBox ~= box then
                            library.activeBox:ReleaseFocus(true)
                        end

                        disconnectAll()
                        box.focused = true
                        library.activeBox = box
                        library.focusedBox = box -- keybinds ignore keys while typing
                        input = clear and '' or box.input -- stay in sync with SetInput / config loads
                        self.objects.inputText.ThemeColor = 'Option Text 1'

                        -- sit the real TextBox over the drawn one (keeps IME / emoji popups in the right spot)
                        local data = library.drawings[self.objects.background.Object]
                        if data then
                            tb.Position = UDim2.fromOffset(data.AbsolutePosition.X, data.AbsolutePosition.Y)
                            tb.Size = UDim2.fromOffset(math.max(data.AbsoluteSize.X, 10), math.max(data.AbsoluteSize.Y, 10))
                        end
                        tb.Text = input

                        local function refresh()
                            if box.focused then
                                render(input, tb.CursorPosition)
                            end
                        end

                        table.insert(conns, tb:GetPropertyChangedSignal('Text'):Connect(function()
                            if not box.focused then return end
                            -- single line only (pasted text with newlines gets flattened)
                            local text = tb.Text
                            if text:find('[\r\n]') then
                                text = text:gsub('[\r\n]+', ' ')
                                tb.Text = text
                                return
                            end
                            input = text
                            refresh()
                        end))
                        table.insert(conns, tb:GetPropertyChangedSignal('CursorPosition'):Connect(refresh))

                        -- Ctrl+C with nothing selected copies the whole box (the selection itself isn't drawn)
                        table.insert(conns, inputservice.InputBegan:Connect(function(inp)
                            if box.focused and inp.KeyCode == Enum.KeyCode.C
                                and (inputservice:IsKeyDown(Enum.KeyCode.LeftControl) or inputservice:IsKeyDown(Enum.KeyCode.RightControl))
                                and (tb.SelectionStart == -1 or tb.SelectionStart == tb.CursorPosition) then
                                setclip(input)
                            end
                        end))

                        table.insert(conns, tb.FocusLost:Connect(function(enterPressed, causedBy)
                            if not box.focused then return end
                            local escaped = causedBy and causedBy.KeyCode == Enum.KeyCode.Escape
                            box:ReleaseFocus(not escaped, enterPressed)
                        end))

                        tb:CaptureFocus()
                        task.defer(function()
                            if box.focused then
                                tb.CursorPosition = #tb.Text + 1
                                refresh()
                            end
                        end)
                        refresh()
                    end

                    -- apply: keep the typed text. force: fire the callback even if the text didn't change (Enter)
                    function box:ReleaseFocus(apply, force)
                        if not box.focused then return end
                        box.focused = false;
                        disconnectAll()

                        if library.focusedBox == box then
                            library.focusedBox = nil;
                            -- remembered so the Enter/Escape that closed the box doesn't also trigger a bind
                            library.boxReleasedAt = os.clock();
                        end
                        if library.activeBox == box then
                            library.activeBox = nil;
                        end

                        local tb = library.inputBox
                        if tb then
                            pcall(function()
                                if tb:IsFocused() then
                                    tb:ReleaseFocus()
                                end
                                tb.Text = ''
                                tb.Position = UDim2.fromOffset(-10000, -10000) -- park it so stray clicks can't focus it
                            end)
                        end

                        self.objects.inputText.ThemeColor = 'Option Text 2';
                        if apply and (force or input ~= box.input) then
                            box:SetInput(input);
                        else
                            input = box.input;
                            render(box.input);
                        end
                    end

                    tooltip(box);
                    box:SetText(box.text);
                    box:SetInput(box.input, true);
                    self:UpdateOptions();
                    return box
                end

                -- // Keybind
                function section:AddBind(data)
                    local bind = {
                        class = 'bind';
                        flag = data.flag;
                        text = '';
                        tooltip = '';
                        bind = 'none';
                        mode = 'toggle';
                        order = #self.options+1;
                        callback = function() end;
                        keycallback = function() end;
                        indicatorValue = library.keyIndicator:AddValue({value = 'value', key = 'key', enabled = false});
                        noindicator = false;
                        state = false;
                        nomouse = false;
                        enabled = true;
                        binding = false;
                        risky = false;
                        objects = {};
                    };

                    local blacklist = {'objects'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and bind[i] ~= nil then
                            bind[i] = v
                        end
                    end
                    
                    table.insert(self.options, bind)

                    if bind.flag then
                        library.options[bind.flag] = bind;
                    end

                    --- Create Objects ---
                    do
                        local objs = bind.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,19);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = section.objects.optionholder;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,2,0,2);
                            ThemeColor = bind.risky and 'Risky Text' or 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        objs.keyText = utility:Draw('Text', {
                            ThemeColor = 'Option Text 3';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Parent = objs.holder;
                        })

                        utility:Connection(objs.holder.MouseEnter, function()
                            objs.keyText.ThemeColor = 'Accent';
                        end)

                        utility:Connection(objs.holder.MouseLeave, function()
                            objs.keyText.ThemeColor = bind.binding and 'Accent' or 'Option Text 3';
                        end)

                        utility:Connection(objs.holder.MouseButton1Down, function()
                            if not bind.binding then
                                bind:SetKeyText('...');
                                bind.bindingStarted = os.clock();
                                bind.binding = true;
                            end
                        end)

                    end
                    ----------------------

                    local c

                    function bind:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                            self.indicatorValue:SetKey(str);
                        end
                    end

                    function bind:SetBind(keybind)
                        if c then
                            c:Disconnect();
                            c = nil;
                            if bind.flag then
                                library.flags[bind.flag] = false;
                            end
                            bind.callback(false);
                        end
                        local keyName = 'NONE'
                        -- false/nil means "cancelled" (blacklisted key), keep the previous bind
                        if keybind == 'none' or typeof(keybind) == 'EnumItem' then
                            self.bind = keybind
                        end
                        if self.bind == Enum.KeyCode.Backspace or self.bind == 'none' then
                            self.bind = 'none';
                        else
                            keyName = getKeyName(self.bind)
                        end
                        self.keycallback(self.bind);
                        self:SetKeyText(keyName:upper());
                        self.indicatorValue:SetKey((self.text == nil or self.text == '') and (self.flag == nil and 'unknown' or self.flag) or self.text); -- this is so dumb
                        self.indicatorValue:SetValue('['..keyName:upper()..']');
                        self.objects.keyText.ThemeColor = self.objects.holder.Hover and 'Accent' or 'Option Text 3';
                    end

                    function bind:SetKeyText(str)
                        str = tostring(str);
                        self.objects.keyText.Text = '['..str..']';
                        self.objects.keyText.Position = newUDim2(1,-self.objects.keyText.TextBounds.X, 0, 2);
                    end

                    utility:Connection(inputservice.InputBegan, function(inp)
                        if inputservice:GetFocusedTextBox() or library:IsTyping() then
                            return
                        elseif bind.binding then
                            -- ignore the same click that started binding
                            if inp.UserInputType == Enum.UserInputType.MouseButton1 and os.clock() - (bind.bindingStarted or 0) < 0.05 then
                                return
                            end
                            bind:SetBind(getInputKey(inp, bind.nomouse))
                            bind.binding = false
                        elseif not bind.binding and bind.bind == 'none' then
                            bind.state = true
                            if bind.flag then
                                library.flags[bind.flag] = bind.state
                            end
                        elseif (inp.KeyCode == bind.bind or inp.UserInputType == bind.bind) and not bind.binding then
                            if bind.mode == 'toggle' then
                                bind.state = not bind.state
                                if bind.flag then
                                    library.flags[bind.flag] = bind.state;
                                end
                                bind.callback(bind.state)
                                bind.indicatorValue:SetEnabled(bind.state and not bind.noindicator);
                            elseif bind.mode == 'hold' then
                                if bind.flag then
                                    library.flags[bind.flag] = true;
                                end
                                bind.indicatorValue:SetEnabled(true and not bind.noindicator);
                                c = utility:Connection(runservice.RenderStepped, function()
                                    bind.callback(true);
                                end)
                            end
                        end
                    end)

                    utility:Connection(inputservice.InputEnded, function(inp)
                        if bind.bind ~= 'none' then
                            if inp.KeyCode == bind.bind or inp.UserInputType == bind.bind then
                                if c then
                                    c:Disconnect();
                                    c = nil;
                                    if bind.flag then
                                        library.flags[bind.flag] = false;
                                    end
                                    bind.callback(false);
                                    bind.indicatorValue:SetEnabled(false);
                                end
                            end
                        end
                    end)

                    tooltip(bind);
                    bind:SetBind(bind.bind);
                    bind:SetText(bind.text);
                    self:UpdateOptions();
                    return bind
                end

                -- // Dropdown
                function section:AddList(data)
                    local list = {
                        class = 'list';
                        flag = data.flag;
                        text = '';
                        selected = '';
                        tooltip = '';
                        order = #self.options+1;
                        callback = function() end;
                        enabled = true;
                        multi = false;
                        maxVisible = false; -- rows shown before scrolling (false = window default)
                        open = false;
                        risky = false;
                        values = {};
                        objects = {};
                    }

                    table.insert(self.options, list);

                    local blacklist = {'objects'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) ~= list[i] ~= nil then
                            list[i] = v
                        end
                    end

                    if list.flag then
                        library.flags[list.flag] = list.selected;
                        library.options[list.flag] = list;
                    end

                    -- Create Objects --
                    do
                        local objs = list.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Size = newUDim2(1,0,0,40);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-4,0,15);
                            Position = newUDim2(0,2,1,-19);
                            ThemeColor = 'Option Background';
                            ZIndex = z+2;
                            Parent = objs.holder;
                        })

                        objs.border1 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 1';
                            ZIndex = z+1;
                            Parent = objs.background;
                        })

                        objs.border2 = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z;
                            Parent = objs.border1;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp90;
                            Transparency = .65;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,2,0,2);
                            ThemeColor = list.risky and 'Risky Text Enabled' or 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        objs.inputText = utility:Draw('Text', {
                            Position = newUDim2(0,4,0,0);
                            ThemeColor = 'Option Text 2';
                            Text = 'none',
                            Size = 13;
                            Font = 2;
                            ZIndex = z+5;
                            Outline = true;
                            Parent = objs.background;
                        })

                        objs.openText = utility:Draw('Text', {
                            Position = newUDim2(1,-10,0,0);
                            ThemeColor = 'Option Text 3';
                            Text = '+';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+5;
                            Outline = true;
                            Parent = objs.background;
                        })

                        utility:Connection(objs.holder.MouseEnter, function()
                            objs.border1.ThemeColor = 'Accent';
                        end)

                        utility:Connection(objs.holder.MouseLeave, function()
                            objs.border1.ThemeColor = 'Option Border 1';
                        end)

                        utility:Connection(objs.holder.MouseButton1Down, function()
                            if list.open then
                                list.open = false;
                                objs.openText.Text = '+';
                                if window.dropdown.selected == list then
                                    window.dropdown.selected = nil;
                                    window.dropdown.objects.background.Visible = false;
                                end
                            else
                                if window.dropdown.selected ~= nil then
                                    window.dropdown.selected.open = false
                                end
                                list.open = true;
                                objs.openText.Text = '-';
                                window.dropdown.selected = list;
                                window.dropdown.objects.background.Visible = true;
                                window.dropdown.objects.background.Parent = objs.holder;
                                window.dropdown:Refresh();
                                window.dropdown:AnimateOpen();
                            end
                        end)


                    end
                    --------------------

                    function list:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                        end
                    end

                    function list:Select(option, nocallback)
                        option = typeof(option) == 'table' and (self.multi == true and option or (#option == 0 and nil or option[1])) or self.multi == true and {option} or option;
                        if option ~= nil then
                            self.selected = option;
                            local text = typeof(option) == 'table' and (#option == 0 and "none" or table.concat(option, ', ')) or tostring(option);
                            local label = self.objects.inputText
                            label.Text = text;
                            if label.TextBounds.X > self.objects.background.Object.Size.X - 10 then
                                local split = text:split('');
                                for i = 1,#split do
                                    label.Text = table.concat(split, '', 1, i)
                                    if label.TextBounds.X > self.objects.background.Object.Size.X - 10 then
                                        label.Text = label.Text:sub(1,-6)..'...';
                                        break
                                    end
                                end
                            end
                            if self.flag then
                                library.flags[self.flag] = self.selected
                            end
                            if not nocallback then
                                self.callback(self.selected);
                            end
                        end
                    end

                    function list:AddValue(value)
                        table.insert(list.values, tostring(value));
                        if window.dropdown.selected == list then
                            window.dropdown:Refresh()
                        end
                    end

                    function list:RemoveValue(value)
                        if table.find(list.values, value) then
                            table.remove(list.values, table.find(list.values, value));
                            if window.dropdown.selected == list then
                                window.dropdown:Refresh()
                            end
                        end
                    end

                    function list:ClearValues()
                        table.clear(list.values);
                        if window.dropdown.selected == list then
                            window.dropdown:Refresh()
                        end
                    end

                    tooltip(list);
                    list:Select((data.value or data.selected) or (list.multi and 'none' or list.values[1]), true);
                    list:SetText(list.text);
                    self:UpdateOptions();
                    return list
                end

                -- Text
                function section:AddText(data)
                    local text = {
                        class = 'text';
                        flag = data.flag;
                        text = '';
                        tooltip = '';
                        order = #self.options+1;
                        enabled = true;
                        risky = false;
                        objects = {};
                    };

                    local blacklist = {'objects'};
                    for i,v in next, data do
                        if not table.find(blacklist, i) and text[i] ~= nil then
                            text[i] = v
                        end
                    end

                    if data.flag then
                        library.options[data.flag] = text;
                    end

                    table.insert(self.options, text)

                    --- Create Objects ---
                    do
                        local objs = text.objects;
                        local z = library.zindexOrder.window+25;

                        objs.holder = utility:Draw('Square', {
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = section.objects.optionholder;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,2,0,2);
                            ThemeColor = text.risky and 'Risky Text Enabled' or 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })
                    end
                    ----------------------

                    function text:SetText(str)
                        if typeof(str) == 'string' then
                            self.text = str;
                            self.objects.text.Text = str;
                            self.objects.holder.Size = newUDim2(1,0,0,self.objects.text.TextBounds.Y + 6);
                            section:UpdateOptions();
                        end
                    end

                    text:SetText(text.text);
                    self:UpdateOptions();
                    return text
                end

                -----------------------

                section:UpdateOptions();
                section:SetText(section.text);
                self:UpdateSections();
                return section;
            end

            function tab:UpdateSections()
                table.sort(self.sections, function(a,b)
                    return a.order < b.order
                end)

                local last1,last2;
                local padding = 15;
                for _,section in next, self.sections do

                    if section.objects.background.Visible ~= (section.enabled and tab.selected) then
                        section.objects.background.Visible = section.enabled and tab.selected
                        section:UpdateOptions();
                    end
                    
                    if section.enabled then
                        if section.side == 1 then
                            if last1 then
                                section.objects.background.Position = last1.objects.background.Position + newUDim2(0,0,0,last1.objects.background.Object.Size.Y + padding);
                            end
                            last1 = section;
                        elseif section.side == 2 then
                            if last2 then
                                section.objects.background.Position = last2.objects.background.Position + newUDim2(0,0,0,last2.objects.background.Object.Size.Y + padding);
                            end
                            last2 = section;
                        end
                    end

                    section:SetText(section.text)
                    
                end
            end

            function tab:SetText(str)
                if typeof(str) == 'string' then
                    self.text = str;
                    self.objects.text.Text = str;
                    window:UpdateTabs();
                end
            end

            function tab:Select()
                local previous = window.selectedTab;
                window.selectedTab = tab;
                if window.dropdown.selected then
                    window.dropdown:Close();
                end
                if window.colorpicker.selected then
                    window.colorpicker.selected:SetOpen(false);
                end
                window:UpdateTabs();
                library.hoverDirty = true;

                -- switching tabs: new sections fade in while the columns rise into place
                if previous ~= nil and previous ~= tab and window.open then
                    local anim = library.animations;
                    local offset = newUDim2(0, 0, 0, anim.tabOffset);
                    utility:SlideIn(window.objects.columnholder1, newUDim2(.01, 0, .02, 0), offset, anim.tab);
                    utility:SlideIn(window.objects.columnholder2, newUDim2(1 - (.48 + .01), 0, .02, 0), offset, anim.tab);
                    for _, section in next, tab.sections do
                        if section.enabled then
                            utility:FadeIn(section.objects.background, anim.tab);
                        end
                    end
                end

                for i,v in next, window.tabs do
                    if v.callback then
                        v.callback(v == tab)
                    end
                end
            end

            if window.selectedTab == nil then
                tab:Select();
            end

            tab:SetText(tab.text);
            window:UpdateTabs();
            return tab;
        end

        function window:UpdateTabs()
            table.sort(self.tabs, function(a,b)
                return a.order < b.order
            end)
            local pos = 0;
            for i,v in next, self.tabs do
                local objs = v.objects;
                v.selected = v == self.selectedTab;
                objs.background.ThemeColor = v.selected and 'Selected Tab Background' or 'Unselected Tab Background';
                objs.background.Size = newUDim2(0, objs.text.TextBounds.X + 14, 1, v.selected and 1 or 0);
                objs.background.Position = newUDim2(0, pos, 0, 0)

                objs.text.ThemeColor = v.selected and 'Selected Tab Text' or 'Unselected Tab Text';
                objs.text.Position = newUDim2(.5, 0, 0, 3);

                -- the accent line is drawn by the sliding tabIndicator now
                objs.topBorder.ThemeColor = v.selected and 'Selected Tab Background' or 'Unselected Tab Background';

                if v.selected then
                    local indicator = self.objects.tabIndicator;
                    local targetPos = newUDim2(0, pos, 0, 0);
                    local targetSize = newUDim2(0, objs.background.Size.X.Offset, 0, 1);
                    local anim = library.animations;
                    local placed = indicator.Size.X.Offset > 0;

                    if placed and self.open and anim.enabled and anim.indicator > 0 then
                        if indicator.Position ~= targetPos then
                            utility:Tween(indicator, 'Position', targetPos, anim.indicator, Enum.EasingDirection.Out, Enum.EasingStyle.Quint);
                        end
                        if indicator.Size ~= targetSize then
                            utility:Tween(indicator, 'Size', targetSize, anim.indicator, Enum.EasingDirection.Out, Enum.EasingStyle.Quint);
                        end
                    else
                        indicator.Position = targetPos;
                        indicator.Size = targetSize;
                    end
                end

                pos += objs.background.Size.X.Offset + 1

                v:UpdateSections();

            end
        end

        window:SetOpen(true);
        return window;
    end

    -- Tooltip
    do
        local z = library.zindexOrder.window + 2000;
        tooltipObjects.background = utility:Draw('Square', {
            ThemeColor = 'Group Background';
            ZIndex = z;
            Visible = false;
        })

        tooltipObjects.border1 = utility:Draw('Square', {
            Size = UDim2.new(1,2,1,2);
            Position = UDim2.new(0,-1,0,-1);
            ThemeColor = 'Border 1';
            ZIndex = z-1;
            Parent = tooltipObjects.background;
        })

        tooltipObjects.border2 = utility:Draw('Square', {
            Size = UDim2.new(1,4,1,4);
            Position = UDim2.new(0,-2,0,-2);
            ThemeColor = 'Border 3';
            ZIndex = z-2;
            Parent = tooltipObjects.background;
        })

        tooltipObjects.text = utility:Draw('Text', {
            Position = UDim2.new(0,3,0,0);
            ThemeColor = 'Primary Text';
            Size = 13;
            Font = 2;
            ZIndex = z+1;
            Outline = true;
            Parent = tooltipObjects.background;
        })

        tooltipObjects.riskytext = utility:Draw('Text', {
            Position = UDim2.new(0,3,0,0);
            ThemeColor = 'Risky Text Enabled';
            Text = '[RISKY]';
            Size = 13;
            Font = 2;
            ZIndex = z+1;
            Outline = true;
            Parent = tooltipObjects.background;
        })

    end
    
    -- Watermark
    do
        -- optional user info: pass startupArgs.user = {User = 'name', UID = 1}, defaults to the local player
        local userInfo = startupArgs.user or {
            User = localplayer and localplayer.Name or 'user',
            UID = localplayer and localplayer.UserId or 0,
        }
        self.watermark = {
            objects = {};
            text = {
                {self.cheatname, true},
                {("%s (uid %s)"):format(tostring(userInfo.User), tostring(userInfo.UID)), true},
                {self.gamename, true},
                {'0 fps', true},
                {'0ms', true},
                {'00:00:00', true},
                {'M, D, Y', true},
            };
            -- nil = default spot (very top, centered). otherwise Vector2(centerX, topY) set by dragging,
            -- stored as the center so the watermark stays put while its text width changes
            anchor = nil;
            position = newUDim2(0,0,0,0);
            refreshrate = 250; -- ms between text updates (was 25 = 40 rebuilds a second)
        }

        function self.watermark:ApplyPosition()
            local size = self.objects.background.Object.Size;
            local screensize = workspace.CurrentCamera.ViewportSize;
            local anchor = self.anchor or newVector2(screensize.X / 2, 4);
            local x = clamp(anchor.X - size.X / 2, 0, math.max(screensize.X - size.X, 0));
            local y = clamp(anchor.Y, 0, math.max(screensize.Y - size.Y, 0));
            self.position = newUDim2(0, floor(x), 0, floor(y));
            self.objects.background.Position = self.position;
        end

        function self.watermark:SetAnchor(anchor)
            self.anchor = typeof(anchor) == 'Vector2' and anchor or nil;
            self:ApplyPosition();
        end

        function self.watermark:Update()
            self.objects.background.Visible = library.flags.watermark_enabled == true
            if library.flags.watermark_enabled then
                local day = tonumber(os.date('%d',os.time())) or 1
                local lastDigit = day % 10
                local suffix = (day >= 11 and day <= 13) and 'th' or (lastDigit == 1 and 'st' or lastDigit == 2 and 'nd' or lastDigit == 3 and 'rd' or 'th')
                local date = {os.date('%b',os.time()), tostring(day)..suffix, os.date('%Y',os.time())}

                self.text[4][1] = library.stats.fps..' fps'
                self.text[5][1] = floor(library.stats.ping)..'ms'
                self.text[6][1] = os.date('%X', os.time())
                self.text[7][1] = table.concat(date, ', ')

                local text = {};
                for _,v in next, self.text do
                    if v[2] then
                        table.insert(text, v[1]);
                    end
                end

                self.objects.text.Text = table.concat(text,' | ')
                self.objects.background.Size = newUDim2(0, self.objects.text.TextBounds.X + 10, 0, 17)

                -- don't fight the mouse while it's being dragged
                if not (self.drag and self.drag.dragging) then
                    self:ApplyPosition()
                end
            end
        end

        do
            local objs = self.watermark.objects;
            local z = self.zindexOrder.watermark;
            
            objs.background = utility:Draw('Square', {
                Visible = false;
                Size = newUDim2(0, 200, 0, 17);
                Position = newUDim2(0,800,0,100);
                ThemeColor = 'Background';
                ZIndex = z;
            })

            objs.border1 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 2';
                Parent = objs.background;
                ZIndex = z-1;
            })

            objs.border2 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 3';
                Parent = objs.border1;
                ZIndex = z-2;
            })
            
            objs.topbar = utility:Draw('Square', {
                Size = newUDim2(1,0,0,1);
                ThemeColor = 'Accent';
                ZIndex = z+1;
                Parent = objs.background;
            })

            objs.text = utility:Draw('Text', {
                Position = newUDim2(.5,0,0,2);
                ThemeColor = 'Primary Text';
                Text = 'Watermark Text';
                Size = 13;
                Font = 2;
                ZIndex = z+1;
                Outline = true;
                Center = true;
                Parent = objs.background;
            })

            -- drag it anywhere while the menu is open
            local watermark = self.watermark
            watermark.drag = utility:MakeDraggable({objs.background, objs.topbar}, function()
                return objs.background.Object.Position
            end, function(p)
                local size = objs.background.Object.Size
                watermark.anchor = newVector2(p.X + size.X / 2, p.Y)
                watermark:ApplyPosition()
            end, function()
                if watermark.onMoved then
                    watermark.onMoved(watermark.anchor)
                end
            end)

        end
    end

    local lasttick = tick();
    utility:Connection(runservice.RenderStepped, function(step)
        if step > 0 then
            library.stats.fps = floor(1/step)
        end
        pcall(function()
            library.stats.ping = stats.Network.ServerStatsItem["Data Ping"]:GetValue()
            library.stats.sendkbps = stats.DataSendKbps
            library.stats.receivekbps = stats.DataReceiveKbps
        end)

        if (tick()-lasttick)*1000 > library.watermark.refreshrate then
            lasttick = tick()
            local ok, err = pcall(library.watermark.Update, library.watermark)
            if not ok then
                log('watermark update failed: '..tostring(err))
            end
        end
    end)

    -- default spots: keybinds on the left edge around 40% down the screen, target info under it
    local defaultPositions = {
        keybinds = newUDim2(0, 12, .4, 0),
        target = newUDim2(0, 12, .62, 0),
    }

    self.keyIndicator = self.NewIndicator({title = 'Keybinds', position = defaultPositions.keybinds, enabled = false});
    
    self.targetIndicator = self.NewIndicator({title = 'Target Info', position = defaultPositions.target, enabled = false});
    self.targetName = self.targetIndicator:AddValue({key = 'Name     :', value = 'nil'})
    self.targetDisplay = self.targetIndicator:AddValue({key = 'DName    :', value = 'nil'})
    self.targetHealth = self.targetIndicator:AddValue({key = 'Health   :', value = '0'})
    self.targetDistance = self.targetIndicator:AddValue({key = 'Distance :', value = '0m'})
    self.targetTool = self.targetIndicator:AddValue({key = 'Weapon   :', value = 'nil'})

    -- // Layout
    -- dragged positions of the watermark and indicators are remembered between sessions
    -- (one file for every game, since it's about your screen, not the game)
    local layoutPath = self.cheatname..'/layout.json'
    local layoutIndicators = {
        keybinds = self.keyIndicator,
        target = self.targetIndicator,
    }

    function self:SaveLayout()
        if not writefile then return end
        local data = {}
        if self.watermark.anchor then
            data.watermark = {self.watermark.anchor.X, self.watermark.anchor.Y}
        end
        for name, indicator in next, layoutIndicators do
            if indicator.moved then
                data[name] = {indicator.position.X.Offset, indicator.position.Y.Offset}
            end
        end
        pcall(writefile, layoutPath, http:JSONEncode(data))
    end

    function self:ResetLayout()
        self.watermark:SetAnchor(nil)
        for name, indicator in next, layoutIndicators do
            indicator.moved = false
            indicator:SetPosition(defaultPositions[name])
        end
        if delfile and isfile and isfile(layoutPath) then
            pcall(delfile, layoutPath)
        end
    end

    self.watermark.onMoved = function()
        self:SaveLayout()
    end
    for _, indicator in next, layoutIndicators do
        indicator.onMoved = function()
            indicator.moved = true
            self:SaveLayout()
        end
    end

    -- restore the saved layout
    if isfile and readfile and isfile(layoutPath) then
        pcall(function()
            local data = http:JSONDecode(readfile(layoutPath))
            if typeof(data.watermark) == 'table' then
                self.watermark.anchor = newVector2(tonumber(data.watermark[1]) or 0, tonumber(data.watermark[2]) or 0)
            end
            for name, indicator in next, layoutIndicators do
                local p = data[name]
                if typeof(p) == 'table' then
                    indicator.moved = true
                    indicator:SetPosition(newUDim2(0, tonumber(p[1]) or 0, 0, tonumber(p[2]) or 0))
                end
            end
        end)
    end

    self:SetTheme(library.theme);
    self:SetOpen(true);
    self.hasInit = true

end

function library:CreateSettingsTab(menu)
    local settingsTab = menu:AddTab('Settings', 999);
    local configSection = settingsTab:AddSection('Config', 2);
    local mainSection = settingsTab:AddSection('Main', 1);

    configSection:AddBox({text = 'Config Name', flag = 'configinput'})
    configSection:AddList({text = 'Config', flag = 'selectedconfig'})

    local configFolder = self.cheatname..'/'..self.gamename..'/configs'

    local function refreshConfigs()
        local list = library.options.selectedconfig
        list:ClearValues();

        local ok, files = pcall(function()
            return listfiles and listfiles(configFolder) or {}
        end)
        if not ok or typeof(files) ~= 'table' then
            files = {}
        end

        for _,v in next, files do
            -- executors return either \ or / separators
            local fileName = tostring(v):gsub('\\', '/'):match('([^/]+)$') or tostring(v)
            if fileName:sub(-#self.fileext) == self.fileext then
                list:AddValue(fileName:sub(1, -#self.fileext - 1))
            end
        end

        -- keep the current selection if it still exists, otherwise pick the first config
        if not table.find(list.values, list.selected) then
            if list.values[1] then
                list:Select(list.values[1], true)
            else
                list.selected = ''
                list.objects.inputText.Text = 'none'
                library.flags.selectedconfig = ''
            end
        end
    end

    local function validConfigName(name)
        return typeof(name) == 'string' and name:gsub('%s', '') ~= '' and not name:find('[\\/:%*%?"<>|]')
    end

    configSection:AddButton({text = 'Load', confirm = true, callback = function()
        library:LoadConfig(library.flags.selectedconfig);
    end}):AddButton({text = 'Save', confirm = true, callback = function()
        library:SaveConfig(library.flags.selectedconfig);
    end})

    configSection:AddButton({text = 'Create', confirm = true, callback = function()
        local name = library.flags.configinput
        if not validConfigName(name) then
            library:SendNotification('Enter a valid config name first.', 5, c3new(1,0,0));
            return
        end
        if library:GetConfig(name) then
            library:SendNotification('Config \''..name..'\' already exists.', 5, c3new(1,0,0));
            return
        end
        if not writefile then
            library:SendNotification('Your executor does not support writefile.', 5, c3new(1,0,0));
            return
        end
        writefile(configFolder..'/'..name..self.fileext, http:JSONEncode({}));
        refreshConfigs()
        library.options.selectedconfig:Select(name)
        library:SendNotification('Created config: '..name, 5, c3new(0,1,0));
    end}):AddButton({text = 'Delete', confirm = true, callback = function()
        local name = library.flags.selectedconfig
        if library:GetConfig(name) and delfile then
            delfile(configFolder..'/'..name..self.fileext);
            refreshConfigs()
            if library:GetAutoload() == name then
                library:SetAutoload(nil)
            end
            library:SendNotification('Deleted config: '..name, 5, c3new(0,1,0));
        end
    end})

    -- // Autoload
    -- the chosen config name is stored per game and loaded automatically next time the script runs
    local autoloadPath = self.cheatname..'/'..self.gamename..'/autoload.txt'
    local autoloadLabel

    function library:GetAutoload()
        if isfile and readfile and isfile(autoloadPath) then
            local ok, name = pcall(readfile, autoloadPath)
            if ok and typeof(name) == 'string' and name ~= '' then
                return name
            end
        end
        return nil
    end

    function library:SetAutoload(name)
        if name then
            if writefile then
                pcall(writefile, autoloadPath, name)
            end
        elseif delfile and isfile and isfile(autoloadPath) then
            pcall(delfile, autoloadPath)
        end
        if autoloadLabel then
            autoloadLabel:SetText('Autoload: '..(name or 'none'))
        end
    end

    configSection:AddSeparator({text = 'Autoload'})
    autoloadLabel = configSection:AddText({text = 'Autoload: '..(library:GetAutoload() or 'none')})

    configSection:AddButton({text = 'Set Autoload', callback = function()
        local name = library.flags.selectedconfig
        if not library:GetConfig(name) then
            library:SendNotification('Select a config to autoload first.', 5, c3new(1,0,0));
            return
        end
        library:SetAutoload(name)
        library:SendNotification('Autoload set to: '..name, 5, c3new(0,1,0));
    end}):AddButton({text = 'Clear Autoload', callback = function()
        library:SetAutoload(nil)
        library:SendNotification('Autoload cleared.', 5);
    end})

    refreshConfigs()

    mainSection:AddBind({text = 'Open / Close', flag = 'togglebind', nomouse = true, noindicator = true, bind = Enum.KeyCode.End, callback = function()
        library:SetOpen(not library.open)
    end});

    mainSection:AddToggle({text = 'Disable Movement If Open', flag = 'disablemenumovement', callback = function(bool)
        if bool and library.open then
            actionservice:BindAction(
                'FreezeMovement',
                function()
                    return Enum.ContextActionResult.Sink
                end,
                false,
                unpack(Enum.PlayerActions:GetEnumItems())
            )
        else
            actionservice:UnbindAction('FreezeMovement');
        end
    end})

    mainSection:AddButton({text = 'Join Discord', flag = 'joindiscord', confirm = true, callback = function()
        if not httpRequest then
            setclip('discord.gg/zPyX4BZH9q')
            library:SendNotification('Executor has no request function, invite copied instead.', 5);
            return
        end
        local ok, res = pcall(httpRequest, {
            Url = 'http://127.0.0.1:6463/rpc?v=1',
            Method = 'POST',
            Headers = {
                ['Content-Type'] = 'application/json',
                Origin = 'https://discord.com'
            },
            Body = game:GetService('HttpService'):JSONEncode({
                cmd = 'INVITE_BROWSER',
                nonce = game:GetService('HttpService'):GenerateGUID(false),
                args = {code = 'zPyX4BZH9q'}
            })
        })
        if ok and typeof(res) == 'table' and res.Success then
            library:SendNotification(library.cheatname..' | joined discord', 3);
        end
    end})
    
    mainSection:AddButton({text = 'Copy Discord', flag = 'copydiscord', callback = function()
        if setclip('discord.gg/zPyX4BZH9q') then
            library:SendNotification('Discord invite copied.', 3);
        end
    end})

    mainSection:AddButton({text = 'Rejoin Server', confirm = true, callback = function()
        game:GetService("TeleportService"):TeleportToPlaceInstance(game.PlaceId, game.JobId);
    end})

    mainSection:AddButton({text = 'Rejoin Game', confirm = true, callback = function()
        game:GetService("TeleportService"):Teleport(game.PlaceId);
    end})

    mainSection:AddButton({text = 'Copy Join Script', callback = function()
        setclip(([[game:GetService("TeleportService"):TeleportToPlaceInstance(%s, "%s")]]):format(game.PlaceId, game.JobId))
    end})

    mainSection:AddButton({text = 'Copy Game Invite', callback = function()
        setclip(([[Roblox.GameLauncher.joinGameInstance(%s, "%s")]]):format(game.PlaceId, game.JobId))
    end})

    mainSection:AddButton({text = 'Unload', confirm = true, callback = function()
        library:Unload();
    end})

    mainSection:AddSeparator({text = 'Keybinds'});
    -- the keybind list and watermark are dragged into place with the mouse while the menu is open
    mainSection:AddSeparator({text = 'Overlay'});
    mainSection:AddToggle({text = 'Keybind Indicator', flag = 'keybind_indicator', tooltip = 'Drag it anywhere while the menu is open', callback = function(bool)
        library.keyIndicator:SetEnabled(bool);
    end})
    mainSection:AddToggle({text = 'Watermark', flag = 'watermark_enabled', tooltip = 'Drag it anywhere while the menu is open'});
    mainSection:AddButton({text = 'Reset Positions', confirm = true, callback = function()
        library:ResetLayout()
        library:SendNotification('Overlay positions reset.', 4);
    end})

    local themeStrings = {"Custom"};
    for _,v in next, library.themes do
        table.insert(themeStrings, v.name)
    end
    local themeTab = menu:AddTab('Theme', 990);
    local themeSection = themeTab:AddSection('Theme', 1);
    local setByPreset = false

    themeSection:AddList({text = 'Presets', flag = 'preset_theme', values = themeStrings, callback = function(newTheme)
        if newTheme == "Custom" then return end
        setByPreset = true
        for _,v in next, library.themes do
            if v.name == newTheme then
                -- update the pickers without callbacks, then recolor everything once
                -- (before, every picker re-applied the whole theme: ~20 full recolors per preset)
                for x, d in pairs(library.options) do
                    if d.class == 'color' and v.theme[tostring(x)] ~= nil then
                        d:SetColor(v.theme[tostring(x)], true)
                    end
                end
                library:SetTheme(v.theme)
                break
            end
        end
        setByPreset = false
    end}):Select('Default');

    -- stable order for the color pickers (pairs order is random)
    local themeKeys = {}
    for i in next, library.theme do
        table.insert(themeKeys, i)
    end
    table.sort(themeKeys)

    for _, i in ipairs(themeKeys) do
        themeSection:AddColor({text = i, flag = i, color = library.theme[i], callback = function(c3)
            library.theme[i] = c3
            library:SetTheme(library.theme)
            if not setByPreset and not setByConfig then 
                library.options.preset_theme:Select('Custom')
            end
        end});
    end

    -- load the autoload config once everything (including the theme pickers) exists.
    -- deferred a moment so options the script adds right after this call still get their values.
    local autoloadName = library:GetAutoload()
    if autoloadName then
        task.delay(.5, function()
            if not library.hasInit then return end -- unloaded in the meantime
            if library:GetConfig(autoloadName) then
                library:LoadConfig(autoloadName)
                if table.find(library.options.selectedconfig.values, autoloadName) then
                    library.options.selectedconfig:Select(autoloadName, true)
                end
            else
                library:SendNotification('Autoload config \''..autoloadName..'\' no longer exists.', 5, c3new(1,0,0));
                library:SetAutoload(nil)
            end
        end)
    end

    return settingsTab;
end

getgenv().library = library
return library
