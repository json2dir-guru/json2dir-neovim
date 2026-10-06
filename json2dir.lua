-- json2dir: create the directory tree a JSON document describes, in the current directory.
-- Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
-- Neovim Lua only: run as `nvim --clean --headless -l json2dir.lua < document.json`.
-- Hand-written JSON parser (vim.json is too lax); all I/O goes through vim.uv (libuv).

local uv = vim.uv
local bit = require("bit")
local byte, sub, char, find = string.byte, string.sub, string.char, string.find

local function fail(msg) error({ msg = msg }, 0) end

------------------------------------------------------------------------------
-- §3: strict UTF-8
------------------------------------------------------------------------------
local function check_utf8(s)
  local i, n = 1, #s
  while i <= n do
    local c = byte(s, i)
    if c < 0x80 then
      i = i + 1
    else
      local len, min
      if c >= 0xC2 and c <= 0xDF then len, min = 2, 0x80
      elseif c >= 0xE0 and c <= 0xEF then len, min = 3, 0x800
      elseif c >= 0xF0 and c <= 0xF4 then len, min = 4, 0x10000
      else fail("input is not valid UTF-8") end
      if i + len - 1 > n then fail("input is not valid UTF-8") end
      local cp = bit.band(c, bit.rshift(0x7F, len))
      for k = 1, len - 1 do
        local d = byte(s, i + k)
        if d < 0x80 or d > 0xBF then fail("input is not valid UTF-8") end
        cp = cp * 64 + (d - 0x80)
      end
      if cp < min or cp > 0x10FFFF or (cp >= 0xD800 and cp <= 0xDFFF) then
        fail("input is not valid UTF-8")
      end
      i = i + len
    end
  end
end

local function utf8_encode(cp)
  if cp < 0x80 then return char(cp)
  elseif cp < 0x800 then
    return char(0xC0 + bit.rshift(cp, 6), 0x80 + bit.band(cp, 0x3F))
  elseif cp < 0x10000 then
    return char(0xE0 + bit.rshift(cp, 12), 0x80 + bit.band(bit.rshift(cp, 6), 0x3F),
      0x80 + bit.band(cp, 0x3F))
  else
    return char(0xF0 + bit.rshift(cp, 18), 0x80 + bit.band(bit.rshift(cp, 12), 0x3F),
      0x80 + bit.band(bit.rshift(cp, 6), 0x3F), 0x80 + bit.band(cp, 0x3F))
  end
end

------------------------------------------------------------------------------
-- §3, §4: strict JSON parser. Objects become {obj=true, keys={...}, map={...}},
-- arrays {arr=true, ...}, strings stay Lua strings (UTF-8 bytes).
-- Numbers, true, false and null are rejected right away (§4.5).
------------------------------------------------------------------------------
local function parse(s)
  local pos = 1
  local escapes = { [34] = '"', [92] = "\\", [47] = "/", [98] = "\b", [102] = "\f",
    [110] = "\n", [114] = "\r", [116] = "\t" }

  local function skip_ws()
    pos = find(s, "[^ \t\r\n]", pos) or #s + 1
  end

  local function bad(what) fail("input is not valid JSON: " .. what .. " at byte " .. pos) end

  local function hex4()
    local h = sub(s, pos, pos + 3)
    if not h:match("^%x%x%x%x$") then bad("bad \\u escape") end
    pos = pos + 4
    return tonumber(h, 16)
  end

  local function parse_string()
    pos = pos + 1 -- opening quote
    local buf = {}
    while true do
      local j = find(s, '["\\%c]', pos)
      if not j then bad("unterminated string") end
      if j > pos then buf[#buf + 1] = sub(s, pos, j - 1) end
      local c = byte(s, j)
      pos = j + 1
      if c == 34 then
        return table.concat(buf)
      elseif c == 92 then
        local e = byte(s, pos)
        if e == 117 then -- \u
          pos = pos + 1
          local cp = hex4()
          if cp >= 0xD800 and cp <= 0xDBFF then
            if sub(s, pos, pos + 1) ~= "\\u" then bad("unpaired surrogate") end
            pos = pos + 2
            local lo = hex4()
            if lo < 0xDC00 or lo > 0xDFFF then bad("unpaired surrogate") end
            cp = 0x10000 + (cp - 0xD800) * 0x400 + (lo - 0xDC00)
          elseif cp >= 0xDC00 and cp <= 0xDFFF then
            bad("unpaired surrogate")
          end
          buf[#buf + 1] = utf8_encode(cp)
        elseif e and escapes[e] then
          buf[#buf + 1] = escapes[e]
          pos = pos + 1
        else
          bad("bad escape")
        end
      elseif c == 127 then
        buf[#buf + 1] = "\127" -- DEL is matched by %c but allowed in JSON
      else
        bad("control character in string")
      end
    end
  end

  local parse_value

  local function parse_object(depth)
    pos = pos + 1
    local o = { obj = true, keys = {}, map = {} }
    skip_ws()
    if byte(s, pos) == 125 then pos = pos + 1; return o end
    while true do
      skip_ws()
      if byte(s, pos) ~= 34 then bad("expected member name") end
      local name = parse_string()
      skip_ws()
      if byte(s, pos) ~= 58 then bad("expected ':'") end
      pos = pos + 1
      local v = parse_value(depth + 1)
      if o.map[name] == nil then o.keys[#o.keys + 1] = name end
      o.map[name] = v -- duplicates: the last occurrence wins (§4.2)
      skip_ws()
      local c = byte(s, pos)
      pos = pos + 1
      if c == 125 then return o end
      if c ~= 44 then pos = pos - 1; bad("expected ',' or '}'") end
    end
  end

  local function parse_array(depth)
    pos = pos + 1
    local a = { arr = true }
    skip_ws()
    if byte(s, pos) == 93 then pos = pos + 1; return a end
    while true do
      a[#a + 1] = parse_value(depth + 1)
      skip_ws()
      local c = byte(s, pos)
      pos = pos + 1
      if c == 93 then return a end
      if c ~= 44 then pos = pos - 1; bad("expected ',' or ']'") end
    end
  end

  function parse_value(depth)
    if depth > 1000 then bad("nesting too deep") end
    skip_ws()
    local c = byte(s, pos)
    if c == 123 then return parse_object(depth)
    elseif c == 91 then return parse_array(depth)
    elseif c == 34 then return parse_string()
    elseif c == nil then bad("unexpected end of input")
    elseif find(s, "^[-0-9tfn]", pos) then bad("numbers, true, false and null are not allowed")
    else bad("unexpected character") end
  end

  if sub(s, 1, 3) == "\239\187\191" then pos = 4 end -- optional BOM
  local v = parse_value(0)
  skip_ws()
  if pos <= #s then bad("trailing data") end
  return v
end

------------------------------------------------------------------------------
-- §4: validate the whole document before touching the file system
------------------------------------------------------------------------------
local function validate(v, where)
  if type(v) == "string" then return end
  if v.arr then
    if #v ~= 2 or type(v[1]) ~= "string" or type(v[2]) ~= "string" then
      fail(where .. ': an array must be ["link", target] or ["script", content]')
    end
    if v[1] ~= "link" and v[1] ~= "script" then fail(where .. ": unknown array kind " .. v[1]) end
    if v[1] == "link" and find(v[2], "\0", 1, true) then fail(where .. ": a link target cannot contain NUL") end
    return
  end
  for _, name in ipairs(v.keys) do
    local child = where == "." and name or where .. "/" .. name
    if name == "" or name == "." or name == ".." or find(name, "/", 1, true) or find(name, "\0", 1, true) then
      fail(child .. ": invalid name")
    end
    validate(v.map[name], child)
  end
end


------------------------------------------------------------------------------
-- §5: file system, through vim.uv (libuv)
------------------------------------------------------------------------------
local function check(p, what, ok, err)
  if ok == nil then fail(p .. ": " .. what .. ": " .. tostring(err)) end
  return ok
end

-- returns nil (missing), "dir" or "other"; never follows symlinks
local function lstat_kind(p)
  local st, err, name = uv.fs_lstat(p)
  if not st then
    if name == "ENOENT" then return nil end
    fail(p .. ": lstat: " .. tostring(err))
  end
  return st.type == "directory" and "dir" or "other"
end

local function clear(p, kind)
  if kind == "dir" then fail(p .. ": a directory is in the way") end
  if kind then check(p, "unlink", uv.fs_unlink(p)) end
end

local function write_file(p, content, executable)
  -- "wx" = O_CREAT|O_EXCL: never writes through an entry that appeared after clear()
  local fd = check(p, "open", uv.fs_open(p, "wx", 438)) -- 0666 & ~umask
  local off, n = 0, #content
  while off < n do
    local w, err = uv.fs_write(fd, sub(content, off + 1), off)
    if not w then uv.fs_close(fd); fail(p .. ": write: " .. tostring(err)) end
    off = off + w
  end
  if executable then
    local st, err = uv.fs_fstat(fd)
    if not st then uv.fs_close(fd); fail(p .. ": fstat: " .. tostring(err)) end
    local ok, err2 = uv.fs_fchmod(fd, bit.bor(bit.band(st.mode, 4095), 73)) -- | 0111
    if not ok then uv.fs_close(fd); fail(p .. ": fchmod: " .. tostring(err2)) end
  end
  check(p, "close", uv.fs_close(fd))
end

local function apply(dir, tree)
  local names = {}
  for i, k in ipairs(tree.keys) do names[i] = k end
  table.sort(names) -- LuaJIT compares strings bytewise: ascending UTF-8 byte order
  for _, name in ipairs(names) do
    local p = dir .. "/" .. name
    local v = tree.map[name]
    local kind = lstat_kind(p)
    if type(v) == "string" then
      clear(p, kind)
      write_file(p, v, false)
    elseif v.arr then
      clear(p, kind)
      if v[1] == "link" then
        check(p, "symlink", uv.fs_symlink(v[2], p))
      else
        write_file(p, v[2], true)
      end
    else
      if kind ~= "dir" then
        if kind then check(p, "unlink", uv.fs_unlink(p)) end
        check(p, "mkdir", uv.fs_mkdir(p, 511)) -- 0777
      end
      apply(p, v)
    end
  end
end

------------------------------------------------------------------------------
-- §7: command line
------------------------------------------------------------------------------
local function read_stdin()
  local chunks = {}
  while true do
    local data, err = uv.fs_read(0, 65536, -1)
    if not data then fail("cannot read standard input: " .. tostring(err)) end
    if data == "" then break end
    chunks[#chunks + 1] = data
  end
  return table.concat(chunks)
end

local function main(args)
  if #args > 0 then
    io.stderr:write("usage: json2dir < document.json\n")
    return 2
  end
  local ok, err = pcall(function()
    local input = read_stdin()
    check_utf8(input)
    local doc = parse(input)
    if type(doc) ~= "table" or not doc.obj then fail("the root of the document must be an object") end
    validate(doc, ".")
    apply(".", doc)
  end)
  if ok then return 0 end
  io.stderr:write("json2dir: " .. (type(err) == "table" and err.msg or tostring(err)) .. "\n")
  return 1
end

os.exit(main(_G.arg or {}))
