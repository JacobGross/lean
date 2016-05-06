import("util.lua")
local ps   = proof_state()
local env  = environment()
local Bool = Const("Bool")
env:add_var("p", Bool)
env:add_var("q", Bool)
local p, q = Consts("p, q")
local ctx  = context()
ctx = ctx:extend("H1", p)
ctx = ctx:extend("H2", q)
ps  = to_proof_state(env, ctx, p)
local ios = io_state()
print(ps)
local ltac = tactic(function(env, ios, s)
                       print("FIRST tactic in Lua, current state: " .. tostring(s));
                       return s
end)