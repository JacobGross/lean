local env = bare_environment()
env = add_decl(env, mk_constant_assumption("A", Prop))
local c1  = type_check(env, mk_axiom("p", Const("A")))
local c2  = type_check(env, mk_axiom("q", Const("A")))
env = env:add(c1)
env = env:add(c2)
