local b1 = binder_info()
assert(not b1:is_implicit())

local f = Const("f")
local a = Const("a")
local t = f(a)
assert(t:fn() == f)
assert(t:arg() == a)
assert(not pcall(function() f:fn() end))

local a1 = Local("a", Prop)
local pi1 = Pi(a1, Type)
assert(pi1:is_pi())
assert(not pcall(function() f:binding_name() end))
local pi2 = mk_pi("a", Prop, Type, binder_info(true, true))
local pi3 = mk_pi("a", Prop, Type)
assert(pi2:binding_info():is_implicit())
assert(not pi3:binding_info():is_implicit())

local l1 = mk_lambda("a", Prop, Var(0))
local l2 = mk_lambda("a", Prop, Var(0), binder_info(true, false))
assert(not l1:binding_info():is_implicit())
assert(l2:binding_info():is_implicit())


local a = Local("a", Prop)
local b = Local("b", Prop)
local pi3 = Pi(a, b, a)
print(pi3)
assert(not pcall(function() Pi(a) end))
local pi4 = Pi(a, b, a)
print(pi4)
assert(pi4:binding_name() == name("a"))
assert(pi4:binding_domain() == Prop)
assert(pi4:binding_body():is_pi())


assert(f:kind() == expr_kind.Constant)
assert(pi3:kind() == expr_kind.Pi)

assert(f:is_constant())
assert(Var(0):is_var())
assert(f(a):is_app())
assert(l1:is_lambda())
assert(pi3:is_pi())
assert(l1:is_binding())
assert(pi3:is_binding())
assert(mk_metavar("m", Prop):is_metavar())
assert(mk_local("m", Prop):is_local())
assert(mk_metavar("m", Prop):is_mlocal())
assert(mk_local("m", Prop):is_mlocal())
assert(mk_metavar("m", Prop):is_meta())
assert(mk_metavar("m", Prop)(a):is_meta())
assert(f(mk_metavar("m", Prop)):has_metavar())
assert(f(mk_local("l", Prop)):has_local())
assert(not f(mk_metavar("m", Prop)):has_local())
assert(not f(mk_local("l", Prop)):has_metavar())
assert(f(mk_sort(mk_param_univ("l"))):has_param_univ())
assert(f(Var(0)):has_free_vars())
assert(not f(Var(0)):closed())
assert(f(a):closed())

assert(Var(0):data() == 0)
assert(Const("a"):data() == name("a"))
assert(mk_sort(mk_param_univ("l")):data() == mk_param_univ("l"))
local f1, a1 = f(a):data()
assert(f1 == f)
assert(a1 == a)
local m1, t1 = mk_metavar("a", Prop):data()
assert(m1 == name("a"))
assert(t1 == Prop)
local m1, t1 = mk_local("a", Prop):data()
assert(m1 == name("a"))
assert(t1 == Prop)
local a1, t, b1, bi = mk_pi("a", Prop, Var(0), binder_info(true)):data()
assert(a1 == name("a"))
assert(t == Prop)
assert(b1 == Var(0))
assert(bi:is_implicit())
assert(f:is_constant())
f(f(a)):for_each(function (e, o) print(tostring(e)); return true; end)
assert(f(Var(0)):lift_free_vars(1) == f(Var(1)))
assert(f(Var(1)):lift_free_vars(1, 1) == f(Var(2)))
assert(f(Var(1)):lift_free_vars(2, 1) == f(Var(1)))
assert(f(Var(1)):lower_free_vars(1, 1) == f(Var(0)))
assert(f(Var(1)):lower_free_vars(4, 1) == f(Var(1)))
assert(f(Var(0), Var(1)):instantiate(a) == f(a, Var(0)))
assert(f(Var(0), Var(1)):instantiate({a, b}) == f(a, b))
assert(f(a, b):abstract(a) == f(Var(0), b))
assert(f(a, b):abstract({a, b}) == f(Var(1), Var(0)))

assert(a:occurs(f(a)))
enable_expr_caching(false)
assert(not f(a):is_eqp(f(a)))
assert(f(a):arg():is_eqp(a))
assert(f(a):weight() == 3)
print(f(a):hash())
