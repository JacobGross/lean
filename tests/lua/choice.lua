local f = Const("f")
local a = Const("a")
local c = mk_choice(f(a), a, f(f(a)))
print(c)
assert(is_choice(c))
assert(get_num_choices(c) == 3)
assert(get_choice(c, 0) == f(a))
assert(get_choice(c, 1) == a)
assert(get_choice(c, 2) == f(f(a)))
assert(mk_choice(f(a)) == f(a))
check_error(function() mk_choice() end)
check_error(function() get_num_choices(f(a)) end)
check_error(function() get_choice(f(a)) end)
check_error(function() get_choice(c, 3) end)