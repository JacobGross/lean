print("hello world")
local env = environment()
env:import("Int")
parse_lean_cmds([[ variables a b : Int ]], env)
print(parse_lean([[a + b + 10]], env))
