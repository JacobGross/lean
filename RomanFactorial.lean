import data.nat.div data.nat.fact data.int data.rat
open nat int rat 

namespace Roman_Factorial

definition neg_fact : ℕ → ℤ
| 0        := 1
| (succ n) := -(succ n) * (neg_fact n)

definition int_fact : ℤ → ℤ 
| (of_nat n) := fact n
| -[1+ n]    := -[1+ n]*(neg_fact n)

definition Roman_fact : ℤ → ℚ :=
  λ n, if n ≥ 0 then 
    int_fact n
  else 
    (-1)^(n + 1) / int_fact(-n - 1) -- get negative powers

end Roman_Factorial
