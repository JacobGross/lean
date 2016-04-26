import logic

namespace setoid
  inductive setoid : Type :=
  mk_setoid: Π (A : Type'), (A → A → Prop) → setoid

  set_option pp.universes true

  check setoid
  definition test : Type.{2} := setoid.{0}

  definition carrier (s : setoid)
  := setoid.rec (λ a eq, a) s

  definition eqv {s : setoid} : carrier s → carrier s → Prop
  := setoid.rec (λ a eqv, eqv) s

  infix `≈` := eqv

  attribute carrier [coercion]

  inductive morphism (s1 s2 : setoid) : Type :=
  mk : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism s1 s2

  check morphism.mk
  check λ (s1 s2 : setoid), s1
  check λ (s1 s2 : Type), s1

  inductive morphism2 (s1 : setoid) (s2 : setoid) : Type :=
  mk : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism2 s1 s2

  check morphism2
  check morphism2.mk

  inductive my_struct : Type :=
  mk_foo : Π (s1 s2 : setoid) (s3 s4 : setoid), morphism2 s1 s2 → morphism2 s3 s4 → my_struct

  check my_struct
  definition tst2 : Type.{4} := my_struct.{1 2 1 2}
end setoid
