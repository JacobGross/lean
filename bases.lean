import data.set theories.topology.basic
open algebra eq.ops set topology function

-- Should we work with bundled structures here?

variables {X : Type} [topology X]

namespace base

definition base (B : set (set X)) :=
  (∀₀ b ∈ B, Open b) ∧ (∀ U, Open U → ∃ s, s ⊆ B ∧ U = ⋃₀ s)

definition basis  (B : set (set X)) :=
  (∀₀ b ∈ B, Open b) ∧ (∀ U, Open U → ∀₀ x ∈ U, ∃₀ V ∈ B, x ∈ V ∧ V ⊆ U)

theorem base_basis {B : set (set X)} :
  base B → basis B :=
sorry

theorem basis_base {B : set (set X)} :
  basis B → base B :=
sorry

-- Define first countable

definition countable {A : Type} (s : set A) :=
  ∃ f : A → ℕ, inj_on f s

structure second_countable [class] (A : Type) extends topology A :=
  (second_countable : ∃ B, (∀₀ b ∈ B, b ∈ opens) ∧ (∀₀ U ∈ opens, ∃ s, s ⊆ B ∧ U = ⋃₀ s) ∧ countable B)

theorem second_countable_countable_base {A : Type} (τ : second_countable A) :
  ∃ B, (@base _ (@second_countable.to_topology _ τ)) B ∧ countable B :=
obtain B [(BaseL) (BaseR) (Countable)], from @second_countable.second_countable A τ,
show _, from exists.intro B (and.intro (and.intro BaseL BaseR) Countable)

-- Show first countable spaces are second countable

-- Move neighborhoods to topology.basic?
 
definition open_neighborhood (U : set X) (x : X) :=
  Open U ∧ x ∈ U

definition neighborhood (N : set X) (x : X) :=
  ∃ U, open_neighborhood U x ∧ U ⊆ N

theorem neighborhood_open_neighborhood (U : set X) (x : X) :
  open_neighborhood U x → neighborhood U x :=
assume H, exists.intro U (and.intro H (subset.refl U))

-- define product topology (first define cartesian products?)

end base
