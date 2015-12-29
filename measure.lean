import data.real data.set data.nat 
open real eq.ops set nat

structure sigma_algebra [class] (X : Type) :=
  (measurables : set (set X))
  (univ_measurable : univ ∈ measurables)
  (complements_measurable : ∀ S, S ∈ measurables → (-S ∈ measurables))
  (sUnion_measurable : ∀ S, S ⊆ measurables → ⋃₀ S ∈ measurables)

attribute sigma_algebra.measurables [coercion]

namespace measure

variable {X : Type}

definition disjoint (S : set (set X)) : Prop := ∀₀ a ∈ S, ∀₀ b ∈ S, a ≠ b → a ∩ b = ∅

theorem disjointI (S : set (set X)) : (∀ a b, a ∈ S → b ∈ S → a ≠ b → a ∩ b = ∅) → disjoint S := sorry

theorem disjointD (S : set (set X)) : disjoint S → (∀ a b, a ∈ S → b ∈ S → a ≠ b → a ∩ b = ∅) := sorry

theorem disjoint_empty : disjoint (∅ : set (set X)) := sorry

theorem disjoint_union {S T : set (set X)} (DS : disjoint S) (DT : disjoint T) : disjoint (S ∪ T) := sorry

theorem disjoint_singleton (S : set (set X)) : disjoint '{S} := sorry

theorem measurable_sUnion {S : set (set X)} {M : sigma_algebra X} (H : ∀₀ a ∈ S, a ∈ M) : ⋃₀ S ∈ M := sorry

theorem measurable_cUnion {S : ℕ → set X} {M : sigma_algebra X} (H : ∀ i, S i ∈ M) : (⋃ i, S i) ∈ M := sorry

theorem measurable_cInter {S : ℕ → set X} {M : sigma_algebra X} (H : ∀ i, S i ∈ M) : (⋂ i, S i) ∈ M := sorry

private definition bin_ext (s t : set X) (n : ℕ) : set X :=
nat.cases_on n s (λ m, t)

private lemma Union_bin_ext (s t : set X) : (⋃ i, bin_ext s t i) = s ∪ t :=
ext (take x, iff.intro
  (suppose x ∈ Union (bin_ext s t),
    obtain i (Hi : x ∈ (bin_ext s t) i), from this,
    by cases i; apply or.inl Hi; apply or.inr Hi)
  (suppose x ∈ s ∪ t,
    or.elim this
      (suppose x ∈ s, exists.intro 0 this)
      (suppose x ∈ t, exists.intro 1 this)))

theorem measurable_union {s t : set X} {M : sigma_algebra X} (Hs : s ∈ M) (Ht : t ∈ M) : (s ∪ t) ∈ M := sorry

theorem measurable_inter {s t : set X} {M : sigma_algebra X} (Hs : s ∈ M) (Ht : t ∈ M) : (s ∩ t) ∈ M := sorry

theorem measurable_sUnion_of_finite {S : set (set X)} {M : sigma_algebra X} [fins : finite S] (H : ∀₀ t ∈ S, t ∈ M) :
  (⋃₀ S) ∈ M := sorry

theorem measurable_sInter_of_finite {S : set (set X)} {M : sigma_algebra X} [fins : finite S] (H : ∀₀ t ∈ S, t ∈ M) :
  (⋂₀ S) ∈ M := sorry

theorem measurable_diff {s t : set X} {M : sigma_algebra X} (Hs : s ∈ M) (Ht : t ∈ M) : (s \ t) ∈ M := sorry

theorem measurable_insert {x : X} {s : set X} {M : sigma_algebra X} (Hx : '{x} ∈ M) (Hs : s ∈ M) : (insert x s) ∈ M := sorry


end measure
