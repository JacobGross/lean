import data.real data.set data.nat 
open real eq.ops set nat

structure sigma_algebra [class] (X : Type) :=
  (measurables : set (set X))
  (univ_measurable : univ ∈ measurables)
  (complements_measurable : ∀ S, S ∈ measurables → (-S ∈ measurables))
  (sUnion_measurable : ∀ {S : set (set X)}, S ⊆ measurables → ⋃₀ S ∈ measurables)

attribute sigma_algebra.measurables [coercion]

namespace measure

variable {X : Type}

definition disjoint (S : set (set X)) : Prop := ∀ a b, a ∈ S → b ∈ S → a ≠ b → a ∩ b = ∅

theorem disjoint_empty : disjoint (∅ : set (set X)) := 
take a b, assume H, !not.elim !not_mem_empty H

theorem disjoint_union {s t : set (set X)} (Hs : disjoint s) (Ht : disjoint t) (H : ∀ x y, x ∈ s ∧ y ∈ t → x ∩ y = ∅) :
  disjoint (s ∪ t) := 
take a b, assume Ha Hb Hneq, or.elim Ha
 (assume H1, or.elim Hb
   (suppose b ∈ s, (Hs a b) H1 this Hneq)
   (suppose b ∈ t, (H a b) (and.intro H1 this)))
 (assume H2, or.elim Hb
   (suppose b ∈ s, !inter.comm ▸ ((H b a) (and.intro this H2)))
   (suppose b ∈ t, (Ht a b) H2 this Hneq))

theorem disjoint_singleton (s : set (set X)) : disjoint '{s} := 
take a b, assume Ha Hb Hneq,
!not.elim Hneq (eq.trans ((iff.elim_left !mem_singleton_iff) Ha) ((iff.elim_left !mem_singleton_iff) Hb)⁻¹)

theorem measurable_univ {M : sigma_algebra X} : univ ∈ M := 
sigma_algebra.univ_measurable X

theorem measurable_empty {M : sigma_algebra X} : ∅ ∈ M := 
comp_univ ▸ !sigma_algebra.complements_measurable measurable_univ

theorem measurable_sUnion {s : set (set X)} {M : sigma_algebra X} (H : ∀₀ a ∈ s, a ∈ M) : ⋃₀ s ∈ M := 
sigma_algebra.sUnion_measurable H

theorem measurable_sInter {s : set (set X)} {M : sigma_algebra X} (H : ∀₀ a ∈ s, a ∈ M) : ⋂₀ s ∈ M := 
have ⋂₀ s = -(⋃₀ (complement '[s])) , from !sInter_eq_comp_sUnion_comp,
have complement '[s] ⊆ M, from 
  take x, suppose x ∈ complement '[s],
  obtain r (Hr : r ∈ s ∧ -r = x), from this,
  have -r ∈ M, from !sigma_algebra.complements_measurable (H (and.elim_left Hr)),
  show _, from (and.elim_right Hr) ▸ this,
have ⋃₀ (complement '[s]) ∈ M, from !sigma_algebra.sUnion_measurable this,
!sInter_eq_comp_sUnion_comp⁻¹ ▸ (!sigma_algebra.complements_measurable this)

theorem measurable_cUnion {s : ℕ → set X} {M : sigma_algebra X} (H : ∀ i, s i ∈ M) : (⋃ i, s i) ∈ M := 
have ∀₀ t ∈ s '[univ], t ∈ M,
  from take t, suppose t ∈ s '[univ],
    obtain i [univi (Hi : s i = t)], from this,
    show t ∈ M, by rewrite -Hi; exact H i,
using this, by rewrite Union_eq_sUnion_image; apply measurable_sUnion this

theorem measurable_cInter {s : ℕ → set X} {M : sigma_algebra X} (H : ∀ i, s i ∈ M) : (⋂ i, s i) ∈ M := 
have ∀₀ t ∈ s '[univ], t ∈ M,
  from take t, suppose t ∈ s '[univ],
    obtain i [univi (Hi : s i = t)], from this,
    show t ∈ M, by rewrite -Hi; exact H i,
using this, by rewrite Inter_eq_sInter_image; apply measurable_sInter this

private definition bin_ext (s t : set X) (n : ℕ) : set X :=
nat.cases_on n s (λ m, t)

private lemma Union_bin_ext (s t : set X) : (⋃ i, bin_ext s t i) = s ∪ t :=
ext (take x, iff.intro
  (assume H,
    obtain i (Hi : x ∈ (bin_ext s t) i), from H,
    by cases i; apply or.inl Hi; apply or.inr Hi)
  (assume H,
    or.elim H
      (suppose x ∈ s, exists.intro 0 this)
      (suppose x ∈ t, exists.intro 1 this)))

private lemma Inter_bin_ext (s t : set X) : (⋂ i, bin_ext s t i) = s ∩ t := 
ext (take x, iff.intro
  (assume H, and.intro (H 0) (H 1))
  (assume H, by intro i; cases i; 
    apply and.elim_left H; apply and.elim_right H))

theorem measurable_union {s t : set X} {M : sigma_algebra X} (Hs : s ∈ M) (Ht : t ∈ M) : (s ∪ t) ∈ M := 
have ∀ i, (bin_ext s t i) ∈ M, by intro i; cases i; exact Hs; exact Ht,
show (s ∪ t) ∈ M, using this, by rewrite -Union_bin_ext; exact measurable_cUnion this

theorem measurable_inter {s t : set X} {M : sigma_algebra X} (Hs : s ∈ M) (Ht : t ∈ M) : (s ∩ t) ∈ M := 
have ∀ i, (bin_ext s t i) ∈ M, by intro i; cases i; exact Hs; exact Ht,
show (s ∩ t) ∈ M, using this, by rewrite -Inter_bin_ext; exact measurable_cInter this

theorem measurable_diff {s t : set X} {M : sigma_algebra X} (Hs : s ∈ M) (Ht : t ∈ M) : (s \ t) ∈ M := 
measurable_inter Hs (!sigma_algebra.complements_measurable Ht)

theorem measurable_insert {x : X} {s : set X} {M : sigma_algebra X} (Hx : '{x} ∈ M) (Hs : s ∈ M) : (insert x s) ∈ M := 
!insert_eq⁻¹ ▸ measurable_union Hx Hs

end measure
