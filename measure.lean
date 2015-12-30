import data.real data.set data.nat theories.topology.basic
open real eq.ops set nat 

/- sigma_algebras -/

structure sigma_algebra [class] (X : Type) :=
  (measurables : set (set X))
  (univ_measurable : univ ∈ measurables)
  (complements_measurable : ∀ S, S ∈ measurables → (-S ∈ measurables))
  (sUnion_measurable : ∀ {S : set (set X)}, S ⊆ measurables → ⋃₀ S ∈ measurables)

namespace sigma_algebra

variable {X : Type}

attribute [coercion] sigma_algebra.measurables

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
  assert -r ∈ M, from !sigma_algebra.complements_measurable (H (and.elim_left Hr)),
  show _, from (and.elim_right Hr) ▸ this,
have ⋃₀ (complement '[s]) ∈ M, from !sigma_algebra.sUnion_measurable this,
show _, from !sInter_eq_comp_sUnion_comp⁻¹ ▸ (!sigma_algebra.complements_measurable this)

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

/- sigma algebra generated by a set and Borel sets  -/

inductive measurables_generated_by (B : set (set X)) : set X → Prop :=
| generators_mem  : ∀ ⦃s : set X⦄, s ∈ B → measurables_generated_by B s
| univ_mem        : measurables_generated_by B univ
| complements_mem : ∀ ⦃s : set X⦄, measurables_generated_by B s → measurables_generated_by B (-s)
| sUnion_mem      : ∀ ⦃S : set (set X)⦄, S ⊆ measurables_generated_by B → measurables_generated_by B (⋃₀ S)

definition sigma_algebra_generated_by [instance] [reducible] (G : set (set X)) : sigma_algebra X :=
⦃sigma_algebra,
  measurables            := measurables_generated_by G,
  univ_measurable        := measurables_generated_by.univ_mem G,
  complements_measurable := measurables_generated_by.complements_mem, 
  sUnion_measurable      := measurables_generated_by.sUnion_mem ⦄

definition Borel_sets [τ : topology X] : sigma_algebra X := sigma_algebra_generated_by (topology.opens X)

/- complete lattice -/

protected definition le (M N : sigma_algebra X) : Prop := M ⊆ N

definition sigma_algebra_has_le [reducible] [instance] :
  has_le (sigma_algebra X) := 
has_le.mk sigma_algebra.le

protected theorem le_refl (M : sigma_algebra X) : M ≤ M := subset.refl M

protected theorem le_trans (M N L : sigma_algebra X) : M ≤ N → N ≤ L → M ≤ L := 
assume H1, assume H2,
subset.trans H1 H2

protected proposition eq {M N : sigma_algebra X} (H : @sigma_algebra.measurables X M = @sigma_algebra.measurables X N) :
  M = N :=
sorry

protected theorem le_antisymm (M N : sigma_algebra X) : M ≤ N → N ≤ M → M = N := 
assume H1, assume H2,
sigma_algebra.eq (subset.antisymm H1 H2)

protected definition inf (M N : sigma_algebra X) : sigma_algebra X := sigma_algebra_generated_by (M ∩ N)

protected definition sup (M N : sigma_algebra X) : sigma_algebra X := sigma_algebra_generated_by (M ∪ N)

private definition to_sets (S : set (sigma_algebra X)) : set (set (set X)) := {s | ∃₀ t ∈ S, s = @sigma_algebra.measurables X t}

protected definition Sup (S : set (sigma_algebra X)) : sigma_algebra X := sigma_algebra_generated_by (⋃₀ (to_sets S))

protected definition Inf (S : set (sigma_algebra X)) : sigma_algebra X := sigma_algebra_generated_by (⋂₀ (to_sets S))

protected theorem inf_le_left : ∀ M N : sigma_algebra X, (sigma_algebra.inf M N) ≤ M := sorry

protected theorem inf_le_right : ∀ M N : sigma_algebra X, (sigma_algebra.inf M N) ≤ N := sorry

protected theorem le_inf : ∀ M N L : sigma_algebra X, L ≤ M → L ≤ N → L ≤ (sigma_algebra.inf M N) := sorry 

protected theorem le_sup_left : ∀ M N : sigma_algebra X, M ≤ (sigma_algebra.sup M N) := sorry

protected theorem le_sup_right : ∀ M N : sigma_algebra X, N ≤ (sigma_algebra.sup M N) := sorry

protected theorem sup_le : ∀ M N L : sigma_algebra X, M ≤ L → N ≤ L → (sigma_algebra.sup M N) ≤ L := sorry

protected theorem Inf_le : ∀ (a : sigma_algebra X) (s : set (sigma_algebra X)), a ∈ s → ((sigma_algebra.Inf s) ≤ a) := sorry

protected theorem le_Inf :
  ∀ (b : sigma_algebra X) (s : set (sigma_algebra X)), (∀ (a : sigma_algebra X), a ∈ s → b ≤ a) → b ≤ (sigma_algebra.Inf s) := sorry

protected theorem le_Sup : ∀ (a : sigma_algebra X) (s : set (sigma_algebra X)), a ∈ s → a ≤ (sigma_algebra.Sup s) := sorry

protected theorem Sup_le :
  ∀ (b : sigma_algebra X) (s : set (sigma_algebra X)) (h : ∀ (a : sigma_algebra X), a ∈ s → a ≤ b), (sigma_algebra.Sup s) ≤ b := sorry

protected definition complete_lattice [reducible] [trans_instance] :
  complete_lattice (sigma_algebra X) :=
⦃complete_lattice,
  le           := sigma_algebra.le,
  le_refl      := sigma_algebra.le_refl,
  le_trans     := sigma_algebra.le_trans,
  le_antisymm  := sigma_algebra.le_antisymm,
  inf          := sigma_algebra.inf,
  sup          := sigma_algebra.sup,
  inf_le_left  := sigma_algebra.inf_le_left,
  inf_le_right := sigma_algebra.inf_le_right,
  le_inf       := sigma_algebra.le_inf,
  le_sup_left  := sigma_algebra.le_sup_left,
  le_sup_right := sigma_algebra.le_sup_right,
  sup_le       := sigma_algebra.sup_le,
  Inf          := sigma_algebra.Inf,
  Sup          := sigma_algebra.Sup,
  Inf_le       := sigma_algebra.Inf_le,
  le_Inf       := sigma_algebra.le_Inf,
  le_Sup       := sigma_algebra.le_Sup,
  Sup_le       := sigma_algebra.Sup_le ⦄

end sigma_algebra
