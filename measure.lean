import data.real data.set data.nat theories.topology.basic
open real eq.ops set nat 

/- sigma algebras -/

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

definition sigma_algebra_inf (M N : sigma_algebra X) : sigma_algebra X :=
⦃sigma_algebra,
  measurables            := M ∩ N,
  univ_measurable        := and.intro (@sigma_algebra.univ_measurable X M) (@sigma_algebra.univ_measurable X N),
  complements_measurable := take s, assume H, and.intro
                             ((@sigma_algebra.complements_measurable X M) s (and.elim_left H))
                             ((@sigma_algebra.complements_measurable X N) s (and.elim_right H)),
  sUnion_measurable      := take s, assume H, and.intro
                            ((@sigma_algebra.sUnion_measurable X M) s (λ x Hx, and.elim_left ((H x) Hx)))
                            ((@sigma_algebra.sUnion_measurable X N) s (λ x Hx, and.elim_right ((H x) Hx))) ⦄

protected definition inf (M N : sigma_algebra X) : sigma_algebra X := sigma_algebra_inf M N

private definition to_sets (S : set (sigma_algebra X)) : set (set (set X)) := {s | ∃₀ t ∈ S, s = @sigma_algebra.measurables X t}

definition sigma_algebra_Inf (S : set (sigma_algebra X)) : sigma_algebra X :=
⦃sigma_algebra,
  measurables            := ⋂₀ (to_sets S),
  univ_measurable        := λ s H, obtain t Ht, from H,
                            show _, from (and.elim_right Ht)⁻¹ ▸ (sigma_algebra.univ_measurable X),
  complements_measurable := λ s H x Hx, obtain t Ht, from Hx,
                            have s ∈ @sigma_algebra.measurables X t, from (and.elim_right Ht) ▸ (H Hx),
                            show _, from (and.elim_right Ht)⁻¹ ▸ (sigma_algebra.complements_measurable s this),
  sUnion_measurable      := λ s H x Hx, obtain t Ht, from Hx,
                            have Htr : x = @sigma_algebra.measurables X t, from and.elim_right Ht,
                            have s ⊆ @sigma_algebra.measurables X t, from 
                              take y, suppose y ∈ s,
                              have ∀₀ z ∈ (to_sets S), y ∈ z, from mem_of_subset_of_mem H this,
                              show _, from Htr ▸ (this Hx),
                            show _, from Htr⁻¹ ▸ (sigma_algebra.sUnion_measurable this)⦄

protected definition Inf (S : set (sigma_algebra X)) : sigma_algebra X := sigma_algebra_Inf S

protected definition sup (M N : sigma_algebra X) : sigma_algebra X := sigma_algebra.Inf {s | (M ∪ N) ⊆ s}

protected definition Sup (S : set (sigma_algebra X)) : sigma_algebra X := sigma_algebra.Inf {s| ⋃₀ (to_sets S) ⊆ s}

protected definition complete_lattice [reducible] [trans_instance] :
  complete_lattice (sigma_algebra X) :=
⦃complete_lattice,
  le           := sigma_algebra.le,
  le_refl      := sigma_algebra.le_refl,
  le_trans     := sigma_algebra.le_trans,
  le_antisymm  := sigma_algebra.le_antisymm,
  inf          := sigma_algebra.inf,
  sup          := sigma_algebra.sup,
  inf_le_left  := λ M N x H, !inter_subset_left H,
  inf_le_right := λ M N x H, !inter_subset_right H,
  le_inf       := sorry,
  le_sup_left  := sorry,
  le_sup_right := sorry,
  sup_le       := sorry,
  Inf          := sigma_algebra.Inf,
  Sup          := sigma_algebra.Sup,
  Inf_le       := sorry,
  le_Inf       := sorry,
  le_Sup       := sorry,
  Sup_le       := sorry ⦄ 

/- Borel sets -/

section
  open topology classical

  variable [τ : topology X]

  include τ

  definition Borel_algebra : sigma_algebra X := sigma_algebra.Inf {s | opens X ⊆ s}

  definition Borel (s : set X) : Prop := s ∈ Borel_algebra

  theorem open_Borel : ∀ s : set X, Open s → Borel s := sorry

  theorem closed_Borel : ∀ s : set X, closed s → Borel s := 
  take s, assume H, !comp_comp ▸ 
    ((@sigma_algebra.complements_measurable X Borel_algebra) (-s) (open_Borel (-s) H)) 

end

end sigma_algebra
