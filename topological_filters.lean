import data.set theories.topology.basic 
open algebra eq.ops set topology set.filter

namespace topological_filter

/- eventually elims -/

variable {X : Type}

theorem eventually_and_elim_left {P Q : X → Prop} {F : filter X} (H : eventually (λ x, P x ∧ Q x) F) :
  eventually P F :=
!filter.is_mono (λ x HPQ, and.elim_left HPQ) H

theorem eventually_and_elim_right {P Q : X → Prop} {F : filter X} (H : eventually (λ x, P x ∧ Q x) F) :
  eventually Q F :=
!filter.is_mono (λ x HPQ, and.elim_right HPQ) H

variables {P Q : X → Prop} (F : filter X)

/- frequently -/

definition frequently (P : X → Prop) (F : filter X) : Prop := ¬ eventually (λ x, ¬ P x) F 

theorem eventually_imp_not_frequently : eventually (λ x, ¬ P x) F → ¬ frequently P F :=
not_not_intro

theorem frequently_mono (H₁ : frequently P F) (H₂ : ∀ x, P x → Q x) : frequently Q F :=
(not.mto (λ H, eventually_mono H ( λ x, not.mto (H₂ x)))) H₁

theorem frequently_mp (ev : eventually (λ x, P x → Q x) F) :
  frequently P F → frequently Q F := 
not.mto (λ H, eventually_mp (eventually_mono ev (λ x HPQ, not.mto HPQ)) H)

theorem not_frequently_false : ¬(frequently (λ x, false) F) := 
not.intro(assume H,
  have @univ X = (λx , ¬false), from ext (take x, iff.intro 
    (λ H, not.intro(λ f, f)) (λ H, !mem_univ)),
  absurd (this ▸ !univ_mem_sets) H)

section
  open classical

theorem not_frequently_iff  : ¬ frequently P F ↔ (eventually (λ x, ¬ P x) F) := 
iff.intro
  (assume H, not_not_elim H)
  (assume H, not_not_intro H)

theorem frequently_ex : frequently P F → ∃ x, P x := 
assume H, obtain x Hx, from !exists_not_of_not_eventually H, 
show _, from exists.intro x (not_not_elim Hx)

theorem frequently_inl (H₁ : frequently P F) : frequently (λx , P x ∨ Q x) F :=
have H1 : ¬(eventually (λ x, ¬ P x ∧ ¬ Q x) F), from not.intro(
  assume H, absurd 
    (and.intro (eventually_and_elim_left H) (eventually_and_elim_right H)) 
    ((iff.elim_right not_and_iff_not_or_not) (or.inl H₁))),
show _, from not.intro(
  assume H,
  have ∀ x, ¬ (P x ∨ Q x) → ¬ P x ∧ ¬ Q x, from take x, assume H',
    (iff.elim_left not_or_iff_not_and_not) H',
  absurd (!filter.is_mono this H) H1)

theorem frequently_inr (H₁ : frequently Q F) : frequently (λx , P x ∨ Q x) F :=
have H1 : ¬(eventually (λ x, ¬ P x ∧ ¬ Q x) F), from not.intro(
  assume H, absurd 
    (and.intro (eventually_and_elim_left H) (eventually_and_elim_right H)) 
    ((iff.elim_right not_and_iff_not_or_not) (or.inr H₁))),
show _, from not.intro(
  assume H,
  have ∀ x, ¬ (P x ∨ Q x) → ¬ P x ∧ ¬ Q x, from take x, assume H',
    (iff.elim_left not_or_iff_not_and_not) H',
  absurd (!filter.is_mono this H) H1)

end

/- generated filters -/

inductive sets_generated_by  {X : Type} (B : set (set X)) : set X → Prop :=
| generators_mem : ∀ ⦃s : set X⦄, s ∈ B → sets_generated_by B s
| univ_mem : sets_generated_by B univ
| inter_mem : ∀ {a b}, sets_generated_by B a → sets_generated_by B b → sets_generated_by B (a ∩ b)
| mono_mem : ∀ {a b}, a ⊆ b → sets_generated_by B a → sets_generated_by B b

definition filter_generated_by [reducible] {X : Type} (B : set (set X)) : filter X :=
⦃filter,
  sets            := sets_generated_by B,
  univ_mem_sets   := sets_generated_by.univ_mem B,
  inter_closed    := @sets_generated_by.inter_mem X B,
  is_mono         := @sets_generated_by.mono_mem X B ⦄

theorem generators_mem_filter_generated_by {X : Type} (B : set (set X)) :
 let T := filter_generated_by B in
  ∀₀ s ∈ B, s ∈ T :=
λ s H, sets_generated_by.generators_mem H

theorem sets_generated_by_initial {X : Type} {B : set (set X)} {F : filter X} (H : B ⊆ F) :
  sets_generated_by B ⊆ F :=
begin
  intro s Hs,
  induction Hs with s sB s t os ot soX toX S SB SOX,
    {exact H sB},
    {exact filter.univ_mem_sets F},
    {exact filter.inter_closed F soX toX},
   exact filter.is_mono F SOX v_0
end

theorem filter_generated_by_initial {X : Type} {B : set (set X)} {F : filter X}
    (H : ∀₀ s ∈ B, s ∈ F) {s : set X} (H1 : s ∈ (filter_generated_by B)) :
  s ∈ F := sets_generated_by_initial H H1

/- principal filter -/

definition principal (s : set X) : filter X := filter_generated_by '{s}

theorem set_in_principal_set {s : set X} : s ∈ principal s := 
!generators_mem_filter_generated_by !mem_singleton

theorem eventually_principal {s : set X} : eventually P (principal s) ↔ (s ⊆ P) :=
iff.intro
  (suppose H : eventually P (principal s), 
    have P ∈ filter_generated_by '{s}, from H,
    take x, suppose x ∈ s,
      begin+
        induction H with s Ps,
          {exact ((iff.elim_left !mem_singleton_iff) Ps)⁻¹ ▸ this},
          {exact !mem_univ},
          {exact and.intro (v_0 a_1) (v_1 a_2)},
          {exact a_1 (v_0 a_2)}
      end)
  (suppose H : s ⊆ P, !filter.is_mono H (! set_in_principal_set))

theorem principal_empty : principal (∅ : set X) = ⊥ := 
have sets(principal (∅ : set X)) = sets (⊥), from ext(take x, iff.intro
  (assume H, !mem_univ)
  (assume H, !filter.is_mono (empty_subset x) (!set_in_principal_set))),
filter.eq this

theorem principal_eq_bot_iff {s : set X} : principal s = bot ↔ s = ∅ := sorry

theorem principal_univ : principal (@univ X) = ⊤ := 
have sets (principal (@univ X)) = ⊤, from ext(take x, iff.intro
  (assume H, have univ ⊆ x, from (iff.elim_left eventually_principal) H, 
    show _, from (!eq_univ_of_univ_subset this)⁻¹ ▸ !mem_singleton)
  (assume H, ((iff.elim_left !mem_singleton_iff) H) ▸ !set_in_principal_set)),
filter.eq this

theorem principal_eq_top_iff {s : set X} : principal s = top ↔ s = univ := sorry

theorem eventually_inf_principal {s : set X} : eventually P (inf F (principal s)) ↔ eventually (λ x, x ∈ s → P x) F := sorry

end topological_filter
