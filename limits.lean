import data.set data.nat
open algebra eq.ops set nat set.filter function

variables {X Y Z : Type}

/- filtermaps -/

attribute [reducible] mem

definition filtermap (f : X → Y) (F : filter X) : filter Y :=
⦃filter,
  sets          := λ P, eventually (λ x, P (f x)) F,
  univ_mem_sets := by rewrite [rfl]; exact !univ_mem_sets,
  inter_closed  := take a b, assume Ha Hb,
                   by rewrite [rfl]; exact (!inter_closed Ha Hb),
  is_mono       := take a b, assume Hab Ha,
                   !is_mono (λ x H, Hab (f x) H) Ha⦄

variables {P : Y → Prop} {F F' : filter X}

theorem eventually_filtermap {f : X → Y} : 
  eventually P (filtermap f F) ↔ eventually (λ x, P (f x)) F := 
!iff.refl

theorem filtermap_id : filtermap (λ x, x) F = F := 
filter.eq rfl

theorem filtermap_filtermap {f : X → Y} {g : Y → Z} :
  filtermap g (filtermap f F) = filtermap (λ x, g (f x)) F :=
rfl

theorem filtermap_mono {f : X → Y} : F ≼ F' → filtermap f F ≼ filtermap f F' := 
suppose F ≼ F', take s, assume H, this H

theorem filtermap_bot {f : X → Y} : filtermap f ⊥ = ⊥ :=
filter.eq (ext(take x, !iff.refl))

theorem filtermap_sup {f : X → Y} : 
  filtermap f (sup F F') = sup (filtermap f F) (filtermap f F') := 
filter.eq (ext(take x, !iff.refl))

theorem filtermap_inf {f : X → Y} : 
  filtermap f (inf F F') ≼ inf (filtermap f F') (filtermap f F) :=
take x, assume H, obtain s Hs t Ht Hst, from H,
show _, from exists.intro _ (and.intro Ht (exists.intro _ (and.intro Hs 
  (take y, assume H', Hst (f y) (by rewrite[inter.comm]; apply H')))))

/- limits -/

definition filterlim (f : X → Y) (F2 : filter Y) (F1 : filter X) : Prop := filtermap f F1 ≼ F2

variables {F1 F1' : filter X} {F2 F2' G G' : filter Y} {F3 : filter Z}

theorem filterlim_iff {f : X → Y} : 
  filterlim f F2 F1 ↔ (∀ P, eventually P F2 → eventually (λ x, P (f x)) F1) := 
iff.intro
  (suppose filterlim f F2 F1, 
    take P, assume H', this H')
  (suppose ∀ P, eventually P F2 → eventually (λ x, P (f x)) F1, 
    take P, assume H', this P H')

theorem filterlim_compose {f : X → Y} {g : Y → Z} :
  filterlim g F3 F2 → filterlim f F2 F1 → filterlim (λ x, g (f x)) F3 F1 := 
suppose Hg : filterlim g F3 F2, 
suppose Hf : filterlim f F2 F1,
take P, assume H, show _, from Hf (Hg H)

theorem filterlim_mono {f : X → Y} :
  filterlim f F2 F1 → F2 ≼ F2' → F1' ≼ F1 → filterlim f F2' F1' :=
suppose Hf : filtermap f F1 ≼ F2,
suppose HF2 : F2 ≼ F2',
suppose HF1 : F1' ≼ F1,
  take P, suppose P ∈ F2',
  have P ∈ filtermap f F1, from Hf (HF2 this),
  show P ∈ filtermap f F1',from (filtermap_mono HF1) this

theorem filterlim_id : filterlim (λx, x) F F :=
take P, assume H, H

theorem filterlim_inf {f : X → Y} :
  ((filterlim f G F) ∧ (filterlim f G F')) → filterlim f G (inf F F'):= 
assume H, take P, assume PG,
exists.intro _ (and.intro ((and.elim_left H) P PG) 
  (exists.intro _ (and.intro ((and.elim_right H) P PG) 
    (take x, assume H', and.elim_left H'))))

theorem filterlim_sup {f : X → Y} :
  filterlim f G F → filterlim f (sup G G') F := 
assume H, λ P H', H P (and.elim_left H')

theorem filterlim_filtermap {f : X → Y} {g : Y → Z} :
  filterlim g F3 (filtermap f F1) ↔ filterlim (λx, g (f x)) F3 F1 :=
!iff.refl

theorem filterlim_Inf1 {f : X → Y} {S : set (filter Y)} : 
  filterlim f (Inf S) F → ∀₀ B ∈ S, filterlim f B F := 
suppose filterlim f (Inf S) F, take B, assume BS, take P, assume PB,
show _, from this take F, suppose ∀ G, G ∈ S → G ≽ F, (this B BS) PB

theorem filterlim_Inf2 {f : X → Y} {S : set (filter Y)} (HS : ∃₀ B ∈ S, ∀₀ G ∈ S, G ≽ B) :
  (∀₀ B ∈ S, filterlim f B F) → filterlim f (Inf S) F :=
assume H, take P, assume H', 
obtain B BS HB, from HS, 
show _, from (@H B BS) P (H' HB)
