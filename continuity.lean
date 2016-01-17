import data.set theories.topology.basic
open algebra eq.ops set topology function

namespace continuity

variables {X Y Z : Type} [TX : topology X] [topology Y] [topology Z]
include TX /- needed to name TX because "continuous_on_const" couldn't find the topology without making it explicit -/

/- preimages -/

attribute mem [reducible]

definition preimage (f : X → Y) (a : set Y) : set X := {x : X | f x ∈ a}

theorem mem_preimage (f : X → Y) (a : set Y) (x : X) (y : Y) (H1 : y ∈ a) (H2 : f x = y) : 
  x ∈ preimage f a := 
show f x ∈ a, from H2⁻¹ ▸ H1 -- Could not just write "H2⁻¹ ▸ H1" here... strange -- this also required marking mem as reducible

theorem mem_preimage_iff (f : X → Y) (a : set Y) (x : X) : 
   (f x) ∈ a ↔ x ∈ preimage f a := 
!iff.refl

theorem preimage_compose (f : Y → Z) (g : X → Y) (a : set Z) : 
  preimage (f ∘ g) a = preimage g (preimage f a) := 
ext(take x, !iff.refl)

theorem preimage_subset {a b : set Y} (f : X → Y) (H : a ⊆ b) : 
  preimage f a ⊆ preimage f b := 
λ x H', H H'

theorem preimage_union (f : X → Y) (s t : set Y) : 
  preimage f (s ∪ t) = preimage f s ∪ preimage f t := 
ext(take x, !iff.refl)

theorem preimage_id (s : set Y) : preimage (λx, x) s = s := 
ext(take x, !iff.refl)

theorem preimage_complement (s : set Y) (f : X → Y) : 
  (-(preimage f s)) = preimage f (-s) := 
ext(take x, !iff.refl)

/- continuity on a set -/

definition continuous_on (U : set X) (f : X → Y) : Prop := ∀ V, Open V → Open (preimage f V ∩ U)

theorem continuous_on_cong (s t : set X) (f g : X → Y) : 
  s = t → (∀₀ x ∈ t, f x = g x) → continuous_on s f → continuous_on t g :=
assume Hst, assume H1 : (∀₀ x ∈ t, f x = g x), assume H2,
take V, suppose OpV : Open V,
have preimage f V ∩ s = preimage g V ∩ t, from ext(take x, iff.intro
  (suppose H : x ∈ preimage f V ∩ s,
    have x ∈ t, from Hst ▸ (and.elim_right H), 
    have g x ∈ V, from (H1 `x ∈ t`) ▸ (and.elim_left H),
    show _, from and.intro this (`x ∈ t`))
  (suppose H : x ∈ preimage g V ∩ t, 
    have x ∈ t, from and.elim_right H,
    have f x ∈ V, from (H1 `x ∈ t`)⁻¹ ▸ (and.elim_left H),
    show _, from and.intro this (Hst⁻¹ ▸ (and.elim_right H)))),
show Open (preimage g V ∩ t), from this ▸ (H2 V OpV)

theorem continuous_imp_open_preimage (U : set X) (V : set Y) (OpV : Open V) (f : X → Y) (sub : preimage f V ⊆ U) : 
   continuous_on U f → Open (preimage f V) := 
assume H : continuous_on U f,
have preimage f V ∩ U = preimage f V, from ext(take x, iff.intro
  (assume H, and.elim_left H)
  (assume H, and.intro H (sub H))),
show _, from this ▸ (H V OpV)

theorem open_preimage (V : set Y) (OpV : Open V) (f : X → Y) : continuous_on univ f → Open (preimage f V) := 
assume H : continuous_on univ f,
have preimage f V ⊆ univ, from λ x xf, !mem_univ,
show _, from (continuous_imp_open_preimage univ V OpV f this) H

theorem closed_preimage (V : set Y) (f : X → Y) (HV : closed V) : 
  continuous_on univ f → closed (preimage f V) := 
suppose continuous_on univ f,
have Open (preimage f (-V)), from open_preimage (-V) HV f this,
show _, from (preimage_complement V f) ▸ this

theorem continuous_on_open_union (s t : set X) (f : X → Y) :
  continuous_on s f → continuous_on t f → continuous_on (s ∪ t) f :=
assume H1, assume H2, take V, suppose OpV : Open V,
have preimage f V ∩ (s ∪ t) = (preimage f V ∩ s) ∪ (preimage f V ∩ t), from ext(λx, !and.left_distrib), -- inter_distrib_left comes up as unidentified
show _, from this⁻¹ ▸ (Open_union (H1 V OpV) (H2 V OpV))

variable {I : Type}

lemma int_distrib_Union_left (s : I → set X) (a : set X) :
  a ∩ (⋃ i, s i) = ⋃ i, a ∩ s i := 
ext(take x, iff.intro
  (assume H, obtain i Hi, from and.elim_right H,
    have x ∈ a ∩ s i, from and.intro (and.elim_left H) Hi,
    show _, from exists.intro i this)
  (assume H, obtain i [xa xsi], from H,
   show _, from and.intro xa (exists.intro i xsi)))

theorem continuous_on_open_Union (s : I → set X) (f : X → Y) :
  (∀ i, continuous_on (s i) f) → continuous_on (⋃ i, s i) f := 
λ H V OpV, !int_distrib_Union_left⁻¹ ▸ (Open_Union (λ i, (H i) V OpV))

theorem continuous_on_id {U : set X} (OpU: Open U) : continuous_on U (λx, x) := 
  by intro V OpV; rewrite[*preimage_id]; exact Open_inter OpV OpU

section
  open classical

theorem continuous_on_const {U : set X} (OpU : Open U) {c : Y} : continuous_on U (λ x : X, c) := 
take V,
suppose OpV : Open V,
if Hc : c ∈ V then 
  have preimage (λx : X, c) V = univ, from ext(take y, 
     iff.intro 
       (assume H, !mem_univ)
       (assume H, Hc)),
  show _, from this⁻¹ ▸ (Open_inter Open_univ OpU)
else 
  have preimage (λx : X, c) V = ∅, from ext(take y,
    iff.intro 
      (assume H, !not.elim Hc H) 
      (assume H, !not.elim !not_mem_empty H)),
  show _, from Open_inter (this⁻¹ ▸ Open_empty) OpU

end

theorem continuous_composition (f : Y → Z) (g : X → Y) {U : set X} :
 continuous_on U g → continuous_on (g '[U]) f → continuous_on U (f ∘ g) := 
assume H1 : continuous_on U g, 
assume H2, take V, assume OpV,
have preimage g (preimage f V ∩ (g '[U])) ∩ U = preimage (f ∘ g) V ∩ U, from ext(
  take x, iff.intro
    (assume H, have x ∈ U, from and.elim_right H,
     have x ∈ preimage g (preimage f V ∩ (g '[U])), from and.elim_left H,
     show f (g x) ∈ V ∧ x ∈ U, from and.intro (and.elim_left this) `x ∈ U`)
    (assume H, have xU : x ∈ U, from and.elim_right H,
      have g x ∈ g '[U], from mem_image_of_mem g xU,
      have g x ∈ preimage f V, by rewrite[↑preimage]; exact and.elim_left H,
      show _, from and.intro (and.intro this (mem_image_of_mem g xU)) xU)),
show _, from this ▸ (!H1 (H2 V OpV))

theorem continuous_composition2 (g : Y → Z) (f : X → Y) (U : set X) :
continuous_on (f '[U]) g → continuous_on U f → continuous_on U (g ∘ f) := 
assume H1, assume H2 : continuous_on U f,
take V, suppose OpV : Open V,
have preimage f (preimage g V ∩ (f '[U])) ∩ U = preimage (g ∘ f) V ∩ U, from ext (take x, iff.intro
    (assume H, have x ∈ U, from and.elim_right H,
     have x ∈ preimage f (preimage g V ∩ (f '[U])), from and.elim_left H,
     show g (f x) ∈ V ∧ x ∈ U, from and.intro (and.elim_left this) `x ∈ U`)
    (assume H, have xU : x ∈ U, from and.elim_right H,
      have f x ∈ f '[U], from mem_image_of_mem f xU,
      have f x ∈ preimage g V, by rewrite[↑preimage]; exact and.elim_left H,
      show _, from and.intro (and.intro this (mem_image_of_mem f xU)) xU)),
show _, from this ▸ (!H2 (H1 V OpV))

end continuity
