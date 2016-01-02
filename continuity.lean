import data.set theories.topology.basic algebra.category
open algebra eq.ops set topology function category

namespace continuity

variables {X Y Z : Type} 

/- preimages -/

section preimage

definition preimage (f : X → Y) (a : set Y) : set X := {x : X | ∃ y, y ∈ a ∧ f x = y}

theorem mem_preimage {f : X → Y} {a : set Y} {x : X} {y : Y} (H1 : y ∈ a) (H2 : f x = y) : 
  x ∈ preimage f a := 
exists.intro y (and.intro H1 H2)

theorem preimage_compose (f : Y → Z) (g : X → Y) (a : set Z) : preimage (f ∘ g) a = preimage g (preimage f a) := 
ext(take x,
  iff.intro
    (assume Hz : x ∈ preimage (f ∘ g) a,
      obtain z [Hz₁ Hz₂], from Hz,
      have g x ∈ preimage f a, from exists.intro z (and.intro Hz₁ Hz₂),
      show _, from exists.intro (g x) (and.intro this rfl))
    (assume Hz : x ∈ preimage g (preimage f a), 
      obtain y [Hy₁ Hy₂], from Hz,
      obtain z [Hz₁ Hz₂], from Hy₁,
      have f (g x) = z, by rewrite[-Hz₂]; apply Hy₂ ▸ rfl,
      show _, from exists.intro z (and.intro Hz₁ this)))

theorem preimage_subset {a b : set Y} (f : X → Y) (H : a ⊆ b) : preimage f a ⊆ preimage f b := 
take x, assume Hf, 
obtain y [Hy₁ Hy₂], from Hf,
exists.intro y (and.intro (!H Hy₁) Hy₂)

theorem preimage_union (f : X → Y) (s t : set Y) : preimage f (s ∪ t) = preimage f s ∪ preimage f t := 
ext(take x, iff.intro
  (assume H, obtain y [xst fxy], from H,
    or.elim xst
     (assume xs, or.inl (mem_preimage xs fxy))
     (assume xt, or.inr (mem_preimage xt fxy)))
  (assume H, or.elim H
      (assume xifs : x ∈ preimage f s, 
         obtain y [xs fxy], from xifs,
         exists.intro y (and.intro (or.inl xs) fxy))
      (assume xift : x ∈ preimage f t, 
         obtain y [xr fxy], from xift,
         exists.intro y (and.intro (or.inr xr) fxy))))

theorem preimage_id (s : set Y) : preimage (λ x, x) s = s := 
ext(take x, iff.intro
  (assume H, obtain y [Hy₁ Hy₂], from H,
    show _, by rewrite[Hy₂]; apply Hy₁)
  (assume H, exists.intro x (and.intro H rfl)))

end preimage

/- continuity -/

section continuous

variables [TX : topology X] [TY : topology Y]
include TX TY

definition continuous (f : X → Y) : Prop := ∀ V : set Y, Open V → Open (preimage f V)

definition continuous_at (f : X → Y) (x : X) : Prop :=
∀ V, Open V ∧ (f x) ∈ V → Open (preimage f V) ∧ x ∈ preimage f V

theorem pointwise_continuity_iff_continuity (f : X → Y) : ∀ x, continuous_at f x ↔ continuous f := 
sorry

variable [TZ : topology Z]
include TZ

theorem continuous_composition (f : Y → Z) (g : X → Y) (Hf : continuous f) (Hg : continuous g) :
  continuous (f ∘ g) := 
sorry

theorem continuous_id : continuous (λ x : X, x) := 
sorry

end continuous

section Top

definition topological_space : Type := Σ X, topology X


/-use sigma type projections -/
definition continuity : Type := Π [TX : topology X] [TY : topology Y], Σ f : X → Y, continuous f

definition TOP [reducible] [trans_instance] : category (topological_space) :=
⦃category,  
  hom      := sorry, 
  comp     := sorry,
  ID       := sorry,
  assoc    := sorry,
  id_left  := sorry,
  id_right := sorry ⦄

end Top

section homeomorphism

end homeomorphism

end continuity
