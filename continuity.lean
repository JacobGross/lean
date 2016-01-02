import data.set theories.topology.basic algebra.category 
open algebra eq.ops sigma.ops set topology function category

namespace continuity

variables {X Y Z : Type} [TX : topology X] [TY : topology Y] [TZ : topology Z]

/- preimages -/

section preimage

definition preimage (f : X → Y) (a : set Y) : set X := {x : X | ∃ y, y ∈ a ∧ f x = y}

theorem mem_preimage {f : X → Y} {a : set Y} {x : X} {y : Y} (H1 : y ∈ a) (H2 : f x = y) : 
  x ∈ preimage f a := 
exists.intro y (and.intro H1 H2)

theorem mem_preimage_iff (f : X → Y) (a : set Y) (x : X) : 
   (f x) ∈ a ↔ x ∈ preimage f a := 
iff.intro
  (assume H, exists.intro (f x) (and.intro H rfl))
  (assume H, obtain y [H1 H2], from H, by rewrite[H2]; apply H1)

theorem preimage_compose (f : Y → Z) (g : X → Y) (a : set Z) : 
  preimage (f ∘ g) a = preimage g (preimage f a) := 
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

theorem preimage_subset {a b : set Y} (f : X → Y) (H : a ⊆ b) : 
  preimage f a ⊆ preimage f b := 
take x, assume Hf, 
obtain y [Hy₁ Hy₂], from Hf,
exists.intro y (and.intro (!H Hy₁) Hy₂)

theorem preimage_union (f : X → Y) (s t : set Y) : 
  preimage f (s ∪ t) = preimage f s ∪ preimage f t := 
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

theorem preimage_id (s : set Y) : preimage (λx, x) s = s := 
ext(take x, iff.intro
  (assume H, obtain y [Hy₁ Hy₂], from H,
    show _, by rewrite[Hy₂]; apply Hy₁)
  (assume H, exists.intro x (and.intro H rfl)))

end preimage

/- continuity -/

section continuous

include TX TY

definition continuous (f : X → Y) : Prop := ∀ V : set Y, Open V → Open (preimage f V)

definition continuous_at (f : X → Y) (x : X) : Prop :=
∀ V, Open V ∧ (f x) ∈ V → Open (preimage f V) ∧ x ∈ preimage f V

section 
  open classical

theorem continuous_at_all_iff_continuous (f : X → Y) : (∀ x, continuous_at f x) ↔ continuous f := 
iff.intro
  (suppose H : ∀ x, continuous_at f x, 
    take V : set Y, suppose OpV : Open V,
    if HV : preimage f V = ∅ then
      by rewrite[HV]; apply Open_empty
    else
      obtain x (Hx : x ∈ preimage f V), from by_contradiction 
        (assume H', HV (eq_empty_of_forall_not_mem (forall_not_of_not_exists H'))),
      have (f x) ∈ V, from (iff.elim_right !mem_preimage_iff) Hx,
      show _, from and.elim_left (((H x) V) (and.intro OpV this)))
  (suppose H : continuous f, 
    take x, take V, assume HV,
    show _, from and.intro 
      (H V (and.elim_left HV)) 
      ((iff.elim_left !mem_preimage_iff) (and.elim_right HV)))

end

include TZ

theorem continuous_composition (f : Y → Z) (g : X → Y) (Hf : continuous f) (Hg : continuous g) :
  continuous (f ∘ g) :=
begin 
  intro V H,
  rewrite[preimage_compose],
  exact (Hg (preimage f V)) ((Hf V) H)
end

theorem continuous_id : continuous (λ x : X, x) := 
take V, assume H, by rewrite[preimage_id]; apply H

end continuous

/- homeomorphisms -/

section homeomorphism

include TX TY

definition homeomorphism (f : X → Y) : Prop := continuous f ∧ bijective f ∧ (∃ g, inv_on g f (@univ X) (@univ Y) ∧ continuous g)

definition open_map (f : X → Y) : Prop := ∀ U, Open U → Open (image f U)

theorem homeomorphism_is_open_map : ∀ f : X → Y, homeomorphism f → open_map f := 
take f, assume H,
obtain g [Hf Hg], from and.elim_right (and.elim_right H), 
take U, assume HU,
  have image f U = preimage g U, from ext(
    take x, iff.intro
      (suppose x ∈ image f U, 
        obtain y [(Hy₁ : y ∈ U) (Hy₂ : f y = x)], from this,
        have g x = y, by rewrite[-Hy₂]; apply (and.elim_left Hf) y !mem_univ,
        exists.intro y (and.intro Hy₁ this))
      (suppose x ∈ preimage g U, 
        obtain y [(Hy₁ : y ∈ U) (Hy₂ : g x = y)], from this,
        have f y = x, by rewrite[-Hy₂]; apply (and.elim_right Hf) x !mem_univ,
        exists.intro y (and.intro Hy₁ this))),
 show Open (image f U), from this⁻¹ ▸ (Hg U HU)

definition invertible (f : X → Y) : Prop := ∃ g, inv_on g f (@univ X) (@univ Y)

theorem inverible_open_map_is_homeomorphism : ∀ f : X → Y, invertible f → continuous f → open_map f → homeomorphism f := sorry

end homeomorphism

/- The category TOP -/

section Top

definition topological_space : Type := Σ X : Type, topology X

definition continuous_top_explicit (TX : topology X) (TY : topology Y) (f : X → Y) : Prop := continuous f

definition continuous_map (X Y : topological_space) : Type := Σ f : X.1 → Y.1, continuous_top_explicit X.2 Y.2 f

protected theorem ID : Π (A : topological_space), continuous_map A A := 
take A : topological_space,
have continuous_top_explicit A.2 A.2 (λ x : A.1, x), from 
  take V, assume H, by rewrite[preimage_id]; apply H,
show continuous_map A A, from sigma.mk (λ x : A.1, x) this

protected theorem comp : Π⦃A B C : topological_space⦄, continuous_map B C → continuous_map A B → continuous_map A C := 
sorry

protected theorem assoc : Π ⦃A B C D : topological_space⦄ (h : continuous_map C D) (g : continuous_map B C) (f : continuous_map A B),
 continuity.comp h (continuity.comp g f) = continuity.comp (continuity.comp h g) f := 
sorry

protected theorem id_left : Π ⦃A B : topological_space⦄ (f : continuous_map A B), continuity.comp !continuity.ID f = f := 
sorry

protected theorem id_right : Π ⦃A B : topological_space⦄ (f : continuous_map A B), continuity.comp f !continuity.ID = f := 
sorry

noncomputable definition TOP [reducible] [trans_instance] : category (topological_space) :=
mk (continuous_map)
   (continuity.comp)
   (continuity.ID)
   (continuity.assoc)
   (continuity.id_left)
   (continuity.id_right)

end Top

end continuity
