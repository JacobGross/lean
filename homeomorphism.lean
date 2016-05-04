import data.set theories.topology.basic theories.topology.continuous
open algebra eq.ops set topology function

variables {X Y Z : Type} [topology X] [topology Y] [topology Z]

namespace homeomorphism

definition homeomorphism_between (f : X → Y) (s : set X) (t : set Y) : Prop :=
  continuous_on f s ∧ ∃ g, inv_on g f s t ∧ continuous_on g t

definition homeomorphism_on (f : X → Y) (s : set X) : Prop :=
  homeomorphism_between f s (f ' s) 

definition homeomorphism (f : X → Y) : Prop :=
 homeomorphism_on f (@univ X)

lemma inv_on_id (s : set X) : 
  inv_on id id s s :=
and.intro (λ x xs, by trivial) (λ x xs, by trivial)

theorem homeomorphism_id {s : set X} :
  homeomorphism_on id s :=
have Hinv: inv_on id id s (id ' s), from !image_id ▸ !inv_on_id,
have ctsid : continuous_on id s, from continuous_on_id s,
have continuous_on id (id ' s), from continuous_on_id (id ' s),
show _, from and.intro ctsid (exists.intro id (and.intro Hinv this))

-- inv_on_comp belongs in set/function

lemma inv_on_comp {s : set X} (f : X → Y) (g : Y → Z) (f' : Y → X) (g' : Z → Y) :
  inv_on f' f s (f ' s) → inv_on g' g (f ' s) (g ' (f ' s)) → inv_on (f' ∘ g') (g ∘ f) s ((g ∘ f) ' s) :=
assume Hf'f,
assume Hg'g,
sorry

theorem homeomorphism_comp {s t: set X} (f : X → Y) (g : Y → Z)
(Hf : homeomorphism_on f s) (Hg : homeomorphism_on g (f ' s) ) :
  homeomorphism_on (g ∘ f) s :=
have continuous_on f s, from and.elim_left Hf,
have continuous_on g (f ' s), from and.elim_left Hg,
obtain f' [(Hinvf : inv_on f' f s (f ' s)) (Hf' : continuous_on f' (f ' s))], from and.elim_right Hf,
obtain g' [(Hinvg : inv_on g' g (f ' s) (g ' (f ' s))) (Hg' : continuous_on g' (g ' (f ' s)))], from and.elim_right Hg,
have ctsfg : continuous_on (g ∘ f) s, from continuous_on_comp (and.elim_left Hf) (and.elim_left Hg),
have invfg : inv_on (f' ∘ g') (g ∘ f) s ((g ∘ f) ' s), from inv_on_comp f g f' g' Hinvf Hinvg,
have ctsg' : continuous_on g' ((g ∘ f) ' s), by rewrite[image_comp]; apply Hg',
have f ' s = g' ' ((g ∘ f) ' s), from ext(take x, iff.intro
  (suppose x ∈ f ' s, 
    obtain z [(zs : z ∈ s) (fzx : f z = x)], from this,
    have Hgfz : (g ∘ f) z ∈ (g ∘ f) ' s, from exists.intro z (and.intro zs rfl),
    have g' (g (f z)) = x, from sorry, -- use inverse property
    have ∃ y, y ∈ ((g ∘ f) ' s) ∧ g' y = x, from exists.intro (g (f z)) (and.intro Hgfz this), 
    show _, from this)
  (suppose x ∈ g' ' ((g ∘ f) ' s), sorry)),
have continuous_on f' (g' ' ((g ∘ f) ' s)), from this ▸ Hf',
have continuous_on (f' ∘ g') ((g ∘ f) ' s), from continuous_on_comp ctsg' this,
show _, from and.intro ctsfg (exists.intro (f' ∘ g') (and.intro invfg this))

theorem homeo_inv_homeo {s : set X} {t : set Y} (f : X → Y) (Hf : homeomorphism_between f s t) :
  ∃ g, inv_on g f s t ∧ continuous_on g t → homeomorphism g :=
sorry
-- move inv_on_id to function (set?) file

definition homeomorphic (s : set X) (t : set Y) : Prop :=
  ∃ f, homeomorphism_between f s t

theorem homeomorphic.refl [refl] (s : set X) : 
  homeomorphic s s := 
have homeomorphism_on id s, from homeomorphism_id,
show _, from exists.intro id (!image_id ▸ this)

theorem homeomorphic.symm [symm] {s t : set X} (H : homeomorphic s t) :
  homeomorphic t s := 
obtain f Hf, from H,
obtain g [invg ctsg], from and.elim_right Hf,
have right_inv_on f g s, from (and.elim_left invg),
have left_inv_on f g t, from (and.elim_right invg),
have inv_on f g t s, from and.intro this (and.elim_left invg),
exists.intro g (and.intro ctsg (exists.intro f (and.intro this (and.elim_left Hf))))

theorem homeomorphic.trans [trans] {s t r : set X} (H1 : homeomorphic s t) (H2 : homeomorphic t r) :
  homeomorphic s r :=
obtain f Hf, from H1,
obtain g Hg, from H2,
have continuous_on f s, from and.elim_left Hf,
have continuous_on g t, from and.elim_left Hg,
obtain f' [(Hf' : inv_on f' f s t)(cf' : continuous_on f' t)], from and.elim_right Hf,
obtain g' [(Hg' : inv_on g' g t r)(cf' : continuous_on g' r)], from and.elim_right Hg, 
-- show that f' and g' are also homeomorphisms
have H1 : continuous_on (g ∘ f) s, from sorry,
have H2 : continuous_on (f' ∘ g') r, from sorry,
have inv_on (f' ∘ g') (g ∘ f) s r, from sorry,
show ∃ h, homeomorphism_between h s r, from exists.intro (g ∘ f)
  (and.intro H1 (exists.intro (f' ∘ g') (and.intro this H2)))


-- instantiate homeomorphism as equivalence... why is that wrong?

definition open_map_on (f : X → Y) (s : set X) : Prop :=
  ∀ t, t ⊆ s → Open t → Open (f ' t)

definition open_map (f : X → Y) : Prop :=
  open_map_on f univ

theorem homeo_on_open_open_map_on {s : set X} (f : X → Y) :
  Open (f ' s) → homeomorphism_on f s → open_map_on f s :=
proof
  assume H1, assume H2,
  obtain g [invg ctsg], from and.elim_right H2,
  take t, assume ts, assume Opt,
  obtain A [OpA HA], from ctsg t Opt,
  have Open (A ∩ f ' s), from Open_inter OpA H1,
  have H : preimage g t ∩ f ' s = f ' t, from ext(take x, iff.intro
    (suppose x ∈ preimage g t ∩ f ' s,
      have g x ∈ t, from mem_of_mem_preimage (and.elim_left this),
      have left_inv_on f g (f ' s), from and.elim_right invg, 
      have f (g x) = x, from this (and.elim_right `x ∈ preimage g t ∩ f ' s`),
      show _, from mem_image `g x ∈ t` this)
    (suppose x ∈ f ' t, 
      obtain y [yt fyx], from this,
      have x ∈ f ' s, from exists.intro y (and.intro (ts yt) fyx),
      have left_inv_on g f s, from and.elim_left invg,
      have g (f y) = y, from this (ts yt),
      have g x ∈ t, by rewrite[-fyx, this]; exact yt,
      show _, from and.intro this `x ∈ f ' s`)),
  show Open (f ' t), by rewrite[-H, -HA]; exact `Open (A ∩ f ' s)`
qed

theorem inj_open_map_on_imp_homeo_on (f : X → Y) (s : set X) :
  inj_on f s → open_map_on f s → homeomorphism_between f s (f ' s) :=
sorry

-- more open mapping theorems

definition closed_map_on (f : X → Y) (s : set X) : Prop :=
  ∀ t, t ⊆ s → closed t → closed (f ' t)

definition closed_map (f : X → Y) : Prop :=
  closed_map_on f univ

-- do closed mapping theorems

-- instantiate as isomorphism in TOP

end homeomorphism
