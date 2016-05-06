import data.set theories.topology.basic theories.topology.continuous
open algebra eq.ops set topology function

-- shorthanded interated connectives

variables {a b c d : Prop} {A : Type}

proposition and.intro2 (Ha : a) (Hb : b) (Hc : c) : 
  a ∧ b ∧ c :=
and.intro Ha (and.intro Hb Hc)

proposition and.intro2' (Ha : a) (Hb : b) (Hc : c) : 
  (a ∧ b) ∧ c :=
and.intro (and.intro Ha Hb) Hc

proposition and.intro3 (Ha : a) (Hb : b) (Hc : c) (Hd : d) :
  a ∧ b ∧ c ∧ d :=
and.intro Ha (and.intro Hb (and.intro Hc Hd))

proposition and.elimLR (H : a ∧ b ∧ c) :
  b :=
and.elim_left (and.elim_right H)

proposition and.elimRR (H : a ∧ b ∧ c) :
  c :=
and.elim_right (and.elim_right H)

proposition and.elimLL (H : (a ∧ b) ∧ c) :
  a :=
and.elim_left (and.elim_left H)

proposition and.elimRL (H : (a ∧ b) ∧ c) :
  b :=
and.elim_right (and.elim_left H)

proposition exists.intro2 (x y : A) {P : A → A → Prop} (H : P x y) :
  ∃ a b, P a b :=
exists.intro x (exists.intro y H)

-- preliminary lemmas (to be moved to set/function)

variables {X Y Z : Type} [topology X] [topology Y] [topology Z]

lemma image_maps_to (f : X → Y) (s : set X) :
  maps_to f s (f ' s) :=
take a H, mem_image_of_mem f H

lemma image_maps_to_inv {f : X → Y} {g : Y → X} {s : set X} (Hinv : inv_on g f s (f ' s)) :
  maps_to g (f ' s) s :=
take a H, obtain y [(ys : y ∈ s) (fya : f y = a)], from H,
have left_inv_on g f s, from and.elim_left Hinv,
have g a = y, from fya ▸ (this ys),
show g a ∈ s, from this⁻¹ ▸ ys

lemma inv_on_comp {s : set X} {t : set Y} {r : set Z} {f : X → Y} {g : Y → Z} {f' : Y → X} {g' : Z → Y}
(fst : maps_to f s t) (g'rt : maps_to g' r t) :
  inv_on f' f s t → inv_on g' g t r → inv_on (f' ∘ g') (g ∘ f) s r :=
assume Hf'f, assume Hg'g,
have Hleft : left_inv_on (f' ∘ g') (g ∘ f) s, from left_inv_on_comp fst (and.elim_left Hf'f) (and.elim_left Hg'g),
have Hright : right_inv_on (f' ∘ g') (g ∘ f) r, from right_inv_on_comp g'rt (and.elim_right Hf'f) (and.elim_right Hg'g),
show _, from and.intro Hleft Hright

lemma inv_on_comp_image {s : set X} (f : X → Y) (g : Y → Z) (f' : Y → X) (g' : Z → Y) :
  inv_on f' f s (f ' s) → inv_on g' g (f ' s) (g ' (f ' s)) → inv_on (f' ∘ g') (g ∘ f) s ((g ∘ f) ' s) :=
assume Hf'f, assume Hg'g,
have mapf : maps_to f s (f ' s), from image_maps_to f s,
have mapg : maps_to g' (g ' (f ' s)) (f ' s), from image_maps_to_inv Hg'g,
have inv_on (f' ∘ g') (g ∘ f) s (g ' (f ' s)), from inv_on_comp mapf mapg Hf'f Hg'g,
show _, by rewrite[image_comp]; exact this

-- homeomorphism begins here

namespace homeomorphism

definition homeomorphism_between (f : X → Y) (s : set X) (t : set Y) : Prop :=
  maps_to f s t ∧ continuous_on f s ∧ ∃ g, inv_on g f s t ∧ continuous_on g t ∧ maps_to g t s

definition homeomorphism_on (f : X → Y) (s : set X) : Prop :=
  homeomorphism_between f s (f ' s) 

theorem homeomorphism_on.intro {f : X → Y} {g : Y → X} {s : set X} (cts : continuous_on f s)
(Hinv : inv_on g f s (f ' s)) (ctsinv : continuous_on g (f ' s)) :
  homeomorphism_on f s :=
and.intro2 (image_maps_to f s) cts (exists.intro g (and.intro2 Hinv ctsinv (image_maps_to_inv Hinv)))

definition homeomorphism (f : X → Y) : Prop :=
 homeomorphism_on f (@univ X)

lemma inv_on_id (s : set X) : 
  inv_on id id s s :=
and.intro (λ x xs, by trivial) (λ x xs, by trivial)

theorem homeomorphism_id {s : set X} :
  homeomorphism_on id s :=
proof 
  have Hinv: inv_on id id s (id ' s), from !image_id ▸ !inv_on_id,
  have ctsid : continuous_on id s, from continuous_on_id s,
  have continuous_on id (id ' s), from continuous_on_id (id ' s),
  show _, from homeomorphism_on.intro ctsid Hinv this
qed

theorem homeomorphism_comp {s t : set X} {f : X → Y} {g : Y → Z}
(Hf : homeomorphism_on f s) (Hg : homeomorphism_on g (f ' s)) :
  homeomorphism_on (g ∘ f) s :=
proof
  obtain f' [invf [ctsf' mapf']], from and.elimRR Hf,
  obtain g' [invg [ctsg' mapg']], from and.elimRR Hg,
  have ctsfg : continuous_on (g ∘ f) s, from continuous_on_comp (and.elimLR Hf) (and.elimLR Hg),
  have invfg : inv_on (f' ∘ g') (g ∘ f) s ((g ∘ f) ' s), from inv_on_comp_image f g f' g' invf invg,
  have f ' s = g' ' ((g ∘ f) ' s), from ext(take x, iff.intro
    (suppose x ∈ f ' s, 
      obtain z [(zs : z ∈ s) (fzx : f z = x)], from this,
      have Hgfz : (g ∘ f) z ∈ (g ∘ f) ' s, from exists.intro z (and.intro zs rfl),
      have f z ∈ f ' s, from mem_image zs rfl,
      have g' (g (f z)) = f z, from (and.elim_left invg) (f z) this,
      have g' (g (f z)) = x, from fzx ▸ this,
      have ∃ y, y ∈ ((g ∘ f) ' s) ∧ g' y = x, from exists.intro (g (f z)) (and.intro Hgfz this), 
      show _, from this)
    (suppose x ∈ g' ' ((g ∘ f) ' s), 
      obtain y [(Hy : y ∈ (g ∘ f) ' s) (gyx : g' y = x)], from this,
      obtain z [(Hz : z ∈ s) (gfzy : (g ∘ f) z = y)], from Hy,
      have g' (g (f z)) = x, by rewrite[gfzy]; exact gyx,
      have g' (g (f z)) = f z, from (and.elim_left invg) (f z) (mem_image Hz rfl),
      have f z = x, from this ▸ `g' (g (f z)) = x`,
      show _, from exists.intro z (and.intro Hz this))),
  have continuous_on f' (g' ' ((g ∘ f) ' s)), from this ▸ ctsf',
  have continuous_on (f' ∘ g') ((g ∘ f) ' s), from continuous_on_comp (by rewrite[image_comp]; apply ctsg') this,
  have mf : maps_to f s (f ' s), from and.elim_left Hf,
  have mg : maps_to g (f ' s) ((g ∘ f) ' s), by rewrite[image_comp]; exact (and.elim_left Hg),
  have Maps : maps_to (g ∘ f) s ((g ∘ f) ' s), from maps_to_comp mg mf,
  show _, from homeomorphism_on.intro ctsfg invfg this
qed

definition homeomorphic (s : set X) (t : set Y) : Prop :=
  ∃ f, homeomorphism_between f s t

theorem homeomorphic.refl [refl] (s : set X) : 
  homeomorphic s s := 
have homeomorphism_on id s, from homeomorphism_id,
show _, from exists.intro id (!image_id ▸ this)

theorem homeomorphic.symm [symm] {s t : set X} (H : homeomorphic s t) :
  homeomorphic t s := 
proof
  obtain f Hf, from H,
  obtain g [invg [ctsg mapg]], from and.elimRR Hf,
  have mapf : maps_to f s t, from and.elim_left Hf,
  have right_inv_on f g s, from (and.elim_left invg),
  have left_inv_on f g t, from (and.elim_right invg),
  have inv_on f g t s, from and.intro this (and.elim_left invg),
  exists.intro g (and.intro2 (mapg) ctsg (exists.intro f (and.intro2 this (and.elimLR Hf) mapf)))
qed

theorem homeomorphic.trans [trans] {s t r : set X} (H1 : homeomorphic s t) (H2 : homeomorphic t r) :
  homeomorphic s r :=
proof
  obtain f Hf, from H1,
  obtain g Hg, from H2,
  have ctsf : continuous_on f s, from and.elimLR Hf,
  have ctsg : continuous_on g t, from and.elimLR Hg,
  obtain f' [(Hf' : inv_on f' f s t)(ctsf' : continuous_on f' t) (mapf')], from and.elimRR Hf,
  obtain g' [(Hg' : inv_on g' g t r)(ctsg' : continuous_on g' r) (mapg')], from and.elimRR Hg, 
  have f ' s ⊆ t, from image_subset_of_maps_to (and.elim_left Hf),
  have H1 : continuous_on (g ∘ f) s, from continuous_on_comp' ctsf ctsg this,
  have g' ' r ⊆ t, from image_subset_of_maps_to mapg',
  have H2 : continuous_on (f' ∘ g') r, from continuous_on_comp' ctsg' ctsf' this,
  have inv_on (f' ∘ g') (g ∘ f) s r, from inv_on_comp (and.elim_left Hf) mapg' Hf' Hg',
  have Maps : maps_to (g ∘ f) s r, from maps_to_comp (and.elim_left Hg) (and.elim_left Hf),
  show ∃ h, homeomorphism_between h s r, from exists.intro (g ∘ f)
  (and.intro2 Maps H1 (exists.intro (f' ∘ g') (and.intro2 this H2 (maps_to_comp mapf' mapg'))))
qed

definition open_map_on (f : X → Y) (s : set X) : Prop :=
  ∀ t, t ⊆ s → Open t → Open (f ' t)

definition open_map (f : X → Y) : Prop :=
  open_map_on f univ

theorem homeo_on_open_open_map_on {s : set X} (f : X → Y) :
  Open (f ' s) → homeomorphism_on f s → open_map_on f s :=
proof
  assume H1, assume H2,
  obtain g [invg [ctsg mapg]], from and.elimRR H2,
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
  inj_on f s → open_map_on f s → homeomorphism_on f s :=
sorry

-- show if f : X → Y bijection and open, f⁻¹ is continuous

definition closed_map_on (f : X → Y) (s : set X) : Prop :=
  ∀ t, t ⊆ s → closed t → closed (f ' t)

definition closed_map (f : X → Y) : Prop :=
  closed_map_on f univ

-- show if f : X → Y bijection and closed, f⁻¹ is continuous

-- prove homeo_on_closed_map_on 

-- prove inj_closed_map_on_imp_homeo_on (if it is actually true)

-- instantiate as isomorphism in TOP

end homeomorphism
