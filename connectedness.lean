import data.set theories.topology.basic data.bool
open algebra eq.ops set topology nat bool

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

proposition and.elim₂₁ (H : a ∧ b ∧ c) :
  b :=
and.elim_left (and.elim_right H)

proposition and.elim₂₂ (H : a ∧ b ∧ c) :
  c :=
and.elim_right (and.elim_right H)

proposition and.elim₁₁ (H : (a ∧ b) ∧ c) :
  a :=
and.elim_left (and.elim_left H)

proposition and.elim₁₂ (H : (a ∧ b) ∧ c) :
  b :=
and.elim_right (and.elim_left H)

proposition exists.intro2 (x y : A) {P : A → A → Prop} (H : P x y) :
  ∃ a b, P a b :=
exists.intro x (exists.intro y H)

-- connectedness begins here

namespace connectedness

variables {X : Type} [topology X]

definition connected (s : set X) :=
  ¬(∃ A B, Open A ∧ Open B  ∧ s ⊆ A ∪ B ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅)

theorem connected.intro (s : set X) :
  (∀ A B, Open A → Open B →  A ∩ s ≠ ∅  → B ∩ s ≠ ∅ → A ∩ B ∩ s = ∅ → s ⊆ A ∪ B → false) → connected s :=
assume H, assume H',
obtain A B [OpA OpB sAB ABs As Bs], from H',
show _, from H A B OpA OpB As Bs ABs sAB

theorem connected.elim (s : set X) :
  connected s → (∀ A B, Open A → Open B →  A ∩ s ≠ ∅  → B ∩ s ≠ ∅ → A ∩ B ∩ s = ∅ → s ⊆ A ∪ B → false) :=
assume H, take A B, assume OpA, assume OpB, assume As, assume Bs, assume ABs, assume sAB,
show _, from absurd (exists.intro2 A B (and.intro2 OpA OpB (and.intro3 sAB ABs As Bs))) H

theorem connected_empty : 
  connected (∅ : set X) :=
!connected.intro (λ A B OpA OpB As Bs ABs sAB, absurd !inter_empty As) 

lemma mem_mem_singleton {A : set X} {a x : X} (aA : a ∈ A) (ax : a ∈ '{x}):
  x ∈ A :=
by rewrite[-(eq_of_mem_singleton ax)]; exact aA

theorem connected_sing (x : X) :
 connected '{x} :=
!connected.intro (λ A B OpA OpB As Bs ABs sAB,
obtain a [(aA : a ∈ A) (ax : a ∈ '{x})], from exists_mem_of_ne_empty As,
have xA : x ∈ A, from mem_mem_singleton aA ax,
obtain b [(bB : b ∈ B) (bx : b ∈ '{x})], from exists_mem_of_ne_empty Bs,
have xB : x ∈ B, from mem_mem_singleton bB bx,
absurd (and.intro2' xA xB !mem_singleton) (ABs⁻¹ ▸ !not_mem_empty))

section
 open classical

private lemma aux1 {a b s : set X} (Hbs : b ∩ s ≠ ∅) (abs : a ∩ b ∩ s = ∅) :
  (-a) ∩ s ≠ ∅ :=
obtain y [yb ys], from (exists_mem_of_ne_empty Hbs),
have y ∉ a, from not.intro( 
  assume ya,
  have y ∈ a ∩ b ∩ s, from and.intro (and.intro ya yb) ys,
  absurd this (abs⁻¹ ▸ !not_mem_empty)),
show _, from ne_empty_of_mem (and.intro this ys)

private lemma aux2 {a b s : set X} (Has : a ∩ s ≠ ∅) (abs : a ∩ b ∩ s = ∅) :
  (-b) ∩ s ≠ ∅ :=
obtain x [xa xs], from (exists_mem_of_ne_empty Has),
have x ∉ b, from not.intro(
  assume xb,
  have x ∈ a ∩ b ∩ s, from and.intro (and.intro xa xb) xs,
  show false, from absurd this (abs⁻¹ ▸ !not_mem_empty)),
show _, from ne_empty_of_mem (and.intro this xs)

theorem connected_closed (s : set X) :
  connected s → ¬(∃ A B, closed A ∧ closed B ∧ s ⊆ A ∪ B ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅) :=
assume H, assume H',
obtain A B [clA clB sAB ABs As Bs], from H',
obtain x [xA xs], from (exists_mem_of_ne_empty As),
have HnB : (-B) ∩ s ≠ ∅, from aux2 As ABs,
have HnA: (-A) ∩ s ≠ ∅, from aux1 Bs ABs,
have snAnB : s ⊆ (-A) ∪ (-B), from 
  take t, assume ts,
  have ¬(t ∈ (-A)) → t ∈ (-B), from 
    assume nntA, assume tB,
    have t ∈ A, from not_not_elim nntA,
    have t ∈ A ∩ B ∩ s, from and.intro2' this tB ts,
    show false, from absurd this (ABs⁻¹ ▸ !not_mem_empty),
  or.elim ((iff.elim_left !imp_iff_not_or) this)
    (assume HA, or.inl (not_not_elim HA))
    (assume HB, or.inr HB),
have (-A) ∩ (-B) ∩ s = ∅, from eq_empty_of_forall_not_mem(
   take t, assume tABs, 
   or.elim (sAB (and.elim_right tABs))
     (suppose t ∈ A, absurd this (and.elim₁₁ tABs))
     (suppose t ∈ B, absurd this (and.elim₁₂ tABs))),
show _, from !connected.elim H (-A) (-B) clA clB HnA HnB this snAnB

theorem closed_connected (s : set X) :
  ¬(∃ A B, closed A ∧ closed B ∧ s ⊆ A ∪ B ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅) → connected s :=
assume H, !connected.intro(λ A B OpA OpB As Bs ABs sAB,
obtain x [xB xs], from exists_mem_of_ne_empty Bs,
obtain y [yA ys], from exists_mem_of_ne_empty As,
have HnA : (-A) ∩ s ≠ ∅, from aux1 Bs ABs,
have HnB : (-B) ∩ s ≠ ∅, from aux2 As ABs,
have snAnB : s ⊆ (-A) ∪ (-B), from 
  take t, assume ts,
  have t ∉ A ∩ B, from 
    assume tAB,
    have t ∈ A ∩ B ∩ s, from and.intro tAB ts,
    absurd this (ABs⁻¹ ▸ !not_mem_empty),
  show _, from (iff.elim_left !not_and_iff_not_or_not) this,
have nAnBs : (-A) ∩ (-B) ∩ s = ∅, from eq_empty_of_forall_not_mem(
  take t, assume tABs,
  have t ∈ (-A) ∩ (-B), from and.elim_left tABs,
  have t ∉ (A ∪ B), from (iff.elim_right !not_or_iff_not_and_not) this,
  have t ∈ (A ∪ B), from `s ⊆ A ∪ B` (and.elim_right tABs),
  show _, from absurd this `t ∉ A ∪ B`),
have ∃ A B, closed A ∧ closed B ∧ s ⊆ A ∪ B ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅, from 
  exists.intro2 (-A) (-B) (and.intro2 (closed_compl OpA) (closed_compl OpB)
    (and.intro3 snAnB  nAnBs HnA HnB)), 
show false, from H this)

theorem connected_cUnion (s : ℕ → set X) :
  (∀ i, connected (s i)) → (⋂ i, s i) ≠ ∅ → connected (⋃ i, s i) :=
assume H, assume neq,
!connected.intro(λ A B OpA OpB As Bs ABs sAB,
have (⋃ i, A ∩ B ∩ (s i)) = ∅, by rewrite[-inter_distrib_Union_left]; apply ABs, 
have disji : ∀ i, A ∩ B ∩ (s i) = ∅, from take i,
  have A ∩ B ∩ (s i) ⊆ ⋃ i, A ∩ B ∩ (s i), from 
    take x, assume H, exists.intro i H,
  eq_empty_of_subset_empty (`(⋃ i, A ∩ B ∩ (s i)) = ∅` ▸ this),
have siAB : ∀ i, (s i) ⊆ A ∪ B, from 
  take i, take y, assume ysi,
  show y ∈ A ∪ B, from sAB y (exists.intro i ysi),
obtain x Hx, from exists_mem_of_ne_empty neq,
have x ∈ A ∪ B, from sAB (exists.intro 0 (Hx 0)), 
or.elim this
  (assume xA,
   obtain y [yB ys], from exists_mem_of_ne_empty Bs,
   obtain j (ysj : y ∈ s j), from ys,
   have Bsj : B ∩ s j ≠ ∅, from ne_empty_of_mem (and.intro yB ysj),
   have Asj : A ∩ s j ≠ ∅, from ne_empty_of_mem (and.intro xA (Hx j)),
   show false, from !connected.elim (H j) A B OpA OpB Asj Bsj (disji j) (siAB j))
  (assume xB,
   obtain y [yA ys], from exists_mem_of_ne_empty As,
   obtain j (ysj : y ∈ s j), from ys,
   have Asj : A ∩ s j ≠ ∅, from ne_empty_of_mem (and.intro yA ysj),
   have Bsj : B ∩ s j ≠ ∅, from ne_empty_of_mem (and.intro xB (Hx j)),
   show false, from !connected.elim (H j) A B OpA OpB Asj Bsj (disji j) (siAB j)))

theorem connected_union (s t : set X) :
 connected s → connected t → s ∩ t ≠ ∅ → connected (s ∪ t) :=
assume cs, assume ct, assume st, 
have ∀ i, connected (bin_ext s t i),
  by intro i; cases i; exact cs; exact ct,
have (⋂ i, bin_ext s t i) ≠ ∅, from !Inter_bin_ext⁻¹ ▸ st,
have connected (⋃ i, bin_ext s t i), from 
  !connected_cUnion `∀ i, connected (bin_ext s t i)` this,
show _, from !Union_bin_ext ▸ this

theorem connected_sUnion (S : set (set X)) :
  (∀₀ s ∈ S, connected s) → ⋂₀ S ≠ ∅ → connected ⋃₀ S := 
if HS : S ≠ ∅ then
assume H, assume neq,
!connected.intro(λ A B OpA OpB As Bs ABs sAB,
have disj : ∀₀ s ∈ S, A ∩ B ∩ s = ∅, from 
  take s, assume sS,
  have A ∩ B ∩ s ⊆ A ∩ B ∩ ⋃₀ S, from 
   take y, assume Hy,
   have y ∈ A, from and.elim_left (and.elim_left Hy),
   have y ∈ B, from and.elim_right (and.elim_left Hy),
   have y ∈ ⋃₀ S, from (subset_sUnion_of_mem sS) (and.elim_right Hy),
   show y ∈ A ∩ B ∩ ⋃₀ S, from and.intro (and.intro `y ∈ A` `y ∈ B`) this,
  show A ∩ B ∩ s = ∅, from eq_empty_of_subset_empty (ABs ▸ this),
have ⋃₀ S ⊆ A ∪ B, from sAB,
have HsAB : ∀₀ s ∈ S, s ⊆ A ∪ B, from 
  take s, assume sS, take x, assume xs,
  show x ∈ A ∪ B, from sAB x ((subset_sUnion_of_mem sS) xs),
obtain x (Hx : x ∈ ⋂₀ S), from exists_mem_of_ne_empty neq,
obtain s (sS : s ∈ S), from exists_mem_of_ne_empty HS,
have s ⊆ (⋃₀ S), from subset_sUnion_of_mem sS,
have x ∈ A ∪ B, from sAB (`s ⊆ (⋃₀ S)` ((sInter_subset_of_mem sS) Hx)),
or.elim this
  (assume xA,
   obtain y [(yB : y ∈ B) (ys : y ∈ ⋃₀ S)], from exists_mem_of_ne_empty Bs,
   obtain t [(tS : t ∈ S) (yt : y ∈ t)], from ys,
   have Bst : B ∩ t ≠ ∅, from ne_empty_of_mem (and.intro yB yt),
   have x ∈ t, from (sInter_subset_of_mem tS) Hx,
   have Ast : A ∩ t ≠ ∅, from ne_empty_of_mem (and.intro xA (this)),
   show false, from !connected.elim (H tS) A B OpA OpB Ast Bst (disj tS) (HsAB tS))
  (assume xB,
   obtain y [(yA : y ∈ A) (ys : y ∈ ⋃₀ S)], from exists_mem_of_ne_empty As,
   obtain t [(tS : t ∈ S) (yt : y ∈ t)], from ys,
   have Ast : A ∩ t ≠ ∅, from ne_empty_of_mem (and.intro yA yt),
   have x ∈ t, from (sInter_subset_of_mem tS) Hx,
   have Bst : B ∩ t ≠ ∅, from ne_empty_of_mem (and.intro xB (this)),
   show false, from !connected.elim (H tS) A B OpA OpB Ast Bst (disj tS) (HsAB tS)))
else
  assume H, assume neq,
  by rewrite[(not_not_elim HS), sUnion_empty]; apply connected_empty

definition clopen (s : set X) :=
  Open s ∧ closed s

theorem connected_no_clopen :
 ¬(∃ t, clopen t ∧ t ⊂ (@univ X) ∧ t ≠ ∅) → connected (@univ X) :=
assume H, !connected.intro(λ A B OpA OpB As Bs ABs sAB,
 have H1 : A ∪ B = univ, from eq_univ_of_univ_subset sAB,
 have H2 : A ∩ B = ∅, by rewrite[-inter_univ]; exact ABs,
 have -A = B,
   by rewrite [-inter_univ, -H1, inter_distrib_left, compl_inter_self, -H2,
               -inter_distrib_right, union_compl_self, univ_inter], 
have clopen (-A), from and.intro (this⁻¹ ▸ OpB) (closed_compl OpA),
have -A ⊆ univ, from subset_univ (-A),
have -A ≠ univ, from not.intro(
  assume H',
  obtain x xA, from (exists_mem_of_ne_empty (!inter_univ ▸ As)),
  have x ∉ (-A), from not.intro(assume H, absurd xA H),
  absurd !mem_univ (`-A = univ` ▸ this)),
have (-A) ⊂ univ, from and.intro `-A ⊆ univ` this,
have (-A) ≠ ∅, from not.intro(
  suppose -A = ∅,
  have B ≠ ∅, from !inter_univ ▸ Bs,
  show false, from absurd `-A = ∅` (`-A = B`⁻¹ ▸ this)),
have ∃ t, clopen t ∧ t ⊂ univ ∧ t ≠ ∅, from exists.intro (-A)
 (and.intro2 `clopen (-A)` `(-A) ⊂ univ` this),
show false, from absurd this H)

theorem no_clopen_connected :
  connected (@univ X) →  ¬(∃ t, clopen t ∧ t ⊂ (@univ X) ∧ t ≠ ∅) :=
assume H, assume H',
obtain t [clot tu tn], from H',
have H1 : Open t, from and.elim_left clot,
have H2 : Open (-t), from and.elim_right clot,
have H3 : t ∩ univ ≠ ∅, from !inter_univ⁻¹ ▸ tn,
have t ≠ univ, from and.elim_right tu,
have H4 : (-t) ∩ univ ≠ ∅, from not.intro(
  suppose (-t) ∩ univ = ∅,
  have -t = (∅ : set X), from !inter_univ ▸ this,
  have -(-t) = @univ X, from this⁻¹ ▸ compl_empty,
  show false, from absurd ( !compl_compl ▸ this) `t ≠ univ`),
have H5 : t ∩ (-t) ∩ univ = ∅, by rewrite[inter_univ, inter_compl_self],
have H6 : univ ⊆ t ∪ (-t), by rewrite[union_compl_self]; exact λx H, H,
show false, from !connected.elim H t (-t) H1 H2 H3 H4 H5 H6

-- show continuous image of connected set is connected and we're done

end

end connectedness
