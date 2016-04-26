import data.set theories.topology.basic data.bool
open algebra eq.ops set topology nat bool

namespace connectedness

variables {X : Type} [topology X]

definition connected (s : set X) :=
  ¬(∃ A B, Open A ∧ Open B  ∧ s ⊆ A ∪ B ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅)

theorem connected.intro (s : set X) :
  (∀ A B, Open A → Open B →  A ∩ s ≠ ∅  → B ∩ s ≠ ∅ → A ∩ B ∩ s = ∅ → s ⊆ A ∪ B → false) → connected s :=
assume H, assume H',
obtain A B [OpA OpB sAB ABs As Bs], from H',
show false, from H A B OpA OpB As Bs ABs sAB

theorem connected.elim (s : set X) :
  connected s → (∀ A B, Open A → Open B →  A ∩ s ≠ ∅  → B ∩ s ≠ ∅ → A ∩ B ∩ s = ∅ → s ⊆ A ∪ B → false) :=
assume H, take A B, assume OpA, assume OpB, assume As, assume Bs, assume ABs, assume sAB,
have Open A ∧ Open B ∧ s ⊆ A ∪ B  ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅, from and.intro OpA (and.intro OpB
 (and.intro sAB (and.intro ABs (and.intro As Bs)))),
show false, from absurd (exists.intro A (exists.intro B this)) H

theorem connected_empty : 
  connected (∅ : set X) :=
!connected.intro (λ A B OpA OpB As Bs ABs sAB, absurd !inter_empty As)

theorem connected_sing (x : X) :
 connected '{x} :=
!connected.intro (λ A B OpA OpB As Bs ABs sAB,
obtain a Ha, from exists_mem_of_ne_empty As,
have a ∈ '{x}, from and.elim_right Ha,
have a = x, from (iff.elim_left !mem_singleton_iff) this,
have x ∈ A, from this ▸ (and.elim_left Ha),
obtain b Hb, from exists_mem_of_ne_empty Bs,
have b ∈ '{x}, from and.elim_right Hb,
have b = x, from (iff.elim_left !mem_singleton_iff) this,
have x ∈ B, from this ▸ (and.elim_left Hb),
have x ∈ '{x}, from !mem_singleton,
have x ∈ A ∩ B ∩ '{x}, from and.intro (and.intro `x ∈ A` `x ∈ B`) this,
show false, from absurd this (ABs⁻¹ ▸ !not_mem_empty))

section
 open classical

theorem connected_closed (s : set X) :
  connected s → ¬(∃ A B, closed A ∧ closed B ∧ s ⊆ A ∪ B ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅) :=
assume H, assume H',
obtain A B [clA clB sAB ABs As Bs], from H',
obtain x [xA xs], from (exists_mem_of_ne_empty As),
have x ∉ B, from not.intro(
  assume xB,
  have x ∈ A ∩ B ∩ s, from and.intro (and.intro xA xB) xs,
  show false, from absurd this (ABs⁻¹ ▸ !not_mem_empty)),
have HnB : (-B) ∩ s ≠ ∅, from ne_empty_of_mem (and.intro this xs),
obtain y [yB ys], from (exists_mem_of_ne_empty Bs),
have y ∉ A, from not.intro( 
  assume yA,
  have y ∈ A ∩ B ∩ s, from and.intro (and.intro yA yB) ys,
  show false, from absurd this (ABs⁻¹ ▸ !not_mem_empty)),
have HnA: (-A) ∩ s ≠ ∅, from ne_empty_of_mem (and.intro this ys),
have snAnB : s ⊆ (-A) ∪ (-B), from 
  take t, assume ts,
  have ¬(t ∈ (-A)) → t ∈ (-B), from 
    assume nntA, assume tB,
    have t ∈ A, from not_not_elim nntA,
    have t ∈ A ∩ B ∩ s, from and.intro (and.intro this tB) ts,
    show false, from absurd this (ABs⁻¹ ▸ !not_mem_empty),
  or.elim ((iff.elim_left !imp_iff_not_or) this)
    (assume HA, or.inl (not_not_elim HA))
    (assume HB, or.inr HB),
have (-A) ∩ (-B) ∩ s = ∅, from eq_empty_of_forall_not_mem(
   take t, assume tABs, 
   or.elim (sAB (and.elim_right tABs))
     (suppose t ∈ A, absurd this (and.elim_left (and.elim_left tABs)))
     (suppose t ∈ B, absurd this (and.elim_right (and.elim_left tABs)))),
show _, from !connected.elim H (-A) (-B) clA clB HnA HnB this snAnB

theorem closed_connected (s : set X) :
  ¬(∃ A B, closed A ∧ closed B ∧ s ⊆ A ∪ B ∧ A ∩ B ∩ s = ∅ ∧ A ∩ s ≠ ∅ ∧ B ∩ s ≠ ∅) → connected s :=
assume H, !connected.intro(λ A B OpA OpB As Bs ABs sAB,
have HnA : (-A) ∩ s ≠ ∅, from not.intro(
  assume H',
  have ∃ x, x ∈ B ∩ s, from exists_mem_of_ne_empty Bs,
  obtain x [xB xs], from this,
  have x ∉ A, from not.intro(
    assume xA,
    have x ∈ A ∩ B ∩ s, from and.intro (and.intro xA xB) xs,
    absurd this (ABs⁻¹ ▸ !not_mem_empty)),
  have x ∈ (-A) ∩ s, from and.intro this xs,
  show false, from absurd this (H'⁻¹ ▸ !not_mem_empty)),
have HnB : (-B) ∩ s ≠ ∅, from not.intro(
  assume H',
  have ∃ y, y ∈ A ∩ s, from exists_mem_of_ne_empty As,
  obtain y [yA ys], from this,
  have y ∉ B, from not.intro(
    assume yB,
    have y ∈ A ∩ B ∩ s, from and.intro (and.intro yA yB) ys,
    absurd this (ABs⁻¹ ▸ !not_mem_empty)),
  have y ∈ (-B) ∩ s, from and.intro this ys,
  show false, from absurd this (H'⁻¹ ▸ !not_mem_empty)),
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
  exists.intro (-A) (exists.intro (-B) (and.intro (closed_compl OpA) (and.intro (closed_compl OpB)
    (and.intro snAnB (and.intro nAnBs (and.intro HnA HnB)))))), 
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
  have A ∩ B ∩ s ⊆ ∅, from ABs ▸ this,
  show A ∩ B ∩ s = ∅, from eq_empty_of_subset_empty this,
have ⋃₀ S ⊆ A ∪ B, from sAB,
have HsAB : ∀₀ s ∈ S, s ⊆ A ∪ B, from 
  take s, assume sS, take x, assume xs,
  show x ∈ A ∪ B, from sAB x ((subset_sUnion_of_mem sS) xs),
obtain x (Hx : x ∈ ⋂₀ S), from exists_mem_of_ne_empty neq,
obtain s (sS : s ∈ S), from exists_mem_of_ne_empty HS,
have s ⊆ (⋃₀ S), from subset_sUnion_of_mem sS,
have ⋂₀ S ⊆ s, from sInter_subset_of_mem sS,
have x ∈ s, from this Hx,
have x ∈ ⋃₀ S, from `s ⊆ (⋃₀ S)` this,
have x ∈ A ∪ B, from sAB this,
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
  have ⋃₀ S = ∅, from (not_not_elim HS)⁻¹ ▸ sUnion_empty,
  this⁻¹ ▸ connected_empty

definition clopen (s : set X) :=
  Open s ∧ closed s

theorem connected_no_clopen :
 ¬(∃ t, clopen t ∧ t ⊂ (@univ X) ∧ t ≠ ∅) → connected (@univ X) :=
assume H, !connected.intro(λ A B OpA OpB As Bs ABs sAB,
have A ∪ B = univ, from eq_univ_of_univ_subset sAB,
have A ∩ B = ∅, by rewrite[-inter_univ]; exact ABs,
have -A = B, from ext (take x, iff.intro
  (assume nxA,
    have x ∈ A ∨ x ∈ B, from `A ∪ B = univ`⁻¹ ▸ !mem_univ,
    or.elim this
      (assume H', !not.elim nxA H') 
      (assume H', H'))
  (assume xB, assume xA,
    have x ∈ ∅, from `A ∩ B = ∅` ▸ (and.intro xA xB),
    show false, from absurd this !not_mem_empty)), 
have clopen (-A), from and.intro (this⁻¹ ▸ OpB) (closed_compl OpA),
have -A ⊆ univ, from subset_univ (-A),
have -A ≠ univ, from not.intro(
  assume H',
  obtain x xA, from (exists_mem_of_ne_empty (!inter_univ ▸ As)),
  have x ∉ (-A), from not.intro(
    suppose x ∈ (-A),
    absurd xA this),
  absurd !mem_univ (`-A = univ` ▸ this)),
have (-A) ⊂ univ, from and.intro `-A ⊆ univ` this,
have (-A) ≠ ∅, from not.intro(
  suppose -A = ∅,
  have B ≠ ∅, from !inter_univ ▸ Bs,
  show false, from absurd `-A = ∅` (`-A = B`⁻¹ ▸ this)),
have ∃ t, clopen t ∧ t ⊂ univ ∧ t ≠ ∅, from exists.intro (-A)
 (and.intro `clopen (-A)` (and.intro `(-A) ⊂ univ` this)),
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
have t ∪ (-t) = univ, from !union_compl_self,
have H6 : univ ⊆ t ∪ (-t), by rewrite[union_compl_self]; exact λx H, H,
show false, from !connected.elim H t (-t) H1 H2 H3 H4 H5 H6

end

end connectedness
