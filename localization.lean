/-

Remarks:

  - we do not allow 0 to be inverted, although this is of course not strictly necessary
  we do not want to constantly be splitting by cases on whether we've gotten the trivial
  ring or not after inversion. 

  - in the ring theory library integral domains require 1 ≠ 0, but the trivial ring is an integral domain

  - it should be shown that the localization of an integral domain is an integral domain, however this file 
was getting unbearably buggy and slow, so the plan was to wait until its in the library so that proof can be
worked out in a shorter file, which imports this one, and then added in a subsequent pull request.

  - "open simplifier.distrib" did not work in the sense that the simplifier was still not aware of distributivity 
laws

  - Could we go back and define ℚ := Frac ℤ?

-/

import data.set algebra.ring logic.eq
open algebra eq.ops set quot

variables {R : Type} [ring_structure : comm_ring R]

 /- "ring_structure" unfortunately could not be made anonymous, the name had
 to be used for equiv.is_equivalence -/

include ring_structure

definition multiplicative (S : set R) :=
  (1 ∈ S) ∧ (0 ∉ S) ∧ ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S 

theorem nontrivial_multiplicative (S : set R) : 
  multiplicative S → ((1 : R) ≠ 0) :=
assume H, not.intro(
  suppose 1 = 0,
  have 0 ∉ S, from and.elim_left (and.elim_right H),
  show false, from absurd (`1 = 0` ▸ (and.elim_left H)) this)

variables {S : set R} {HS : multiplicative S}

structure preloc {S : set R} (HS : multiplicative S) : Type :=
  (fst : R) 
  (snd : R) 
  (Hsnd : snd ∈ S)

private definition equiv {S : set R} (mS : multiplicative S) (a b : preloc mS) :=
  ∃₀ s ∈ S, s * (preloc.fst a * preloc.snd b - preloc.fst b * preloc.snd a) = 0 

namespace prelocalization

theorem equiv.refl [refl] (a : preloc HS) : 
  equiv HS a a :=
have 1 ∈ S, from and.elim_left HS,
exists.intro 1 (and.intro `1 ∈ S` (by simp))

private lemma aux (a b c : R) :
  c * (-b + a) = -c * (b - a) :=
calc
  c * (-b + a) = c * ((-1) * b + (-1) * -a) : by blast
           ... = (c * (-1)) * (b + -a)      : by rewrite[-left_distrib, mul.assoc]
           ... = -c * (b - a)               : by blast

theorem equiv.symm [symm] {a b : preloc HS} (H : equiv HS a b) :
  equiv HS b a :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b in
proof
  obtain s [(sS : s ∈ S) (Hs : s * (a₁ * b₂ - b₁ * a₂) = 0)], from H,
  have  s * (b₁ * a₂ - a₁ * b₂) = 0, from calc
    s * (b₁ * a₂ - a₁ * b₂) = s* (-(a₁ * b₂) + b₁ * a₂) : by simp
                        ... = -s * (a₁ * b₂ - b₁ * a₂)  : aux
                        ... = 0                         : by simp,
  show _, from exists.intro s (and.intro sS (by simp))
qed

theorem equiv.trans [trans] {a b c : preloc HS} (H1 : equiv HS a b) (H2 : equiv HS b c) :
  equiv HS a c :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b, 
    c₁ := preloc.fst c, c₂ := preloc.snd c in
proof
  obtain s [(sS : s ∈ S) (Hs : s * (a₁ * b₂ - b₁ * a₂) = 0)], from H1,
  obtain t [(tS : t ∈ S) (Ht : t * (b₁ * c₂ - c₁ * b₂) = 0)], from H2,
  have ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S, from and.elim_right (and.elim_right HS),
  have s * t * b₂ ∈ S, from this (this sS tS) (preloc.Hsnd b),
  have Hc₂ : s * t *( a₁ * c₂ * b₂ - b₁ * c₂ * a₂) = 0, from calc
    s * t * (a₁ * c₂ * b₂ - b₁ * c₂ * a₂) = (s * t) * (c₂ * (a₁ * b₂) - c₂ * (b₁ * a₂)) : by simp
                                      ... = s * t * (c₂ * (a₁ * b₂ - b₁ * a₂))          : by rewrite[-mul_sub_left_distrib]     
                                      ... = (t * c₂) * (s * (a₁ * b₂ - b₁ * a₂))        : by blast
                                      ... = (t * c₂) * 0                                : Hs 
                                      ... = 0                                           : by simp, 
  have Ha₂ : s*t*(b₁ * c₂ * a₂ - a₂ * c₁ * b₂) = 0, from calc
    s * t * (b₁ * c₂ * a₂ - a₂ * c₁ * b₂) = (s * t) * (a₂ * (b₁ * c₂) - a₂ * (c₁ * b₂)) : by simp
                                      ... = (s * t) * (a₂ * (b₁ * c₂ - c₁ * b₂))        : by rewrite[-mul_sub_left_distrib]
                                      ... = (s * a₂) * (t * (b₁ * c₂ - c₁ * b₂))        : by blast
                                      ... = (s * a₂) * 0                                : Ht         
                                      ... = 0                                           : by simp,
  have s * t * (b₁ * c₂ * a₂ - a₂ * c₁ * b₂) + s * t * ( a₁ * c₂ * b₂ - b₁ * c₂ * a₂) = 0, by rewrite[Hc₂, Ha₂, zero_add],
  have s * t * (a₁ * c₂ * b₂ - a₂ * c₁ * b₂) = 0, from calc
    s * t * (a₁ * c₂ * b₂ - a₂ * c₁ * b₂) = s * t * ((b₁ * c₂ * a₂ - a₂ * c₁ * b₂) + (a₁ * c₂ * b₂ - b₁ * c₂ * a₂))       : by simp
                                      ... = s * t * (b₁ * c₂ * a₂ - a₂ * c₁ * b₂) + s * t * (a₁ * c₂ * b₂ - b₁ * c₂ * a₂) : by rewrite[left_distrib]
                                      ... = 0 : this,
  have (s * t * b₂) * (a₁ * c₂ - c₁ * a₂) = 0, from calc
    (s * t * b₂) * (a₁ * c₂ - c₁ * a₂) = (s * t) * (b₂ * (a₁ * c₂ - a₂ * c₁))        : by simp
                                   ... = (s * t) * (b₂ * (a₁ * c₂) - b₂ * (a₂ * c₁)) : by rewrite[mul_sub_left_distrib]
                                   ... = s * t * (a₁ * c₂ * b₂ - a₂ * c₁ * b₂)       : by blast
                                   ... = 0                                           : this, 
  exists.intro (s*t*b₂) (and.intro `s * t * b₂ ∈ S` this)
qed 

check equiv HS

protected theorem equiv.is_equivalence (T : set R) (HT : multiplicative T) : equivalence (equiv HT) :=
  mk_equivalence (equiv HT) 
    (equiv.refl) 
    (@equiv.symm R ring_structure T HT) 
    (@equiv.trans R ring_structure T HT)

lemma frac_denom_closed (a b : preloc HS) : 
  preloc.snd a * preloc.snd b ∈ S := 
have ∀₀ s ∈ S, ∀₀ t ∈ S, s * t ∈ S, from and.elim_right (and.elim_right HS),
show _, from this (preloc.Hsnd a) (preloc.Hsnd b)

protected definition add (a b : preloc HS) : preloc HS := 
⦃preloc,
  fst  := preloc.fst a * preloc.snd b + preloc.fst b * preloc.snd a,
  snd  := preloc.snd a * preloc.snd b,
  Hsnd := frac_denom_closed a b
⦄

protected definition mul (a b : preloc HS) : preloc HS :=
⦃preloc,
  fst  := preloc.fst a * preloc.fst b,
  snd  := preloc.snd a * preloc.snd b,
  Hsnd := frac_denom_closed a b
⦄

protected definition neg (a : preloc HS) : preloc HS :=
⦃preloc,
  fst  := -preloc.fst a,
  snd  := preloc.snd a,
  Hsnd := preloc.Hsnd a
⦄

definition π_preloc (a : R) : preloc HS := 
⦃preloc,
  fst  := a,
  snd  := 1,
  Hsnd := and.elim_left HS
⦄

definition preloc_has_zero [instance] : has_zero (preloc HS) :=
  has_zero.mk (π_preloc 0)

definition preloc_has_one [instance] : has_one (preloc HS) :=
  has_one.mk (π_preloc 1)

-- operations respect the equivalence relation 

protected theorem add_equiv_add {a₁ b₁ a₂ b₂ : preloc HS} (eqv1 : equiv HS a₁ a₂) (eqv2 : equiv HS b₁ b₂) :
  equiv HS (prelocalization.add a₁ b₁) (prelocalization.add a₂ b₂) :=
  let a₁₁ := preloc.fst a₁, a₁₂ := preloc.snd a₁,
      a₂₁ := preloc.fst a₂, a₂₂ := preloc.snd a₂,
      b₁₁ := preloc.fst b₁, b₁₂ := preloc.snd b₁,
      b₂₁ := preloc.fst b₂, b₂₂ := preloc.snd b₂ in
proof
  obtain s [(sS : s ∈ S) (Hs : s * (a₁₁ * a₂₂ - a₂₁ * a₁₂) = 0)], from eqv1,
  obtain t [(tS : t ∈ S) (Ht : t * (b₁₁ * b₂₂ - b₂₁ * b₁₂) = 0)], from eqv2,
  have H_zero : (s * t) * ((a₁₁ * b₁₂ + b₁₁ * a₁₂) * (a₂₂ * b₂₂) - (a₂₁ * b₂₂ + b₂₁ * a₂₂) * (a₁₂ * b₁₂)) = 0, from calc
    (s * t) * ((a₁₁ * b₁₂ + b₁₁ * a₁₂) * (a₂₂ * b₂₂) - (a₂₁ * b₂₂ + b₂₁ * a₂₂) * (a₁₂ * b₁₂)) = 
      (s * t) * (a₁₁ * b₁₂ * (a₂₂ * b₂₂) + b₁₁ * a₁₂ * (a₂₂ * b₂₂) - (a₂₁ * b₂₂ * (a₁₂ * b₁₂) + b₂₁ * a₂₂ * (a₁₂ * b₁₂)))              : by rewrite[*right_distrib]
   ... = (s * t) * (((b₁₂ * b₂₂) * (a₁₁ * a₂₂) - (b₁₂ * b₂₂) * (a₂₁ * a₁₂)) + ((a₁₂ * a₂₂) * (b₁₁ * b₂₂) - (a₁₂ * a₂₂) * (b₂₁ * b₁₂))) : by blast
   ... = (s * t) * ((b₁₂ * b₂₂) * (a₁₁ * a₂₂ - a₂₁ * a₁₂)) + (s * t) * ((a₁₂ * a₂₂) * (b₁₁ * b₂₂ - b₂₁ * b₁₂)) : 
     by rewrite[-mul_sub_left_distrib, -mul_sub_left_distrib, left_distrib]
   ... = (b₁₂ * b₂₂ * t) * (s * (a₁₁ * a₂₂ - a₂₁ * a₁₂)) + (a₁₂ * a₂₂ * s) * (t * (b₁₁ * b₂₂ - b₂₁ * b₁₂))                             : by blast
   ... = (b₁₂ * b₂₂ * t) * 0 + (a₁₂ * a₂₂ * s) * (t * (b₁₁ * b₂₂ - b₂₁ * b₁₂))                                                         : Hs
   ... = (b₁₂ * b₂₂ * t) * 0 + (a₁₂ * a₂₂ * s) * 0                                                                                     : Ht
   ... = 0                                                                                                                             : by simp,
  have ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S, from and.elim_right (and.elim_right HS),
  show _, from  exists.intro (s * t) (and.intro (this sS tS) H_zero)
qed

protected theorem mul_equiv_mul {a₁ b₁ a₂ b₂ : preloc HS} (eqv1 : equiv HS a₁ a₂) (eqv2 : equiv HS b₁ b₂) :
  equiv HS (prelocalization.mul a₁ b₁) (prelocalization.mul a₂ b₂) :=
let a₁₁ := preloc.fst a₁, a₁₂ := preloc.snd a₁,
    a₂₁ := preloc.fst a₂, a₂₂ := preloc.snd a₂,
    b₁₁ := preloc.fst b₁, b₁₂ := preloc.snd b₁,
    b₂₁ := preloc.fst b₂, b₂₂ := preloc.snd b₂ in
proof
  obtain s [(sS : s ∈ S) (Hs : s * (a₁₁ * a₂₂ - a₂₁ * a₁₂) = 0)], from eqv1,
  obtain t [(tS : t ∈ S) (Ht : t * (b₁₁ * b₂₂ - b₂₁ * b₁₂) = 0)], from eqv2,
  have H_zero : (s * t) * ((a₁₁ * b₁₁) * (a₂₂ * b₂₂) - (a₂₁ * b₂₁) * (a₁₂ * b₁₂)) = 0, from calc
    (s * t) * ((a₁₁ * b₁₁) * (a₂₂ * b₂₂) - (a₂₁ * b₂₁) * (a₁₂ * b₁₂)) = 
      s * t * (a₁₁ * b₁₁ * a₂₂ * b₂₂ + a₂₁ * a₁₂ * b₁₁ * b₂₂ - a₂₁ * a₁₂ * b₁₁ * b₂₂ - a₁₂ * b₁₂ * a₂₁ * b₂₁)                    : by blast
   ... = s * t * ((b₁₁ * b₂₂) * (a₁₁ * a₂₂) - (b₁₁ * b₂₂) * (a₂₁ * a₁₂) + (a₂₁ * a₁₂) * (b₁₁ * b₂₂) - (a₂₁ * a₁₂) * (b₁₂ * b₂₁)) : by simp
   ... = (s * t) * ((b₁₁ * b₂₂) * (a₁₁ * a₂₂ - a₂₁ * a₁₂) + (a₂₁ * a₁₂) * (b₁₁ * b₂₂) - (a₂₁ * a₁₂) * (b₁₂ * b₂₁))               : by rewrite[-mul_sub_left_distrib]
   ... = (s * t) * ((b₁₁ * b₂₂) * (a₁₁ * a₂₂ - a₂₁ * a₁₂) + ((a₂₁ * a₁₂) * (b₁₁ * b₂₂) - (a₂₁ * a₁₂) * (b₁₂ * b₂₁)))             : by simp
   ... = (s * t) * ((b₁₁ * b₂₂) * (a₁₁ * a₂₂ - a₂₁ * a₁₂)) + (s * t) * ((a₂₁ * a₁₂) * (b₁₁ * b₂₂ - b₁₂ * b₂₁))                   : by rewrite[-mul_sub_left_distrib, left_distrib]
   ... = (b₁₁ * b₂₂ * t) * (s * (a₁₁ * a₂₂ - a₂₁ * a₁₂)) + (a₂₁ * a₁₂ * s) * (t * (b₁₁ * b₂₂ - b₂₁ * b₁₂))                       : by blast
   ... = (b₁₁ * b₂₂ * t) * 0 + (a₂₁ * a₁₂ * s) * (t * (b₁₁ * b₂₂ - b₂₁ * b₁₂))                                                   : Hs
   ... = (b₁₁ * b₂₂ * t) * 0 + (a₂₁ * a₁₂ * s) * 0                                                                               : Ht
   ... = 0                                                                                                                       : by blast,
  have ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S, from and.elim_right (and.elim_right HS),
  show _, from exists.intro (s * t) (and.intro (this sS tS) H_zero)
qed

protected theorem neg_equiv_neg {a b : preloc HS} (eqv : equiv HS a b) :
  equiv HS (prelocalization.neg a) (prelocalization.neg b) :=
let a₁ := preloc.fst a, a₂ := preloc.snd a,
    b₁ := preloc.fst b, b₂ := preloc.snd b in
proof
  obtain s [(sS : s ∈ S) (Hs : s * (a₁ * b₂ - b₁ * a₂) = 0)], from eqv,
  have s * ((-a₁) * b₂ - (-b₁) * a₂) = 0, from calc
    s * ((-a₁) * b₂ - (-b₁) * a₂) = s * (-1*(a₁ * b₂) - -1*(b₁ * a₂)) : by blast
    ... = s * ((-1) * (a₁ * b₂ - b₁ * a₂)) : by rewrite[-mul_sub_left_distrib]
    ... = (s * (-1)) * (a₁ * b₂ - b₁ * a₂) : by rewrite[mul.assoc]
    ... = (a₁ * b₂ - b₁ * a₂) * (s * (-1)) : by rewrite[mul.comm]
    ... = ((a₁ * b₂ - b₁ * a₂) * s) * (-1) : by rewrite[mul.assoc]
    ... = (-1) * ((a₁ * b₂ - b₁ * a₂) * s) : by rewrite[mul.comm]
    ... = (-1) * (s * (a₁ * b₂ - b₁ * a₂)) : by blast
    ... = (-1) * 0 : Hs
    ... = 0 : by blast,
  show _, from exists.intro s (and.intro sS this)
qed

-- some theorems about operations

protected theorem add.comm (a b : preloc HS) : 
  (equiv HS) (prelocalization.add a b) (prelocalization.add b a) := 
let a₁ := preloc.fst a, a₂ := preloc.snd a,
    b₁ := preloc.fst b, b₂ := preloc.snd b in
have 1 * ((a₁ * b₂ + b₁ * a₂) * (b₂ * a₂) - (b₁ * a₂ + a₁ * b₂) * (a₂ * b₂)) = 0, by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem add.assoc (a b c : preloc HS) : 
  (equiv HS) (prelocalization.add (prelocalization.add a b) c) (prelocalization.add a (prelocalization.add b c)) :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b, 
    c₁ := preloc.fst c, c₂ := preloc.snd c in
have 1 * (((a₁ * b₂ + b₁ * a₂) * c₂ + c₁ * (a₂ * b₂)) * (a₂ * (b₂ * c₂)) - (a₁ * (b₂ * c₂) + (b₁ * c₂+c₁ * b₂) * a₂) * ((a₂ * b₂) * c₂)) = 0, from calc
  1 * (((a₁ * b₂ + b₁ * a₂) * c₂ + c₁ * (a₂ * b₂)) * (a₂ * (b₂ * c₂)) - (a₁ * (b₂ * c₂) + (b₁ * c₂+c₁ * b₂) * a₂) * ((a₂ * b₂) * c₂)) = 
    ((a₁ * b₂ + b₁ * a₂) * c₂ + c₁ * (a₂ * b₂)) * (a₂ * b₂ * c₂) - (a₁ * (b₂ * c₂) + (b₁ * c₂+c₁ * b₂) * a₂) * ((a₂ * b₂ * c₂))            : by blast
  ... = (((a₁ * b₂ + b₁ * a₂) * c₂ + c₁ * (a₂ * b₂)) - (a₁ * (b₂ * c₂) + (b₁ * c₂ + c₁ * b₂) * a₂)) * (a₂ * b₂ * c₂)                       : by rewrite[-mul_sub_right_distrib]
  ... = ((a₁ * b₂ + b₁ * a₂) * c₂ + c₁ * (a₂ * b₂) - a₁ * (b₂ * c₂) - (b₁ * c₂ + c₁ * b₂) * a₂) * (a₂ * b₂ * c₂)                           : by blast
  ... = ((a₁ * b₂) * c₂ + (b₁ * a₂) * c₂ + c₁ * (a₂ * b₂) - a₁ * (b₂ * c₂) - ((b₁ * c₂) * a₂ + (c₁ * b₂) * a₂)) * (a₂ * b₂ * c₂)           : by rewrite[*right_distrib]
  ... = ((a₁ * b₂) * c₂ + (b₁ * a₂) * c₂ + c₁ * (a₂ * b₂) - a₁ * (b₂ * c₂) + ((-1) * ((b₁ * c₂) * a₂ + (c₁ * b₂) * a₂))) * (a₂ * b₂ * c₂)  : by simp
  ... = ((a₁ * b₂) * c₂ + (b₁ * a₂) * c₂ + c₁ * (a₂ * b₂) - a₁ * (b₂ * c₂) + ((-1) * ((b₁ * c₂) * a₂) + (-1) * ((c₁ * b₂) * a₂))) * (a₂ * b₂ * c₂) 
      : by rewrite[*left_distrib]
  ... = 0                                                                                                                                  : by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem add.zero (a : preloc HS) :
  (equiv HS) (prelocalization.add a zero) a :=
let a₁ := preloc.fst a, a₂ := preloc.snd a in
have 1 * ((a₁ * 1 + 0 * a₂) * a₂ - a₁ * (a₂ * 1)) = 0, by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem add_left_inv (a : preloc HS) :
  (equiv HS) (prelocalization.add (prelocalization.neg a) a) zero :=
let a₁ := preloc.fst a, a₂ := preloc.snd a in
have 1 * (((neg a₁) * a₂ + a₁ * a₂) * 1 - (0 * (a₂ * a₂))) = 0, by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem mul_comm (a b : preloc HS) :
  (equiv HS) (prelocalization.mul a b) (prelocalization.mul b a) :=
let a₁ := preloc.fst a, a₂ := preloc.snd a,
    b₁ := preloc.fst b, b₂ := preloc.snd b in
have 1 * ((a₁ * b₁) * (b₂ * a₂) - (b₁ * a₁) * (a₂ * b₂)) = 0, by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem mul_assoc (a b c : preloc HS) : 
  (equiv HS) (prelocalization.mul (prelocalization.mul a b) c) (prelocalization.mul a (prelocalization.mul b c)) :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b, 
    c₁ := preloc.fst c, c₂ := preloc.snd c in
have 1 * (((a₁ * b₁) * c₁) * (a₂ * (b₂ * c₂)) - (a₁ * (b₁ * c₁)) * ((a₂ * b₂) * c₂)) = 0, by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem one_mul (a : preloc HS) :
  (equiv HS) (prelocalization.mul one a) a :=
let a₁ := preloc.fst a, a₂ := preloc.snd a in
have 1 * ((1 * a₁) * a₂ - a₁ * (1 * a₂)) = 0, by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem left_distrib (a b c : preloc HS) :
  (equiv HS) 
    (prelocalization.mul a (prelocalization.add b c)) 
    (prelocalization.add (prelocalization.mul a b) (prelocalization.mul a c)) :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b, 
    c₁ := preloc.fst c, c₂ := preloc.snd c in
have 1 * ((a₁ * (b₁ * c₂ + c₁ * b₂)) * ((a₂ * b₂) * (a₂ * c₂)) - ((a₁ * b₁) * (a₂ * c₂) + (a₁ * c₁) * (a₂ * b₂)) * (a₂ * (b₂ * c₂))) = 0, from calc
  1 * ((a₁ * (b₁ * c₂ + c₁ * b₂)) * ((a₂ * b₂) * (a₂ * c₂)) - ((a₁ * b₁) * (a₂ * c₂) + (a₁ * c₁) * (a₂ * b₂)) * (a₂ * (b₂ * c₂))) =
    1 * ((a₁ * (b₁ * c₂)) * ((a₂ * b₂) * (a₂ * c₂)) + (a₁ * (c₁ * b₂)) * ((a₂ * b₂) * (a₂ * c₂)) -
        (((a₁ * b₁) * (a₂ * c₂)) * (a₂ * (b₂ * c₂)) + ((a₁ * c₁) * (a₂ * b₂)) * (a₂ * (b₂ * c₂)))) : by rewrite[left_distrib, *right_distrib]
  ... = 0                                                                                          : by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this)

protected theorem right_distrib (a b c : preloc HS) :
  (equiv HS)
    (prelocalization.mul (prelocalization.add a b) c)
    (prelocalization.add (prelocalization.mul a c) (prelocalization.mul b c)) :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b, 
    c₁ := preloc.fst c, c₂ := preloc.snd c in
have 1 * (((a₁ * b₂ + b₁ * a₂) * c₁) * ((a₂ * c₂) * (b₂ * c₂)) - ((a₁ * c₁) * (b₂ * c₂) + (b₁ * c₁) * (a₂ * c₂)) * ((a₂ * b₂) * c₂)) = 0, from calc
  1 * (((a₁ * b₂ + b₁ * a₂) * c₁) * ((a₂ * c₂) * (b₂ * c₂)) - ((a₁ * c₁) * (b₂ * c₂) + (b₁ * c₁) * (a₂ * c₂)) * ((a₂ * b₂) * c₂)) =
    1 * (((a₁ * b₂) * c₁) * ((a₂ * c₂) * (b₂ * c₂)) + ((b₁ * a₂) * c₁) * ((a₂ * c₂) * (b₂ * c₂)) - 
      (((a₁ * c₁) * (b₂ * c₂)) * ((a₂ * b₂) * c₂) + ((b₁ * c₁) * (a₂ * c₂)) * ((a₂ * b₂) * c₂))) :
      by rewrite[*right_distrib]
  ... = 0 : by blast,
show _, from exists.intro 1 (and.intro (and.elim_left HS) this) 

end prelocalization

-- localization

definition loc.setoid (T : set R) (HT : multiplicative T) : setoid (preloc HT) :=
setoid.mk (equiv HT) (prelocalization.equiv.is_equivalence T HT)

definition loc {T : set R} (HT : multiplicative T) : Type :=
  quot (loc.setoid T HT)

local attribute loc.setoid [instance]

namespace localization

-- canonical localization map

definition π_loc (a : R) : loc HS := ⟦prelocalization.π_preloc a⟧

definition loc_has_zero [instance] : has_zero (loc HS) :=
  has_zero.mk (π_loc 0)

definition loc_has_one [instance] : has_one (loc HS) :=
  has_one.mk (π_loc 1)

-- operations

protected definition add : (loc HS) → (loc HS) → (loc HS) :=
quot.lift₂
  (λ a b : preloc HS, ⟦prelocalization.add a b⟧)
  (take a₁ a₂ b₁ b₂, assume H1 H2, quot.sound (prelocalization.add_equiv_add H1 H2))

protected definition mul : (loc HS) → (loc HS) → (loc HS) :=
quot.lift₂
  (λ a b : preloc HS, ⟦prelocalization.mul a b⟧)
  (take a₁ a₂ b₁ b₂, assume H1 H2, quot.sound (prelocalization.mul_equiv_mul H1 H2))

protected definition neg : (loc HS) → (loc HS) :=
quot.lift
  (λ a : preloc HS, ⟦prelocalization.neg a⟧)
  (take a₁ a₂, assume H, quot.sound (prelocalization.neg_equiv_neg H))

definition loc_has_add [instance] : has_add (loc HS) :=
  has_add.mk localization.add

definition loc_has_mul [instance] : has_mul (loc HS) :=
  has_mul.mk localization.mul

definition loc_has_neg [instance] : has_neg (loc HS) :=
  has_neg.mk localization.neg

protected theorem add_comm (a b : loc HS) : 
  a + b = b + a :=
quot.induction_on₂ a b (take u v, quot.sound !prelocalization.add.comm)

protected theorem add_assoc (a b c : loc HS) : 
  a + b + c = a + (b + c) :=
quot.induction_on₃ a b c (take u v w, quot.sound !prelocalization.add.assoc)

protected theorem add_zero (a : loc HS) : 
  a + 0 = a :=
quot.induction_on a (take u, quot.sound !prelocalization.add.zero)

protected theorem zero_add (a : loc HS) :
  0 + a = a :=
!localization.add_comm ▸ !localization.add_zero

protected theorem add_left_inv (a : loc HS) :
  -a + a = 0 :=
quot.induction_on a (take u, quot.sound !prelocalization.add_left_inv)

protected theorem mul_comm (a b : loc HS) :
  a * b = b * a :=
quot.induction_on₂ a b (take u v, quot.sound !prelocalization.mul_comm)

protected theorem mul_assoc (a b c : loc HS) :
  a * b * c = a * (b * c) :=
quot.induction_on₃ a b c (take u v w, quot.sound !prelocalization.mul_assoc)

protected theorem one_mul (a : loc HS) :
  1 * a = a :=
quot.induction_on a (take u, quot.sound !prelocalization.one_mul)

protected theorem mul_one (a : loc HS) :
  a * 1 = a :=
!localization.mul_comm ▸ !localization.one_mul

protected theorem left_distrib (a b c : loc HS) :
  a * (b + c) = a * b + a * c :=
quot.induction_on₃ a b c (take u v w, quot.sound !prelocalization.left_distrib)

protected theorem right_distrib (a b c : loc HS) :
  (a + b) * c = a * c + b * c :=
quot.induction_on₃ a b c (take u v w, quot.sound !prelocalization.right_distrib)

protected definition comm_ring [trans_instance] : comm_ring (loc HS) :=
⦃comm_ring,
  add            := localization.add,
  add_assoc      := localization.add_assoc,
  zero           := 0,
  zero_add       := localization.zero_add,
  add_zero       := localization.add_zero,
  neg            := localization.neg,
  add_left_inv   := localization.add_left_inv,
  add_comm       := localization.add_comm,
  mul            := localization.mul,
  mul_assoc      := localization.mul_assoc,
  one            := 1,
  one_mul        := localization.one_mul,
  mul_one        := localization.mul_one,
  left_distrib   := localization.left_distrib,
  right_distrib  := localization.right_distrib,
  mul_comm       := localization.mul_comm⦄

-- field of fractions

definition Frac (X : Type) [integral_domain X] :=
  loc (abstract 
        let S := {x : X | x ≠ 0} in 
        have (1 ∈ S) ∧ (0 ∉ S) ∧ ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S, from sorry,
        show multiplicative S, from this
      end)

-- insantiate Frac as a field

end localization
