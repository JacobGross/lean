import data.set algebra.ring logic.eq
open algebra eq.ops set quot

variables {R : Type} [ring_structure : comm_ring R]
include ring_structure

definition multiplicative (S : set R) :=
  (1 ∈ S) ∧ (0 ∉ S) ∧ ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S -- should we not let 0 be inverted or split by cases all the time?

theorem nontrivial_multiplicative (S : set R) : -- instantiate as unit non_zero thingy?
  multiplicative S → ((1 : R) ≠ 0) :=
assume H, not.intro(
  suppose 1 = 0,
  have 0 ∉ S, from and.elim_left (and.elim_right H),
  show false, from absurd (`1 = 0` ▸ (and.elim_left H)) this)

variables {S : set R} {mS : multiplicative S}

structure preloc (S : set R) (HS : multiplicative S) : Type :=
  (fst : R) 
  (snd : R) 
  (sndS : snd ∈ S) -- call this Hsnd instead?

private definition equiv (S : set R) (mS : multiplicative S) (a b : preloc S mS) :=
  ∃₀ s ∈ S, s * (preloc.fst a * preloc.snd b - preloc.fst b * preloc.snd a) = 0 

namespace prelocalization

theorem equiv.refl [refl] (a : preloc S mS) : 
  equiv S mS a a :=
have 1 ∈ S, from and.elim_left mS,
exists.intro 1 (and.intro `1 ∈ S` (by simp))

protected lemma aux (a b c : R) : -- remove aux
  c * (-b + a) = -c * (b - a) :=
sorry

/-theorem equiv.symm [symm] {a b : preloc S mS} (H : equiv S mS a b) :
  equiv S mS b a :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b in
proof
  obtain s [(sS : s ∈ S) (Hs : s * (a₁ * b₂ - b₁ * a₂) = 0)], from H,
  have  s * (b₁ * a₂ - a₁ * b₂) = 0, from calc
    s * (b₁ * a₂ - a₁ * b₂) = s* (-(a₁ * b₂) + b₁ * a₂) : by simp
                        ... = -s * (a₁ * b₂ - b₁ * a₂)  : prelocalization.aux
                        ... = 0                         : by simp,
  show _, from exists.intro s (and.intro sS (by simp))
qed

theorem equiv.trans [trans] {a b c : preloc S mS} (H1 : equiv S mS a b) (H2 : equiv S mS b c) :
  equiv S mS a c :=
let a₁ := preloc.fst a, a₂ := preloc.snd a, 
    b₁ := preloc.fst b, b₂ := preloc.snd b, 
    c₁ := preloc.fst c, c₂ := preloc.snd c in
proof
  obtain s [(sS : s ∈ S) (Hs : s * (a₁ * b₂ - b₁ * a₂) = 0)], from H1,
  obtain t [(tS : t ∈ S) (Ht : t * (b₁ * c₂ - c₁ * b₂) = 0)], from H2,
  have ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S, from and.elim_right (and.elim_right mS),
  have s * t * b₂ ∈ S, from this (this sS tS) (preloc.sndS b),
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
qed-/

check equiv S mS

protected theorem equiv.is_equivalence (T : set R) (mT : multiplicative T) : equivalence (equiv T mT) :=
  mk_equivalence (equiv T mT) 
    (equiv.refl) 
    (@equiv.symm R ring_structure T mT) 
    (@equiv.trans R ring_structure T mT)

lemma frac_denom_closed (a b : preloc S mS) : 
  preloc.snd a * preloc.snd b ∈ S := 
have ∀₀ s ∈ S, ∀₀ t ∈ S, s * t ∈ S, from and.elim_right (and.elim_right mS),
show _, from this (preloc.sndS a) (preloc.sndS b)

protected definition add (a b : preloc S mS) : preloc S mS := 
⦃preloc,
  fst  := preloc.fst a * preloc.snd b + preloc.fst b * preloc.snd a,
  snd  := preloc.snd a * preloc.snd b,
  sndS := frac_denom_closed a b
⦄

protected definition mul (a b : preloc S mS) : preloc S mS :=
⦃preloc,
  fst  := preloc.fst a * preloc.fst b,
  snd  := preloc.snd a * preloc.snd b,
  sndS := frac_denom_closed a b
⦄

definition pre_neg (a : preloc S mS) : preloc S mS :=
⦃preloc,
  fst  := -preloc.fst a,
  snd  := preloc.snd a,
  sndS := preloc.sndS a
⦄

definition π_preloc (a : R) : preloc S mS := 
⦃preloc,
  fst  := a,
  snd  := 1,
  sndS := and.elim_left mS
⦄

definition zero : preloc S mS := π_preloc 0

definition one : preloc S mS := π_preloc 1

-- operations respect the equivalence relation 

/-protected theorem add_equiv_add {a₁ b₁ a₂ b₂ : preloc S mS} (eqv1 : equiv S mS a₁ a₂) (eqv2 : equiv S mS b₁ b₂) :
  equiv S mS (prelocalization.add a₁ b₁) (prelocalization.add a₂ b₂) :=
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
  have ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S, from and.elim_right (and.elim_right mS),
  show _, from  exists.intro (s * t) (and.intro (this sS tS) H_zero)
qed

protected theorem mul_equiv_mul {a₁ b₁ a₂ b₂ : preloc S mS} (eqv1 : equiv S mS a₁ a₂) (eqv2 : equiv S mS b₁ b₂) :
  equiv S mS (prelocalization.mul a₁ b₁) (prelocalization.mul a₂ b₂) :=
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
  have ∀₀ s ∈ S, ∀₀ a ∈ S, s * a ∈ S, from and.elim_right (and.elim_right mS),
  show _, from exists.intro (s * t) (and.intro (this sS tS) H_zero)
qed-/

protected theorem neg_equiv_neg {a b : preloc S mS} (eqv : equiv S mS a b) :
  equiv S mS (prelocalization.pre_neg a) (prelocalization.pre_neg b) :=
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

protected theorem add.comm (a b : preloc S mS) : 
  (equiv S mS) (prelocalization.add a b) (prelocalization.add b a) := -- have to show there is some s
sorry

protected theorem add.assoc (a b c : preloc S mS) : 
  (equiv S mS) (prelocalization.add (prelocalization.add a b) c) (prelocalization.add a (prelocalization.add b c)) :=
sorry

end prelocalization

-- localization

definition loc.setoid (T : set R) (mT : multiplicative T) : setoid (preloc T mT) :=
setoid.mk (equiv T mT) (prelocalization.equiv.is_equivalence T mT)

definition loc (T : set R) (mT : multiplicative T) : Type :=
  quot (loc.setoid T mT)

local attribute loc.setoid [instance]

namespace localization

-- canonical localization map

definition π_loc (a : R) : loc S mS := ⟦prelocalization.π_preloc a⟧

definition loc_has_zero [instance] : has_zero (loc S mS) :=
  has_zero.mk (π_loc 0)

definition loc_has_one [instance] : has_one (loc S mS) :=
  has_one.mk (π_loc 1)

-- operations

protected definition add : (loc S mS) → (loc S mS) → (loc S mS) :=
quot.lift₂
  (λ a b : preloc S mS, ⟦prelocalization.add a b⟧)
  (take a₁ a₂ b₁ b₂, assume H1 H2, quot.sound (prelocalization.add_equiv_add H1 H2))

protected definition mul : (loc S mS) → (loc S mS) → (loc S mS) :=
quot.lift₂
  (λ a b : preloc S mS, ⟦prelocalization.mul a b⟧)
  (take a₁ a₂ b₁ b₂, assume H1 H2, quot.sound (prelocalization.mul_equiv_mul H1 H2))

protected definition neg : (loc S mS) → (loc S mS) :=
quot.lift
  (λ a : preloc S mS, ⟦prelocalization.pre_neg a⟧)
  (take a₁ a₂, assume H, quot.sound (prelocalization.neg_equiv_neg H))

definition loc_has_add [instance] : has_add (loc S mS) :=
  has_add.mk localization.add

definition loc_has_mul [instance] : has_mul (loc S mS) :=
  has_mul.mk localization.mul

definition loc_has_neg [instance] : has_neg (loc S mS) :=
  has_neg.mk localization.neg

protected theorem add.comm (a b : loc S mS) : 
  a + b = b + a :=
quot.induction_on₂ a b (take u v, quot.sound !prelocalization.add.comm)

protected theorem add_assoc (a b c : loc S mS) : 
  a + b + c = a + (b + c) :=
quot.induction_on₃ a b c (take u v w, quot.sound !prelocalization.add.assoc)

protected theorem add_zero (a : loc S mS) : 
  a + 0 = a :=
quot.induction_on a (take u, quot.sound sorry)

protected theorem zero_add (a : loc S mS) :
  0 + a = a :=
!localization.add.comm ▸ !localization.add_zero

protected theorem add_left_inv (a : loc S mS) :
  -a + a = 0 :=
quot.induction_on a (take u, quot.sound sorry)

protected theorem mul_comm (a b : loc S mS) :
  a * b = b * a :=
quot.induction_on₂ a b (take u v, quot.sound sorry)

protected definition comm_ring [trans_instance] : comm_ring (loc S mS) :=
⦃comm_ring,
  add            := localization.add,
  add_assoc      := localization.add_assoc,
  zero           := 0,
  zero_add       := localization.zero_add,
  add_zero       := localization.add_zero,
  neg            := localization.neg,
  add_left_inv   := localization.add_left_inv,
  add_comm       := localization.add.comm,
  mul            := localization.mul,
  mul_assoc      := sorry,
  one            := 1,
  one_mul        := sorry,
  mul_one        := sorry,
  left_distrib   := sorry,
  right_distrib  := sorry,
  mul_comm       := sorry⦄

end localization

-- for integral domains "∃ s" is unnecessary
-- when R is an integral domain reinstantiated as an integral domain
