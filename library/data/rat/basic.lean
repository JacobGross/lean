/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The rational numbers as a field generated by the integers, defined as the usual quotient.
-/
import data.int algebra.field
open int quot eq.ops

record prerat : Type :=
(num : ℤ) (denom : ℤ) (denom_pos : denom > 0)

/-
  prerat: the representations of the rationals as integers num, denom, with denom > 0.
  note: names are not protected, because it is not expected that users will open prerat.
-/

namespace prerat

/- the equivalence relation -/

definition equiv (a b : prerat) : Prop := num a * denom b = num b * denom a

infix ≡ := equiv

theorem equiv.refl [refl] (a : prerat) : a ≡ a := rfl

theorem equiv.symm [symm] {a b : prerat} (H : a ≡ b) : b ≡ a := !eq.symm H

theorem num_eq_zero_of_equiv {a b : prerat} (H : a ≡ b) (na_zero : num a = 0) : num b = 0 :=
have num a * denom b = 0, from !zero_mul ▸ na_zero ▸ rfl,
have num b * denom a = 0, from H ▸ this,
show num b = 0, from or_resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero this) (ne_of_gt (denom_pos a))

theorem num_pos_of_equiv {a b : prerat} (H : a ≡ b) (na_pos : num a > 0) : num b > 0 :=
have num a * denom b > 0, from mul_pos na_pos (denom_pos b),
have num b * denom a > 0, from H ▸ this,
show num b > 0, from pos_of_mul_pos_right this (le_of_lt (denom_pos a))

theorem num_neg_of_equiv {a b : prerat} (H : a ≡ b) (na_neg : num a < 0) : num b < 0 :=
have H₁ : num a * denom b = num b * denom a, from H,
have num a * denom b < 0,     from mul_neg_of_neg_of_pos na_neg (denom_pos b),
have -(-num b * denom a) < 0,   begin rewrite [neg_mul_eq_neg_mul, neg_neg, -H₁], exact this end,
have -num b > 0, from pos_of_mul_pos_right (pos_of_neg_neg this) (le_of_lt (denom_pos a)),
neg_of_neg_pos this

theorem equiv_of_num_eq_zero {a b : prerat} (H1 : num a = 0) (H2 : num b = 0) : a ≡ b :=
by rewrite [↑equiv, H1, H2, *zero_mul]

theorem equiv.trans [trans] {a b c : prerat} (H1 : a ≡ b) (H2 : b ≡ c) : a ≡ c :=
decidable.by_cases
  (suppose num b = 0,
    have num a = 0, from num_eq_zero_of_equiv (equiv.symm H1) `num b = 0`,
    have num c = 0, from num_eq_zero_of_equiv H2 `num b = 0`,
    equiv_of_num_eq_zero `num a = 0` `num c = 0`)
  (suppose num b ≠ 0,
    have H3 : num b * denom b ≠ 0, from mul_ne_zero this (ne_of_gt (denom_pos b)),
    have H4 : (num b * denom b) * (num a * denom c) = (num b * denom b) * (num c * denom a),
      from calc
        (num b * denom b) * (num a * denom c) = (num a * denom b) * (num b * denom c) :
                    by rewrite [*mul.assoc, *mul.left_comm (num a), *mul.left_comm (num b)]
          ... = (num b * denom a) * (num b * denom c)                                 : {H1}
          ... = (num b * denom a) * (num c * denom b)                                 : {H2}
          ... = (num b * denom b) * (num c * denom a)                                 :
                    by rewrite [*mul.assoc, *mul.left_comm (denom a),
                                   *mul.left_comm (denom b), mul.comm (denom a)],
    eq_of_mul_eq_mul_left H3 H4)

theorem equiv.is_equivalence : equivalence equiv :=
  mk_equivalence equiv equiv.refl @equiv.symm @equiv.trans

definition setoid : setoid prerat :=
setoid.mk equiv equiv.is_equivalence

/- field operations -/

definition of_int (i : int) : prerat := prerat.mk i 1 !of_nat_succ_pos

definition zero : prerat := of_int 0

definition one : prerat := of_int 1

private theorem mul_denom_pos (a b : prerat) : denom a * denom b > 0 :=
mul_pos (denom_pos a) (denom_pos b)

definition add (a b : prerat) : prerat :=
prerat.mk (num a * denom b + num b * denom a) (denom a * denom b) (mul_denom_pos a b)

definition mul (a b : prerat) : prerat :=
prerat.mk (num a * num b) (denom a * denom b) (mul_denom_pos a b)

definition neg (a : prerat) : prerat :=
prerat.mk (- num a) (denom a) (denom_pos a)

definition smul (a : ℤ) (b : prerat) (H : a > 0) : prerat :=
prerat.mk (a * num b) (a * denom b) (mul_pos H (denom_pos b))

theorem of_int_add (a b : ℤ) : of_int (a + b) ≡ add (of_int a) (of_int b) :=
by esimp [equiv, one, add, of_int]; rewrite [*int.mul_one]

theorem of_int_mul (a b : ℤ) : of_int (a * b) ≡ mul (of_int a) (of_int b) :=
!equiv.refl

theorem of_int_neg (a : ℤ) : of_int (-a) ≡ neg (of_int a) :=
!equiv.refl

theorem of_int.inj {a b : ℤ} : of_int a ≡ of_int b → a = b :=
by rewrite [↑of_int, ↑equiv, *mul_one]; intros; assumption

definition inv : prerat → prerat
| inv (prerat.mk nat.zero d dp)     := zero
| inv (prerat.mk (nat.succ n) d dp) := prerat.mk d (nat.succ n) !of_nat_succ_pos
| inv (prerat.mk -[1+n] d dp)       := prerat.mk (-d) (nat.succ n) !of_nat_succ_pos

theorem equiv_zero_of_num_eq_zero {a : prerat} (H : num a = 0) : a ≡ zero :=
by rewrite [↑equiv, H, ↑zero, ↑of_int, *zero_mul]

theorem num_eq_zero_of_equiv_zero {a : prerat} : a ≡ zero → num a = 0 :=
by rewrite [↑equiv, ↑zero, ↑of_int, mul_one, zero_mul]; intro H; exact H

theorem inv_zero {d : int} (dp : d > 0) : inv (mk nat.zero d dp) = zero :=
begin rewrite [↑inv, ▸*] end

theorem inv_zero' : inv zero = zero := inv_zero (of_nat_succ_pos nat.zero)

open nat

theorem inv_of_pos {n d : int} (np : n > 0) (dp : d > 0) : inv (mk n d dp) ≡ mk d n np :=
obtain (n' : nat) (Hn' : n = of_nat n'), from exists_eq_of_nat (le_of_lt np),
have (n' > nat.zero), from lt_of_of_nat_lt_of_nat (Hn' ▸ np),
obtain (k : nat) (Hk : n' = nat.succ k), from nat.exists_eq_succ_of_lt this,
have d * n = d * nat.succ k, by rewrite [Hn', Hk],
Hn'⁻¹ ▸ (Hk⁻¹ ▸ this)

theorem inv_neg {n d : int} (np : n > 0) (dp : d > 0) : inv (mk (-n) d dp) ≡ mk (-d) n np :=
obtain (n' : nat) (Hn' : n = of_nat n'), from exists_eq_of_nat (le_of_lt np),
have (n' > nat.zero), from lt_of_of_nat_lt_of_nat (Hn' ▸ np),
obtain (k : nat) (Hk : n' = nat.succ k), from nat.exists_eq_succ_of_lt this,
have -d * n = -d * nat.succ k, by rewrite [Hn', Hk],
have H3 : inv (mk -[1+k] d dp) ≡ mk (-d) n np, from this,
have H4 : -[1+k] = -n, from calc
  -[1+k] = -(nat.succ k) : rfl
      ... = -n            : by rewrite [Hk⁻¹, Hn'],
H4 ▸ H3

theorem inv_of_neg {n d : int} (nn : n < 0) (dp : d > 0) :
  inv (mk n d dp) ≡ mk (-d) (-n) (neg_pos_of_neg nn) :=
have inv (mk (-(-n)) d dp) ≡ mk (-d) (-n) (neg_pos_of_neg nn),
  from inv_neg (neg_pos_of_neg nn) dp,
!neg_neg ▸ this

/- operations respect equiv -/

theorem add_equiv_add {a1 b1 a2 b2 : prerat} (eqv1 : a1 ≡ a2) (eqv2 : b1 ≡ b2) :
  add a1 b1 ≡ add a2 b2 :=
calc
  (num a1 * denom b1 + num b1 * denom a1) * (denom a2 * denom b2)
      = num a1 * denom a2 * denom b1 * denom b2 + num b1 * denom b2 * denom a1 * denom a2 :
          by rewrite [right_distrib, *mul.assoc, mul.left_comm (denom b1),
                      mul.comm (denom b2), *mul.assoc]
  ... = num a2 * denom a1 * denom b1 * denom b2 + num b2 * denom b1 * denom a1 * denom a2 :
          by rewrite [↑equiv at *, eqv1, eqv2]
  ... = (num a2 * denom b2 + num b2 * denom a2) * (denom a1 * denom b1) :
          by rewrite [right_distrib, *mul.assoc, *mul.left_comm (denom b2),
                      *mul.comm (denom b1), *mul.assoc, mul.left_comm (denom a2)]

theorem mul_equiv_mul {a1 b1 a2 b2 : prerat} (eqv1 : a1 ≡ a2) (eqv2 : b1 ≡ b2) :
  mul a1 b1 ≡ mul a2 b2 :=
calc
  (num a1 * num b1) * (denom a2 * denom b2)
      = (num a1 * denom a2) * (num b1 * denom b2) : by rewrite [*mul.assoc, mul.left_comm (num b1)]
  ... = (num a2 * denom a1) * (num b2 * denom b1) : by rewrite [↑equiv at *, eqv1, eqv2]
  ... = (num a2 * num b2) * (denom a1 * denom b1) : by rewrite [*mul.assoc, mul.left_comm (num b2)]

theorem neg_equiv_neg {a b : prerat} (eqv : a ≡ b) : neg a ≡ neg b :=
calc
  -num a * denom b = -(num a * denom b) : neg_mul_eq_neg_mul
               ... = -(num b * denom a) : {eqv}
               ... = -num b * denom a   : neg_mul_eq_neg_mul

theorem inv_equiv_inv : ∀{a b : prerat}, a ≡ b → inv a ≡ inv b
| (mk an ad adp) (mk bn bd bdp) :=
  assume H,
  lt.by_cases
    (assume an_neg : an < 0,
      have bn_neg : bn < 0, from num_neg_of_equiv H an_neg,
      calc
        inv (mk an ad adp) ≡ mk (-ad) (-an) (neg_pos_of_neg an_neg) : inv_of_neg an_neg adp
                       ... ≡ mk (-bd) (-bn) (neg_pos_of_neg bn_neg) :
                             by rewrite [↑equiv at *, ▸*, *neg_mul_neg, mul.comm ad, mul.comm bd, H]
                       ... ≡ inv (mk bn bd bdp)                     : (inv_of_neg bn_neg bdp)⁻¹)
    (assume an_zero : an = 0,
      have bn_zero : bn = 0, from num_eq_zero_of_equiv H an_zero,
      eq.subst (calc
        inv (mk an ad adp) = inv (mk 0 ad adp)  : {an_zero}
                       ... = zero               : inv_zero adp
                       ... = inv (mk 0 bd bdp)  : inv_zero bdp
                       ... = inv (mk bn bd bdp) : bn_zero) !equiv.refl)
    (assume an_pos : an > 0,
      have bn_pos : bn > 0, from num_pos_of_equiv H an_pos,
      calc
        inv (mk an ad adp) ≡ mk ad an an_pos    : inv_of_pos an_pos adp
                       ... ≡ mk bd bn bn_pos    :
                                by rewrite [↑equiv at *, ▸*, mul.comm ad, mul.comm bd, H]
                       ... ≡ inv (mk bn bd bdp) : (inv_of_pos bn_pos bdp)⁻¹)

theorem smul_equiv {a : ℤ} {b : prerat} (H : a > 0) : smul a b H ≡ b :=
by esimp[equiv, smul]; rewrite[mul.assoc, mul.left_comm]

/- properties -/

protected theorem add.comm (a b : prerat) : add a b ≡ add b a :=
by rewrite [↑add, ↑equiv, ▸*, add.comm, mul.comm (denom a)]

protected theorem add.assoc (a b c : prerat) : add (add a b) c ≡ add a (add b c) :=
by rewrite [↑add, ↑equiv, ▸*, *(mul.comm (num c)), *(λy, mul.comm y (denom a)), *left_distrib,
            *right_distrib, *mul.assoc, *add.assoc]

protected theorem add_zero (a : prerat) : add a zero ≡ a :=
by rewrite [↑add, ↑equiv, ↑zero, ↑of_int, ▸*, *mul_one, zero_mul, add_zero]

protected theorem add_left_inv (a : prerat) : add (neg a) a ≡ zero :=
by rewrite [↑add, ↑equiv, ↑neg, ↑zero, ↑of_int, ▸*, -neg_mul_eq_neg_mul, add.left_inv, *zero_mul]

protected theorem mul_comm (a b : prerat) : mul a b ≡ mul b a :=
by rewrite [↑mul, ↑equiv, mul.comm (num a), mul.comm (denom a)]

protected theorem mul_assoc (a b c : prerat) : mul (mul a b) c ≡ mul a (mul b c) :=
by rewrite [↑mul, ↑equiv, *mul.assoc]

protected theorem mul_one (a : prerat) : mul a one ≡ a :=
by rewrite [↑mul, ↑one, ↑of_int, ↑equiv, ▸*, *mul_one]

protected theorem mul_left_distrib (a b c : prerat) : mul a (add b c) ≡ add (mul a b) (mul a c) :=
have H : smul (denom a) (mul a (add b c)) (denom_pos a) =
   add (mul a b) (mul a c), from begin
  rewrite[↑smul, ↑mul, ↑add],
  congruence,
  rewrite[*left_distrib, *right_distrib, -+(int.mul_assoc)],
  have T : ∀ {x y z w : ℤ}, x*y*z*w=y*z*x*w, from
    λx y z w, (!int.mul_assoc ⬝ !int.mul_comm) ▸ rfl,
  exact !congr_arg2 T T,
  rewrite [mul.left_comm (denom a) (denom b) (denom c)],
  rewrite int.mul_assoc
end,
equiv.symm (H ▸ smul_equiv (denom_pos a))

theorem mul_inv_cancel : ∀{a : prerat}, ¬ a ≡ zero → mul a (inv a) ≡ one
| (mk an ad adp) :=
  assume H,
  let a := mk an ad adp in
  lt.by_cases
    (assume an_neg : an < 0,
      let ia := mk (-ad) (-an) (neg_pos_of_neg an_neg) in
      calc
        mul a (inv a) ≡ mul a ia : mul_equiv_mul !equiv.refl (inv_of_neg an_neg adp)
                  ... ≡ one      : begin
                                     esimp [equiv, one, mul, of_int],
                                     rewrite [*int.mul_one, *int.one_mul, mul.comm,
                                              neg_mul_comm]
                                   end)
    (assume an_zero : an = 0, absurd (equiv_zero_of_num_eq_zero an_zero) H)
    (assume an_pos : an > 0,
      let ia := mk ad an an_pos in
      calc
        mul a (inv a) ≡ mul a ia : mul_equiv_mul !equiv.refl (inv_of_pos an_pos adp)
                  ... ≡ one      : begin
                                     esimp [equiv, one, mul, of_int],
                                     rewrite [*int.mul_one, *int.one_mul, mul.comm]
                                   end)

theorem zero_not_equiv_one : ¬ zero ≡ one :=
begin
  esimp [equiv, zero, one, of_int],
  rewrite [zero_mul, int.mul_one],
  exact zero_ne_one
end

theorem mul_denom_equiv (a : prerat) : mul a (of_int (denom a)) ≡ of_int (num a) :=
by esimp [mul, of_int, equiv]; rewrite [*int.mul_one]

/- Reducing a fraction to lowest terms. Needed to choose a canonical representative of rat, and
   define numerator and denominator. -/

definition reduce : prerat → prerat
| (mk an ad adpos) :=
    have pos : ad / gcd an ad > 0, from div_pos_of_pos_of_dvd adpos !gcd_nonneg !gcd_dvd_right,
    if an = 0 then prerat.zero
              else mk (an / gcd an ad) (ad / gcd an ad) pos

protected theorem eq {a b : prerat} (Hn : num a = num b) (Hd : denom a = denom b) : a = b :=
begin
  cases a with [an, ad, adpos],
  cases b with [bn, bd, bdpos],
  generalize adpos, generalize bdpos,
  esimp at *,
  rewrite [Hn, Hd],
  intros, apply rfl
end

theorem reduce_equiv : ∀ a : prerat, reduce a ≡ a
| (mk an ad adpos) :=
    decidable.by_cases
      (assume anz : an = 0,
        begin rewrite [↑reduce, if_pos anz, ↑equiv, anz], krewrite zero_mul end)
      (assume annz : an ≠ 0,
        by rewrite [↑reduce, if_neg annz, ↑equiv, mul.comm, -!int.mul_div_assoc
                    !gcd_dvd_left, -!int.mul_div_assoc !gcd_dvd_right, mul.comm])

theorem reduce_eq_reduce : ∀ {a b : prerat}, a ≡ b → reduce a = reduce b
| (mk an ad adpos) (mk bn bd bdpos) :=
  assume H : an * bd = bn * ad,
  decidable.by_cases
    (assume anz : an = 0,
      have H' : bn * ad = 0, by rewrite [-H, anz, zero_mul],
      have bnz : bn = 0,
        from or_resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero H') (ne_of_gt adpos),
      by rewrite [↑reduce, if_pos anz, if_pos bnz])
    (assume annz : an ≠ 0,
      have bnnz : bn ≠ 0, from
        assume bnz,
        have H' : an * bd = 0, by rewrite [H, bnz, zero_mul],
        have anz : an = 0,
          from or_resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero H') (ne_of_gt bdpos),
        show false, from annz anz,
      begin
        rewrite [↑reduce, if_neg annz, if_neg bnnz],
        apply prerat.eq,
          {apply div_gcd_eq_div_gcd H adpos bdpos},
          {esimp, rewrite [gcd.comm, gcd.comm bn],
            apply div_gcd_eq_div_gcd_of_nonneg,
              rewrite [mul.comm, -H, mul.comm],
              apply annz,
              apply bnnz,
              apply le_of_lt adpos,
              apply le_of_lt bdpos},
      end)

end prerat

/-
  the rationals
-/

definition rat : Type.{1} := quot prerat.setoid
notation `ℚ` := rat

local attribute prerat.setoid [instance]

namespace rat

/- operations -/

definition of_int [coercion] (i : ℤ) : ℚ := ⟦prerat.of_int i⟧
definition of_nat [coercion] (n : ℕ) : ℚ := n
definition of_num [coercion] [reducible] (n : num) : ℚ := n

protected definition prio := num.pred int.prio

definition rat_has_zero [instance] [priority rat.prio] : has_zero rat :=
has_zero.mk (of_int 0)

definition rat_has_one [instance] [priority rat.prio] : has_one rat :=
has_one.mk (of_int 1)

theorem of_int_zero : of_int (0:int) = (0:rat) :=
rfl

theorem of_int_one : of_int (1:int) = (1:rat) :=
rfl

protected definition add : ℚ → ℚ → ℚ :=
quot.lift₂
  (λ a b : prerat, ⟦prerat.add a b⟧)
  (take a1 a2 b1 b2, assume H1 H2, quot.sound (prerat.add_equiv_add H1 H2))

protected definition mul : ℚ → ℚ → ℚ :=
quot.lift₂
  (λ a b : prerat, ⟦prerat.mul a b⟧)
  (take a1 a2 b1 b2, assume H1 H2, quot.sound (prerat.mul_equiv_mul H1 H2))

protected definition neg : ℚ → ℚ :=
quot.lift
  (λ a : prerat, ⟦prerat.neg a⟧)
  (take a1 a2, assume H, quot.sound (prerat.neg_equiv_neg H))

protected definition inv : ℚ → ℚ :=
quot.lift
  (λ a : prerat, ⟦prerat.inv a⟧)
  (take a1 a2, assume H, quot.sound (prerat.inv_equiv_inv H))

definition reduce : ℚ → prerat :=
quot.lift
  (λ a : prerat, prerat.reduce a)
  @prerat.reduce_eq_reduce

definition num (a : ℚ) : ℤ := prerat.num (reduce a)
definition denom (a : ℚ) : ℤ := prerat.denom (reduce a)

theorem denom_pos (a : ℚ): denom a > 0 :=
prerat.denom_pos (reduce a)

definition rat_has_add [instance] [priority rat.prio] : has_add rat :=
has_add.mk rat.add

definition rat_has_mul [instance] [priority rat.prio] : has_mul rat :=
has_mul.mk rat.mul

definition rat_has_neg [instance] [priority rat.prio] : has_neg rat :=
has_neg.mk rat.neg

definition rat_has_inv [instance] [priority rat.prio] : has_inv rat :=
has_inv.mk rat.inv

protected definition sub [reducible] (a b : ℚ) : rat := a + (-b)

definition rat_has_sub [instance] [priority rat.prio] : has_sub rat :=
has_sub.mk rat.sub

lemma sub.def (a b : ℚ) : a - b = a + (-b) :=
rfl

/- properties -/

theorem of_int_add (a b : ℤ) : of_int (a + b) = of_int a + of_int b :=
quot.sound (prerat.of_int_add a b)

theorem of_int_mul (a b : ℤ) : of_int (a * b) = of_int a * of_int b :=
quot.sound (prerat.of_int_mul a b)

theorem of_int_neg (a : ℤ) : of_int (-a) = -(of_int a) :=
quot.sound (prerat.of_int_neg a)

theorem of_int_sub (a b : ℤ) : of_int (a - b) = of_int a - of_int b :=
calc
  of_int (a - b) = of_int a + of_int (-b) : of_int_add
             ... = of_int a - of_int b    : {of_int_neg b}

theorem of_int.inj {a b : ℤ} (H : of_int a = of_int b) : a = b :=
prerat.of_int.inj (quot.exact H)

theorem eq_of_of_int_eq_of_int {a b : ℤ} (H : of_int a = of_int b) : a = b :=
of_int.inj H

theorem of_int_eq_of_int_iff (a b : ℤ) : of_int a = of_int b ↔ a = b :=
iff.intro eq_of_of_int_eq_of_int !congr_arg

theorem of_nat_eq (a : ℕ) : of_nat a = of_int (int.of_nat a) :=
rfl

open nat

theorem of_nat_add (a b : ℕ) : of_nat (a + b) = of_nat a + of_nat b :=
by rewrite [of_nat_eq, int.of_nat_add, rat.of_int_add]

theorem of_nat_mul (a b : ℕ) : of_nat (a * b) = of_nat a * of_nat b :=
by rewrite [of_nat_eq, int.of_nat_mul, rat.of_int_mul]

theorem of_nat_sub {a b : ℕ} (H : a ≥ b) : of_nat (a - b) = of_nat a - of_nat b :=
begin
  rewrite of_nat_eq,
  rewrite [int.of_nat_sub H],
  rewrite [rat.of_int_sub]
end

theorem of_nat.inj {a b : ℕ} (H : of_nat a = of_nat b) : a = b :=
int.of_nat.inj (of_int.inj H)

theorem eq_of_of_nat_eq_of_nat {a b : ℕ} (H : of_nat a = of_nat b) : a = b :=
of_nat.inj H

theorem of_nat_eq_of_nat_iff (a b : ℕ) : of_nat a = of_nat b ↔ a = b :=
iff.intro of_nat.inj !congr_arg

protected theorem add_comm (a b : ℚ) : a + b = b + a :=
quot.induction_on₂ a b (take u v, quot.sound !prerat.add.comm)

protected theorem add_assoc (a b c : ℚ) : a + b + c = a + (b + c) :=
quot.induction_on₃ a b c (take u v w, quot.sound !prerat.add.assoc)

protected theorem add_zero (a : ℚ) : a + 0 = a :=
quot.induction_on a (take u, quot.sound !prerat.add_zero)

protected theorem zero_add (a : ℚ) : 0 + a = a := !rat.add_comm ▸ !rat.add_zero

protected theorem add_left_inv (a : ℚ) : -a + a = 0 :=
quot.induction_on a (take u, quot.sound !prerat.add_left_inv)

protected theorem mul_comm (a b : ℚ) : a * b = b * a :=
quot.induction_on₂ a b (take u v, quot.sound !prerat.mul_comm)

protected theorem mul_assoc (a b c : ℚ) : a * b * c = a * (b * c) :=
quot.induction_on₃ a b c (take u v w, quot.sound !prerat.mul_assoc)

protected theorem mul_one (a : ℚ) : a * 1 = a :=
quot.induction_on a (take u, quot.sound !prerat.mul_one)

protected theorem one_mul (a : ℚ) : 1 * a = a := !rat.mul_comm ▸ !rat.mul_one

protected theorem left_distrib (a b c : ℚ) : a * (b + c) = a * b + a * c :=
quot.induction_on₃ a b c (take u v w, quot.sound !prerat.mul_left_distrib)

protected theorem right_distrib (a b c : ℚ) : (a + b) * c = a * c + b * c :=
by rewrite [rat.mul_comm, rat.left_distrib, *rat.mul_comm c]

protected theorem mul_inv_cancel {a : ℚ} : a ≠ 0 → a * a⁻¹ = 1 :=
quot.induction_on a
  (take u,
    assume H,
    quot.sound (!prerat.mul_inv_cancel (assume H1, H (quot.sound H1))))

protected theorem inv_mul_cancel {a : ℚ} (H : a ≠ 0) : a⁻¹ * a = 1 :=
!rat.mul_comm ▸ rat.mul_inv_cancel H

protected theorem zero_ne_one : (0 : ℚ) ≠ 1 :=
assume H, prerat.zero_not_equiv_one (quot.exact H)

definition has_decidable_eq [instance] : decidable_eq ℚ :=
take a b, quot.rec_on_subsingleton₂ a b
  (take u v,
     if H : prerat.num u * prerat.denom v = prerat.num v * prerat.denom u
       then decidable.inl (quot.sound H)
       else decidable.inr (assume H1, H (quot.exact H1)))

protected theorem inv_zero : inv 0 = (0 : ℚ) :=
quot.sound (prerat.inv_zero' ▸ !prerat.equiv.refl)

theorem quot_reduce (a : ℚ) : ⟦reduce a⟧ = a :=
quot.induction_on a (take u, quot.sound !prerat.reduce_equiv)

section
local attribute rat [reducible]
theorem mul_denom (a : ℚ) : a * denom a = num a :=
have H : ⟦reduce a⟧ * of_int (denom a) = of_int (num a), from quot.sound (!prerat.mul_denom_equiv),
quot_reduce a ▸ H
end

theorem coprime_num_denom (a : ℚ) : coprime (num a) (denom a) :=
decidable.by_cases
  (suppose a = 0, by substvars)
  (quot.induction_on a
    (take u H,
      have H' : prerat.num u ≠ 0, from take H'', H (quot.sound (prerat.equiv_zero_of_num_eq_zero H'')),
      begin
        cases u with un ud udpos,
        rewrite [▸*, ↑num, ↑denom, ↑reduce, ↑prerat.reduce, if_neg H', ▸*],
        have gcd un ud ≠ 0, from ne_of_gt (!gcd_pos_of_ne_zero_left H'),
        apply coprime_div_gcd_div_gcd this
      end))


protected definition discrete_field [trans_instance] : discrete_field rat :=
⦃discrete_field,
 add              := rat.add,
 add_assoc        := rat.add_assoc,
 zero             := 0,
 zero_add         := rat.zero_add,
 add_zero         := rat.add_zero,
 neg              := rat.neg,
 add_left_inv     := rat.add_left_inv,
 add_comm         := rat.add_comm,
 mul              := rat.mul,
 mul_assoc        := rat.mul_assoc,
 one              := 1,
 one_mul          := rat.one_mul,
 mul_one          := rat.mul_one,
 left_distrib     := rat.left_distrib,
 right_distrib    := rat.right_distrib,
 mul_comm         := rat.mul_comm,
 mul_inv_cancel   := @rat.mul_inv_cancel,
 inv_mul_cancel   := @rat.inv_mul_cancel,
 zero_ne_one      := rat.zero_ne_one,
 inv_zero         := rat.inv_zero,
 has_decidable_eq := has_decidable_eq⦄

definition rat_has_div [instance] [priority rat.prio] : has_div rat :=
has_div.mk has_div.div

definition rat_has_pow_nat [instance] [priority rat.prio] : has_pow_nat rat :=
has_pow_nat.mk has_pow_nat.pow_nat

theorem eq_num_div_denom (a : ℚ) : a = num a / denom a :=
have H : of_int (denom a) ≠ 0, from assume H', ne_of_gt (denom_pos a) (of_int.inj H'),
iff.mpr (!eq_div_iff_mul_eq H) (mul_denom a)

theorem of_int_div {a b : ℤ} (H : b ∣ a) : of_int (a / b) = of_int a / of_int b :=
decidable.by_cases
  (assume bz : b = 0,
    by rewrite [bz, int.div_zero, of_int_zero, div_zero])
  (assume bnz : b ≠ 0,
    have bnz' : of_int b ≠ 0, from assume oibz, bnz (of_int.inj oibz),
    have H' : of_int (a / b) * of_int b = of_int a, from
      dvd.elim H
        (take c, assume Hc : a = b * c,
          by rewrite [Hc, !int.mul_div_cancel_left bnz, mul.comm]),
    iff.mpr (!eq_div_iff_mul_eq bnz') H')

theorem of_nat_div {a b : ℕ} (H : b ∣ a) : of_nat (a / b) = of_nat a / of_nat b :=
have H' : (int.of_nat b ∣ int.of_nat a), by rewrite [int.of_nat_dvd_of_nat_iff]; exact H,
by rewrite [of_nat_eq, int.of_nat_div, of_int_div H']

theorem of_int_pow (a : ℤ) (n : ℕ) : of_int (a^n) = (of_int a)^n :=
begin
  induction n with n ih,
    apply eq.refl,
  rewrite [pow_succ, pow_succ, of_int_mul, ih]
end

theorem of_nat_pow (a : ℕ) (n : ℕ) : of_nat (a^n) = (of_nat a)^n :=
by rewrite [of_nat_eq, int.of_nat_pow, of_int_pow]

end rat
