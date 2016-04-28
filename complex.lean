import data.real
open real eq.ops 

namespace complex

record complex : Type :=
(Re : ℝ) (Im : ℝ)

protected proposition eq {z w : complex} (H1 : complex.Re z = complex.Re w) 
(H2 : complex.Im z = complex.Im w) : z = w :=
begin
  induction z,
  induction w,
  rewrite [H1, H2]
end

definition add_c (z w : complex) : complex :=
    complex.mk (complex.Re z + complex.Re w) (complex.Im z + complex.Im w)
    
infix `+` := add_c

theorem add_c.comm (w z : complex) : w + z = z + w :=
     have H1 : complex.Re (w + z) = complex.Re (z + w), from !add.comm,
     have H2 : complex.Im (w + z) = complex.Im (z + w), from !add.comm,
     show _, from complex.eq H1 H2
     
theorem add_c.assoc (w z u : complex) : (w + z) + u = w + (z + u) :=
    have H1 : complex.Re ((w + z) + u) = complex.Re (w + (z + u)),  from !add.assoc,
    have H2 : complex.Im ((w + z) + u) = complex.Im (w + (z + u)),  from !add.assoc,
    show _, from complex.eq H1 H2
     
definition of_real (x : ℝ) : complex := complex.mk x 0

definition zero : complex := of_real 0

definition one : complex := of_real 1
    
theorem c.add_zero {z : complex} : z + zero = z :=
    have H1 : complex.Re (z + zero) = complex.Re z, from  !add.comm ▸ !zero_add,
    have H2 : complex.Im (z + zero) = complex.Im z, from !add.comm ▸ !zero_add,
    show _, from complex.eq H1 H2
    
theorem c.zero_add (z : complex) : zero + z = z := !add_c.comm ▸ !c.add_zero
    
definition smul_c (x : ℝ)(z : complex) : complex :=
complex.mk (x*complex.Re z) (x*complex.Im z)

definition neg_c (z : complex) : complex :=
complex.mk (-(complex.Re z)) (-(complex.Im z))

theorem add_c.inv_right {z : complex} : z + neg_c z = zero :=
    have H1 : complex.Re (z + neg_c z) = complex.Re zero,
    from calc
         complex.Re (z + neg_c z)= -(complex.Re z) + complex.Re z : !add.comm
                             ... = complex.Re zero : add.left_inv,
    have H2 : complex.Im (z + neg_c z)  = complex.Im zero,
    from calc
        complex.Im (z + neg_c z) = -(complex.Im z) + complex.Im z : !add.comm
                             ... = complex.Im zero : add.left_inv,
    show _, from complex.eq H1 H2
    
theorem add_c.inv_left {z : complex} : neg_c z + z = zero := !add_c.comm ▸ !add_c.inv_right 
    
definition mul_c (z w : complex) : complex :=
    complex.mk (complex.Re w * complex.Re z - complex.Im w * complex.Im z)
               (complex.Re w * complex.Im z + complex.Im w * complex.Re z)
               
infix `*` := mul_c

theorem mul_c.comm {w z : complex} : w * z = z * w :=
    have H1 : complex.Re (mul_c w z) = complex.Re (mul_c z w),
from calc
    complex.Re (w * z) = complex.Re z * complex.Re w - complex.Im z * complex.Im w : rfl
                       ... = complex.Re w * complex.Re z - complex.Im z * complex.Im w : !mul.comm
                       ... = complex.Re w * complex.Re z - complex.Im w * complex.Im z : !mul.comm
                       ... = complex.Re (z * w) : rfl,
    have H2 : complex.Im (w * z) = complex.Im (z * w),
from calc
    complex.Im (mul_c w z) = complex.Im z * complex.Re w + complex.Re z * complex.Im w : !add.comm
                       ... = complex.Re w * complex.Im z + complex.Re z * complex.Im w : !mul.comm
                       ... = complex.Re w * complex.Im z + complex.Im w * complex.Re z : !mul.comm
                       ... = complex.Im (z * w) : rfl,
show _, from complex.eq H1 H2
           
theorem one_mul {z : complex} :  one * z = z :=
have H1 : complex.Re (one * z) = complex.Re z, from
calc
    complex.Re (one * z) = complex.Re z * 1 - complex.Im z * 0 : rfl
                     ... = complex.Re z - complex.Im z * 0 : !mul_one
                     ... = complex.Re z - 0 : !mul_zero
                     ... = complex.Re z : !add_zero,
have H2 : complex.Im (one * z) = complex.Im z, from 
calc
    complex.Im (one * z) = complex.Re z * 0 + complex.Im z * 1 : rfl
                     ... = complex.Re z * 0 + complex.Im z : !mul_one
                     ... = 0 + complex.Im z : !mul_zero
                     ... = complex.Im z : !zero_add,
show _, from complex.eq H1 H2

theorem mul_one {z : complex} :  z * one = z := !mul_c.comm ▸ !one_mul
	   
theorem mul.r_distrib_Re1 (a b c : ℝ) : a - b - c = a - c - b := 
have H : -b - c = -c -b, from !add.comm,
show _, from
calc
    a - b - c = a + (- b - c) : !add.assoc
          ... = a + (-c - b): H
          ... = a - c - b : !add.assoc

lemma mul.r_distrib_Re2 {a b c : ℝ} : a + b - c = a - c + b := 
have H : b - c = -c + b, from !add.comm,
show _, from
calc
    a + b - c = a + (b - c) : !add.assoc
          ... = a + (-c + b) : H
          ... = a - c + b : !add.assoc


lemma mul.r_distrib_Re {a1 b1 c1 a2 b2 c2 : ℝ} : b1*(a1+c1)-(b2*(a2+c2)) = b1*a1-b2*a2+b1*c1-b2*c2 :=
calc
    b1*(a1+c1)-(b2*(a2+c2)) = b1*a1 + b1*c1 - (b2*(a2+c2)) : !left_distrib
                        ... = b1*a1 + b1*c1 - (b2*a2+b2*c2) : !left_distrib
                        ... = b1*a1 + b1*c1 - b2*c2 - b2*a2 : !sub_add_eq_sub_sub_swap 
                        ... = b1*a1 + b1*c1 - b2*a2 - b2*c2 : !mul.r_distrib_Re1
                        ... = b1*a1-b2*a2+b1*c1-b2*c2 : !mul.r_distrib_Re2

theorem c.right_distrib_Re {z w u : complex} :
 complex.Re ((z + u) * w) = complex.Re (z * w + u * w) :=
calc
    complex.Re ((z + u) * w) = complex.Re w * complex.Re z - complex.Im w * complex.Im z +
complex.Re w * complex.Re u - complex.Im w * complex.Im u : !mul.r_distrib_Re
                         ... = complex.Re (z * w + u * w) : !add.assoc
                         
lemma mul.r_distrib_Im' {a b c : ℝ} : a + b + c = a + c + b :=
have H : b + c = c + b, from !add.comm,
show _, from
calc
    a + b + c = a + (b + c) : !add.assoc
          ... = a + (c + b) : H
          ... = a + c + b : !add.assoc
                         
lemma mul.r_distrib_Im {a1 a2 a3 b1 b2 b3 : ℝ} : a2 * (b1 + b3) + b2 * (a1 + a3) =
a2 * b1 + b2 * a1 + a2 * b3 + b2 * a3 :=
have H : b2 * (a1 + a3) = b2 * a1 + b2 * a3, from !left_distrib,
show _, from
calc
    a2 * (b1 + b3) + b2 * (a1 + a3) = a2 * b1 + a2 * b3 + b2 * (a1 + a3) : !left_distrib
                                ... = a2 * b1 + a2 * b3 + (b2 * a1 + b2 * a3) : H
                                ... = (a2 * b1 + a2 * b3 + b2 * a1) + b2 * a3 : !add.assoc
                                ... = a2 * b1 + b2 * a1 + a2 * b3 + b2 * a3 : !mul.r_distrib_Im'
  
                         
theorem c.right_distrib_Im {z w u : complex} :
 complex.Im ((z + u) * w) = complex.Im (z * w + u * w) :=
calc
    complex.Im ((z + u) * w) = complex.Re w * complex.Im z + complex.Im w * complex.Re z +
complex.Re w * complex.Im u + complex.Im w * complex.Re u : !mul.r_distrib_Im 
                         ... = complex.Im (z * w + u * w) : !add.assoc
                         
theorem c.right_distrib {z w u : complex} : (z + u) * w = z * w + u * w :=
complex.eq c.right_distrib_Re c.right_distrib_Im


lemma c.left_distrib_Re' {z1 z2 w1 w2 u1 u2 : ℝ} : (u1 + w1) * z1 - (u2 + w2) * z2 =
u1 * z1 - u2 * z2 + w1 * z1 - w2 * z2 := 
calc
    (u1 + w1) * z1 - (u2 + w2) * z2 = u1 * z1 + w1 * z1 - (u2 + w2) * z2 : !right_distrib
                                ... = u1 * z1 + w1 * z1 - (u2 * z2 + w2 * z2) : !right_distrib
                                ... = u1 * z1 + w1 * z1 - u2 * z2 - w2 * z2 : !sub_add_eq_sub_sub 
                                ... = u1 * z1 - u2 * z2 + w1 * z1 - w2 * z2 : !mul.r_distrib_Re2

lemma c.left_distrib_Re {z w u : complex} :
 complex.Re (z * (u + w)) = complex.Re (z * u + z * w) := 
 calc
    complex.Re(z * (u + w)) = complex.Re u * complex.Re z - complex.Im u * complex.Im z +
complex.Re w * complex.Re z - complex.Im w * complex.Im z : c.left_distrib_Re'
                        ... = complex.Re (z * u + z * w) : !add.assoc 
                        
lemma c.left_distrib_Im' {z1 z2 w1 w2 u1 u2 : ℝ} : (u1 + w1) * z2 + (u2 + w2) * z1 =
u1 * z2 + u2 * z1 + w1 * z2 + w2 * z1 :=
have H : (u2 + w2) * z1  = u2 * z1 + w2 * z1, from !right_distrib,
show (u1 + w1) * z2 + (u2 + w2) * z1 = u1 * z2 + u2 * z1 + w1 * z2 + w2 * z1, from
calc 
    (u1 + w1) * z2 + (u2 + w2) * z1 = u1 * z2 + w1 * z2 + (u2 + w2) * z1 : !right_distrib
                                ... = u1 * z2 + w1 * z2 + (u2 * z1 + w2 * z1) : H
                                ... = u1 * z2 + w1 * z2 + u2 * z1 + w2 * z1 : !add.assoc
                                ... = u1 * z2 + u2 * z1 + w1 * z2 + w2 * z1 : !mul.r_distrib_Im'
                        
lemma c.left_distrib_Im {z w u : complex} :
 complex.Im (z * (u + w)) = complex.Im (z * u + z * w) := 
 calc
    complex.Im (z * (u + w))= complex.Re u * complex.Im z + complex.Im u * 
complex.Re z + complex.Re w * complex.Im z + complex.Im w * complex.Re z : !c.left_distrib_Im'
                        ... = complex.Im (z * u + z * w) : !add.assoc
                        
theorem c.left_distrib {z w u : complex} : z * (u + w) = z * u + z * w :=
complex.eq c.left_distrib_Re c.left_distrib_Im

lemma neg_right_distrib {x y z : ℝ} : (x - y) * z = x * z - y * z :=
have H : -1*(y*z) = - (y*z), from !neg_eq_neg_one_mul⁻¹, 
show _, from
calc
    (x - y)*z = (x + -y)*z : !sub_eq_add_neg
          ... = x*z + -y*z : !right_distrib
          ... = x*z + -1*y*z : !neg_eq_neg_one_mul
          ... = x*z + -1*(y*z) : !mul.assoc
          ... = x*z + - (y*z) : H
          ... = x * z - y * z : !sub_eq_add_neg⁻¹
          
lemma neg_left_distrib {x y z : ℝ} : z * (x - y) = z * x - z * y :=
have H : -1*(z*y) = -(z*y), from !neg_eq_neg_one_mul⁻¹,
show _, from
calc
    z*(x - y) = z*(x + -y) : !sub_eq_add_neg
          ... = z*x + z*-y : !left_distrib
          ... = z*x + z*(-1*y) : !neg_eq_neg_one_mul
          ... = z*x + z*-1*y : !mul.assoc
          ... = z*x + -1*z*y : !mul.comm
          ... = z*x + -1*(z*y) : !mul.assoc
          ... = z*x + -(z*y) : H
          ... = z*x - z*y : !sub_eq_add_neg⁻¹
          
lemma c.permute_1 {b c d : ℝ} : b + c + d = d + b + c :=
calc 
    b + c + d = b + (c + d) : !add.assoc
          ... = b + (d + c) : !add.comm
          ... = b + d + c : !add.assoc
          ... = d + b + c : !add.comm
          ... = d + (b + c) : !add.assoc
          ... = d + b + c : !add.assoc
          
lemma c.assoc_Re'' {a b c d : ℝ} :  a - b - c - d = a - d - b - c :=
have Hb: -1*b = -b, from !neg_eq_neg_one_mul⁻¹, 
have Hc: -1*c = -c, from !neg_eq_neg_one_mul⁻¹, 
have Hd: -1*d = -d, from !neg_eq_neg_one_mul⁻¹, 
show  a - b - c - d = a - d - b - c, from
calc
    a - b - c - d = a + -b - c - d : !sub_eq_add_neg
              ... = a + -b + -c -d : !sub_eq_add_neg
              ... = a + -b + -c + -d : !sub_eq_add_neg
              ... = (a + (-b + -c)) + -d : !add.assoc
              ... = (a + -(b + c)) + -d : !neg_add
              ... = a + (-(b + c) + -d) : !add.assoc
              ... = a + -(b + c + d) : !neg_add
              ... = a + -(d + b + c) : !c.permute_1
              ... = a + -1*(d + b + c) : !neg_eq_neg_one_mul
              ... = a + (-1*(d+b) + -1*c) : !left_distrib
              ... = a + (-1*d + -1*b + -1*c) : !left_distrib
              ... = a + (-d + -1*b + -1*c) : Hd
              ... = a + (-d + -b + -1*c) : Hb
              ... = a + (-d + -b + -c) : Hc
              ... = (a + (-d + -b)) + -c : !add.assoc
              ... = a + -d + -b + -c : !add.assoc
              ... = a - d + -b + -c : !sub_eq_add_neg⁻¹
              ... = a - d - b - c : !sub_eq_add_neg⁻¹
              ... = a - d - b - c : !sub_eq_add_neg⁻¹

lemma c.assoc_Re' {z1 z2 w1 w2  u1 u2 : ℝ} : u1 * (w1 * z1 - w2 * z2) - u2 * (w1 * z2 + w2 * z1)
= (u1 * w1 - u2 * w2) * z1 - (u1 * w2 + u2 * w1) * z2 := 
    have H1 : u1 * w1 * z1 - u2 * w2 * z1 = (u1 * w1 - u2 * w2) * z1, from !neg_right_distrib⁻¹,
    have H2 : u1 * w2 * z2 + u2 * w1 * z2 = (u1 * w2 + u2 * w1) * z2, from !right_distrib⁻¹,
    show _, from
calc 
    u1 * (w1 * z1 - w2 * z2) - u2 * (w1 * z2 + w2 * z1) = u1 * (w1 * z1) - u1 * (w2 * z2) - 
u2 * (w1 * z2 + w2 * z1) : !neg_left_distrib
                                                    ... = u1 * (w1 * z1) - u1 * (w2 * z2) - (u2 * (w1 * z2) + u2 * (w2 * z1)) : !left_distrib
                                                    ... = u1 * (w1 * z1) - u1 * (w2 * z2) - u2 * (w1 * z2) - u2 * (w2 * z1) : !sub_add_eq_sub_sub
                                                    ... = u1 * (w1 * z1) - u2 * (w2 * z1) - u1 * (w2 * z2) - u2 * (w1 * z2) : c.assoc_Re''
                                                    ... = u1 * w1 * z1 - u2 * (w2 * z1) - u1 * (w2 * z2) - u2 * (w1 * z2) : !mul.assoc
                                                    ... = u1 * w1 * z1 - u2 * w2 * z1 - u1 * (w2 * z2) - u2 * (w1 * z2) : !mul.assoc
                                                    ... = u1 * w1 * z1 - u2 * w2 * z1 - u1 * w2 * z2 - u2 * (w1 * z2) : !mul.assoc
                                                    ... = u1 * w1 * z1 - u2 * w2 * z1 - u1 * w2 * z2 - u2 * w1 * z2 : !mul.assoc
                                                    ... = (u1 * w1 - u2 * w2) * z1 - u1 * w2 * z2 - u2 * w1 * z2 : H1
                                                    ... = (u1 * w1 - u2 * w2) * z1 - (u1 * w2 * z2 + u2 * w1 * z2) : !sub_add_eq_sub_sub⁻¹
                                                    ... = (u1 * w1 - u2 * w2) * z1 - (u1 * w2 + u2 * w1) * z2 : H2
    
lemma c.assoc_Re {z w u : complex} : complex.Re ((z * w) * u) = complex.Re(z * (w * u)) :=
!c.assoc_Re' 

lemma c.permute_2 {a b c d : ℝ} : a + b + c + d = a + d + b + c := 
calc
    a + b + c + d  = (a + (b + c)) + d : !add.assoc
               ... = a + (b + c + d) : !add.assoc
               ... = a + (d + b + c) : !c.permute_1
               ... = (a + (d + b)) + c : !add.assoc
               ... = a + d + b + c : !add.assoc

lemma sub_mul_lemma {x y z : ℝ} : x + -y*z = x - y*z := 
calc
    x + -y*z = x + (-1*y)*z : !neg_eq_neg_one_mul
         ... = x + -1*(y*z) : !mul.assoc
         ... = x + -(y*z) : !neg_eq_neg_one_mul
         ... = x - y*z : !sub_eq_add_neg⁻¹

lemma c.assoc_Im' {z1 z2 w1 w2 u1 u2 : real} : u1 * (w1 * z2 + w2 * z1) + u2 * (w1 * z1 -
w2*z2) = (u1 * w1 - u2 * w2) * z2 + (u1 * w2 + u2 * w1) * z1 :=
have H1 : u1 * w2 * z1 + u2 * w1 * z1 = (u1 * w2 + u2 * w1) * z1, from !right_distrib⁻¹,
have G : w1 * z1 - w2 * z2 = w1 * z1 + - w2*z2, from !sub_mul_lemma⁻¹,
have G' : -1 * u2 = - u2, from !neg_eq_neg_one_mul⁻¹,
have G'' : u2 * (w1 * z1) + - u2*(w2*z2) = u2 * (w1 * z1) - u2*(w2*z2), from 
!sub_mul_lemma,
have H2 : u2 * (w1 * z1 - w2*z2) = u2 * (w1 * z1) - u2 * (w2*z2), from 
calc
    u2 * (w1 * z1 - w2*z2) = u2 * (w1 * z1 + -w2*z2) : G
                       ... = u2 * (w1 * z1) + u2 * (-w2*z2) : !left_distrib
                       ... = u2 * (w1 * z1) + u2 * (-1*w2*z2) : !neg_eq_neg_one_mul
                       ... = u2 * (w1 * z1) + u2 * (-1*(w2*z2)) : !mul.assoc
                       ... = u2 * (w1 * z1) + (u2 * -1)*(w2*z2) : !mul.assoc
                       ... = u2 * (w1 * z1) + (-1 * u2)*(w2*z2) : !mul.comm
                       ... = u2 * (w1 * z1) + -u2*(w2*z2) : G'
                       ... = u2 * (w1 * z1) - u2*(w2*z2) : G'',
have H3 : u1 * w1 * z2 - u2 * w2 * z2 = (u1 * w1 - u2 * w2) * z2, from 
calc
    u1 * w1 * z2 - u2 * w2 * z2 = u1 * w1 * z2 + -(u2 * w2) * z2 : !sub_mul_lemma⁻¹
                            ... = (u1 * w1 + -(u2 * w2))*z2 : !right_distrib⁻¹
                            ... = (u1 * w1 + (-1*(u2 * w2)))*z2 : !neg_eq_neg_one_mul
                            ... = (u1 * w1 + (-1*u2 * w2))*z2 : !mul.assoc
                            ... = (u1 * w1 + -u2 * w2)*z2 : !neg_eq_neg_one_mul
                            ... = (u1 * w1 - u2 * w2) * z2 : !sub_mul_lemma,
show _, from
calc 
    u1 * (w1 * z2 + w2 * z1) + u2 * (w1 * z1 - w2*z2) = u1 * (w1 * z2) + u1 * (w2 * z1) 
+ u2 * (w1 * z1 - w2*z2) : !left_distrib
 ... = u1 * (w1 * z2) + u1 * (w2 * z1) + (u2 * (w1 * z1) - u2 * (w2 * z2)) : H2
 ... = u1 * (w1 * z2) + u1 * (w2 * z1) + u2 * (w1 * z1) - u2 * (w2 * z2) : !add.assoc
 ... = u1 * w1 * z2 + u1 * (w2 * z1) + u2 * (w1 * z1) - u2 * (w2*z2) : !mul.assoc
 ... = u1 * w1 * z2 + u1 * w2 * z1 + u2 * (w1 * z1) - u2 * (w2*z2) : !mul.assoc
 ... = u1 * w1 * z2 + u1 * w2 * z1 + u2 * w1 * z1 - u2 * (w2*z2) : !mul.assoc
 ... = u1 * w1 * z2 + u1 * w2 * z1 + u2 * w1 * z1 - u2 * w2*z2 : !mul.assoc
 ... = u1 * w1 * z2 - u2 * w2 * z2 + u1 * w2 * z1 + u2 * w1 * z1 : !c.permute_2
 ... = (u1 * w1 - u2 * w2) * z2 + u1 * w2 * z1 + u2 * w1 * z1 : H3
 ... = (u1 * w1 - u2 * w2) * z2 + (u1 * w2 * z1 + u2 * w1 * z1) : !add.assoc
 ... = (u1 * w1 - u2 * w2) * z2 + (u1 * w2 + u2 * w1) * z1 : H1

lemma c.assoc_Im {z w u : complex} : complex.Im ((z * w) * u) = complex.Im(z * (w * u)) :=
!c.assoc_Im'
    
theorem c_mul.assoc {z w u : complex} : (z * w) * u = z * (w * u) := 
complex.eq c.assoc_Re c.assoc_Im


protected definition comm_ring [reducible] : algebra.comm_ring complex :=
  begin
    fapply algebra.comm_ring.mk,
    exact add_c,
    exact add_c.assoc,
    exact zero,
    exact c.zero_add,
    exact c.add_zero,
    exact neg_c,
    exact add_c.inv_left,
    exact add_c.comm,
    exact mul_c,
    exact c_mul.assoc,
    apply one,
    apply one_mul,
    apply mul_one,
    apply c.left_distrib,
    apply c.right_distrib,
    apply mul_c.comm
  end

noncomputable definition inv_c {z : complex} : complex :=
complex.mk (complex.Re z /((complex.Re z)*(complex.Re z) + (complex.Im z)*(complex.Im z)))
           (-(complex.Im z /((complex.Re z)*(complex.Re z) + (complex.Im z)*(complex.Im z))))

postfix `⁻¹` := inv_c

definition abs {z : complex} : complex :=
complex.mk ((complex.Re z)*(complex.Re z)) ((complex.Im z)*(complex.Im z))
           
end complex
