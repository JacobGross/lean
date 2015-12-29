import data.set theories.topology.basic algebra.intervals
open algebra eq.ops set intervals topology

namespace order_topology

variables {X : Type} [L : linear_strong_order_pair X]

include L

notation `linorder_generators` := {y | ∃ a, y = '(a, ∞) } ∪ {y | ∃ a, y = '(-∞, a)}

definition linorder_topology [instance] [reducible] : topology X := 
  topology_generated_by linorder_generators

theorem open_lt {a : X} : Open '(a, ∞) := 
(generators_mem_topology_generated_by linorder_generators) (!mem_unionl (exists.intro a rfl))

theorem open_gt {a : X} : Open '(-∞, a) := 
(generators_mem_topology_generated_by linorder_generators) (!mem_unionr (exists.intro a rfl))

theorem closed_le {a : X} : closed ('[a,∞)) := 
have '(-∞, a) = -'[a,∞), from ext(take x, iff.intro 
  (assume H, not_le_of_gt H) 
  (assume H, lt_of_not_ge H)),
this ▸ open_gt

theorem closed_ge {a : X} : closed '(-∞,a] :=
have '(a, ∞) = -'(-∞,a], from ext(take x, iff.intro 
  (assume H, not_le_of_gt H) 
  (assume H, lt_of_not_ge H)),
this ▸ open_lt

section
  open classical

  theorem linorder_separation {x y : X} :
    x < y → ∃ a b, (x < a ∧ b < y) ∧ '(-∞, a) ∩ '(b, ∞) = ∅ := 
  suppose x < y,
  if H1 : ∃ z, x < z ∧ z < y then
    obtain z (Hz : x < z ∧ z < y), from H1,
    have '(-∞, z) ∩ '(z, ∞) = ∅, from ext(take r, iff.intro
      (assume H, absurd (!lt.trans (and.elim_left H) (and.elim_right H)) !lt.irrefl)
      (assume H, !not.elim !not_mem_empty H)), 
    exists.intro z (exists.intro z (and.intro Hz this))
  else
    have '(-∞, y) ∩ '(x, ∞) = ∅, from ext(take r, iff.intro
      (assume H, absurd (exists.intro r (iff.elim_left and.comm H)) H1)
      (assume H, !not.elim !not_mem_empty H)),
    exists.intro y (exists.intro x (and.intro (and.intro `x < y` `x < y`) this))

end
 
protected definition T2_space.of_linorder_topology [reducible] [trans_instance] :
  T2_space X :=
⦃ T2_space, linorder_topology,
  T2 := abstract
         take x y, assume H,
         or.elim (lt_or_gt_of_ne H) 
           (assume H,
            obtain a [b Hab], from linorder_separation H,
            show _, from exists.intro '(-∞, a) (exists.intro '(b, ∞) 
              (and.intro open_gt (and.intro open_lt (iff.elim_left and.assoc Hab)))))
           (assume H,
            obtain a [b Hab], from linorder_separation H,
            have Hx : x ∈ '(b, ∞), from and.elim_right (and.elim_left Hab),
            have Hy : y ∈ '(-∞, a), from and.elim_left (and.elim_left Hab),
            have Hi : '(b, ∞) ∩ '(-∞, a) = ∅, from !inter.comm ▸ (and.elim_right Hab),
            have (Open '(b,∞)) ∧ (Open '(-∞, a)) ∧ x ∈ '(b, ∞) ∧ y ∈ '(-∞, a) ∧ '(b, ∞) ∩ '(-∞, a) = ∅, from 
             and.intro open_lt (and.intro open_gt (and.intro Hx (and.intro Hy Hi))),
           show _, from exists.intro '(b,∞) (exists.intro '(-∞, a) this))
        end ⦄

theorem open_right {S : set X} {x y : X} :
  (Open S ∧ x ∈ S ∧ x < y) → ∃ b, b > x ∧ '(-∞, b) ⊆ S := 
assume H,
sorry

theorem open_left {S : set X} {x y : X} :
  (Open S ∧ x ∈ S ∧ y < x) → ∃ b, b < x ∧ '(b, ∞) ⊆ S :=
assume H,
sorry

end order_topology

namespace topological_filters

variables {X : Type} [topology (set X)]

definition nhds (a : set X) : filter X := filter.Inf {S | Open S ∧ a ∈ S}

end topological_filters
