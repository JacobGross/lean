import logic.eq data.unit data.sigma data.prod
import algebra.binary algebra.priority data.real

open eq eq.ops   -- note: ⁻¹ will be overloaded
open binary real

namespace metric

structure distance [class] (X : Type) :=
(dist : X → X → ℝ)

structure pos_def [class] (X : Type) extends distance X :=
(pos_def : ∀x y, dist x y ≥ 0 ∧ (dist x y = 0 ↔ x = y))

structure symmetric [class] (X : Type) extends pos_def  X :=
(symmetric : ∀x y, dist x y = dist y x)

structure metric [class] (X : Type) extends symmetric X :=
(triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)



end metric
