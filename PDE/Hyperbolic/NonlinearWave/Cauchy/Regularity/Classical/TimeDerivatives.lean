/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Multiplication
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.SpatialDerivatives
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongEvolution
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongSolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A primitive detected through an injective bounded linear map

Let `v` and `w` be continuous curves in a Banach space and `A` an injective bounded linear map.
If `∫ s in a..t, A (w s) = A (v t) - A (v a)` for every `t ∈ [a, b]`, then `v` has the derivative
`w t` within `[a, b]` at every `t ∈ [a, b]` (`hasDerivWithinAt_of_mapped_integral`). No bounded
inverse of `A` is needed.

The wave theory applies this with the Sobolev base coordinate and with the pivot map into the
`H¹` dual: an integrated energy equation then gives a strong time derivative at a higher Sobolev
level.

The lemma needs only the fundamental theorem of calculus. The other imports are the modules of the
wave regularity theory that the importers of this module reach through it.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- An injective bounded linear map detects a continuous vector-valued primitive.
This does not require a bounded inverse for that map. -/
theorem hasDerivWithinAt_of_mapped_integral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (A : E →L[ℝ] F)
    (hA : Function.Injective A) (v w : C(ℝ, E)) {a b : ℝ}
    (hi : ∀ t ∈ Icc a b, (∫ s in a..t, A (w s)) = A (v t) - A (v a)) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt v (w t) (Icc a b) t := by
  have hprimitive (r : ℝ) (hr : r ∈ Icc a b) : v r = (∫ s in a..r, w s) + v a := by
    apply hA
    rw [map_add, ← A.intervalIntegral_comp_comm (w.continuous.intervalIntegrable a r),
      hi r hr, sub_add_cancel]
  have hd := intervalIntegral.integral_hasDerivAt_right (w.continuous.intervalIntegrable a t)
    w.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter w.continuous.continuousAt
  exact (hd.add_const (v a)).hasDerivWithinAt.congr_of_mem hprimitive ht

end PDE.Hyperbolic.NonlinearWave.Cauchy
