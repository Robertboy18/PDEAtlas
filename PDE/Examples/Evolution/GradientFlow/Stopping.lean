/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Existence.Domain
public import PDE.Analysis.Evolution.Time.WeakDerivative.AbsolutelyContinuous
import CAS.ExactTactic

/-!
# A trajectory that stops in finite time

The curve `max (3 - t) 0` is the gradient flow of the constrained affine energy. Its
corner at the stopping time is allowed in the weak solution class, and the whole curve
has a distributional velocity. The computer algebra system checks the derivative of
each branch and the affine identity.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution
open scoped ENNReal Topology

namespace PDE.Examples.GradientFlow

/-- Unit-speed motion from three to zero, followed by rest. -/
def stoppingCurve (t : ℝ) : ℝ := max (3 - t) 0

/-- The almost-everywhere velocity, chosen to vanish at the corner. -/
def stoppingVelocity (t : ℝ) : ℝ := if t < 3 then -1 else 0

/-- The complete curve is one-Lipschitz, including the stopping time. -/
theorem stoppingCurve_lipschitz : LipschitzWith 1 stoppingCurve := by
  apply LipschitzWith.max_const (f := fun t : ℝ ↦ 3 - t)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hid : 3 - x - (3 - y) = -(x - y) := by cas
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, hid, abs_neg, le_refl]

/-- The piecewise velocity is globally essentially bounded. -/
theorem stoppingVelocity_memLp : MemLp stoppingVelocity ∞ volume := by
  apply memLp_top_of_bound (C := 1)
  · exact ((measurable_const.piecewise measurableSet_Iio measurable_const) :
      Measurable stoppingVelocity).aestronglyMeasurable
  · exact Eventually.of_forall fun t ↦ by
      by_cases ht : t < 3 <;> simp [stoppingVelocity, ht]

/-- Away from its corner, the curve has the stated derivative. -/
theorem stoppingCurve_hasDerivAt {t : ℝ} (ht : t ≠ 3) :
    HasDerivAt stoppingCurve (stoppingVelocity t) t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hd : HasDerivAt (fun s : ℝ ↦ 3 - s) (-1) t := by cas
    rw [stoppingVelocity, ite_eq_left ht]
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact max_eq_left (sub_nonneg.2 hs.le)
  · rw [stoppingVelocity, ite_eq_right ht.not_gt]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact max_eq_right (sub_nonpos.2 hs.le)

/-- The piecewise velocity is the weak derivative of the curve. -/
theorem stoppingCurve_hasWeakTimeDerivativeOn :
    HasWeakTimeDerivativeOn (Ioi 0) stoppingCurve stoppingVelocity := by
  suffices h : HasWeakTimeDerivativeOn univ stoppingCurve stoppingVelocity from
    h.mono (subset_univ _)
  apply HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    stoppingCurve_lipschitz.continuous.locallyIntegrable
    (stoppingVelocity_memLp.locallyIntegrable le_top)
  · intro a b
    exact stoppingCurve_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval
  · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 3 := by simp [ae_iff]
    filter_upwards [hne] with t ht
    exact stoppingCurve_hasDerivAt ht

/-- Concrete distinct values before stopping and the permanent zero value afterward. -/
theorem stoppingCurve_values :
    stoppingCurve 0 = 3 ∧ stoppingCurve 1 = 2 ∧ ∀ t : ℝ, 3 ≤ t → stoppingCurve t = 0 := by
  refine ⟨by norm_num [stoppingCurve], by norm_num [stoppingCurve], ?_⟩
  intro t ht
  exact max_eq_right (sub_nonpos.2 ht)

end PDE.Examples.GradientFlow
