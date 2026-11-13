/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Continuation

/-!
# The constructed three-dimensional quadratic higher evolution

The reaction is `f(z) = -z²`, so the wave equation is `u_tt - Δu = u²`.
We use the canonical integer Sobolev spaces H⁵ × H⁴. These orders allow the
classical observation and both strong time derivatives; no optimal-regularity
claim is made. The trajectory and lifespan are the semigroup
construction for the smooth quadratic source.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev

namespace WaveEquation.SmallData.Classical.NormBlowup

/-- The focusing quadratic reaction is smooth, including at zero. -/
theorem contDiff_neg_sq : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ ↦ -(z ^ 2)) :=
  (contDiff_id.pow 2).neg

/-- The mass-canceling quadratic source on H⁵ × H⁴ in dimension three. -/
def quadraticStateMap : C(W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3),
    W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3)) :=
  higherSmoothMap (by norm_num : (3 : ℝ) < 2 * ((4 : ℝ) - 1)) contDiff_neg_sq (by simp)

/-- The quadratic source is locally Lipschitz in the full higher state norm. -/
theorem locallyLipschitz_quadraticStateMap : LocallyLipschitz quadraticStateMap :=
  locallyLipschitz_higherSmoothSource _ contDiff_neg_sq (by simp)

/-- The constructed maximal higher Sobolev lifetime for zero displacement
and the velocity represented by `H`, restricted from H⁵ to H⁴. -/
def quadraticLifespan (H : W^{5,2}(ℝ^3)) : ℝ≥0∞ :=
  (higherLinearSemigroup 3 4).mildLifespan quadraticStateMap
    (0, lowerOrderCLM (by omega : 4 ≤ 5) H)

/-- The maximal semilinear trajectory with zero displacement. Its
values outside the forward lifetime are the arbitrary initial-state extension
used by the generic construction. -/
def quadraticTrajectory (H : W^{5,2}(ℝ^3)) :
    ℝ → W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3) :=
  (higherLinearSemigroup 3 4).maximalMildSolution
    locallyLipschitz_quadraticStateMap (0, lowerOrderCLM (by omega : 4 ≤ 5) H)

/-- Local existence is supplied by the smooth Sobolev source construction. -/
theorem quadraticLifespan_pos (H : W^{5,2}(ℝ^3)) : 0 < quadraticLifespan H :=
  (higherLinearSemigroup 3 4).mildLifespan_pos locallyLipschitz_quadraticStateMap _

/-- The constructed state has exactly the prescribed initial data. -/
theorem quadraticTrajectory_zero (H : W^{5,2}(ℝ^3)) :
    quadraticTrajectory H 0 = (0, lowerOrderCLM (by omega : 4 ≤ 5) H) :=
  (higherLinearSemigroup 3 4).maximalMildSolution_zero locallyLipschitz_quadraticStateMap _

/-- Before a finite endpoint the constructed trajectory is a
continuous mild solution, with the quadratic Duhamel equation. -/
theorem isMildSolutionBefore_quadraticTrajectory
    (H : W^{5,2}(ℝ^3)) (hfinite : quadraticLifespan H ≠ ∞) :
    (higherLinearSemigroup 3 4).IsMildSolutionBefore quadraticStateMap
      (0, lowerOrderCLM (by omega : 4 ≤ 5) H)
      (quadraticLifespan H).toReal (quadraticTrajectory H) :=
  (higherLinearSemigroup 3 4).isMildSolutionBefore_maximalMildSolution
    locallyLipschitz_quadraticStateMap _ hfinite

end WaveEquation.SmallData.Classical.NormBlowup
