/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Estimates.NormalGradient
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.LocalizedEnergy

/-!
# A fixed constant for localized nonlinear H² regularity

Tangential quotient estimates, the divergence equation, and normal
inverse recovery successively bound the localized gradient. The final
H² assembly adds only cutoff operator norms. The constant below
contains no solution, flux field, or load.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal

variable {n : ℕ} [Fact (0 < n)]

/-- The local H² estimate constant, determined by coefficient bounds,
dimension, and the chosen cutoff. `D` is its Lipschitz bound. -/
def localizedH2EstimateConstant (m : ℝ) (K C D : ℝ≥0)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  let M := ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖
  let T := |localizedTangentialEstimateConstant m K C η|
  let B := T + D
  let Bq := K * M * n + C * T + D
  let R := M + n * (M +
    (∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖) + (n + 1) * Bq)
  Fintype.card (DerivIndex n 2) *
    (‖cutoffCLM (p := 2) (Ω := HalfSpace.upper n) η‖ +
      n * localizedGradientRecoveryConstant m K C D B R η +
        ∑ i : Fin n, ‖cutoffCLM (p := 2) (Ω := HalfSpace.upper n)
          (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) η)‖)

/-- The local estimate constant is nonnegative for positive
monotonicity. -/
theorem localizedH2EstimateConstant_nonneg {m : ℝ} (hm : 0 < m)
    (K C D : ℝ≥0) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    0 ≤ localizedH2EstimateConstant m K C D η := by
  have hnormal := localizedGradientRecoveryConstant_nonneg
    hm K.coe_nonneg C.coe_nonneg D.coe_nonneg
    (show 0 ≤ |localizedTangentialEstimateConstant m K C η| + (D : ℝ) by positivity)
    (show 0 ≤ ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ +
      n * (‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ +
        (∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖) +
        (n + 1) * ((K : ℝ) * ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ * n +
          C * |localizedTangentialEstimateConstant m K C η| + D)) by positivity) η
  unfold localizedH2EstimateConstant
  positivity

end PDE.Elliptic.Regularity.Quasilinear
