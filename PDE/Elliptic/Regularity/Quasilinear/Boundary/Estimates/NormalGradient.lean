/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.Implicit.Bounds
public import PDE.Spaces.Sobolev.Calculus.Product.Localization.DerivativeBounds

/-!
# Constants for normal gradient recovery

A common bound on the original fields, a transverse derivative bound,
and a bound on the localized normal flux determine all localized second
derivatives. These constants separate the fixed coefficient and cutoff
data from the norms of the fields.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/-- The coefficient in the recovered normal derivative estimate.
`B` bounds the transverse derivatives and `R` bounds the localized
normal flux, both relative to the same norm scale. -/
def localizedNormalDerivativeConstant (m K C D B R : ℝ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  let E := ‖(SobolevSpace.Extension.GraphSpace.HalfSpace.operator n 2).toContinuousLinearMap‖
  let T := n * B + localizedDerivativeCutoffConstant (HalfSpace.upper n) η
  (E * R + K * (n + 1) + C * (E * n * T + D * n) + D * (1 + m)) / m

/-- A common coefficient for the H¹ norms of all localized gradient
components, including the recovered normal component. -/
def localizedGradientRecoveryConstant (m K C D B R : ℝ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  n * B + localizedDerivativeCutoffConstant (HalfSpace.upper n) η +
    ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ +
      n * (B + localizedNormalDerivativeConstant m K C D B R η)

/-- The normal derivative coefficient is nonnegative for positive
monotonicity and nonnegative input bounds. -/
theorem localizedNormalDerivativeConstant_nonneg {m K C D B R : ℝ}
    (hm : 0 < m) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    0 ≤ localizedNormalDerivativeConstant m K C D B R η := by
  have hcut := localizedDerivativeCutoffConstant_nonneg (Ω := HalfSpace.upper n) η
  unfold localizedNormalDerivativeConstant
  positivity

/-- The full gradient coefficient is nonnegative under the same
quantitative hypotheses. -/
theorem localizedGradientRecoveryConstant_nonneg {m K C D B R : ℝ}
    (hm : 0 < m) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    0 ≤ localizedGradientRecoveryConstant m K C D B R η := by
  have hcut := localizedDerivativeCutoffConstant_nonneg (Ω := HalfSpace.upper n) η
  have hnormal := localizedNormalDerivativeConstant_nonneg hm hK hC hD hB hR η
  unfold localizedGradientRecoveryConstant
  positivity

end PDE.Elliptic.Regularity.Quasilinear
