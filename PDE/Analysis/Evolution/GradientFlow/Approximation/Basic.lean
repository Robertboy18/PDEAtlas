/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Yosida.Approximation
public import PDE.Analysis.Evolution.ODE.Autonomous.Lipschitz
public import PDE.Analysis.Evolution.ODE.Autonomous.Dissipative

/-!
# Constructed Yosida trajectories

Let `I : H → EReal` be proper, convex and lower semicontinuous on a real Hilbert
space `H`, and let `λ > 0`. The Yosida approximation `A_λ = λ⁻¹ (id - J_λ)` of
`∂I`, built from the resolvent `J_λ`, is globally Lipschitz, so `u' = -A_λ u`,
`u(0) = x₀`, has a solution `yosidaFlow` on `[0, ∞)`. Since `A_λ` is monotone,
`‖A_λ u(t)‖ ≤ ‖A_λ x₀‖ ≤ ‖v‖` for every `v ∈ ∂I(x₀)` and `t ≥ 0`, so the flow is
`‖v‖`-Lipschitz on `[0, ∞)` uniformly in `λ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis.Convex

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- The half-line trajectory of the negative Yosida approximation, constructed by
the Banach-space autonomous existence theorem. -/
def yosidaFlow (I : H → EReal) (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    (lambda : ℝ) (hlambda : 0 < lambda) (x₀ : H) : ℝ → H :=
  (exists_isIntegralCurveOn_Ici_of_lipschitz
    (lipschitzWith_yosidaApproximation hproper hconvex hlsc hlambda).neg x₀).choose

variable (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
  (hlsc : LowerSemicontinuous I) {lambda : ℝ} (hlambda : 0 < lambda)

/-- The constructed Yosida curve has the prescribed initial value. -/
theorem yosidaFlow_zero (x₀ : H) :
    yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ 0 = x₀ :=
  (exists_isIntegralCurveOn_Ici_of_lipschitz
    (lipschitzWith_yosidaApproximation hproper hconvex hlsc hlambda).neg x₀).choose_spec.1

/-- The constructed Yosida curve solves its autonomous equation on the closed half-line. -/
theorem isIntegralCurveOn_yosidaFlow (x₀ : H) :
    IsIntegralCurveOn (yosidaFlow I hproper hconvex hlsc lambda hlambda x₀)
      (fun _ x ↦ -yosidaApproximation I hproper hconvex hlsc lambda hlambda x)
      (Ici 0) :=
  (exists_isIntegralCurveOn_Ici_of_lipschitz
    (lipschitzWith_yosidaApproximation hproper hconvex hlsc hlambda).neg x₀).choose_spec.2

private theorem yosida_dissipative (x y : H) :
    inner ℝ
      (-yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
        -yosidaApproximation I hproper hconvex hlsc lambda hlambda y) (x - y) ≤ 0 := by
  rw [show -yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
      -yosidaApproximation I hproper hconvex hlsc lambda hlambda y =
      -(yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
        yosidaApproximation I hproper hconvex hlsc lambda hlambda y) by abel,
    inner_neg_left, neg_nonpos]
  rw [real_inner_comm]
  exact yosidaApproximation_monotone hproper hconvex hlsc hlambda x y

/-- Every initial subgradient bounds the Yosida velocity: `‖A_λ u(t)‖ ≤ ‖v‖` for
`v ∈ ∂I(x₀)`, every `t ≥ 0` and every `λ > 0`. -/
theorem norm_yosidaFlow_velocity_le {x₀ v : H} (hv : v ∈ subdifferential I x₀)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖yosidaApproximation I hproper hconvex hlsc lambda hlambda
      (yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t)‖ ≤ ‖v‖ := by
  have h := norm_field_le_initial_of_dissipative
    (yosida_dissipative hproper hconvex hlsc hlambda)
    (isIntegralCurveOn_yosidaFlow hproper hconvex hlsc hlambda x₀) ht
  simp only [norm_neg, yosidaFlow_zero] at h
  exact h.trans
    (norm_yosidaApproximation_le_of_mem_subdifferential hproper hconvex hlsc hlambda hv)

/-- The same initial subgradient norm bounds all time increments of the constructed
Yosida curve. -/
theorem lipschitzOnWith_yosidaFlow {x₀ v : H} (hv : v ∈ subdifferential I x₀) :
    LipschitzOnWith ‖v‖₊ (yosidaFlow I hproper hconvex hlsc lambda hlambda x₀) (Ici 0) := by
  apply (convex_Ici 0).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (isIntegralCurveOn_yosidaFlow hproper hconvex hlsc hlambda x₀)
  intro t ht
  simpa only [← NNReal.coe_le_coe, coe_nnnorm, norm_neg] using
    norm_yosidaFlow_velocity_le hproper hconvex hlsc hlambda hv ht

end PDE.Analysis.Evolution
