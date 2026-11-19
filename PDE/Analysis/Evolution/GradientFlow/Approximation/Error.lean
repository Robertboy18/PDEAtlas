/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Approximation.Limit

/-!
# Quantitative error of Yosida trajectories

Letting `μ → 0` in `‖u_λ(t) - u_μ(t)‖² ≤ ((λ + μ)/2) t ‖v‖²` gives
`‖u_λ(t) - u(t)‖² ≤ (λ/2) t ‖v‖²` for the uniform limit `u` of the Yosida flows
and any `v ∈ ∂I(x₀)`.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis.Convex
open scoped Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- If the Yosida flows with parameters `1/(n+1)` converge to `u` uniformly on every
`[0, T]`, then `‖u_λ(t) - u(t)‖² ≤ (λ/2) t ‖v‖²` for every `λ > 0`, `t ≥ 0` and
`v ∈ ∂I(x₀)`. -/
theorem norm_yosidaFlow_sub_limit_sq_le (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    {x₀ v : H} (hv : v ∈ subdifferential I x₀) {u : ℝ → H}
    (hu : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn
      (fun n : ℕ ↦ yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
        (by positivity) x₀) u atTop (Icc 0 T))
    {lambda : ℝ} (hlambda : 0 < lambda) {t : ℝ} (ht : 0 ≤ t) :
    ‖yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t - u t‖ ^ 2 ≤
      lambda / 2 * t * ‖v‖ ^ 2 := by
  have hpoint := (hu t ht).tendsto_at (right_mem_Icc.2 ht)
  have hleft := (((tendsto_const_nhds (x :=
    yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t)).sub hpoint).norm).pow 2
  have hright := ((((tendsto_const_nhds (x := lambda)).add
    tendsto_one_div_add_atTop_nhds_zero_nat).div_const 2).mul_const t).mul_const (‖v‖ ^ 2)
  apply le_of_tendsto_of_tendsto hleft (by simpa using hright)
  apply Eventually.of_forall
  intro n
  simpa only [one_div] using norm_yosidaFlow_sub_sq_le
    hproper hconvex hlsc hlambda (by positivity : 0 < 1 / ((n : ℝ) + 1)) hv ht

end PDE.Analysis.Evolution
