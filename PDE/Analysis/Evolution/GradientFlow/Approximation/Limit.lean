/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Approximation.Comparison
public import PDE.Analysis.Metric.Convergence.Quadratic

/-!
# One strong limit of the Yosida trajectories

Let `v ∈ ∂I(x₀)`. By the two-parameter comparison, the Yosida flows with
parameters `1/(n+1)` form a uniformly Cauchy sequence on every interval `[0, T]`.
Completeness of `H` gives a pointwise limit `u` on `[0, ∞)`, the convergence is
uniform on each `[0, T]`, and `u` inherits the time-Lipschitz bound
`‖u(s) - u(t)‖ ≤ ‖v‖ |s - t|` of the approximations. The space `H` need not be
separable.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis.Convex
open scoped Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- For proper convex lower semicontinuous `I` and `v ∈ ∂I(x₀)`, the Yosida flows
with parameters `1/(n+1)` converge uniformly on every `[0, T]` to a function `u`
with `u(0) = x₀` that is `‖v‖`-Lipschitz on `[0, ∞)`. -/
theorem exists_yosidaFlow_limit (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    {x₀ v : H} (hv : v ∈ subdifferential I x₀) :
    ∃ u : ℝ → H, u 0 = x₀ ∧ LipschitzOnWith ‖v‖₊ u (Ici 0) ∧
      ∀ T : ℝ, 0 ≤ T →
        TendstoUniformlyOn
          (fun n : ℕ ↦ yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
            (by positivity) x₀)
          u atTop (Icc 0 T) := by
  let parameter := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < parameter n := by dsimp [parameter]; positivity
  let f := fun n ↦ yosidaFlow I hproper hconvex hlsc (parameter n) (hpos n) x₀
  have hparameter : Tendsto parameter atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcauchy (T : ℝ) (hT : 0 ≤ T) : UniformCauchySeqOn f atTop (Icc 0 T) := by
    apply Metric.uniformCauchySeqOn_of_dist_sq_le_add
      (error := fun n ↦ parameter n / 2 * T * ‖v‖ ^ 2)
      (by simpa using ((hparameter.div_const 2).mul_const T).mul_const (‖v‖ ^ 2))
    intro i j t ht
    have h := norm_yosidaFlow_sub_sq_le hproper hconvex hlsc (hpos i) (hpos j) hv ht.1
    rw [dist_eq_norm]
    calc
      ‖f i t - f j t‖ ^ 2 ≤ (parameter i + parameter j) / 2 * t * ‖v‖ ^ 2 := h
      _ ≤ (parameter i + parameter j) / 2 * T * ‖v‖ ^ 2 := by
        gcongr
        exact ht.2
      _ = _ := by ring
  choose w hw using fun t : Ici (0 : ℝ) ↦
    cauchySeq_tendsto_of_complete ((hcauchy t.1 t.2).cauchySeq (right_mem_Icc.2 t.2))
  let u := fun t : ℝ ↦ w ⟨max t 0, le_max_right t 0⟩
  have hlimit {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun n ↦ f n t) atTop (𝓝 (u t)) := by
    simpa only [u, max_eq_left ht] using hw ⟨t, ht⟩
  refine ⟨u, ?_, ?_, fun T _ ↦ (hcauchy T (by assumption)).tendstoUniformlyOn_of_tendsto
    (fun t ht ↦ hlimit ht.1)⟩
  · have h := hlimit (t := 0) le_rfl
    simp only [f, yosidaFlow_zero] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    apply le_of_tendsto ((hlimit hs).dist (hlimit ht))
    exact Eventually.of_forall fun n ↦
      (lipschitzOnWith_yosidaFlow hproper hconvex hlsc (hpos n) hv).dist_le_mul s hs t ht

end PDE.Analysis.Evolution
