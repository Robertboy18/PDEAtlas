/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.ForwardSmoothing
public import PDE.Fluid.Incompressible.LerayProjection.Heat
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarAncient

/-!
# Forward gaining paths of free self-similar evolution

At positive lag the gaining kernel restarts: the gain at `τ + σ` is free evolution for `σ`
followed by gain for `τ`, and also gain for `τ` followed by free evolution for `σ`. The
projected kernel satisfies the same identities after the Leray projection, and it is the gain
applied after the projection. Forgetting the gained derivative recovers the free evolution.
Forgetting the top order commutes with the free evolution and with both gaining kernels, so the
kernels on `Hᵏ⁺¹` restrict the kernels on `Hᵏ`.

Above the free decay rate `(2 - n) / 4`, the gaining kernel has the singular bound
`C r^(-1/2) exp (ω r)`. The weight `√t exp (-ω t)` therefore makes the gaining orbit
`t ↦ S₀(t) u` from `Hᵏ` to `Hᵏ⁺¹` a bounded continuous path over positive times, with norm
at most `singularSelfsimilarConstant n k ω * ‖u‖`. This path is the forcing of the forward
Volterra equation that perturbs the free evolution by an operator losing one derivative.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution SobolevSpace.Fractional
open scoped NNReal Sobolev BoundedContinuousFunction

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- The gaining kernel at positive lag forgets to the free evolution. -/
theorem vectorLower_vectorSelfsimilarHeatGainKernel {r : ℝ} (hr : 0 < r) (u : VectorH n k) :
    vectorLower n k (vectorSelfsimilarHeatGainKernel n k r u) =
      vectorSelfsimilarHeat n k r.toNNReal u := by
  rw [vectorSelfsimilarHeatGainKernel_eq_toNNReal hr, vectorLower_vectorSelfsimilarHeatGain]

/-- Leray projection commutes with the free gain, so the projected kernel at `τ + σ` is
projected free evolution for `σ` followed by gain for `τ`. -/
theorem projectedSelfsimilarHeatGainKernel_add {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (u : VectorH n k) :
    projectedSelfsimilarHeatGainKernel n k (τ + σ) u =
      vectorSelfsimilarHeatGainKernel n k τ
        (leraySobolev n k (vectorSelfsimilarHeat n k σ.toNNReal u)) := by
  rw [projectedSelfsimilarHeatGainKernel, ContinuousLinearMap.comp_apply,
    vectorSelfsimilarHeatGainKernel_add hτ hσ, vectorSelfsimilarHeatGainKernel_eq_toNNReal hτ,
    leraySobolev_vectorSelfsimilarHeatGain]

/-- The projected gaining kernel at positive lag forgets to projected free evolution. -/
theorem vectorLower_projectedSelfsimilarHeatGainKernel {r : ℝ} (hr : 0 < r)
    (u : VectorH n k) :
    vectorLower n k (projectedSelfsimilarHeatGainKernel n k r u) =
      leraySobolev n k (vectorSelfsimilarHeat n k r.toNNReal u) := by
  rw [projectedSelfsimilarHeatGainKernel, ContinuousLinearMap.comp_apply,
    vectorLower_leraySobolev, vectorLower_vectorSelfsimilarHeatGainKernel hr]

/-- Forgetting the top order commutes with the free evolution. -/
theorem vectorLower_vectorSelfsimilarHeat (τ : ℝ≥0) (u : VectorH n (k + 1)) :
    vectorLower n k (vectorSelfsimilarHeat n (k + 1) τ u) =
      vectorSelfsimilarHeat n k τ (vectorLower n k u) := by
  apply PiLp.ext
  intro j
  apply baseL2_injective
  rw [vectorLower_apply, baseL2_lowerOrderCLM, vectorSelfsimilarHeat_apply,
    vectorSelfsimilarHeat_apply, baseL2_selfsimilarHeatSobolev, baseL2_selfsimilarHeatSobolev,
    vectorLower_apply, baseL2_lowerOrderCLM]

/-- The gain from `Hᵏ⁺¹` to `Hᵏ⁺²`, with the top order forgotten, is the gain from `Hᵏ` to
`Hᵏ⁺¹` of the field with the top order forgotten. -/
theorem vectorLower_succ_vectorSelfsimilarHeatGain (τ : ℝ≥0) (hτ : 0 < τ)
    (u : VectorH n (k + 1)) :
    vectorLower n (k + 1) (vectorSelfsimilarHeatGain n (k + 1) τ hτ u) =
      vectorSelfsimilarHeatGain n k τ hτ (vectorLower n k u) := by
  apply l2SobolevRow_base_injective
  rw [l2SobolevRow_base_vectorLower, l2SobolevRow_vectorSelfsimilarHeatGain,
    l2SobolevRow_vectorSelfsimilarHeatGain, ← vectorLower_vectorSelfsimilarHeat,
    l2SobolevRow_base_vectorLower]

/-- Forgetting the top order commutes with the gaining kernel. -/
theorem vectorLower_succ_vectorSelfsimilarHeatGainKernel (r : ℝ) (u : VectorH n (k + 1)) :
    vectorLower n (k + 1) (vectorSelfsimilarHeatGainKernel n (k + 1) r u) =
      vectorSelfsimilarHeatGainKernel n k r (vectorLower n k u) := by
  by_cases hr : 0 < r
  · rw [vectorSelfsimilarHeatGainKernel_eq_toNNReal hr,
      vectorSelfsimilarHeatGainKernel_eq_toNNReal hr, vectorLower_succ_vectorSelfsimilarHeatGain]
  · simp only [vectorSelfsimilarHeatGainKernel, dite_eq_right hr, zero_apply, map_zero]

/-- Forgetting the top order commutes with the projected gaining kernel. -/
theorem vectorLower_succ_projectedSelfsimilarHeatGainKernel (r : ℝ) (u : VectorH n (k + 1)) :
    vectorLower n (k + 1) (projectedSelfsimilarHeatGainKernel n (k + 1) r u) =
      projectedSelfsimilarHeatGainKernel n k r (vectorLower n k u) := by
  rw [projectedSelfsimilarHeatGainKernel, ContinuousLinearMap.comp_apply, vectorLower_leraySobolev,
    vectorLower_succ_vectorSelfsimilarHeatGainKernel, projectedSelfsimilarHeatGainKernel,
    ContinuousLinearMap.comp_apply]

/-- Free evolution after the gaining kernel is the gaining kernel at the later time. -/
theorem vectorSelfsimilarHeat_vectorSelfsimilarHeatGainKernel {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 < b) (u : VectorH n k) :
    vectorSelfsimilarHeat n (k + 1) a.toNNReal (vectorSelfsimilarHeatGainKernel n k b u) =
      vectorSelfsimilarHeatGainKernel n k (a + b) u := by
  have hab : 0 < a + b := by linarith
  rw [vectorSelfsimilarHeatGainKernel_eq_toNNReal hb,
    vectorSelfsimilarHeatGainKernel_eq_toNNReal hab, ← vectorSelfsimilarHeatGain_add,
    vectorSelfsimilarHeatGain_congr (Real.toNNReal_add ha hb.le).symm]

/-- Free evolution after the projected gaining kernel is the projected gaining kernel at the
later time. -/
theorem vectorSelfsimilarHeat_projectedSelfsimilarHeatGainKernel {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 < b) (u : VectorH n k) :
    vectorSelfsimilarHeat n (k + 1) a.toNNReal (projectedSelfsimilarHeatGainKernel n k b u) =
      projectedSelfsimilarHeatGainKernel n k (a + b) u := by
  rw [projectedSelfsimilarHeatGainKernel, ContinuousLinearMap.comp_apply,
    ← leraySobolev_vectorSelfsimilarHeat,
    vectorSelfsimilarHeat_vectorSelfsimilarHeatGainKernel ha hb,
    projectedSelfsimilarHeatGainKernel, ContinuousLinearMap.comp_apply]

/-- The projected gaining kernel is the gaining kernel applied after the Leray projection. -/
theorem vectorSelfsimilarHeatGainKernel_leraySobolev (r : ℝ) (u : VectorH n k) :
    vectorSelfsimilarHeatGainKernel n k r (leraySobolev n k u) =
      projectedSelfsimilarHeatGainKernel n k r u := by
  rw [projectedSelfsimilarHeatGainKernel, ContinuousLinearMap.comp_apply]
  by_cases hr : 0 < r
  · rw [vectorSelfsimilarHeatGainKernel_eq_toNNReal hr, leraySobolev_vectorSelfsimilarHeatGain]
  · simp only [vectorSelfsimilarHeatGainKernel, dite_eq_right hr,
      zero_apply, map_zero]

/-- Above the free decay rate the gaining kernel has a singular exponential bound. -/
theorem norm_vectorSelfsimilarHeatGainKernel_apply_le {ω r : ℝ}
    (hω : ((2 : ℝ) - n) / 4 < ω) (hr : 0 < r) (u : VectorH n k) :
    ‖vectorSelfsimilarHeatGainKernel n k r u‖ ≤
      singularSelfsimilarConstant n k ω * ‖u‖ * r ^ (-(1 / 2 : ℝ)) * Real.exp (ω * r) := by
  have he : Real.exp (((2 : ℝ) - n) * r / 4) *
      Real.exp ((ω - ((2 : ℝ) - n) / 4) * r) = Real.exp (ω * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hS := selfsimilarSmoothingConstant_nonneg n k
  rw [vectorSelfsimilarHeatGainKernel_eq hr]
  calc
    _ ≤ selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * r / 4) *
        (1 + (Real.sqrt r)⁻¹) * ‖u‖ :=
      norm_vectorSelfsimilarHeatGain_le_exp (.mk r hr.le) hr u
    _ ≤ selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * r / 4) *
        ((1 + (Real.sqrt (2 * (ω - ((2 : ℝ) - n) / 4)))⁻¹) *
          r ^ (-(1 / 2 : ℝ)) * Real.exp ((ω - ((2 : ℝ) - n) / 4) * r)) * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (one_add_inv_sqrt_le_singular_exp (sub_pos.mpr hω) hr)
          (mul_nonneg hS (Real.exp_pos _).le)) (norm_nonneg u)
    _ = _ := by
      unfold singularSelfsimilarConstant
      rw [← he]
      ring

/-- A common square-root constant for the free and the projected gaining kernels from `Hᵏ` to
`Hᵏ⁺¹` and from `Hᵏ⁺¹` to `Hᵏ⁺²`. Above dimension two the free decay rate is negative, so the
kernels have the bound `C r^(-1/2)` at every positive lag. -/
def selfsimilarForwardGainConstant (n k : ℕ) : ℝ :=
  max (singularSelfsimilarConstant n k 0) (singularSelfsimilarConstant n (k + 1) 0)

private theorem free_decay_rate_neg (hn : 2 < n) : ((2 : ℝ) - n) / 4 < 0 := by
  have h : (2 : ℝ) < n := by exact_mod_cast hn
  linarith

/-- The projected gaining kernel from `Hᵏ` has the bound `C r^(-1/2)` above dimension two. -/
theorem norm_projectedSelfsimilarHeatGainKernel_le_selfsimilarForwardGainConstant (hn : 2 < n)
    {r : ℝ} (hr : 0 < r) :
    ‖projectedSelfsimilarHeatGainKernel n k r‖ ≤
      selfsimilarForwardGainConstant n k * r ^ (-(1 / 2 : ℝ)) := by
  have h := norm_projectedSelfsimilarHeatGainKernel_le_singular_exp (n := n) (k := k)
    (free_decay_rate_neg hn) hr
  rw [zero_mul, Real.exp_zero, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _))

/-- The projected gaining kernel from `Hᵏ⁺¹` has the bound `C r^(-1/2)` above dimension
two. -/
theorem norm_projectedSelfsimilarHeatGainKernel_succ_le_selfsimilarForwardGainConstant
    (hn : 2 < n) {r : ℝ} (hr : 0 < r) :
    ‖projectedSelfsimilarHeatGainKernel n (k + 1) r‖ ≤
      selfsimilarForwardGainConstant n k * r ^ (-(1 / 2 : ℝ)) := by
  have h := norm_projectedSelfsimilarHeatGainKernel_le_singular_exp (n := n) (k := k + 1)
    (free_decay_rate_neg hn) hr
  rw [zero_mul, Real.exp_zero, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _))

/-- The gaining kernel from `Hᵏ⁺¹` has the bound `C r^(-1/2)` above dimension two. -/
theorem norm_vectorSelfsimilarHeatGainKernel_succ_le_selfsimilarForwardGainConstant
    (hn : 2 < n) {r : ℝ} (hr : 0 < r) :
    ‖vectorSelfsimilarHeatGainKernel n (k + 1) r‖ ≤
      selfsimilarForwardGainConstant n k * r ^ (-(1 / 2 : ℝ)) := by
  have hC : 0 ≤ selfsimilarForwardGainConstant n k * r ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg ((singularSelfsimilarConstant_nonneg n k 0).trans (le_max_left _ _))
      (Real.rpow_nonneg hr.le _)
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun u ↦ ?_
  have h := norm_vectorSelfsimilarHeatGainKernel_apply_le (n := n) (k := k + 1)
    (free_decay_rate_neg hn) hr u
  rw [zero_mul, Real.exp_zero, mul_one] at h
  calc
    _ ≤ _ := h
    _ = singularSelfsimilarConstant n (k + 1) 0 * r ^ (-(1 / 2 : ℝ)) * ‖u‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)) (norm_nonneg u)

/-- The weight `√t exp (-ω t)` absorbs the short-time singularity and the growth of the free
gain. -/
theorem norm_weighted_vectorSelfsimilarHeatGainKernel_le {ω : ℝ}
    (hω : ((2 : ℝ) - n) / 4 < ω) {t : ℝ} (ht : 0 < t) (u : VectorH n k) :
    ‖(Real.sqrt t * Real.exp (-(ω * t))) • vectorSelfsimilarHeatGainKernel n k t u‖ ≤
      singularSelfsimilarConstant n k ω * ‖u‖ := by
  have hC : 0 ≤ singularSelfsimilarConstant n k ω * ‖u‖ :=
    mul_nonneg (singularSelfsimilarConstant_nonneg n k ω) (norm_nonneg u)
  simpa only [max_eq_left hC] using
    norm_sqrt_mul_exp_smul_le le_rfl ht (norm_vectorSelfsimilarHeatGainKernel_apply_le hω ht u)

/-- The weighted gaining path `t ↦ √t exp (-ω t) S₀(t) u` of free self-similar evolution, from
`Hᵏ` into bounded continuous `Hᵏ⁺¹` paths over positive times, for a rate above the free decay
rate. -/
def vectorSelfsimilarHeatGainPath (n k : ℕ) (ω : ℝ) (hω : ((2 : ℝ) - n) / 4 < ω) :
    VectorH n k →L[ℝ] (Ioi (0 : ℝ) →ᵇ VectorH n (k + 1)) := by
  have hcont (u : VectorH n k) : Continuous (fun t : Ioi (0 : ℝ) ↦
      (Real.sqrt t * Real.exp (-(ω * t))) • vectorSelfsimilarHeatGainKernel n k t u) := by
    have hK : Continuous (fun t : Ioi (0 : ℝ) ↦ vectorSelfsimilarHeatGainKernel n k t u) := by
      refine (continuousOn_vectorSelfsimilarHeatGainKernel_apply (n := n) (k := k)).comp_continuous
        (continuous_subtype_val.prodMk continuous_const) ?_
      intro t
      exact ⟨t.2, mem_univ _⟩
    exact (show Continuous fun t : Ioi (0 : ℝ) ↦ Real.sqrt t * Real.exp (-(ω * t)) by
      fun_prop).smul hK
  let T : VectorH n k →ₗ[ℝ] (Ioi (0 : ℝ) →ᵇ VectorH n (k + 1)) :=
    { toFun u := BoundedContinuousFunction.ofNormedAddCommGroup _ (hcont u)
        (singularSelfsimilarConstant n k ω * ‖u‖)
        (fun t ↦ norm_weighted_vectorSelfsimilarHeatGainKernel_le hω t.2 u)
      map_add' u v := by
        refine BoundedContinuousFunction.ext fun t ↦ ?_
        change (Real.sqrt t * Real.exp (-(ω * t))) •
            vectorSelfsimilarHeatGainKernel n k t (u + v) =
          (Real.sqrt t * Real.exp (-(ω * t))) • vectorSelfsimilarHeatGainKernel n k t u +
            (Real.sqrt t * Real.exp (-(ω * t))) • vectorSelfsimilarHeatGainKernel n k t v
        rw [map_add, smul_add]
      map_smul' a u := by
        refine BoundedContinuousFunction.ext fun t ↦ ?_
        change (Real.sqrt t * Real.exp (-(ω * t))) •
            vectorSelfsimilarHeatGainKernel n k t (a • u) =
          a • ((Real.sqrt t * Real.exp (-(ω * t))) • vectorSelfsimilarHeatGainKernel n k t u)
        rw [map_smul, smul_comm] }
  exact T.mkContinuous (singularSelfsimilarConstant n k ω) fun u ↦
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
      (mul_nonneg (singularSelfsimilarConstant_nonneg n k ω) (norm_nonneg u))
      (fun t ↦ norm_weighted_vectorSelfsimilarHeatGainKernel_le hω t.2 u)

theorem vectorSelfsimilarHeatGainPath_apply {ω : ℝ} (hω : ((2 : ℝ) - n) / 4 < ω)
    (u : VectorH n k) (t : Ioi (0 : ℝ)) :
    vectorSelfsimilarHeatGainPath n k ω hω u t =
      (Real.sqrt t * Real.exp (-(ω * t))) • vectorSelfsimilarHeatGainKernel n k t u :=
  rfl

theorem norm_vectorSelfsimilarHeatGainPath_apply_le {ω : ℝ} (hω : ((2 : ℝ) - n) / 4 < ω)
    (u : VectorH n k) :
    ‖vectorSelfsimilarHeatGainPath n k ω hω u‖ ≤ singularSelfsimilarConstant n k ω * ‖u‖ := by
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (singularSelfsimilarConstant_nonneg n k ω) (norm_nonneg u))).mpr fun t ↦ ?_
  rw [vectorSelfsimilarHeatGainPath_apply]
  exact norm_weighted_vectorSelfsimilarHeatGainKernel_le hω t.2 u

end HeatEquation.WholeSpace
