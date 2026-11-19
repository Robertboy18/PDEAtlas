/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PDE.Analysis.Approximation.EndpointFlattening
import PDE.FDeriv.Calculus
import PDE.FDeriv.Euclidean.Laplacian
import PDE.Analysis.Calculus.SmoothTransitionDerivatives

/-!
# Integration by parts on a ball against fields with vanishing normal component

Let `B` be the ball of radius `R` about the origin in `ℝ^n` and let `v` have integrable weak
derivatives on `B`, with no boundary condition. For a smooth matrix field `T` whose normal
component `∑ⱼ Tᵢⱼ(x) xⱼ` vanishes on the sphere `‖x‖ = R`,

`∫_B ∑ᵢⱼ (vᵢ ∂ⱼTᵢⱼ + ∂ⱼvᵢ Tᵢⱼ) = 0`.

The weak derivatives of `v` are tested against `χ T`, where `χ` is a radial cutoff equal to one
away from a thin collar of the sphere. The gradient of `χ` is a multiple of `x`, so the collar
term only involves the normal component `T x`. A `C¹` function vanishing on the sphere is
bounded by a constant times `R² - ‖x‖²` (`exists_abs_le_mul_sq_sub_norm_sq`), so this term is of
the order of the collar width, which balances the size of `∇χ`. Dominated convergence removes the
cutoff, and no trace theorem is needed.

## Main results

* `exists_abs_le_mul_sq_sub_norm_sq`: a `C¹` function vanishing on the sphere of radius `R` is
  bounded by a constant times `R² - ‖x‖²` inside the ball.
* `integral_sum_mul_partialDeriv_add_mul_eq_zero`: the integration by parts identity.
-/

@[expose] public noncomputable section

open MeasureTheory
open PDE (partialDeriv)
open Filter Metric Set Topology PDE.Analysis.Calculus
open scoped ContDiff Distributions NNReal

namespace PDE.Analysis

variable {n : ℕ}

/-- A `C¹` function that vanishes on the sphere of radius `R` is bounded on the punctured
closed ball by a constant times `R² - ‖x‖²`. -/
theorem exists_abs_le_mul_sq_sub_norm_sq {R : ℝ} (hR : 0 < R) {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ 1 f) (hzero : ∀ x : ℝ^n, ‖x‖ = R → f x = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ^n, x ≠ 0 → ‖x‖ ≤ R → |f x| ≤ L * (R ^ 2 - ‖x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ^n) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max C 0 / R, by positivity, fun x hx0 hxR ↦ ?_⟩
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set y : ℝ^n := (R / ‖x‖) • x with hy
  have hyR : ‖y‖ = R := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hnx), div_mul_cancel₀ _ hnx.ne']
  have hxy : ‖y - x‖ = R - ‖x‖ := by
    have hge : 0 ≤ R / ‖x‖ - 1 := sub_nonneg.2 ((one_le_div hnx).2 hxR)
    rw [hy, show (R / ‖x‖) • x - x = (R / ‖x‖ - 1) • x by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hge, sub_mul, div_mul_cancel₀ _ hnx.ne', one_mul]
  have hmvt := (convex_closedBall (0 : ℝ^n) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (hf.differentiable one_ne_zero).differentiableAt)
    (fun z hz ↦ (hC z hz).trans (le_max_left C 0))
    (mem_closedBall_zero_iff.2 hxR) (mem_closedBall_zero_iff.2 hyR.le)
  rw [hzero y hyR, zero_sub, norm_neg, Real.norm_eq_abs, hxy] at hmvt
  rw [div_mul_eq_mul_div, le_div_iff₀ hR]
  have h₁ : (R - ‖x‖) * R ≤ R ^ 2 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  calc |f x| * R ≤ max C 0 * (R - ‖x‖) * R := mul_le_mul_of_nonneg_right hmvt hR.le
    _ ≤ max C 0 * (R ^ 2 - ‖x‖ ^ 2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h₁ (le_max_right C 0)

/-- The radial cutoff `x ↦ endpointCutoff (R²) ε (‖x‖²)`. It equals one where
`‖x‖² ≤ R² - 2ε` and vanishes where `‖x‖² ≥ R² - ε`. -/
private def shellCutoff (R ε : ℝ) (x : ℝ^n) : ℝ :=
  endpointCutoff (R ^ 2) ε (‖x‖ ^ 2)

/-- The radial factor of the gradient of `shellCutoff`. -/
private def shellSlope (R ε : ℝ) (x : ℝ^n) : ℝ :=
  2 * deriv (endpointCutoff (R ^ 2) ε) (‖x‖ ^ 2)

/-- The radial cutoff is smooth. -/
private theorem contDiff_shellCutoff (R ε : ℝ) : ContDiff ℝ ∞ (shellCutoff (n := n) R ε) :=
  (contDiff_endpointCutoff _ _).comp (contDiff_norm_sq ℝ)

/-- The gradient of the radial cutoff is `shellSlope R ε x • x`. -/
private theorem partialDeriv_shellCutoff (R ε : ℝ) (j : Fin n) (x : ℝ^n) :
    ∂[j] (shellCutoff R ε) x = shellSlope R ε x * x j := by
  have h := partialDeriv_comp_real j (u := fun y : ℝ^n ↦ ‖y‖ ^ 2)
    ((contDiff_endpointCutoff (R ^ 2) ε (n := 1)).differentiable one_ne_zero (‖x‖ ^ 2))
    ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero x)
  rw [EuclideanLaplacian.partialDeriv_norm_sq] at h
  rw [shellSlope]
  exact h.trans (by ring)

/-- The closed support of the radial cutoff lies in the open ball. -/
private theorem tsupport_shellCutoff_subset {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    tsupport (shellCutoff (n := n) R ε) ⊆ ball 0 R := by
  have hsub : Function.support (shellCutoff (n := n) R ε) ⊆ {x | ‖x‖ ^ 2 ≤ R ^ 2 - ε} := by
    intro x hx
    by_contra h
    simp only [Set.mem_ofPred_eq, not_le] at h
    exact hx (endpointCutoff_eq_zero hε h.le)
  refine (closure_minimal hsub (isClosed_le (continuous_norm.pow 2) continuous_const)).trans
    fun x (hx : ‖x‖ ^ 2 ≤ R ^ 2 - ε) ↦ mem_ball_zero_iff.2 ?_
  nlinarith [norm_nonneg x]

/-- The radial cutoff equals one away from the collar. -/
private theorem shellCutoff_eq_one {R ε : ℝ} (hε : 0 < ε) {x : ℝ^n}
    (hx : ‖x‖ ^ 2 ≤ R ^ 2 - 2 * ε) : shellCutoff R ε x = 1 :=
  endpointCutoff_eq_one hε hx

/-- The gradient factor vanishes strictly away from the collar. -/
private theorem shellSlope_eq_zero {R ε : ℝ} (hε : 0 < ε) {x : ℝ^n}
    (hx : ‖x‖ ^ 2 < R ^ 2 - 2 * ε) : shellSlope R ε x = 0 := by
  have h : endpointCutoff (R ^ 2) ε =ᶠ[𝓝 (‖x‖ ^ 2)] fun _ ↦ 1 :=
    (eventually_lt_nhds hx).mono fun t ht ↦ endpointCutoff_eq_one hε ht.le
  rw [shellSlope, h.deriv_eq, deriv_const, mul_zero]

/-- The radial cutoff takes values in `[0, 1]`. -/
private theorem abs_shellCutoff_le_one (R ε : ℝ) (x : ℝ^n) : |shellCutoff R ε x| ≤ 1 :=
  abs_le.2 ⟨(neg_nonpos.2 zero_le_one).trans (endpointCutoff_nonneg (R ^ 2) ε (‖x‖ ^ 2)),
    endpointCutoff_le_one (R ^ 2) ε (‖x‖ ^ 2)⟩

/-- The gradient factor is of size `ε⁻¹`. -/
private theorem abs_shellSlope_le {K : ℝ≥0} (hK : LipschitzWith K Real.smoothTransition)
    {R ε : ℝ} (hε : 0 < ε) (x : ℝ^n) : |shellSlope R ε x| ≤ 2 * K / ε := by
  rw [shellSlope, abs_mul, abs_two, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (abs_deriv_endpointCutoff_le hK hε) zero_le_two

/-- The first-order weak derivative identity tested against a smooth compactly supported
function with closed support in `Ω`, together with integrability of both pairings. -/
private theorem weak_pairing {Ω : Set (ℝ^n)} {j : Fin n} {f g φ : ℝ^n → ℝ}
    (h : SobolevSpace.HasWeakDerivativeOn Ω [j] f g) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x ↦ f x * ∂[j] φ x + g x * φ x) (volume.restrict Ω) ∧
      ∫ x in Ω, (f x * ∂[j] φ x + g x * φ x) = 0 := by
  let ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.mk φ hφ hc (Set.subset_univ _)
  have h₁ : Integrable (fun x ↦ f x * ∂[j] φ x) (volume.restrict Ω) :=
    h.integrable_mul_iteratedPartialDeriv ψ hs
  have h₂ : Integrable (fun x ↦ g x * φ x) (volume.restrict Ω) :=
    h.integrable_mul_testFunction ψ hs
  refine ⟨h₁.add h₂, ?_⟩
  have h₃ := h.integral_identity ψ hs
  change ∫ x in Ω, f x * ∂[j] φ x = (-1) ^ 1 * ∫ x in Ω, g x * φ x at h₃
  rw [integral_add h₁ h₂, h₃]
  ring

/-- Integration by parts on a ball against a smooth matrix field with vanishing normal
component. Let `v` have weak derivatives `Dv i j = ∂ⱼ vᵢ` on the ball `B` of radius `R`, with
`v` and `Dv` integrable on `B`. If `T` is a smooth matrix field with `∑ⱼ Tᵢⱼ(x) xⱼ = 0` on the
sphere `‖x‖ = R`, then `∫_B ∑ᵢⱼ (vᵢ ∂ⱼTᵢⱼ + ∂ⱼvᵢ Tᵢⱼ) = 0`. -/
theorem integral_sum_mul_partialDeriv_add_mul_eq_zero {R : ℝ} (hR : 0 < R)
    {T : Fin n → Fin n → ℝ^n → ℝ} (hT : ∀ i j, ContDiff ℝ ∞ (T i j))
    (hTn : ∀ x : ℝ^n, ‖x‖ = R → ∀ i, ∑ j, T i j x * x j = 0)
    {v : Fin n → ℝ^n → ℝ} {Dv : Fin n → Fin n → ℝ^n → ℝ}
    (hv : ∀ i, IntegrableOn (v i) (ball (0 : ℝ^n) R))
    (hDv : ∀ i j, IntegrableOn (Dv i j) (ball (0 : ℝ^n) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (ball (0 : ℝ^n) R) [j] (v i) (Dv i j)) :
    ∫ x in ball (0 : ℝ^n) R, ∑ i, ∑ j, (v i x * ∂[j] (T i j) x + Dv i j x * T i j x) = 0 := by
  set B := ball (0 : ℝ^n) R
  set G : ℝ^n → ℝ := fun x ↦ ∑ i, ∑ j, (v i x * ∂[j] (T i j) x + Dv i j x * T i j x) with hG
  obtain ⟨K, hK⟩ := exists_lipschitzWith_smoothTransition
  -- The normal component `wᵢ = ∑ⱼ Tᵢⱼ xⱼ` decays linearly at the sphere.
  have hw : ∀ i, ContDiff ℝ 1 (fun x : ℝ^n ↦ ∑ j, T i j x * x j) := fun i ↦
    ContDiff.sum fun j _ ↦ (contDiff_infty.1 (hT i j) 1).mul (contDiff_piLp_apply 2)
  choose L hL0 hL using fun i ↦
    exists_abs_le_mul_sq_sub_norm_sq hR (hw i) fun x hx ↦ hTn x hx i
  choose C₁ hC₁ using fun i j ↦ (isCompact_closedBall (0 : ℝ^n) R).exists_bound_of_continuousOn
    (contDiff_top_partialDeriv (i := j) (hT i j)).continuous.continuousOn
  choose C₂ hC₂ using fun i j ↦ (isCompact_closedBall (0 : ℝ^n) R).exists_bound_of_continuousOn
    (hT i j).continuous.continuousOn
  obtain ⟨ε, hε, hε0⟩ : ∃ ε : ℕ → ℝ, (∀ m, 0 < ε m) ∧ Tendsto ε atTop (𝓝 0) :=
    ⟨fun m ↦ 1 / ((m : ℝ) + 1), fun m ↦ Nat.one_div_pos_of_nat,
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
  -- The tested identities for the cutoff fields `χₘ Tᵢⱼ`.
  have hsupp : ∀ m i j, tsupport (fun y ↦ shellCutoff R (ε m) y * T i j y) ⊆ B :=
    fun m i j ↦ tsupport_mul_subset_left.trans (tsupport_shellCutoff_subset hR (hε m))
  have hpair : ∀ m i j,
      Integrable (fun x ↦ v i x * ∂[j] (fun y ↦ shellCutoff R (ε m) y * T i j y) x +
        Dv i j x * (shellCutoff R (ε m) x * T i j x)) (volume.restrict B) ∧
      ∫ x in B, (v i x * ∂[j] (fun y ↦ shellCutoff R (ε m) y * T i j y) x +
        Dv i j x * (shellCutoff R (ε m) x * T i j x)) = 0 := fun m i j ↦
    weak_pairing (hweak i j) ((contDiff_shellCutoff R (ε m)).mul (hT i j))
      ((isCompact_closedBall (0 : ℝ^n) R).of_isClosed_subset (isClosed_tsupport _)
        ((hsupp m i j).trans ball_subset_closedBall)) (hsupp m i j)
  set F : ℕ → ℝ^n → ℝ := fun m x ↦ ∑ i, ∑ j,
    (v i x * ∂[j] (fun y ↦ shellCutoff R (ε m) y * T i j y) x +
      Dv i j x * (shellCutoff R (ε m) x * T i j x)) with hF
  have hF_int : ∀ m, Integrable (F m) (volume.restrict B) := fun m ↦
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hpair m i j).1
  have hF0 : ∀ m, ∫ x in B, F m x = 0 := fun m ↦ by
    simp only [hF]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hpair m i j).1]
    exact Finset.sum_eq_zero fun i _ ↦ (integral_finsetSum _ fun j _ ↦ (hpair m i j).1).trans
      (Finset.sum_eq_zero fun j _ ↦ (hpair m i j).2)
  -- The integrand splits into the collar term and the cutoff of `G`.
  have hformula : ∀ m x, F m x =
      ∑ i, v i x * (shellSlope R (ε m) x * ∑ j, T i j x * x j) + G x * shellCutoff R (ε m) x := by
    intro m x
    have hd : ∀ i j, ∂[j] (fun y ↦ shellCutoff R (ε m) y * T i j y) x =
        shellSlope R (ε m) x * x j * T i j x + shellCutoff R (ε m) x * ∂[j] (T i j) x := by
      intro i j
      rw [partialDeriv_mul ((contDiff_shellCutoff R (ε m)).differentiable (by simp) x)
        ((hT i j).differentiable (by simp) x), partialDeriv_shellCutoff]
    simp only [hF, hG, hd, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- The collar term is bounded uniformly in `m`.
  have hslope : ∀ m i, ∀ x ∈ B,
      |shellSlope R (ε m) x * ∑ j, T i j x * x j| ≤ 4 * K * L i := by
    intro m i x hx
    have hxR : ‖x‖ < R := mem_ball_zero_iff.1 hx
    have h4 : 0 ≤ 4 * (K : ℝ) * L i := mul_nonneg (by positivity) (hL0 i)
    by_cases hx0 : x = 0
    · simpa [hx0] using h4
    by_cases hfar : ‖x‖ ^ 2 < R ^ 2 - 2 * ε m
    · rwa [shellSlope_eq_zero (hε m) hfar, zero_mul, abs_zero]
    -- in the collar `R² - ‖x‖² ≤ 2 ε`, so `|χ'| |T x| ≤ (2K/ε) L (2ε)`
    replace hfar := not_lt.1 hfar
    rw [abs_mul]
    refine (mul_le_mul (abs_shellSlope_le hK (hε m) x)
      ((hL i x hx0 hxR.le).trans (mul_le_mul_of_nonneg_left
        (by linarith : R ^ 2 - ‖x‖ ^ 2 ≤ 2 * ε m) (hL0 i)))
      (abs_nonneg _) (div_nonneg (by positivity) (hε m).le)).trans_eq ?_
    field_simp [(hε m).ne']
    ring
  -- Dominated convergence.
  have hbound_int : Integrable (fun x ↦ ∑ i, 4 * K * L i * |v i x| +
      ∑ i, ∑ j, (C₁ i j * |v i x| + C₂ i j * |Dv i j x|)) (volume.restrict B) :=
    (integrable_finsetSum _ fun i _ ↦ (hv i).integrable.abs.const_mul _).add
      (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
        ((hv i).integrable.abs.const_mul _).add ((hDv i j).integrable.abs.const_mul _))
  have h_bound : ∀ m, ∀ᵐ x ∂(volume.restrict B), ‖F m x‖ ≤ ∑ i, 4 * K * L i * |v i x| +
      ∑ i, ∑ j, (C₁ i j * |v i x| + C₂ i j * |Dv i j x|) := by
    intro m
    refine ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦ ?_
    have hxc : x ∈ closedBall (0 : ℝ^n) R := ball_subset_closedBall hx
    have hmul {a b C : ℝ} (h : ‖a‖ ≤ C) : |b * a| ≤ C * |b| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    rw [hformula, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ ↦ hmul (hslope m i x hx))
    · rw [abs_mul]
      refine (mul_le_of_le_one_right (abs_nonneg _) (abs_shellCutoff_le_one _ _ _)).trans ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      exact (abs_add_le _ _).trans (add_le_add (hmul (hC₁ i j x hxc)) (hmul (hC₂ i j x hxc)))
  have h_lim : ∀ᵐ x ∂(volume.restrict B), Tendsto (fun m ↦ F m x) atTop (𝓝 (G x)) := by
    refine ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦ ?_
    have hxR : ‖x‖ < R := mem_ball_zero_iff.1 hx
    have hgap : 0 < (R ^ 2 - ‖x‖ ^ 2) / 2 := by nlinarith [norm_nonneg x]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hε0.eventually (gt_mem_nhds hgap)] with m hm
    have hfar : ‖x‖ ^ 2 < R ^ 2 - 2 * ε m := by linarith
    rw [hformula, shellSlope_eq_zero (hε m) hfar, shellCutoff_eq_one (hε m) hfar.le]
    simp
  have htend := tendsto_integral_of_dominated_convergence _
    (fun m ↦ (hF_int m).aestronglyMeasurable) hbound_int h_bound h_lim
  simp only [hF0] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

end PDE.Analysis
