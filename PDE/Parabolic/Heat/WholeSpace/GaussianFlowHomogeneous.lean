/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.GaussianFlow
import PDE.Analysis.Calculus.Homogeneous
import PDE.Parabolic.Heat.Kernel.Integrability
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Heat flow of fields homogeneous of degree -1

Let `A : ℝ^n → E` be homogeneous of degree `0` and `C¹` away from the origin, and let
`u x = ‖x‖⁻¹ A x`. For `2 ≤ n ≤ 3` and a continuous compactly supported cutoff `χ` equal to one
near the origin, `G₁ * u - (1 - χ) u` lies in `L² ∩ L∞`.

Split `u = χ u + (1 - χ) u`. The near part `χ u` is integrable, since `‖x‖⁻¹` is locally
integrable for `n ≥ 2`, so its heat flow lies in every `Lʳ`. The far part `v = (1 - χ) u` is
bounded and `G₁ * v - v = ∫ G₁(y) (v(x - y) - v(x)) dy`. For `‖y‖ ≤ ‖x‖/2` homogeneity and the
mean value theorem on a ball around `x/‖x‖` give `‖v(x - y) - v(x)‖ ≤ L ‖y‖ ‖x‖⁻²`; for
`‖y‖ > ‖x‖/2` the bound `‖v(x - y) - v(x)‖ ≤ 2 sup ‖v‖` is absorbed by `1 < 4 ‖y‖² ‖x‖⁻²`. The
moments of `G₁` are finite, so `‖G₁ * v - v‖ ≤ C ‖x‖⁻²` for large `x`, which is square
integrable for `n < 4`.
-/

@[expose] public noncomputable section

open PDE (polynomialWeight)
open MeasureTheory Metric Set Filter SchwartzMap
open scoped ENNReal

namespace HeatEquation.WholeSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ^n → E}

/-- The field `‖x‖⁻¹ A x` is Lipschitz on the balls of radius `1/2` centred on the unit sphere,
with one constant. -/
theorem exists_lipschitz_norm_inv_smul (hA1 : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 A x) :
    ∃ L, 0 ≤ L ∧ ∀ ω : ℝ^n, ‖ω‖ = 1 → ∀ z ∈ closedBall ω (1 / 2),
      ‖‖z‖⁻¹ • A z - ‖ω‖⁻¹ • A ω‖ ≤ L * ‖z - ω‖ := by
  set u : ℝ^n → E := fun z ↦ ‖z‖⁻¹ • A z
  set K : Set (ℝ^n) := closedBall 0 (3 / 2) ∩ {z | 1 / 2 ≤ ‖z‖}
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hK0 : ∀ z ∈ K, z ≠ 0 := by
    rintro z ⟨_, hz⟩ rfl
    norm_num at hz
  have hu1 (z : ℝ^n) (hz : z ≠ 0) : ContDiffAt ℝ 1 u z := PDE.contDiffAt_inv_norm_smul hz (hA1 z hz)
  obtain ⟨L₀, hL₀⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ u) fun z hz ↦
    (((hu1 z (hK0 z hz)).fderiv_right (m := 0) (by simp)).continuousAt |>.continuousWithinAt)
  refine ⟨max L₀ 0, le_max_right _ _, fun ω hω z hz ↦ ?_⟩
  have hsub : closedBall ω (1 / 2) ⊆ K := fun w hw ↦ by
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_le_norm_add_norm_sub' w ω
    have h2 := norm_le_norm_add_norm_sub' ω w
    rw [norm_sub_rev] at h2
    exact ⟨by rw [mem_closedBall, dist_zero_right]; linarith, by change 1 / 2 ≤ ‖w‖; linarith⟩
  exact (convex_closedBall ω (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw ↦ (hu1 w (hK0 w (hsub hw))).differentiableAt one_ne_zero)
    (fun w hw ↦ (hL₀ w (hsub hw)).trans (le_max_left _ _))
    (mem_closedBall_self (by norm_num)) hz

/-- Away from the support of the cutoff the far part has the Lipschitz increment
`‖v(x - y) - v(x)‖ ≤ ‖x‖⁻² (L ‖y‖ + 8 B ‖y‖²)`, with `B` a bound for `v`. -/
theorem norm_far_sub_le (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) {L B R : ℝ}
    (hLip : ∀ ω : ℝ^n, ‖ω‖ = 1 → ∀ z ∈ closedBall ω (1 / 2),
      ‖‖z‖⁻¹ • A z - ‖ω‖⁻¹ • A ω‖ ≤ L * ‖z - ω‖)
    {v : ℝ^n → E} (hvB : ∀ x, ‖v x‖ ≤ B) (hvu : ∀ x, R < ‖x‖ → v x = ‖x‖⁻¹ • A x)
    {x : ℝ^n} (hx : 2 * (R + 1) ≤ ‖x‖) (hR : 0 ≤ R) (y : ℝ^n) :
    ‖v (x - y) - v x‖ ≤ ‖x‖⁻¹ ^ 2 * (L * ‖y‖ + 8 * B * ‖y‖ ^ 2) := by
  have hxpos : 0 < ‖x‖ := by linarith
  have hL : 0 ≤ L := by
    have hω : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
    have hd : ‖(5 / 4 : ℝ) • (‖x‖⁻¹ • x) - ‖x‖⁻¹ • x‖ = 1 / 4 := by
      rw [show (5 / 4 : ℝ) • (‖x‖⁻¹ • x) - ‖x‖⁻¹ • x = (1 / 4 : ℝ) • (‖x‖⁻¹ • x) by module,
        norm_smul, hω]
      norm_num
    have h := (norm_nonneg _).trans (hLip _ hω ((5 / 4 : ℝ) • (‖x‖⁻¹ • x))
      (by rw [mem_closedBall, dist_eq_norm, hd]; norm_num))
    rw [hd] at h
    linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans (hvB 0)
  by_cases hy : ‖y‖ ≤ ‖x‖ / 2
  · have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
    rw [hvu (x - y) (by linarith), hvu x (by linarith)]
    set ω : ℝ^n := ‖x‖⁻¹ • x with hωdef
    have hω : ‖ω‖ = 1 := by
      rw [hωdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
    have hxω : x = ‖x‖ • ω := by
      rw [hωdef, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    have hxyω : x - y = ‖x‖ • (ω - ‖x‖⁻¹ • y) := by
      rw [smul_sub, ← hxω, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    have hz : ω - ‖x‖⁻¹ • y ∈ closedBall ω (1 / 2) := by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, norm_inv,
        norm_norm, inv_mul_le_iff₀ hxpos]
      linarith
    have hd : ‖(ω - ‖x‖⁻¹ • y) - ω‖ = ‖x‖⁻¹ * ‖y‖ := by
      rw [sub_sub_cancel_left, norm_neg, norm_smul, norm_inv, norm_norm]
    have hlip := (hLip ω hω _ hz).trans_eq (by rw [hd])
    have hhom (z : ℝ^n) : ‖‖x‖ • z‖⁻¹ • A (‖x‖ • z) = ‖x‖⁻¹ • (‖z‖⁻¹ • A z) :=
      PDE.inv_norm_smul_apply_smul_of_homogeneous hA z hxpos
    calc
      _ = ‖‖x‖⁻¹ • (‖ω - ‖x‖⁻¹ • y‖⁻¹ • A (ω - ‖x‖⁻¹ • y) - ‖ω‖⁻¹ • A ω)‖ := by
        rw [smul_sub, ← hhom, ← hhom, ← hxyω, ← hxω]
      _ ≤ ‖x‖⁻¹ * (L * (‖x‖⁻¹ * ‖y‖)) := by
        rw [norm_smul, norm_inv, norm_norm]
        exact mul_le_mul_of_nonneg_left hlip (by positivity)
      _ = ‖x‖⁻¹ ^ 2 * (L * ‖y‖) := by ring
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · rw [not_le] at hy
    have hlarge : 1 ≤ 4 * ‖y‖ ^ 2 * ‖x‖⁻¹ ^ 2 := by
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      nlinarith
    calc
      _ ≤ ‖v (x - y)‖ + ‖v x‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hvB (x - y), hvB x]
      _ ≤ 2 * B * (4 * ‖y‖ ^ 2 * ‖x‖⁻¹ ^ 2) := le_mul_of_one_le_right (by positivity) hlarge
      _ ≤ _ := by
        have : 0 ≤ ‖x‖⁻¹ ^ 2 * (L * ‖y‖) := by positivity
        nlinarith

/-- The field `‖x‖⁻¹ A x` is integrable against the polynomial weight of order `n + 1`, for
`n ≥ 2`. -/
theorem integrable_polynomialWeight_smul_norm_inv_smul (hn : 2 ≤ n)
    (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) (hA1 : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 A x) :
    Integrable (fun y ↦ polynomialWeight (n + 1) y • (‖y‖⁻¹ • A y)) := by
  obtain ⟨M, hM, hu⟩ : ∃ M, 0 ≤ M ∧ ∀ x : ℝ^n, ‖‖x‖⁻¹ • A x‖ ≤ M * ‖x‖⁻¹ :=
    PDE.exists_norm_le_mul_inv_norm_of_homogeneous
      (fun x _ hc ↦ PDE.inv_norm_smul_apply_smul_of_homogeneous hA x hc)
      fun x hx ↦ (PDE.contDiffAt_inv_norm_smul hx (hA1 x hx)).continuousAt
  have hnt : Nontrivial (ℝ^n) := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hum : AEStronglyMeasurable (fun x : ℝ^n ↦ ‖x‖⁻¹ • A x) volume :=
    PDE.aestronglyMeasurable_of_continuousAt_of_ne (x₀ := 0) fun x hx ↦
      (PDE.contDiffAt_inv_norm_smul hx (hA1 x hx)).continuousAt
  have hwm := (PDE.continuous_polynomialWeight (n := n) (n + 1)).aestronglyMeasurable
    (μ := (volume : Measure (ℝ^n)))
  have hw1 : Integrable (polynomialWeight (n := n) (n + 1)) :=
    memLp_one_iff_integrable.mp (PDE.memLp_polynomialWeight le_rfl)
  have hwle (y : ℝ^n) : ‖polynomialWeight (n + 1) y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (PDE.polynomialWeight_pos _ y)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by simp))
  have huB : IntegrableOn (fun y ↦ ‖y‖⁻¹ • A y) (ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (α := 1) (C := M)
      (by rw [finrank_euclideanSpace_fin]; omega)
      (by rw [finrank_euclideanSpace_fin]; exact_mod_cast (by omega : 1 < n))
      (ae_of_all _ fun x ↦ ?_) hum
    rw [Real.rpow_neg_one]
    exact hu x
  rw [← integrableOn_univ, ← union_compl_self (ball (0 : ℝ^n) 1)]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' huB.norm (hwm.smul hum).restrict (ae_of_all _ fun y ↦ ?_)
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hwle y)
  · refine Integrable.mono' (hw1.const_mul M).integrableOn (hwm.smul hum).restrict
      (ae_restrict_of_forall_mem (measurableSet_ball.compl) fun y hy ↦ ?_)
    rw [mem_compl_iff, mem_ball, dist_zero_right, not_lt] at hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (PDE.polynomialWeight_pos _ y), mul_comm]
    refine mul_le_mul_of_nonneg_right ((hu y).trans ?_) (PDE.polynomialWeight_pos _ y).le
    exact mul_le_of_le_one_right hM (inv_le_one_of_one_le₀ hy)

/-- The time-one heat flow of `‖x‖⁻¹ A x` is smooth, for `n ≥ 2`. -/
theorem contDiff_gaussianFlow_one_norm_inv_smul (hn : 2 ≤ n)
    (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) (hA1 : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 A x) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianFlow 1 fun y ↦ ‖y‖⁻¹ • A y) :=
  contDiff_gaussianFlow_one (integrable_polynomialWeight_smul_norm_inv_smul hn hA hA1)

/-- The heat flow of a field homogeneous of degree `-1` is self-similar:
`(G_t * u)(x) = t^(-1/2) (G₁ * u)(x/√t)`. -/
theorem gaussianFlow_norm_inv_smul_eq (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) {t : ℝ}
    (ht : 0 < t) (x : ℝ^n) :
    gaussianFlow t (fun y ↦ ‖y‖⁻¹ • A y) x =
      (Real.sqrt t)⁻¹ • gaussianFlow 1 (fun y ↦ ‖y‖⁻¹ • A y) ((Real.sqrt t)⁻¹ • x) := by
  have hs := Real.sqrt_pos.mpr ht
  rw [gaussianFlow_eq_comp_smul ht]
  have hfun : (fun y ↦ ‖Real.sqrt t • y‖⁻¹ • A (Real.sqrt t • y)) =
      fun y ↦ (Real.sqrt t)⁻¹ • (‖y‖⁻¹ • A y) :=
    funext fun y ↦ PDE.inv_norm_smul_apply_smul_of_homogeneous hA y hs
  simp only [hfun, gaussianFlow_const_smul]
  rfl

/-- The heat flow at time one as `∫ G₁(y) • f (x - y) dy`. -/
theorem gaussianFlow_one_apply_eq (f : ℝ^n → E) (x : ℝ^n) :
    gaussianFlow 1 f x = ∫ y, fundamentalSolutionHeat y 1 • f (x - y) := by
  rw [gaussianFlow_apply one_pos]
  have h := integral_sub_left_eq_self (μ := (volume : Measure (ℝ^n)))
    (fun y ↦ fundamentalSolutionHeat (x - y) 1 • f y) x
  simp only [sub_sub_cancel] at h
  exact h.symm

/-- Bounded data have integrable heat integrands. -/
theorem integrable_heatKernel_smul_of_bound {v : ℝ^n → E} (hvm : AEStronglyMeasurable v volume)
    {B : ℝ} (hvB : ∀ x, ‖v x‖ ≤ B) (x : ℝ^n) :
    Integrable (fun y ↦ fundamentalSolutionHeat y 1 • v (x - y)) := by
  have hG := fundamentalSolutionHeat_integrable (n := n) 1 one_pos
  refine Integrable.mono' (hG.mul_const B) ?_ (Eventually.of_forall fun y ↦ ?_)
  · exact ((heatKernelSchwartz n).continuous.aestronglyMeasurable).smul
      (hvm.comp_measurePreserving (Measure.measurePreserving_sub_left volume x))
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (fundamentalSolutionHeat_pos _ _ one_pos)]
    exact mul_le_mul_of_nonneg_left (hvB _) (fundamentalSolutionHeat_pos _ _ one_pos).le

/-- The heat flow of bounded data is bounded by the same constant. -/
theorem norm_gaussianFlow_one_le_of_bound {v : ℝ^n → E} {B : ℝ} (hvB : ∀ x, ‖v x‖ ≤ B)
    (x : ℝ^n) : ‖gaussianFlow 1 v x‖ ≤ B := by
  rw [gaussianFlow_one_apply_eq]
  have hG := fundamentalSolutionHeat_integrable (n := n) 1 one_pos
  refine (norm_integral_le_of_norm_le (hG.mul_const B) (Eventually.of_forall fun y ↦ ?_)).trans
    (le_of_eq ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (fundamentalSolutionHeat_pos _ _ one_pos)]
    exact mul_le_mul_of_nonneg_left (hvB _) (fundamentalSolutionHeat_pos _ _ one_pos).le
  · rw [integral_mul_const, fundamentalSolutionHeat_integral 1 one_pos, one_mul]

/-- For bounded data, `G₁ * v - v` is the average of the increments of `v`. -/
theorem gaussianFlow_one_sub_self_eq [CompleteSpace E] {v : ℝ^n → E}
    (hvm : AEStronglyMeasurable v volume) {B : ℝ} (hvB : ∀ x, ‖v x‖ ≤ B) (x : ℝ^n) :
    gaussianFlow 1 v x - v x = ∫ y, fundamentalSolutionHeat y 1 • (v (x - y) - v x) := by
  have hG := fundamentalSolutionHeat_integrable (n := n) 1 one_pos
  simp_rw [smul_sub]
  rw [integral_sub (integrable_heatKernel_smul_of_bound hvm hvB x) (hG.smul_const (v x)),
    integral_smul_const, fundamentalSolutionHeat_integral 1 one_pos, one_smul,
    gaussianFlow_one_apply_eq]

/-- The far part satisfies `‖G₁ * v - v‖ ≤ C ‖x‖⁻²` at large `x`; the constant is
`L m₁ + 8 B m₂` with `mₖ` the moments of the heat kernel. -/
theorem exists_norm_gaussianFlow_one_far_sub_le [CompleteSpace E]
    (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) {L B R : ℝ}
    (hLip : ∀ ω : ℝ^n, ‖ω‖ = 1 → ∀ z ∈ closedBall ω (1 / 2),
      ‖‖z‖⁻¹ • A z - ‖ω‖⁻¹ • A ω‖ ≤ L * ‖z - ω‖)
    {v : ℝ^n → E} (hvm : AEStronglyMeasurable v volume) (hvB : ∀ x, ‖v x‖ ≤ B)
    (hvu : ∀ x, R < ‖x‖ → v x = ‖x‖⁻¹ • A x) (hR : 0 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ x : ℝ^n, 2 * (R + 1) ≤ ‖x‖ →
      ‖gaussianFlow 1 v x - v x‖ ≤ ‖x‖⁻¹ ^ 2 * C := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hvB 0)
  have hK (y : ℝ^n) : ‖heatKernelSchwartz n y‖ = fundamentalSolutionHeat y 1 := by
    rw [heatKernelSchwartz_apply, Real.norm_eq_abs,
      abs_of_pos (fundamentalSolutionHeat_pos _ _ one_pos)]
  have h1 := (heatKernelSchwartz n).integrable_pow_mul volume 1
  have h2 := (heatKernelSchwartz n).integrable_pow_mul volume 2
  set g₀ : ℝ^n → ℝ := fun y ↦
    L * (‖y‖ ^ 1 * ‖heatKernelSchwartz n y‖) + 8 * B * (‖y‖ ^ 2 * ‖heatKernelSchwartz n y‖)
  have hg₀ : Integrable g₀ := (h1.const_mul L).add (h2.const_mul (8 * B))
  refine ⟨max (∫ y, g₀ y) 0, le_max_right _ _, fun x hx ↦
    le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))⟩
  rw [gaussianFlow_one_sub_self_eq hvm hvB x, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg₀.const_mul (‖x‖⁻¹ ^ 2))
    (Eventually.of_forall fun y ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (fundamentalSolutionHeat_pos _ _ one_pos)]
  simp only [g₀, hK]
  calc
    _ ≤ fundamentalSolutionHeat y 1 * (‖x‖⁻¹ ^ 2 * (L * ‖y‖ + 8 * B * ‖y‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (norm_far_sub_le hA hLip hvB hvu hx hR y)
        (fundamentalSolutionHeat_pos _ _ one_pos).le
    _ = _ := by ring

/-- For a field `A` homogeneous of degree `0` and `C¹` away from the origin, and a continuous
compactly supported cutoff `χ` equal to one near the origin, the heat flow at time one of
`u x = ‖x‖⁻¹ A x` differs from `(1 - χ) u` by a field in `L² ∩ L∞`, in dimensions two and
three. -/
theorem memLp_gaussianFlow_one_sub_cutoff [CompleteSpace E] (hn : 2 ≤ n) (hn4 : n < 4)
    (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) (hA1 : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 A x)
    {χ : ℝ^n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hχ1 : ∀ x, ‖x‖ < r₀ → χ x = 1) :
    MemLp (fun x ↦ gaussianFlow 1 (fun y ↦ ‖y‖⁻¹ • A y) x - (1 - χ x) • (‖x‖⁻¹ • A x)) 2
        volume ∧
      MemLp (fun x ↦ gaussianFlow 1 (fun y ↦ ‖y‖⁻¹ • A y) x - (1 - χ x) • (‖x‖⁻¹ • A x)) ⊤
        volume := by
  set u : ℝ^n → E := fun y ↦ ‖y‖⁻¹ • A y with hudef
  obtain ⟨M, hM, hu⟩ : ∃ M, 0 ≤ M ∧ ∀ x : ℝ^n, ‖‖x‖⁻¹ • A x‖ ≤ M * ‖x‖⁻¹ :=
    PDE.exists_norm_le_mul_inv_norm_of_homogeneous
      (fun x _ hc ↦ PDE.inv_norm_smul_apply_smul_of_homogeneous hA x hc)
      fun x hx ↦ (PDE.contDiffAt_inv_norm_smul hx (hA1 x hx)).continuousAt
  obtain ⟨L, -, hLip⟩ := exists_lipschitz_norm_inv_smul hA1
  obtain ⟨Cχ₀, hCχ₀⟩ := hχ.bounded_above_of_compact_support hχc
  set Cχ := max Cχ₀ 0
  have hCχ (x : ℝ^n) : ‖χ x‖ ≤ Cχ := (hCχ₀ x).trans (le_max_left _ _)
  have hCχ0 : 0 ≤ Cχ := le_max_right _ _
  obtain ⟨R, hR, hsupp⟩ := hχc.isCompact.isBounded.subset_closedBall_lt 0 (0 : ℝ^n)
  have hχ0 (x : ℝ^n) (hx : R < ‖x‖) : χ x = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have := hsupp h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hnt : Nontrivial (ℝ^n) := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hum : AEStronglyMeasurable u volume :=
    PDE.aestronglyMeasurable_of_continuousAt_of_ne (x₀ := 0) fun x hx ↦
      (PDE.contDiffAt_inv_norm_smul hx (hA1 x hx)).continuousAt
  set w : ℝ^n → E := fun x ↦ χ x • u x with hwdef
  set v : ℝ^n → E := fun x ↦ (1 - χ x) • u x with hvdef
  have hwm : AEStronglyMeasurable w volume := hχ.aestronglyMeasurable.smul hum
  have hvm : AEStronglyMeasurable v volume :=
    (continuous_const.sub hχ).aestronglyMeasurable.smul hum
  have huR : IntegrableOn u (ball 0 (R + 1)) volume := by
    refine integrableOn_ball_of_norm_le_rpow (α := 1) (C := M)
      (by rw [finrank_euclideanSpace_fin]; omega)
      (by rw [finrank_euclideanSpace_fin]; exact_mod_cast (by omega : 1 < n))
      (ae_of_all _ fun x ↦ ?_) hum
    rw [Real.rpow_neg_one]
    exact hu x
  have hwint : Integrable w := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := ball 0 (R + 1))
      (Integrable.mono' (huR.norm.const_mul Cχ) hwm.restrict (ae_of_all _ fun x ↦ ?_))
      fun x hx ↦ ?_
    · rw [hwdef, norm_smul]
      exact mul_le_mul_of_nonneg_right (hCχ x) (norm_nonneg _)
    · rw [mem_ball, dist_zero_right, not_lt] at hx
      simp [hwdef, hχ0 x (by linarith)]
  have hwL1 : MemLp w 1 volume := memLp_one_iff_integrable.mpr hwint
  set B := (1 + Cχ) * M / r₀
  have hB : 0 ≤ B := by positivity
  have hvB (x : ℝ^n) : ‖v x‖ ≤ B := by
    by_cases hx : ‖x‖ < r₀
    · simp [hvdef, hχ1 x hx, hB]
    · rw [not_lt] at hx
      calc
        ‖v x‖ = ‖1 - χ x‖ * ‖u x‖ := norm_smul _ _
        _ ≤ (1 + Cχ) * (M * r₀⁻¹) := by
          gcongr
          · exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hCχ x])
          · exact (hu x).trans (by gcongr)
        _ = B := by ring
  have hvL : MemLp v ⊤ volume := memLp_top_of_bound hvm B (ae_of_all _ hvB)
  have hvu (x : ℝ^n) (hx : R < ‖x‖) : v x = ‖x‖⁻¹ • A x := by
    simp [hvdef, hudef, hχ0 x hx]
  have hw' := PDE.integrable_polynomialWeight_smul_of_memLp le_rfl hwL1
  have hv' := PDE.integrable_polynomialWeight_smul_of_memLp le_top hvL
  have huwv : u = w + v := by
    funext x
    simp only [hwdef, hvdef, Pi.add_apply, ← add_smul, add_sub_cancel, one_smul]
  have hu' : Integrable (fun y ↦ polynomialWeight (n + 1) y • u y) := by
    rw [huwv]
    refine (hw'.add hv').congr (Eventually.of_forall fun y ↦ ?_)
    simp [smul_add]
  have hsplit : gaussianFlow 1 v = gaussianFlow 1 u - gaussianFlow 1 w := by
    rw [← gaussianFlow_one_sub hu' hw']
    congr 1
    rw [huwv, add_sub_cancel_left]
  have hF : (fun x ↦ gaussianFlow 1 u x - (1 - χ x) • u x) =
      gaussianFlow 1 w + fun x ↦ gaussianFlow 1 v x - v x := by
    funext x
    rw [hsplit]
    simp only [Pi.add_apply, Pi.sub_apply, hvdef]
    abel
  have hGw2 := memLp_gaussianFlow one_pos le_rfl (by norm_num : (1 : ℝ≥0∞) ≤ 2) hwL1
  have hGwT := memLp_gaussianFlow one_pos le_rfl le_top hwL1
  have hF2m : AEStronglyMeasurable (fun x ↦ gaussianFlow 1 v x - v x) volume :=
    (contDiff_gaussianFlow_one hv').continuous.aestronglyMeasurable.sub hvm
  have hF2B (x : ℝ^n) : ‖gaussianFlow 1 v x - v x‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [norm_gaussianFlow_one_le_of_bound hvB x, hvB x])
  obtain ⟨C₀, hC₀, hfar⟩ := exists_norm_gaussianFlow_one_far_sub_le hA hLip hvm hvB hvu hR.le
  set R₁ := 2 * (R + 1)
  set K' := 4 * C₀ + 2 * B * (1 + R₁) ^ 2 with hK'
  have hdom (x : ℝ^n) : ‖gaussianFlow 1 v x - v x‖ ≤
      ‖K' * polynomialWeight 2 x‖ := by
    have hw := PDE.polynomialWeight_pos (n := n) 2 x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hw,
      abs_of_nonneg (by positivity)]
    simp only [polynomialWeight] at hw ⊢
    by_cases hx : R₁ ≤ ‖x‖
    · have hxpos : 1 ≤ ‖x‖ := by linarith
      refine (hfar x hx).trans ?_
      have hsq : ‖x‖⁻¹ ^ 2 ≤ 4 * ((1 + ‖x‖) ^ 2)⁻¹ := by
        rw [inv_pow, ← one_div, ← one_div, mul_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hB2 : 0 ≤ 2 * B * (1 + R₁) ^ 2 := by positivity
      calc
        _ ≤ 4 * ((1 + ‖x‖) ^ 2)⁻¹ * C₀ := mul_le_mul_of_nonneg_right hsq hC₀
        _ ≤ _ := by rw [hK']; nlinarith [mul_nonneg hB2 hw.le]
    · rw [not_le] at hx
      have hle : (1 + ‖x‖) ^ 2 ≤ (1 + R₁) ^ 2 := by gcongr
      have hone : 1 ≤ (1 + R₁) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, one_le_div₀ (by positivity)]
        exact hle
      calc
        _ ≤ 2 * B := hF2B x
        _ ≤ 2 * B * ((1 + R₁) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹) :=
          le_mul_of_one_le_right (by positivity) hone
        _ ≤ _ := by rw [hK']; nlinarith [mul_nonneg hC₀ hw.le]
  have hF2two : MemLp (fun x ↦ gaussianFlow 1 v x - v x) 2 volume :=
    ((PDE.memLp_polynomialWeight_of_lt (n := n) (N := 2) one_le_two
      ENNReal.ofNat_ne_top (by norm_num; exact_mod_cast hn4)).const_mul K').of_le hF2m
      (ae_of_all _ hdom)
  have hF2top : MemLp (fun x ↦ gaussianFlow 1 v x - v x) ⊤ volume :=
    memLp_top_of_bound hF2m (2 * B) (ae_of_all _ hF2B)
  change MemLp (fun x ↦ gaussianFlow 1 u x - (1 - χ x) • u x) 2 volume ∧
    MemLp (fun x ↦ gaussianFlow 1 u x - (1 - χ x) • u x) ⊤ volume
  rw [hF]
  exact ⟨hGw2.add hF2two, hGwT.add hF2top⟩

end HeatEquation.WholeSpace
