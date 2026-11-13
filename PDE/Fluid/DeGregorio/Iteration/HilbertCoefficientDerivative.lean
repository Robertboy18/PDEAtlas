/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.HilbertCoefficient
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.SecondOrder
import CAS.ExactTactic

/-!
# Spatial regularity of the Hilbert coefficient on the bounded H² class

Extracting the first derivative from the weak H² graph gives an H¹ graph
with the same norm bound. Its Hilbert output is the continuous weak
derivative of the original Hilbert coefficient. The fundamental theorem of
calculus makes this a pointwise derivative. A uniform square-root modulus
then recovers joint continuity from spatial difference quotients.

The input curve is continuous in time for the L² topology.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology ENNReal

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem exists_hilbert_derivative_of_hkBaseBall
    {g : DerivLp 1 2 univ} {B : NNReal} (hg : g ∈ hkBaseBall 1 2 univ B)
    {c : ℝ → ℝ} (hc : Continuous c)
    (hpair : IsHilbertPair (oneDimensionalPushforwardL2 g) c) :
    ∃ d : ℝ → ℝ, Continuous d ∧
      (∀ x, HasDerivAt c (d x) x) ∧
      (∀ x, ‖d x‖ ≤ 2 * (B : ℝ)) ∧
      (∀ x y, |d y - d x| ≤ (B : ℝ) * Real.sqrt |y - x|) := by
  obtain ⟨V, _, hbase, hderiv, hcderiv⟩ :=
    exists_hilbert_derivative_h1_of_hkBaseBall hg hc hpair
  have hcont := continuous_realLineRepresentative V
  have hweak := hasWeakTimeDerivativeOn_realLineRepresentative V
  refine ⟨realLineRepresentative V, hcont, hcderiv, ?_, ?_⟩
  · intro x
    have h := hweak.norm_apply_le_eLpNorm_toReal_add hcont
      (by norm_num : (1 : ℝ≥0∞) < 2) (memLp_realLineRepresentative V)
      (Lp.memLp (realLineCoordinateCLM (singleDerivIndex 1 0) V)) x
    rw [← eLpNorm_congr_ae (realLineCoordinate_ae_representative V),
      ← Lp.norm_def, ← Lp.norm_def] at h
    calc
      _ ≤ _ := h
      _ ≤ (B : ℝ) + B := add_le_add hbase hderiv
      _ = 2 * (B : ℝ) := by cas
  · intro x y
    have h := hweak.enorm_sub_le_eLpNorm_mul_rpow hcont
      (by norm_num : (1 : ℝ≥0∞) < 2) x y
    have hpow : SobolevSpace.morreyExponent 1 2 = (1 / 2 : ℝ) := by
      norm_num [SobolevSpace.morreyExponent]
    rw [hpow] at h
    have hfinite : eLpNorm (realLineCoordinateCLM (singleDerivIndex 1 0) V) 2 volume *
        ENNReal.ofReal |y - x| ^ (1 / 2 : ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) (ENNReal.rpow_ne_top_of_nonneg
        (by norm_num) ENNReal.ofReal_ne_top)
    have hreal := ENNReal.toReal_mono hfinite h
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
    simp only [toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_ofReal (abs_nonneg _),
      ← Real.sqrt_eq_rpow, ← Lp.norm_def] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_right hderiv (Real.sqrt_nonneg _))

private theorem abs_slope_sub_le_sqrt
    {c d : ℝ → ℝ} {B : NNReal} (hd : Continuous d)
    (hc : ∀ x, HasDerivAt c (d x) x)
    (hosc : ∀ x y, |d y - d x| ≤ (B : ℝ) * Real.sqrt |y - x|)
    (x r : ℝ) (hr : 0 < r) :
    |r⁻¹ * (c (x + r) - c x) - d x| ≤ (B : ℝ) * Real.sqrt r := by
  have hbound : ‖∫ s in x..x + r, d s - d x‖ ≤ (B : ℝ) * Real.sqrt r * r := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := x + r) (C := (B : ℝ) * Real.sqrt r)
      (f := fun s ↦ d s - d x) (fun s hs ↦ ?_)
    · simpa only [add_sub_cancel_left, abs_of_pos hr] using h
    · rw [uIoc_of_le (le_add_of_nonneg_right hr.le)] at hs
      have hsr : |s - x| ≤ r := by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
        linarith [hs.2]
      exact (hosc x s).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsr) B.coe_nonneg)
  have hid : r⁻¹ * (c (x + r) - c x) - d x =
      r⁻¹ * (∫ s in x..x + r, d s - d x) := by
    rw [intervalIntegral.integral_sub (hd.intervalIntegrable _ _) intervalIntegrable_const]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hc s)
      (hd.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
    cas using hr.ne'
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hr)]
  calc
    r⁻¹ * |∫ s in x..x + r, d s - d x| ≤ r⁻¹ * ((B : ℝ) * Real.sqrt r * r) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hr.le)
    _ = (B : ℝ) * Real.sqrt r := by
      rw [mul_comm ((B : ℝ) * Real.sqrt r) r, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- Every jointly continuous Hilbert coefficient of a bounded H²
input curve has a jointly continuous spatial derivative, uniformly bounded
by `2 B` with square-root spatial modulus `B`. -/
theorem exists_hkCurve_hilbert_coefficient_hasDerivAt
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry c))
    (hpair : ∀ t, IsHilbertPair (oneDimensionalPushforwardL2 (f (projIcc 0 T hT t)).val)
      (fun x ↦ c x t)) :
    ∃ d : ℝ → ℝ → ℝ, Continuous (Function.uncurry d) ∧
      (∀ x t, HasDerivAt (fun y ↦ c y t) (d x t) x) ∧
      (∀ x t, ‖d x t‖ ≤ 2 * (B : ℝ)) ∧
      (∀ x y t, |d y t - d x t| ≤ (B : ℝ) * Real.sqrt |y - x|) := by
  have hex (t : ℝ) := exists_hilbert_derivative_of_hkBaseBall
    (f (projIcc 0 T hT t)).property.1
    (hc.comp (continuous_id.prodMk continuous_const)) (hpair t)
  choose D hD hDderiv hDbound hDosc using hex
  let d : ℝ → ℝ → ℝ := fun x t ↦ D t x
  let r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  let Q (n : ℕ) (p : ℝ × ℝ) : ℝ := (r n)⁻¹ * (c (p.1 + r n) p.2 - c p.1 p.2)
  have hQ (n : ℕ) : Continuous (Q n) :=
    continuous_const.mul
      ((hc.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub hc)
  have hQbound (n : ℕ) (p : ℝ × ℝ) :
      dist (d p.1 p.2) (Q n p) ≤ (B : ℝ) * Real.sqrt (r n) := by
    rw [dist_comm, Real.dist_eq]
    exact abs_slope_sub_le_sqrt (hD p.2) (hDderiv p.2) (hDosc p.2) p.1 (r n) (hr n)
  have hsmall : Tendsto (fun n ↦ (B : ℝ) * Real.sqrt (r n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt.const_mul (B : ℝ)
  have hlim : TendstoUniformly Q (Function.uncurry d) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with n hn
    intro p
    exact (hQbound n p).trans_lt hn
  exact ⟨d, hlim.continuous (.of_forall hQ), fun x t ↦ hDderiv t x,
    fun x t ↦ hDbound t x, fun x y t ↦ hDosc t x y⟩

end DeGregorio.Iteration
