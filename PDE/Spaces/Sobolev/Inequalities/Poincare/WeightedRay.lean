/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.WeightedRay.Basic

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import PDE.Spaces.Sobolev.Weighted.InterpolationRecursion
import PDE.FDeriv.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import CAS.ExactTactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Integrability criteria for weighted ray inequalities

Quartic decay, inverse-distance budgets, and finite core moments establish
the integrability needed by weighted ray inequalities. The measurable-
representative forms retain the same bases and explicit ray reconstruction.
A local gradient bound pays for the core kernel when derivative weights
are bounded near the origin.

Throughout, `H₊ = {x : ℝ² | 0 ≤ x₀}` is the closed right half-plane.
-/

@[expose] public section

noncomputable section

open PDE.Common (coordinateClosedHalfSpace measurableSet_coordinateClosedHalfSpace
  smul_mem_coordinateClosedHalfSpace_iff)

local notation "H₊" => coordinateClosedHalfSpace (0 : Fin 2)

open PDE.FDeriv

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology

namespace SobolevSpace.Weighted

/-- The decay bound at the origin forces its constant to be nonnegative. -/
private theorem nonneg_of_decay {W : ℝ^2 → ℝ} {A : ℝ} (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hdecay : ∀ x ∈ H₊, W x ≤ A / (1 + ‖x‖) ^ 4) : 0 ≤ A := by
  have h0 : (0 : ℝ^2) ∈ H₊ := by simp [coordinateClosedHalfSpace]
  simpa using (hW 0 h0).trans (hdecay 0 h0)

/-- Fourth-power decay of a coefficient weight gives an inverse-distance ray budget.
The integral is taken before comparing weights, so its singularity is `1 / ‖y‖`,
which is locally integrable in the two-dimensional profile plane. -/
private theorem coefficient_ray_integrable_and_integral_le
    (W : (ℝ^2 → ℝ)) (A : ℝ) (hWmeas : Measurable W)
    (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hdecay : ∀ x ∈ H₊, W x ≤ A / (1 + ‖x‖) ^ 4)
    (y : (ℝ^2)) (hy : y ∈ H₊) (hy0 : y ≠ (0 : (ℝ^2))) :
    IntervalIntegrable (fun t : ℝ ↦ (t ^ 4)⁻¹ * W (t⁻¹ • y)) volume 0 1 ∧
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) ≤
        A / (3 * ‖y‖) := by
  have hA : 0 ≤ A := nonneg_of_decay hW hdecay
  let d := ‖y‖
  have hd : 0 < d := norm_pos_iff.mpr hy0
  have hmajorant : IntervalIntegrable (fun t : ℝ ↦ A / (t + d) ^ 4) volume 0 1 :=
    (continuousOn_const.div (by fun_prop) fun t ht ↦
      (pow_pos (add_pos_of_nonneg_of_pos ht.1 hd) 4).ne').intervalIntegrable_of_Icc zero_le_one
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      (t ^ 4)⁻¹ * W (t⁻¹ • y) ≤ A / (t + d) ^ 4 := by
    have hty : t⁻¹ • y ∈ H₊ :=
      (smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) (inv_pos.mpr ht.1) y).2 hy
    have hnorm : ‖t⁻¹ • y‖ = t⁻¹ * d := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.1.le)]
    calc
      (t ^ 4)⁻¹ * W (t⁻¹ • y) ≤
          (t ^ 4)⁻¹ * (A / (1 + ‖t⁻¹ • y‖) ^ 4) :=
        mul_le_mul_of_nonneg_left (hdecay _ hty) (inv_nonneg.mpr (pow_nonneg ht.1.le 4))
      _ = A / (t + d) ^ 4 := by
        rw [hnorm]
        have htne : t ≠ 0 := ne_of_gt ht.1
        have htd : t + d ≠ 0 := ne_of_gt (add_pos ht.1 hd)
        have hden : 1 + t⁻¹ * d ≠ 0 :=
          ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
            (mul_nonneg (inv_nonneg.mpr ht.1.le) hd.le))
        cas [htne, htd, hden]
  have hkernel : IntervalIntegrable
      (fun t : ℝ ↦ (t ^ 4)⁻¹ * W (t⁻¹ • y)) volume 0 1 := by
    refine hmajorant.mono_fun' (((measurable_id.pow_const 4).inv.mul
      (hWmeas.comp (measurable_id.inv.smul_const y))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.1.le 4))
      (hW _ ((smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) (inv_pos.mpr ht.1) y).2 hy)))]
    exact hpoint t ht
  have hcompare :
      (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) ≤
        ∫ t in (0 : ℝ)..1, A / (t + d) ^ 4 := by
    apply intervalIntegral.integral_mono_on (by norm_num) hkernel hmajorant
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simpa using div_nonneg hA (pow_nonneg hd.le 4)
    · exact hpoint t ⟨ht0, ht.2⟩
  have hzero : (0 : ℝ) ∉ Set.uIcc d (1 + d) := by
    rw [Set.uIcc_of_le (by linarith : d ≤ 1 + d)]
    exact fun h ↦ hd.not_ge h.1
  have hexact : (∫ t in (0 : ℝ)..1, A / (t + d) ^ 4) =
      A / 3 * (d⁻¹ ^ 3 - (1 + d)⁻¹ ^ 3) := by
    calc
      _ = A * ∫ t in (0 : ℝ)..1, (t + d) ^ (-4 : ℤ) := by
        simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv, intervalIntegral.integral_const_mul]
      _ = A * ∫ t in d..(1 + d), t ^ (-4 : ℤ) := by
        simpa only [zero_add] using
          congrArg (fun q : ℝ ↦ A * q)
            (intervalIntegral.integral_comp_add_right
              (f := fun t : ℝ ↦ t ^ (-4 : ℤ)) (a := 0) (b := 1) d)
      _ = _ := by
        rw [integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
        norm_num only [Int.reduceAdd, Int.cast_neg, Int.cast_ofNat, zpow_neg, zpow_ofNat]
        simp only [← inv_pow]
        cas
  refine ⟨hkernel, ?_⟩
  calc
    ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) ≤
        d ^ 2 * (A / 3 * (d⁻¹ ^ 3 - (1 + d)⁻¹ ^ 3)) := by
      exact mul_le_mul_of_nonneg_left (hcompare.trans_eq hexact) (sq_nonneg d)
    _ ≤ d ^ 2 * (A / 3 * d⁻¹ ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg d)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hA (by norm_num))
      exact sub_le_self _ (pow_nonneg (inv_nonneg.mpr (by linarith)) 3)
    _ = A / (3 * ‖y‖) := by
      change d ^ 2 * (A / 3 * d⁻¹ ^ 3) = A / (3 * d)
      cas using ne_of_gt hd

/-- Finite weighted gradient energy and a finite ray budget make both change-of-variables
kernels integrable. First integrate the nonnegative outward-ray kernel in time;
positive spatial dilation then transfers its integrability to the original kernel. -/
private theorem ray_work_integrable_of_weighted_energy
    (u W Φr Φz : (ℝ^2 → ℝ)) (CP : ℝ) (hu : ContDiff ℝ 1 u)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hCP : 0 ≤ CP)
    (hkernel : ∀ y ∈ H₊, y ≠ (0 : (ℝ^2)) →
      IntervalIntegrable (fun t : ℝ ↦ (t ^ 4)⁻¹ * W (t⁻¹ • y)) volume 0 1)
    (hweight : ∀ y ∈ H₊,
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) ≤
        CP * min (Φr y) (Φz y))
    (hr : Integrable (fun x ↦ ((∂[0] u) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz : Integrable (fun x ↦ ((∂[1] u) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    Integrable
        (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
          (((∂[0] u) (p.1 • p.2)) ^ 2 +
            ((∂[1] u) (p.1 • p.2)) ^ 2) * W p.2)
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
          (volume.restrict H₊)) ∧
      Integrable
        (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ *
          (‖p.2‖ ^ 2 * (((∂[0] u) p.2) ^ 2 +
            ((∂[1] u) p.2) ^ 2) * W (p.1⁻¹ • p.2)))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
          (volume.restrict H₊)) := by
  let μt : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let μx : Measure (ℝ^2) := volume.restrict H₊
  let G : (ℝ^2 → ℝ) := fun y ↦ ((∂[0] u) y) ^ 2 + ((∂[1] u) y) ^ 2
  let K : ℝ × (ℝ^2) → ℝ := fun p ↦ ‖p.2‖ ^ 2 * G (p.1 • p.2) * W p.2
  let J : ℝ × (ℝ^2) → ℝ := fun p ↦
    (p.1 ^ 4)⁻¹ * (‖p.2‖ ^ 2 * G p.2 * W (p.1⁻¹ • p.2))
  have hG : Continuous G :=
    ((PDE.contDiff_partialDeriv_of_succ (m := 0) hu).continuous.pow 2).add
      ((PDE.contDiff_partialDeriv_of_succ (m := 0) hu).continuous.pow 2)
  have hGnonneg (y : (ℝ^2)) : 0 ≤ G y := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hJmeas : Measurable J :=
    (measurable_fst.pow_const 4).inv.mul
      (((measurable_snd.norm.pow_const 2).mul (hG.measurable.comp measurable_snd)).mul
        (hWmeas.comp (measurable_fst.inv.smul measurable_snd)))
  have hKmeas : Measurable K :=
    ((measurable_snd.norm.pow_const 2).mul
      (hG.measurable.comp (measurable_fst.smul measurable_snd))).mul
        (hWmeas.comp measurable_snd)
  have hJnonneg (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1)
      (y : (ℝ^2)) (hy : y ∈ H₊) : 0 ≤ J (t, y) :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.1.le 4))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (hGnonneg y))
        (hW _ ((smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) (inv_pos.mpr ht.1) y).2 hy)))
  have hKnonneg (t : ℝ) (x : (ℝ^2)) (hx : x ∈ H₊) :
      0 ≤ K (t, x) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (hGnonneg _)) (hW x hx)
  have hJfiber (y : (ℝ^2)) (hy : y ∈ H₊) :
      Integrable (fun t ↦ J (t, y)) μt := by
    by_cases hy0 : y = (0 : (ℝ^2))
    · subst y
      simpa only [J, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        zero_mul, mul_zero] using
        ((integrable_const_iff (μ := μt) (c := (0 : ℝ))).2 (Or.inl rfl))
    · have hi := (hkernel y hy hy0).1.const_mul (‖y‖ ^ 2 * G y)
      apply hi.congr
      filter_upwards [] with t
      dsimp only [J]
      cas
  have hJinner (y : (ℝ^2)) (hy : y ∈ H₊) :
      (∫ t, J (t, y) ∂μt) ≤
        CP * (((∂[0] u) y) ^ 2 * Φr y + ((∂[1] u) y) ^ 2 * Φz y) := by
    calc
      _ = G y * (‖y‖ ^ 2 * ∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) := by
        rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul,
          ← integral_const_mul]
        exact integral_congr_ae (.of_forall fun t ↦ by dsimp only [J]; ring)
      _ ≤ G y * (CP * min (Φr y) (Φz y)) :=
        mul_le_mul_of_nonneg_left (hweight y hy) (hGnonneg y)
      _ = CP * (((∂[0] u) y) ^ 2 * min (Φr y) (Φz y) +
          ((∂[1] u) y) ^ 2 * min (Φr y) (Φz y)) := by
        dsimp only [G]
        ring
      _ ≤ _ := by gcongr; exacts [min_le_left _ _, min_le_right _ _]
  have hJnorm (y : (ℝ^2)) (hy : y ∈ H₊) :
      (∫ t, ‖J (t, y)‖ ∂μt) = ∫ t, J (t, y) ∂μt :=
    integral_congr_ae <| (ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦
      Real.norm_of_nonneg (hJnonneg t ht y hy)
  have hJ : Integrable J (μt.prod μx) := by
    apply (integrable_prod_iff' hJmeas.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
        with y hy
      exact hJfiber y hy
    · apply ((hr.add hz).const_mul CP).mono'
        hJmeas.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      filter_upwards [ae_restrict_mem (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
        with y hy
      rw [Real.norm_of_nonneg (integral_nonneg (fun t ↦ norm_nonneg _)), hJnorm y hy]
      exact hJinner y hy
  have hdilate (f : (ℝ^2 → ℝ)) {t : ℝ} (ht : 0 < t) (hf : Integrable f μx) :
      Integrable (fun x ↦ f (t • x)) μx := by
    have hc := ((integrable_indicator_iff
      (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))).2 hf).comp_smul ht.ne'
    have hpre : (fun x : ℝ^2 ↦ t • x) ⁻¹' H₊ = H₊ :=
      Set.ext (smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) ht)
    have heq : (fun x : ℝ^2 ↦ H₊.indicator f (t • x)) = H₊.indicator (fun x ↦ f (t • x)) := by
      funext x
      rw [← Set.indicator_comp_right (fun x : ℝ^2 ↦ t • x), hpre]
      rfl
    rw [heq] at hc
    exact (integrable_indicator_iff (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))).1 hc
  have hK : Integrable K (μt.prod μx) := by
    apply (integrable_prod_iff hKmeas.aestronglyMeasurable).2
    constructor
    · filter_upwards [hJ.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with t htJ ht
      have heq : (fun x ↦ K (t, x)) = fun x ↦ t ^ 2 * J (t, t • x) := by
        funext x
        dsimp only [K, J]
        simp only [norm_smul, Real.norm_of_nonneg ht.1.le, smul_smul,
          inv_mul_cancel₀ ht.1.ne', one_smul, mul_pow]
        cas using ht.1.ne'
      rw [heq]
      exact (hdilate _ ht.1 htJ).const_mul _
    · apply hJ.integral_norm_prod_left.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hH := ae_restrict_mem (μ := volume) (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))
      rw [integral_congr_ae (hH.mono fun y hy ↦ Real.norm_of_nonneg (hJnonneg t ht y hy)),
        integral_congr_ae (hH.mono fun x hx ↦ Real.norm_of_nonneg (hKnonneg t x hx))]
      exact (weightedPoincare_scaled_gradient_slice u W ht.1).symm
  exact ⟨hK, hJ⟩

/-- The ray majorant supplies integrability of the coefficient-weighted square.
Thus the weighted Poincaré estimate does not require integrability of its left side as input. -/
private theorem integrable_square_of_ray
    (u W : (ℝ^2 → ℝ)) (hu : ContDiff ℝ 1 u) (hu0 : u (0 : (ℝ^2)) = 0)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hK : Integrable
      (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
        (((∂[0] u) (p.1 • p.2)) ^ 2 +
          ((∂[1] u) (p.1 • p.2)) ^ 2) * W p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊))) :
    Integrable (fun x ↦ u x ^ 2 * W x)
      (volume.restrict H₊) := by
  refine hK.integral_prod_right.mono'
    ((hu.continuous.aestronglyMeasurable.pow 2).mul hWmeas.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hW x hx)), integral_mul_const,
    integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
  exact mul_le_mul_of_nonneg_right
    (sq_profile_le_norm_sq_integral_partialDeriv_sq_along_ray hu hu0 x) (hW x hx)

/-- A fourth-power bound on the solution weight and an inverse-distance budget against
the derivative weights give weighted Poincaré from finite derivative energy alone.
The normalization at the origin supplies the ray formula. Nonnegative ray kernels,
followed by positive dilation, prove the product integrability needed to exchange
the two integrals and also prove integrability of the weighted solution square.

The budget is required only away from the origin. In particular, a positive `A`
can require singular derivative weights there; their values at the single origin
do not affect the integrals. -/
theorem integrable_and_weightedPoincare_squared_halfPlane_of_decay
    (u W Φr Φz : (ℝ^2 → ℝ)) (A CP : ℝ)
    (hu : ContDiff ℝ 1 u) (hu0 : u (0 : (ℝ^2)) = 0)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hΦr : ∀ x ∈ H₊, 0 ≤ Φr x)
    (hΦz : ∀ x ∈ H₊, 0 ≤ Φz x)
    (hCP : 0 ≤ CP)
    (hdecay : ∀ x ∈ H₊, W x ≤ A / (1 + ‖x‖) ^ 4)
    (hbudget : ∀ y ∈ H₊, y ≠ (0 : (ℝ^2)) →
      A ≤ 3 * CP * ‖y‖ * min (Φr y) (Φz y))
    (hr : Integrable (fun x ↦ ((∂[0] u) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz : Integrable (fun x ↦ ((∂[1] u) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    Integrable (fun x ↦ u x ^ 2 * W x) (volume.restrict H₊) ∧
      (∫ x in H₊, u x ^ 2 * W x) ≤
        CP * ((∫ x in H₊, ((∂[0] u) x) ^ 2 * Φr x) +
          ∫ x in H₊, ((∂[1] u) x) ^ 2 * Φz x) := by
  have hweight (y : ℝ^2) (hy : y ∈ H₊) :
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) ≤ CP * min (Φr y) (Φz y) := by
    by_cases hy0 : y = (0 : (ℝ^2))
    · subst y
      simpa using mul_nonneg hCP (le_min (hΦr (0 : (ℝ^2)) hy) (hΦz (0 : (ℝ^2)) hy))
    refine (coefficient_ray_integrable_and_integral_le W A hWmeas hW hdecay
      y hy hy0).2.trans ?_
    rw [div_le_iff₀ (mul_pos (by norm_num) (norm_pos_iff.mpr hy0))]
    exact (hbudget y hy hy0).trans_eq (by ring)
  obtain ⟨hK, hJ⟩ := ray_work_integrable_of_weighted_energy u W Φr Φz CP hu hWmeas hW hCP
    (fun y hy hy0 ↦ (coefficient_ray_integrable_and_integral_le W A hWmeas hW hdecay
      y hy hy0).1) hweight hr hz
  have hi := integrable_square_of_ray u W hu hu0 hWmeas hW hK
  exact ⟨hi, weightedPoincare_squared_halfPlane hu hu0 hW hCP hweight hi hK hJ hr hz⟩

/-- Squared weighted Poincaré for arbitrary derivative representatives once
the Sobolev ray estimate, multiplied by the possibly vanishing solution
weight, is known almost everywhere.  This is the exact pointwise input used
by the weighted ray argument: an unweighted ray estimate would be
unnecessarily strong where `Φu = 0`.  The theorem contains the full weighted
Fubini and dilation argument and has no classical differentiability
assumption.
-/
theorem weightedPoincare_squared_representatives_of_ae_weighted_ray_bound
    {f gr gz : (ℝ^2 → ℝ)} {Φu Φr Φz : (ℝ^2 → ℝ)} {CP : ℝ}
    (hCP : 0 ≤ CP)
    (hweight : ∀ y ∈ H₊,
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * Φu (t⁻¹ • y)) ≤
        CP * min (Φr y) (Φz y))
    (hf_int : Integrable (fun x ↦ f x ^ 2 * Φu x)
      (volume.restrict H₊))
    (hK : Integrable
      (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
        (gr (p.1 • p.2) ^ 2 + gz (p.1 • p.2) ^ 2) * Φu p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hJ : Integrable
      (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ *
        (‖p.2‖ ^ 2 * (gr p.2 ^ 2 + gz p.2 ^ 2) *
          Φu (p.1⁻¹ • p.2)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hr_int : Integrable (fun x ↦ gr x ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz_int : Integrable (fun x ↦ gz x ^ 2 * Φz x)
      (volume.restrict H₊))
    (hRay : ∀ᵐ x ∂(volume.restrict H₊),
      f x ^ 2 * Φu x ≤
        (‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1,
          gr (t • x) ^ 2 + gz (t • x) ^ 2) * Φu x) :
    (∫ x in H₊, f x ^ 2 * Φu x) ≤
      CP * ((∫ x in H₊, gr x ^ 2 * Φr x) +
        ∫ x in H₊, gz x ^ 2 * Φz x) := by
  calc (∫ x in H₊, f x ^ 2 * Φu x)
      ≤ ∫ x in H₊, ∫ t in Set.Ioc (0 : ℝ) 1,
          ‖x‖ ^ 2 * (gr (t • x) ^ 2 + gz (t • x) ^ 2) * Φu x := by
        refine integral_mono_ae hf_int hK.integral_prod_right ?_
        filter_upwards [hRay] with x hx
        rwa [integral_mul_const, integral_const_mul,
          ← intervalIntegral.integral_of_le zero_le_one]
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ x in H₊,
          ‖x‖ ^ 2 * (gr (t • x) ^ 2 + gz (t • x) ^ 2) * Φu x :=
        (integral_integral_swap hK).symm
    -- dilating each time slice by `t⁻¹`
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ y in H₊,
          (t ^ 4)⁻¹ * (‖y‖ ^ 2 * (gr y ^ 2 + gz y ^ 2) * Φu (t⁻¹ • y)) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
        rw [integral_coordinateClosedHalfSpace_norm_sq_comp_smul
          (fun y ↦ gr y ^ 2 + gz y ^ 2) Φu ht.1, integral_const_mul]
    _ = ∫ y in H₊, ∫ t in Set.Ioc (0 : ℝ) 1,
          (t ^ 4)⁻¹ * (‖y‖ ^ 2 * (gr y ^ 2 + gz y ^ 2) * Φu (t⁻¹ • y)) :=
        integral_integral_swap hJ
    _ ≤ ∫ y in H₊, CP * (gr y ^ 2 * Φr y + gz y ^ 2 * Φz y) := by
        refine integral_mono_ae hJ.integral_prod_right ((hr_int.add hz_int).const_mul CP) ?_
        filter_upwards [ae_restrict_mem (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
          with y hy
        calc
          _ = (gr y ^ 2 + gz y ^ 2) *
              (‖y‖ ^ 2 * ∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * Φu (t⁻¹ • y)) := by
            rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul,
              ← integral_const_mul]
            congr 1 with t
            ring
          _ ≤ (gr y ^ 2 + gz y ^ 2) * (CP * min (Φr y) (Φz y)) :=
            mul_le_mul_of_nonneg_left (hweight y hy) (by positivity)
          _ = CP * (gr y ^ 2 * min (Φr y) (Φz y) + gz y ^ 2 * min (Φr y) (Φz y)) := by ring
          _ ≤ _ := by gcongr; exacts [min_le_left _ _, min_le_right _ _]
    _ = _ := by rw [integral_const_mul, integral_add hr_int hz_int]

/-- The more familiar unweighted almost-everywhere ray estimate implies the
exact weighted pointwise input above whenever the solution weight is
nonnegative. -/
theorem weightedPoincare_squared_representatives_of_ae_ray_bound
    {f gr gz : (ℝ^2 → ℝ)} {Φu Φr Φz : (ℝ^2 → ℝ)} {CP : ℝ}
    (hΦu : ∀ x ∈ H₊, 0 ≤ Φu x)
    (hCP : 0 ≤ CP)
    (hweight : ∀ y ∈ H₊,
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * Φu (t⁻¹ • y)) ≤
        CP * min (Φr y) (Φz y))
    (hf_int : Integrable (fun x ↦ f x ^ 2 * Φu x)
      (volume.restrict H₊))
    (hK : Integrable
      (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
        (gr (p.1 • p.2) ^ 2 + gz (p.1 • p.2) ^ 2) * Φu p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hJ : Integrable
      (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ *
        (‖p.2‖ ^ 2 * (gr p.2 ^ 2 + gz p.2 ^ 2) *
          Φu (p.1⁻¹ • p.2)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hr_int : Integrable (fun x ↦ gr x ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz_int : Integrable (fun x ↦ gz x ^ 2 * Φz x)
      (volume.restrict H₊))
    (hRay : ∀ᵐ x ∂(volume.restrict H₊),
      f x ^ 2 ≤ ‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1,
        gr (t • x) ^ 2 + gz (t • x) ^ 2) :
    (∫ x in H₊, f x ^ 2 * Φu x) ≤
      CP * ((∫ x in H₊, gr x ^ 2 * Φr x) +
        ∫ x in H₊, gz x ^ 2 * Φz x) := by
  apply weightedPoincare_squared_representatives_of_ae_weighted_ray_bound
    hCP hweight hf_int hK hJ hr_int hz_int
  filter_upwards [hRay, ae_restrict_mem (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
    with x hx hmem
  exact mul_le_mul_of_nonneg_right hx (hΦu x hmem)

/-- Square-root conversion for the two-component weighted Poincaré energy. -/
theorem weightedPoincare_sqrt_of_integral_bound
    {U R Z CP : ℝ} (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hbound : U ≤ CP * (R + Z)) :
    Real.sqrt U ≤ Real.sqrt CP * (Real.sqrt R + Real.sqrt Z) := by
  rcases lt_or_ge CP 0 with hCP | hCP
  · have hU : U ≤ 0 := by nlinarith
    rw [Real.sqrt_eq_zero_of_nonpos hCP.le, zero_mul, Real.sqrt_eq_zero_of_nonpos hU]
  calc
    Real.sqrt U ≤ Real.sqrt (CP * (R + Z)) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt CP * Real.sqrt (R + Z) := by rw [Real.sqrt_mul hCP]
    _ ≤ Real.sqrt CP * (Real.sqrt R + Real.sqrt Z) :=
      mul_le_mul_of_nonneg_left
        (SobolevSpace.Weighted.sqrt_add_le_add_sqrt hR hZ) (Real.sqrt_nonneg CP)

/-- Square-root weighted Poincaré for arbitrary weak derivative
representatives, reduced to the exact weighted almost-everywhere radial
estimate. -/
theorem weightedPoincare_representatives_of_ae_weighted_ray_bound
    {f gr gz : (ℝ^2 → ℝ)} {Φu Φr Φz : (ℝ^2 → ℝ)} {CP : ℝ}
    (hΦr : ∀ x ∈ H₊, 0 ≤ Φr x)
    (hΦz : ∀ x ∈ H₊, 0 ≤ Φz x)
    (hCP : 0 ≤ CP)
    (hweight : ∀ y ∈ H₊,
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * Φu (t⁻¹ • y)) ≤
        CP * min (Φr y) (Φz y))
    (hf_int : Integrable (fun x ↦ f x ^ 2 * Φu x)
      (volume.restrict H₊))
    (hK : Integrable
      (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
        (gr (p.1 • p.2) ^ 2 + gz (p.1 • p.2) ^ 2) * Φu p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hJ : Integrable
      (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ *
        (‖p.2‖ ^ 2 * (gr p.2 ^ 2 + gz p.2 ^ 2) *
          Φu (p.1⁻¹ • p.2)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hr_int : Integrable (fun x ↦ gr x ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz_int : Integrable (fun x ↦ gz x ^ 2 * Φz x)
      (volume.restrict H₊))
    (hRay : ∀ᵐ x ∂(volume.restrict H₊),
      f x ^ 2 * Φu x ≤
        (‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1,
          gr (t • x) ^ 2 + gz (t • x) ^ 2) * Φu x) :
    Real.sqrt (∫ x in H₊, f x ^ 2 * Φu x) ≤
      Real.sqrt CP *
        (Real.sqrt (∫ x in H₊, gr x ^ 2 * Φr x) +
          Real.sqrt (∫ x in H₊, gz x ^ 2 * Φz x)) := by
  have hsq := weightedPoincare_squared_representatives_of_ae_weighted_ray_bound
    hCP hweight hf_int hK hJ hr_int hz_int hRay
  have hr_nonneg : 0 ≤ ∫ x in H₊, gr x ^ 2 * Φr x :=
    setIntegral_nonneg (measurableSet_coordinateClosedHalfSpace (0 : Fin 2)) fun x hx ↦
      mul_nonneg (sq_nonneg _) (hΦr x hx)
  have hz_nonneg : 0 ≤ ∫ x in H₊, gz x ^ 2 * Φz x :=
    setIntegral_nonneg (measurableSet_coordinateClosedHalfSpace (0 : Fin 2)) fun x hx ↦
      mul_nonneg (sq_nonneg _) (hΦz x hx)
  exact weightedPoincare_sqrt_of_integral_bound hr_nonneg hz_nonneg hsq

/--
Weighted Poincaré estimate in square-root form,
for smooth profiles satisfying the explicit Fubini hypotheses.
-/
theorem weightedPoincare_halfPlane
    {f : (ℝ^2 → ℝ)} {Φu Φr Φz : (ℝ^2 → ℝ)} {CP : ℝ}
    (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0)
    (hΦu : ∀ x ∈ H₊, 0 ≤ Φu x)
    (hΦr : ∀ x ∈ H₊, 0 ≤ Φr x)
    (hΦz : ∀ x ∈ H₊, 0 ≤ Φz x)
    (hCP : 0 ≤ CP)
    (hweight : ∀ y ∈ H₊,
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * Φu (t⁻¹ • y)) ≤
        CP * min (Φr y) (Φz y))
    (hf_int : Integrable (fun x ↦ f x ^ 2 * Φu x)
      (volume.restrict H₊))
    (hK : Integrable
      (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
        (((∂[0] f) (p.1 • p.2)) ^ 2 +
          ((∂[1] f) (p.1 • p.2)) ^ 2) * Φu p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hJ : Integrable
      (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ *
        (‖p.2‖ ^ 2 *
          (((∂[0] f) p.2) ^ 2 +
            ((∂[1] f) p.2) ^ 2) * Φu (p.1⁻¹ • p.2)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hr_int : Integrable
      (fun x ↦ ((∂[0] f) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz_int : Integrable
      (fun x ↦ ((∂[1] f) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    Real.sqrt (∫ x in H₊, f x ^ 2 * Φu x) ≤
      Real.sqrt CP *
        (Real.sqrt (∫ x in H₊,
            ((∂[0] f) x) ^ 2 * Φr x) +
          Real.sqrt (∫ x in H₊,
            ((∂[1] f) x) ^ 2 * Φz x)) := by
  have hsq := weightedPoincare_squared_halfPlane
    hf hf0 hΦu hCP hweight hf_int hK hJ hr_int hz_int
  have hr_nonneg : 0 ≤ ∫ x in H₊, ((∂[0] f) x) ^ 2 * Φr x :=
    setIntegral_nonneg (measurableSet_coordinateClosedHalfSpace (0 : Fin 2)) fun x hx ↦
      mul_nonneg (sq_nonneg _) (hΦr x hx)
  have hz_nonneg : 0 ≤ ∫ x in H₊, ((∂[1] f) x) ^ 2 * Φz x :=
    setIntegral_nonneg (measurableSet_coordinateClosedHalfSpace (0 : Fin 2)) fun x hx ↦
      mul_nonneg (sq_nonneg _) (hΦz x hx)
  exact weightedPoincare_sqrt_of_integral_bound hr_nonneg hz_nonneg hsq

/-- Weighted Poincaré from a checkable outward-decay certificate for the
velocity weight.  The function `rayMajorant` bounds the singular ray integral
because `PhiU (t⁻¹ • y) ≤ rayMajorant y * t⁴`; the separate budget hypothesis
then compares that explicit majorant with the derivative weights.

Unlike a direct assumption of the ray-integral inequality, these hypotheses
split the analytic obligation into pointwise decay and finite algebraic weight
comparison, both suitable for interval certification.  No decay condition is
needed on the zero ray because its prefactor `‖y‖²` vanishes. -/
theorem weightedPoincare_halfPlane_of_quartic_ray_decay
    {f : (ℝ^2 → ℝ)} {PhiU PhiR PhiZ : (ℝ^2 → ℝ)} {CP : ℝ}
    (rayMajorant : (ℝ^2) → ℝ)
    (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0)
    (hPhiU_meas : Measurable PhiU)
    (hPhiU : ∀ x ∈ H₊, 0 ≤ PhiU x)
    (hPhiR : ∀ x ∈ H₊, 0 ≤ PhiR x)
    (hPhiZ : ∀ x ∈ H₊, 0 ≤ PhiZ x)
    (hCP : 0 ≤ CP)
    (hmajorant_nonneg : ∀ y ∈ H₊,
      y ≠ (0 : (ℝ^2)) → 0 ≤ rayMajorant y)
    (hdecay : ∀ y ∈ H₊, y ≠ (0 : (ℝ^2)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        PhiU (t⁻¹ • y) ≤ rayMajorant y * t ^ 4)
    (hbudget : ∀ y ∈ H₊, y ≠ (0 : (ℝ^2)) →
      ‖y‖ ^ 2 * rayMajorant y ≤ CP * min (PhiR y) (PhiZ y))
    (hf_int : Integrable (fun x ↦ f x ^ 2 * PhiU x)
      (volume.restrict H₊))
    (hK : Integrable
      (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
        (((∂[0] f) (p.1 • p.2)) ^ 2 +
          ((∂[1] f) (p.1 • p.2)) ^ 2) * PhiU p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hJ : Integrable
      (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ *
        (‖p.2‖ ^ 2 *
          (((∂[0] f) p.2) ^ 2 +
            ((∂[1] f) p.2) ^ 2) * PhiU (p.1⁻¹ • p.2)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hr_int : Integrable
      (fun x ↦ ((∂[0] f) x) ^ 2 * PhiR x)
      (volume.restrict H₊))
    (hz_int : Integrable
      (fun x ↦ ((∂[1] f) x) ^ 2 * PhiZ x)
      (volume.restrict H₊)) :
    Real.sqrt (∫ x in H₊, f x ^ 2 * PhiU x) ≤
      Real.sqrt CP *
        (Real.sqrt (∫ x in H₊,
            ((∂[0] f) x) ^ 2 * PhiR x) +
          Real.sqrt (∫ x in H₊,
            ((∂[1] f) x) ^ 2 * PhiZ x)) := by
  apply weightedPoincare_halfPlane hf hf0 hPhiU hPhiR hPhiZ hCP
    (hf_int := hf_int) (hK := hK) (hJ := hJ) (hr_int := hr_int)
    (hz_int := hz_int)
  intro y hy
  by_cases hy0 : y = (0 : (ℝ^2))
  · subst y
    have hmin : 0 ≤ min (PhiR (0 : (ℝ^2))) (PhiZ (0 : (ℝ^2))) :=
      le_min (hPhiR (0 : (ℝ^2)) hy) (hPhiZ (0 : (ℝ^2)) hy)
    simpa using mul_nonneg hCP hmin
  · have hray := weightedPoincare_ray_integral_le_of_quartic_decay
      PhiU hPhiU_meas hPhiU y hy (rayMajorant y)
        (hmajorant_nonneg y hy hy0) (hdecay y hy hy0)
    exact (mul_le_mul_of_nonneg_left hray (sq_nonneg ‖y‖)).trans
      (hbudget y hy hy0)


/-- The exact coefficient kernel produced by Cauchy–Schwarz and two-dimensional
ray dilation. Its use in an estimate also requires integrability of the time slices. -/
def weightedPoincareRayKernel (W : (ℝ^2 → ℝ)) (y : (ℝ^2)) : ℝ :=
  ‖y‖ ^ 2 * ∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)

/-- The prefactor annihilates the zero ray. -/
@[simp] theorem weightedPoincareRayKernel_zero (W : (ℝ^2 → ℝ)) :
    weightedPoincareRayKernel W (0 : (ℝ^2)) = 0 := by
  simp [weightedPoincareRayKernel]

/-- The total real ray kernel is measurable whenever its coefficient is measurable. -/
theorem measurable_weightedPoincareRayKernel
    {W : (ℝ^2 → ℝ)} (hW : Measurable W) : Measurable (weightedPoincareRayKernel W) := by
  have hm : Measurable (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ * W (p.1⁻¹ • p.2)) :=
    (measurable_fst.pow_const 4).inv.mul
      (hW.comp (measurable_fst.inv.smul measurable_snd))
  have hi : Measurable (fun y : (ℝ^2) ↦
      ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  change Measurable (fun y : (ℝ^2) ↦
    ‖y‖ ^ 2 * ∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y))
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (measurable_id.norm.pow_const 2).mul hi

/-- A nonnegative coefficient has a nonnegative ray kernel on the physical half-plane. -/
theorem weightedPoincareRayKernel_nonneg
    {W : (ℝ^2 → ℝ)} (hW : ∀ x ∈ H₊, 0 ≤ W x)
    {y : (ℝ^2)} (hy : y ∈ H₊) :
    0 ≤ weightedPoincareRayKernel W y := by
  unfold weightedPoincareRayKernel
  apply mul_nonneg (sq_nonneg _)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.1.le 4))
    (hW _ ((smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) (inv_pos.mpr ht.1) y).2 hy))

/-- The exact ray budget and finite derivative energies imply both weighted-square
integrability and Poincaré. The two Fubini hypotheses are derived internally. -/
theorem integrable_and_weightedPoincare_squared_halfPlane_of_ray_kernel
    (u W Φr Φz : (ℝ^2 → ℝ)) (CP : ℝ)
    (hu : ContDiff ℝ 1 u) (hu0 : u (0 : (ℝ^2)) = 0)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hCP : 0 ≤ CP)
    (hkernel : ∀ y ∈ H₊, y ≠ (0 : (ℝ^2)) →
      IntervalIntegrable (fun t : ℝ ↦ (t ^ 4)⁻¹ * W (t⁻¹ • y)) volume 0 1)
    (hbudget : ∀ y ∈ H₊,
      weightedPoincareRayKernel W y ≤ CP * min (Φr y) (Φz y))
    (hr : Integrable (fun x ↦ ((∂[0] u) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz : Integrable (fun x ↦ ((∂[1] u) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    Integrable (fun x ↦ u x ^ 2 * W x) (volume.restrict H₊) ∧
      (∫ x in H₊, u x ^ 2 * W x) ≤
        CP * ((∫ x in H₊, ((∂[0] u) x) ^ 2 * Φr x) +
          ∫ x in H₊, ((∂[1] u) x) ^ 2 * Φz x) := by
  obtain ⟨hK, hJ⟩ := ray_work_integrable_of_weighted_energy u W Φr Φz CP hu hWmeas hW
    hCP hkernel hbudget hr hz
  have hi := integrable_square_of_ray u W hu hu0 hWmeas hW hK
  exact ⟨hi, weightedPoincare_squared_halfPlane hu hu0 hW hCP hbudget hi hK hJ hr hz⟩

/-- Quartic coefficient decay makes the exact ray kernel integrable on every bounded
half-ball. The `1 / ‖y‖` majorant is locally integrable in dimension two; bounded base
weights are therefore compatible with a separate core contribution. -/
theorem integrableOn_weightedPoincareRayKernel_of_decay
    (W : (ℝ^2 → ℝ)) (A R : ℝ) (hWmeas : Measurable W)
    (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hdecay : ∀ x ∈ H₊, W x ≤ A / (1 + ‖x‖) ^ 4) :
    IntegrableOn (weightedPoincareRayKernel W)
      (H₊ ∩ Metric.ball (0 : (ℝ^2)) R) := by
  have hA : 0 ≤ A := nonneg_of_decay hW hdecay
  let f : (ℝ^2 → ℝ) := H₊.indicator (weightedPoincareRayKernel W)
  have hfmeas : Measurable f :=
    (measurable_weightedPoincareRayKernel hWmeas).indicator
      (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))
  have hi : IntegrableOn f (Metric.ball (0 : (ℝ^2)) R) := by
    refine integrableOn_ball_of_norm_le_rpow (C := A / 3) (α := 1)
      (by simp) (by norm_num) ?_ hfmeas.aestronglyMeasurable
    filter_upwards [] with y
    by_cases hy : y ∈ H₊
    · change ‖H₊.indicator (weightedPoincareRayKernel W) y‖ ≤ _
      rw [Set.indicator_of_mem hy,
        Real.norm_of_nonneg (weightedPoincareRayKernel_nonneg hW hy)]
      by_cases hy0 : y = (0 : (ℝ^2))
      · simp [hy0]
      · calc
          weightedPoincareRayKernel W y ≤ A / (3 * ‖y‖) :=
            (coefficient_ray_integrable_and_integral_le W A hWmeas hW hdecay
              y hy hy0).2
          _ = A / 3 * ‖y‖ ^ (-(1 : ℝ)) := by
            rw [Real.rpow_neg_one]
            have hyne : ‖y‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hy0)
            cas using hyne
    · change ‖H₊.indicator (weightedPoincareRayKernel W) y‖ ≤ _
      rw [Set.indicator_of_notMem hy, norm_zero]
      exact mul_nonneg (div_nonneg hA (by norm_num)) (Real.rpow_nonneg (norm_nonneg _) _)
  exact (integrableOn_indicator_iff
    (measurableSet_coordinateClosedHalfSpace (0 : Fin 2)).nullMeasurableSet).1 hi

/-- Finite ray slices and an integrable exact core kernel suffice for weighted
Poincaré with a core moment. The proof uses the exterior derivative-weight budget
and a local squared-gradient bound; it imposes no coefficient envelope at zero.
Both weighted-square and Fubini-kernel integrability are derived internally. -/
theorem integrable_and_weightedPoincare_squared_halfPlane_of_core_kernel
    (u W Φr Φz : (ℝ^2 → ℝ)) (CP R M : ℝ)
    (hu : ContDiff ℝ 1 u) (hu0 : u (0 : (ℝ^2)) = 0)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hΦr : ∀ x ∈ H₊, 0 ≤ Φr x)
    (hΦz : ∀ x ∈ H₊, 0 ≤ Φz x)
    (hCP : 0 ≤ CP)
    (hkernel : ∀ y ∈ H₊, y ≠ (0 : (ℝ^2)) →
      IntervalIntegrable (fun t : ℝ ↦ (t ^ 4)⁻¹ * W (t⁻¹ • y)) volume 0 1)
    (hCoreKernel : IntegrableOn (weightedPoincareRayKernel W)
      (H₊ ∩ Metric.ball (0 : (ℝ^2)) R))
    (hbudget : ∀ y ∈ H₊, R ≤ ‖y‖ →
      weightedPoincareRayKernel W y ≤ CP * min (Φr y) (Φz y))
    (hcore : ∀ y ∈ H₊, ‖y‖ < R →
      ((∂[0] u) y) ^ 2 + ((∂[1] u) y) ^ 2 ≤ M)
    (hr : Integrable (fun x ↦ ((∂[0] u) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz : Integrable (fun x ↦ ((∂[1] u) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    Integrable (fun x ↦ u x ^ 2 * W x) (volume.restrict H₊) ∧
      (∫ x in H₊, u x ^ 2 * W x) ≤
        CP * ((∫ x in H₊, ((∂[0] u) x) ^ 2 * Φr x) +
          ∫ x in H₊, ((∂[1] u) x) ^ 2 * Φz x) +
        M * ∫ y in H₊ ∩ Metric.ball (0 : (ℝ^2)) R,
          weightedPoincareRayKernel W y := by
  let S := H₊ ∩ Metric.ball (0 : (ℝ^2)) R
  let Q : (ℝ^2 → ℝ) := S.indicator (weightedPoincareRayKernel W)
  let G : (ℝ^2 → ℝ) := fun x ↦ ((∂[0] u) x) ^ 2 + ((∂[1] u) x) ^ 2
  have hS : MeasurableSet S :=
    (measurableSet_coordinateClosedHalfSpace (0 : Fin 2)).inter measurableSet_ball
  have hQnonneg (x : (ℝ^2)) : 0 ≤ Q x :=
    Set.indicator_nonneg (fun y hy ↦ weightedPoincareRayKernel_nonneg hW hy.1) x
  have hQint : Integrable Q (volume.restrict H₊) :=
    (hCoreKernel.integrable_indicator hS).mono_measure Measure.restrict_le_self
  have hd (i : Fin 2) : Continuous fun x ↦ ((∂[i] u) x) ^ 2 :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hu).continuous.pow 2
  -- `G Q ≤ M Q`, since `G ≤ M` on the core `S` that carries `Q`
  have hGQbound (x : (ℝ^2)) : G x * Q x ≤ M * Q x := by
    by_cases hx : x ∈ S
    · exact mul_le_mul_of_nonneg_right (hcore x hx.1 (mem_ball_zero_iff.mp hx.2)) (hQnonneg x)
    · simp [Q, Set.indicator_of_notMem hx]
  have hGQ : Integrable (fun x ↦ G x * Q x) (volume.restrict H₊) :=
    (hQint.const_mul M).mono'
      (((hd 0).add (hd 1)).aestronglyMeasurable.mul hQint.aestronglyMeasurable)
      (.of_forall fun x ↦ (Real.norm_of_nonneg (mul_nonneg (by positivity) (hQnonneg x))).trans_le
        (hGQbound x))
  have hcomponent (i : Fin 2) (hi : ∀ x, ((∂[i] u) x) ^ 2 ≤ G x) :
      Integrable (fun x ↦ ((∂[i] u) x) ^ 2 * Q x) (volume.restrict H₊) :=
    hGQ.mono' ((hd i).aestronglyMeasurable.mul hQint.aestronglyMeasurable) (.of_forall fun x ↦
      (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hQnonneg x))).trans_le
        (mul_le_mul_of_nonneg_right (hi x) (hQnonneg x)))
  have hQr := hcomponent 0 (fun x ↦ le_add_of_nonneg_right (sq_nonneg ((∂[1] u) x)))
  have hQz := hcomponent 1 (fun x ↦ le_add_of_nonneg_left (sq_nonneg ((∂[0] u) x)))
  -- the exact-kernel estimate with the enlarged weights `CP Φ + Q`
  have hweight (y : ℝ^2) (hy : y ∈ H₊) :
      weightedPoincareRayKernel W y ≤ 1 * min (CP * Φr y + Q y) (CP * Φz y + Q y) := by
    rw [one_mul]
    by_cases hyS : y ∈ S
    · rw [show Q y = _ from Set.indicator_of_mem hyS _]
      exact le_min (le_add_of_nonneg_left (mul_nonneg hCP (hΦr y hy)))
        (le_add_of_nonneg_left (mul_nonneg hCP (hΦz y hy)))
    · rw [show Q y = 0 from Set.indicator_of_notMem hyS _, add_zero, add_zero]
      exact (hbudget y hy (not_lt.1 fun h ↦ hyS ⟨hy, mem_ball_zero_iff.mpr h⟩)).trans_eq
        (mul_min_of_nonneg _ _ hCP)
  have hir := (hr.const_mul CP).add hQr
  have hiz := (hz.const_mul CP).add hQz
  obtain ⟨huW, hbound⟩ := integrable_and_weightedPoincare_squared_halfPlane_of_ray_kernel
    u W (fun x ↦ CP * Φr x + Q x) (fun x ↦ CP * Φz x + Q x) 1 hu hu0 hWmeas hW zero_le_one
    hkernel hweight (hir.congr (.of_forall fun x ↦ by simp only [Pi.add_apply]; ring))
    (hiz.congr (.of_forall fun x ↦ by simp only [Pi.add_apply]; ring))
  refine ⟨huW, ?_⟩
  -- split the enlarged energies and pay the core term `∫ G Q ≤ M ∫_S kernel`
  have e₁ : ∫ x in H₊, ((∂[0] u) x) ^ 2 * (CP * Φr x + Q x) =
      CP * (∫ x in H₊, ((∂[0] u) x) ^ 2 * Φr x) + ∫ x in H₊, ((∂[0] u) x) ^ 2 * Q x := by
    rw [← integral_const_mul, ← integral_add (hr.const_mul CP) hQr]
    congr 1 with x
    ring
  have e₂ : ∫ x in H₊, ((∂[1] u) x) ^ 2 * (CP * Φz x + Q x) =
      CP * (∫ x in H₊, ((∂[1] u) x) ^ 2 * Φz x) + ∫ x in H₊, ((∂[1] u) x) ^ 2 * Q x := by
    rw [← integral_const_mul, ← integral_add (hz.const_mul CP) hQz]
    congr 1 with x
    ring
  have e₃ : ∫ x in H₊, G x * Q x =
      (∫ x in H₊, ((∂[0] u) x) ^ 2 * Q x) + ∫ x in H₊, ((∂[1] u) x) ^ 2 * Q x := by
    rw [← integral_add hQr hQz]
    congr 1 with x
    simp only [G]
    ring
  have hcost : ∫ x in H₊, G x * Q x ≤ M * ∫ y in S, weightedPoincareRayKernel W y := by
    refine (integral_mono hGQ (hQint.const_mul M) hGQbound).trans_eq ?_
    rw [integral_const_mul, integral_indicator hS,
      Measure.restrict_restrict_of_subset Set.inter_subset_left]
  rw [one_mul] at hbound
  rw [mul_add]
  linarith

/-- Weighted Poincaré with an exact core moment. Only exterior rays must fit the
base derivative weights. On the core, a bound `M` for the squared gradient pays
`M` times the integral of the coefficient kernel.

The coefficient decay proves slice integrability and finiteness of the core moment.
Finite derivative energy and the local gradient bound then prove integrability of
`u² W` and both Fubini kernels. The base weights can be bounded at the origin.
This estimate retains a core term; it does not assert a pure first-order estimate
from a point normalization in two dimensions. -/
theorem integrable_and_weightedPoincare_squared_halfPlane_of_core_moment
    (u W Φr Φz : (ℝ^2 → ℝ)) (A CP R M : ℝ)
    (hu : ContDiff ℝ 1 u) (hu0 : u (0 : (ℝ^2)) = 0)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hΦr : ∀ x ∈ H₊, 0 ≤ Φr x)
    (hΦz : ∀ x ∈ H₊, 0 ≤ Φz x)
    (hCP : 0 ≤ CP)
    (hdecay : ∀ x ∈ H₊, W x ≤ A / (1 + ‖x‖) ^ 4)
    (hbudget : ∀ y ∈ H₊, R ≤ ‖y‖ →
      weightedPoincareRayKernel W y ≤ CP * min (Φr y) (Φz y))
    (hcore : ∀ y ∈ H₊, ‖y‖ < R →
      ((∂[0] u) y) ^ 2 + ((∂[1] u) y) ^ 2 ≤ M)
    (hr : Integrable (fun x ↦ ((∂[0] u) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz : Integrable (fun x ↦ ((∂[1] u) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    Integrable (fun x ↦ u x ^ 2 * W x) (volume.restrict H₊) ∧
      (∫ x in H₊, u x ^ 2 * W x) ≤
        CP * ((∫ x in H₊, ((∂[0] u) x) ^ 2 * Φr x) +
          ∫ x in H₊, ((∂[1] u) x) ^ 2 * Φz x) +
        M * ∫ y in H₊ ∩ Metric.ball (0 : (ℝ^2)) R,
          weightedPoincareRayKernel W y := by
  apply integrable_and_weightedPoincare_squared_halfPlane_of_core_kernel
    u W Φr Φz CP R M hu hu0 hWmeas hW hΦr hΦz hCP
    (fun y hy hy0 ↦
      (coefficient_ray_integrable_and_integral_le W A hWmeas hW hdecay y hy hy0).1)
    (integrableOn_weightedPoincareRayKernel_of_decay W A R hWmeas hW hdecay)
    hbudget hcore hr hz

/-- A positive core radius turns a floor for the exterior derivative weights into
one scalar ray certificate. The comparison is never imposed as the radius tends to zero. -/
theorem weightedPoincareRayKernel_le_of_exterior_floor
    (W Φr Φz : (ℝ^2 → ℝ)) (A CP R c : ℝ)
    (hCP : 0 ≤ CP) (hR : 0 < R) (hc : 0 ≤ c)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hdecay : ∀ x ∈ H₊, W x ≤ A / (1 + ‖x‖) ^ 4)
    (hfloor : ∀ y ∈ H₊, R ≤ ‖y‖ → c ≤ min (Φr y) (Φz y))
    (hbudget : A ≤ 3 * CP * R * c)
    (y : (ℝ^2)) (hy : y ∈ H₊) (hyR : R ≤ ‖y‖) :
    weightedPoincareRayKernel W y ≤ CP * min (Φr y) (Φz y) := by
  have hypos : 0 < ‖y‖ := hR.trans_le hyR
  have hy0 : y ≠ (0 : (ℝ^2)) := norm_pos_iff.mp hypos
  apply (coefficient_ray_integrable_and_integral_le W A hWmeas hW hdecay
    y hy hy0).2.trans
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3) hypos)).2
  calc
    A ≤ 3 * CP * R * c := hbudget
    _ ≤ 3 * CP * ‖y‖ * c :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hyR (mul_nonneg (by norm_num) hCP)) hc
    _ ≤ 3 * CP * ‖y‖ * min (Φr y) (Φz y) :=
      mul_le_mul_of_nonneg_left (hfloor y hy hyR)
        (mul_nonneg (mul_nonneg (by norm_num) hCP) hypos.le)
    _ = CP * min (Φr y) (Φz y) * (3 * ‖y‖) := by cas

/-- For a `C¹` profile the local gradient bound needed by the core estimate exists
by compactness. Thus an exterior ray budget already proves weighted-square
integrability, without a separately supplied quantitative gradient bound. -/
theorem integrable_sq_mul_of_decay_and_exterior_ray_budget
    (u W Φr Φz : (ℝ^2 → ℝ)) (A CP R : ℝ)
    (hu : ContDiff ℝ 1 u) (hu0 : u (0 : (ℝ^2)) = 0)
    (hWmeas : Measurable W) (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hΦr : ∀ x ∈ H₊, 0 ≤ Φr x)
    (hΦz : ∀ x ∈ H₊, 0 ≤ Φz x)
    (hCP : 0 ≤ CP)
    (hdecay : ∀ x ∈ H₊, W x ≤ A / (1 + ‖x‖) ^ 4)
    (hbudget : ∀ y ∈ H₊, R ≤ ‖y‖ →
      weightedPoincareRayKernel W y ≤ CP * min (Φr y) (Φz y))
    (hr : Integrable (fun x ↦ ((∂[0] u) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz : Integrable (fun x ↦ ((∂[1] u) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    Integrable (fun x ↦ u x ^ 2 * W x) (volume.restrict H₊) := by
  let G : (ℝ^2 → ℝ) := fun x ↦ ((∂[0] u) x) ^ 2 + ((∂[1] u) x) ^ 2
  have hG : Continuous G :=
    ((PDE.contDiff_partialDeriv_of_succ (m := 0) hu).continuous.pow 2).add
      ((PDE.contDiff_partialDeriv_of_succ (m := 0) hu).continuous.pow 2)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : (ℝ^2)) R).exists_bound_of_continuousOn
    hG.continuousOn
  have hcore : ∀ y ∈ H₊, ‖y‖ < R → G y ≤ M := by
    intro y _ hyR
    exact (Real.le_norm_self _).trans (hM y (mem_closedBall_zero_iff.mpr hyR.le))
  exact (integrable_and_weightedPoincare_squared_halfPlane_of_core_moment
    u W Φr Φz A CP R M hu hu0 hWmeas hW hΦr hΦz hCP hdecay hbudget hcore hr hz).1

end SobolevSpace.Weighted
