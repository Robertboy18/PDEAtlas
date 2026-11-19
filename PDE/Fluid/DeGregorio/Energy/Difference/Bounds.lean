/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Energy.Difference.Spatial
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev
import CAS.ExactTactic

/-!
# Bounds for the difference-energy coupling

The frozen input determines the velocity, while the transported output has its
own energy. The coupled estimate specializes this bound when the two coincide
and their common vorticity difference has bounded support.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis

namespace DeGregorio

private theorem abs_frozen_terms_le {d u v v' w w' C : ℝ}
    (hu : |u| ≤ C) (hw : |w| ≤ C) (hw' : |w'| ≤ C) :
    |3 * u * d ^ 2 + 2 * d * v' * w - 2 * d * v * w'| ≤
      C * (5 * d ^ 2 + v' ^ 2 + v ^ 2) := by
  have hYoung (z : ℝ) : 2 * |d| * |z| ≤ d ^ 2 + z ^ 2 := by
    simpa only [sq_abs] using two_mul_le_add_sq |d| |z|
  calc
    _ ≤ |3 * u * d ^ 2| + |2 * d * v' * w| + |2 * d * v * w'| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 3 * |u| * d ^ 2 + (2 * |d| * |v'|) * |w| +
        (2 * |d| * |v|) * |w'| := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_sq]
    _ ≤ 3 * C * d ^ 2 + (d ^ 2 + v' ^ 2) * C + (d ^ 2 + v ^ 2) * C := by
      gcongr
      · exact hYoung v'
      · exact hYoung v
    _ = _ := by cas

/-- The input `f` controls the velocity difference `v` through the Hilbert isometry and
`v 0 = 0`, while the transported output difference `d` contributes its own energy on
`[-L, L]`. -/
theorem norm_integral_frozen_terms_le {f d u v w : ℝ → ℝ} {L C : ℝ}
    (hd : ContDiff ℝ 1 d) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hpair : IsHilbertPair f (deriv v)) (hvzero : v 0 = 0)
    (hbound : ∀ x ∈ Icc (-L) L,
      |deriv u x| ≤ C ∧ |w x| ≤ C ∧ |deriv w x| ≤ C) :
    ‖∫ x in Icc (-L) L,
      3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
        2 * d x * v x * deriv w x‖ ≤
      C * (5 * (∫ x in Icc (-L) L, d x ^ 2) +
        (1 + 2 * L ^ 2) * ∫ x, f x ^ 2) := by
  let E := ∫ x, f x ^ 2
  have hE : 0 ≤ E := integral_nonneg fun _ ↦ sq_nonneg _
  have hderiv : (∫ x in Icc (-L) L, deriv v x ^ 2) ≤ E := by
    rw [show E = ∫ x, deriv v x ^ 2 from hpair.integral_sq_eq.symm]
    exact setIntegral_le_integral hpair.memLp_right.integrable_sq
      (.of_forall fun x ↦ sq_nonneg (deriv v x))
  have hvelocity : (∫ x in Icc (-L) L, v x ^ 2) ≤ 2 * L ^ 2 * E := by
    have hpoint (x : ℝ) (hx : x ∈ Icc (-L) L) : v x ^ 2 ≤ L * E :=
      (hpair.sq_le_abs_mul_integral_sq hv hvzero x).trans
        (mul_le_mul_of_nonneg_right (abs_le.mpr hx) hE)
    calc
      _ ≤ ∫ _x in Icc (-L) L, L * E :=
        setIntegral_mono_on (hv.continuous.pow 2).integrableOn_Icc
          continuous_const.integrableOn_Icc measurableSet_Icc hpoint
      _ = _ := by
        rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc]
        simp only [smul_eq_mul, sub_neg_eq_add,
          ENNReal.toReal_ofReal (add_nonneg hL hL)]
        cas
  have hU := hu.continuous_deriv le_rfl
  have hV := hv.continuous_deriv le_rfl
  have hW := hw.continuous_deriv le_rfl
  have hmajor : Continuous (fun x ↦ C * (5 * d x ^ 2 + deriv v x ^ 2 + v x ^ 2)) := by
    fun_prop
  calc
    _ ≤ ∫ x in Icc (-L) L, C * (5 * d x ^ 2 + deriv v x ^ 2 + v x ^ 2) := by
      apply norm_integral_le_of_norm_le hmajor.integrableOn_Icc
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact abs_frozen_terms_le (hbound x hx).1 (hbound x hx).2.1 (hbound x hx).2.2
    _ = C * (5 * (∫ x in Icc (-L) L, d x ^ 2) +
        (∫ x in Icc (-L) L, deriv v x ^ 2) +
        ∫ x in Icc (-L) L, v x ^ 2) := by
      have h₁ : Continuous (fun x ↦ 5 * d x ^ 2) := by fun_prop
      have h₂ : Continuous (fun x ↦ deriv v x ^ 2) := by fun_prop
      have h₃ : Continuous (fun x ↦ v x ^ 2) := by fun_prop
      have h₁₂ : Continuous (fun x ↦ 5 * d x ^ 2 + deriv v x ^ 2) := h₁.add h₂
      rw [integral_const_mul, integral_add h₁₂.integrableOn_Icc
        h₃.integrableOn_Icc, integral_add h₁.integrableOn_Icc h₂.integrableOn_Icc,
        integral_const_mul]
    _ ≤ C * (5 * (∫ x in Icc (-L) L, d x ^ 2) + E + 2 * L ^ 2 * E) := by
      gcongr
    _ = _ := by dsimp [E]; cas

/-- The two coupling terms are controlled by the difference energy. The
velocity bound uses its normalization and the concrete Hilbert isometry. -/
theorem norm_integral_coupled_terms_le {d u v w : ℝ → ℝ} {L C : ℝ}
    (hd : ContDiff ℝ 1 d) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hpair : IsHilbertPair d (deriv v)) (hvzero : v 0 = 0)
    (hsupp : ∀ x, x ∉ Icc (-L) L → d x = 0)
    (hbound : ∀ x ∈ Icc (-L) L,
      |deriv u x| ≤ C ∧ |w x| ≤ C ∧ |deriv w x| ≤ C) :
    ‖∫ x in Icc (-L) L,
      3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
        2 * d x * v x * deriv w x‖ ≤
      ((6 + 2 * L ^ 2) * C) * ∫ x in Icc (-L) L, d x ^ 2 := by
  have hglobal : (∫ x in Icc (-L) L, d x ^ 2) = ∫ x, d x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hsupp x hx, zero_pow (by decide : 2 ≠ 0)]
  have h := norm_integral_frozen_terms_le hd hu hv hw hL hC hpair hvzero hbound
  rw [← hglobal] at h
  convert h using 1
  cas

end DeGregorio
