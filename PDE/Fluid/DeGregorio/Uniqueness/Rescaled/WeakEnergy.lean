/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Uniqueness.Evolution
import CAS.ExactTactic

/-!
# Spatial energy bounds using an L² vorticity derivative

The difference velocity is bounded by the difference energy through its
normalized Hilbert relation. Young's inequality then controls the transport
coupling using the L² norm of the background vorticity derivative.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis

namespace DeGregorio

/-- Young's inequality separates the derivative coupling into the difference
square, Hilbert square, and velocity-weighted background derivative square. -/
theorem abs_coupled_terms_le_weak_h1 {d u v v' w w' C : ℝ}
    (hu : |u| ≤ C) (hw : |w| ≤ C) :
    |3 * u * d ^ 2 + 2 * d * v' * w - 2 * d * v * w'| ≤
      (4 * C + 1) * d ^ 2 + C * v' ^ 2 + v ^ 2 * w' ^ 2 := by
  have hYoung : 2 * |d| * |v'| ≤ d ^ 2 + v' ^ 2 := by
    simpa only [sq_abs] using two_mul_le_add_sq |d| |v'|
  have hlast : |2 * d * v * w'| ≤ d ^ 2 + v ^ 2 * w' ^ 2 := by
    have h := two_mul_le_add_sq |d| |v * w'|
    simp only [sq_abs, mul_pow, abs_mul] at h
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc] using h
  calc
    _ ≤ |3 * u * d ^ 2| + |2 * d * v' * w| + |2 * d * v * w'| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3 * C * d ^ 2 + (d ^ 2 + v' ^ 2) * C + (d ^ 2 + v ^ 2 * w' ^ 2) := by
      apply add_le_add _ hlast
      apply add_le_add
      · simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_sq]
        gcongr
      · simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul hYoung hw (abs_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by cas

/-- The coupled energy estimate needs only an L² bound on the background
vorticity derivative. The normalized Hilbert primitive controls its multiplier. -/
theorem norm_integral_coupled_terms_le_of_deriv_L2
    {d u v w : ℝ → ℝ} {L C D : ℝ}
    (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (hpair : IsHilbertPair d (deriv v)) (hvzero : v 0 = 0)
    (hsupp : ∀ x, x ∉ Icc (-L) L → d x = 0)
    (hbound : ∀ x ∈ Icc (-L) L, |deriv u x| ≤ C ∧ |w x| ≤ C)
    (hderivLp : MemLp (deriv w) 2 volume)
    (hderivBound : (∫ x, deriv w x ^ 2) ≤ D) :
    ‖∫ x in Icc (-L) L,
      3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
        2 * d x * v x * deriv w x‖ ≤
      (5 * C + 1 + L * D) * ∫ x in Icc (-L) L, d x ^ 2 := by
  rcases lt_or_ge L 0 with hL | hL
  · simp [Icc_eq_empty (by linarith : ¬-L ≤ L)]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbound 0 ⟨by linarith, hL⟩).1
  let E := ∫ x in Icc (-L) L, d x ^ 2
  have hE : 0 ≤ E := integral_nonneg fun _ ↦ sq_nonneg _
  have hglobal : E = ∫ x, d x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hsupp x hx, zero_pow (by decide : 2 ≠ 0)]
  have hderiv : (∫ x in Icc (-L) L, deriv v x ^ 2) ≤ E := by
    rw [hglobal, ← hpair.integral_sq_eq]
    exact setIntegral_le_integral hpair.memLp_right.integrable_sq
      (Eventually.of_forall fun x ↦ sq_nonneg (deriv v x))
  have hbackground : (∫ x in Icc (-L) L, deriv w x ^ 2) ≤ D :=
    (setIntegral_le_integral hderivLp.integrable_sq
      (Eventually.of_forall fun x ↦ sq_nonneg (deriv w x))).trans hderivBound
  have hvelocity (x : ℝ) (hx : x ∈ Icc (-L) L) : v x ^ 2 ≤ L * E := by
    rw [hglobal]
    exact (hpair.sq_le_abs_mul_integral_sq hv hvzero x).trans
      (mul_le_mul_of_nonneg_right (abs_le.mpr hx)
        (integral_nonneg fun y ↦ sq_nonneg (d y)))
  have hV := hv.continuous_deriv le_rfl
  have hW := hw.continuous_deriv le_rfl
  have h₁ : IntegrableOn (fun x ↦ (4 * C + 1) * d x ^ 2) (Icc (-L) L) :=
    (hpair.memLp_left.integrable_sq.const_mul _).integrableOn
  have h₂ : Continuous (fun x ↦ C * deriv v x ^ 2) := by fun_prop
  have h₃ : Continuous (fun x ↦ L * E * deriv w x ^ 2) := by fun_prop
  have h₁₂ : IntegrableOn (fun x ↦ (4 * C + 1) * d x ^ 2 + C * deriv v x ^ 2) (Icc (-L) L) :=
    h₁.add h₂.integrableOn_Icc
  have hmajor : IntegrableOn (fun x ↦
      (4 * C + 1) * d x ^ 2 + C * deriv v x ^ 2 + L * E * deriv w x ^ 2) (Icc (-L) L) :=
    h₁₂.add h₃.integrableOn_Icc
  calc
    _ ≤ ∫ x in Icc (-L) L,
        (4 * C + 1) * d x ^ 2 + C * deriv v x ^ 2 + L * E * deriv w x ^ 2 := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact (abs_coupled_terms_le_weak_h1 (hbound x hx).1 (hbound x hx).2).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hvelocity x hx) (sq_nonneg _)))
    _ = (4 * C + 1) * E + C * (∫ x in Icc (-L) L, deriv v x ^ 2) +
        L * E * (∫ x in Icc (-L) L, deriv w x ^ 2) := by
      rw [integral_add h₁₂ h₃.integrableOn_Icc,
        integral_add h₁ h₂.integrableOn_Icc,
        integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ (4 * C + 1) * E + C * E + L * E * D :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hderiv hC))
        (mul_le_mul_of_nonneg_left hbackground (mul_nonneg hL hE))
    _ = _ := by dsimp [E]; cas

/-- Vanishing transport flux at the two endpoints gives the square-energy
identity on any compact interval. Only spatial C¹ regularity is used. -/
theorem integral_rescaled_square_energy
    {w u : ℝ → ℝ} {l r : ℝ} (hw : ContDiff ℝ 1 w) (hu : ContDiff ℝ 1 u)
    (hlr : l ≤ r) (cl cw : ℝ)
    (hleft : (u l + cl * l) * w l ^ 2 = 0)
    (hright : (u r + cl * r) * w r ^ 2 = 0) :
    (2 * ∫ x in Icc l r, w x *
      ((cw + deriv u x) * w x - (u x + cl * x) * deriv w x)) =
      ∫ x in Icc l r, (2 * cw + 3 * deriv u x + cl) * w x ^ 2 := by
  have hU := hu.continuous_deriv le_rfl
  have hW := hw.continuous_deriv le_rfl
  have hflux : (∫ x in Icc l r,
      (deriv u x + cl) * w x ^ 2 + 2 * (u x + cl * x) * w x * deriv w x) = 0 := by
    have hderiv (x : ℝ) : HasDerivAt (fun y ↦ (u y + cl * y) * w y ^ 2)
        ((deriv u x + cl) * w x ^ 2 + 2 * (u x + cl * x) * w x * deriv w x) x := by
      convert ((hu.differentiable (by simp) x).hasDerivAt.add
        ((hasDerivAt_id x).const_mul cl)).mul
        ((hw.differentiable (by simp) x).hasDerivAt.pow 2) using 1
      · funext y
        rfl
      · cas
    have hc : Continuous (fun x ↦
        (deriv u x + cl) * w x ^ 2 + 2 * (u x + cl * x) * w x * deriv w x) := by
      fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
      (hc.intervalIntegrable l r)
    rw [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc,
      hleft, hright, sub_self] at hi
    exact hi
  have hbase : Continuous (fun x ↦ 2 * (w x *
      ((cw + deriv u x) * w x - (u x + cl * x) * deriv w x))) := by fun_prop
  have hfluxCont : Continuous (fun x ↦
      (deriv u x + cl) * w x ^ 2 + 2 * (u x + cl * x) * w x * deriv w x) := by fun_prop
  calc
    _ = (∫ x in Icc l r, 2 * (w x *
          ((cw + deriv u x) * w x - (u x + cl * x) * deriv w x))) +
        ∫ x in Icc l r,
          (deriv u x + cl) * w x ^ 2 + 2 * (u x + cl * x) * w x * deriv w x := by
      rw [integral_const_mul, hflux, add_zero]
    _ = _ := by
      rw [← integral_add hbase.integrableOn_Icc hfluxCont.integrableOn_Icc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      cas

end DeGregorio
