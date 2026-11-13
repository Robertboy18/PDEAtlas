/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integral bounds for nonnegative quadratic energies

A nonnegative symmetric continuous bilinear form defines an energy seminorm.
Its integral triangle inequality applies to integrable wave forcing even when
the form degenerates outside a spatial region.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x)

include hB hpos in
/-- Cauchy--Schwarz for a possibly degenerate continuous quadratic energy. -/
theorem abs_bilinear_le_sqrt_mul_sqrt (x y : E) :
    |B x y| ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
  let : PreInnerProductSpace.Core ℝ E :=
    { inner := fun x y ↦ B x y
      conj_inner_symm := fun x y ↦ by simpa using hB y x
      re_inner_nonneg := hpos
      add_left := fun x y z ↦ by simp only [map_add, add_apply]
      smul_left := fun x y c ↦ by
        simp only [map_smul, smul_apply, smul_eq_mul, RCLike.conj_to_real] }
  exact InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℝ) x y

/-- A continuous quadratic energy seminorm is bounded by the original norm. -/
theorem sqrt_bilinear_self_le (x : E) :
    Real.sqrt (B x x) ≤ Real.sqrt ‖B‖ * ‖x‖ := by
  calc
    Real.sqrt (B x x) ≤ Real.sqrt (‖B‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt
      ((le_abs_self _).trans ((B x).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg x))))
    _ = Real.sqrt ‖B‖ * ‖x‖ := by
      rw [mul_assoc, Real.sqrt_mul (norm_nonneg B), Real.sqrt_mul_self (norm_nonneg x)]

/-- Integrable trajectories have integrable nonnegative quadratic energy seminorm. -/
theorem integrable_sqrt_bilinear_self {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → E} (hf : Integrable f μ) :
    Integrable (fun a ↦ Real.sqrt (B (f a) (f a))) μ := by
  have hc : Continuous (fun x ↦ Real.sqrt (B x x)) :=
    Real.continuous_sqrt.comp (B.continuous.clm_apply continuous_id)
  apply (hf.norm.const_mul (Real.sqrt ‖B‖)).mono'
    (hc.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_bilinear_self_le B (f a)

include hpos in
/-- Minkowski's inequality for the seminorm defined by a nonnegative continuous
bilinear form. No coercivity or symmetry of the form is needed: only the diagonal enters,
and it is the diagonal of the symmetrization. -/
theorem sqrt_bilinear_integral_le [CompleteSpace E] {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → E} (hf : Integrable f μ) :
    Real.sqrt (B (∫ a, f a ∂μ) (∫ a, f a ∂μ)) ≤ ∫ a, Real.sqrt (B (f a) (f a)) ∂μ := by
  obtain ⟨Bs, hdiag, hBs⟩ : ∃ Bs : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ x, Bs x x = B x x) ∧ ∀ x y, Bs x y = Bs y x :=
    ⟨(1 / 2 : ℝ) • (B + B.flip),
      fun x ↦ by
        simp only [smul_apply, add_apply,
          ContinuousLinearMap.flip_apply, smul_eq_mul]
        ring,
      fun x y ↦ by
        simp only [smul_apply, add_apply,
          ContinuousLinearMap.flip_apply, smul_eq_mul]
        ring⟩
  have hBspos (x : E) : 0 ≤ Bs x x := by
    rw [hdiag]
    exact hpos x
  simp only [← hdiag]
  let z := ∫ a, f a ∂μ
  have hq := integrable_sqrt_bilinear_self Bs hf
  have he : Bs z z = ∫ a, Bs (f a) z ∂μ := ((Bs.flip z).integral_comp_comm hf).symm
  have hi : Bs z z ≤ (∫ a, Real.sqrt (Bs (f a) (f a)) ∂μ) * Real.sqrt (Bs z z) := by
    calc
      Bs z z = ∫ a, Bs (f a) z ∂μ := he
      _ ≤ ∫ a, Real.sqrt (Bs (f a) (f a)) * Real.sqrt (Bs z z) ∂μ :=
        integral_mono ((Bs.flip z).integrable_comp hf) (hq.mul_const (Real.sqrt (Bs z z)))
          (fun a ↦ (le_abs_self _).trans (abs_bilinear_le_sqrt_mul_sqrt Bs hBs hBspos (f a) z))
      _ = _ := integral_mul_const _ _
  by_cases hz : Real.sqrt (Bs z z) = 0
  · rw [show Real.sqrt (Bs (∫ a, f a ∂μ) (∫ a, f a ∂μ)) = 0 from hz]
    exact integral_nonneg fun a ↦ Real.sqrt_nonneg _
  · have hp : 0 < Real.sqrt (Bs z z) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    have hs := Real.sq_sqrt (hBspos z)
    nlinarith

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
