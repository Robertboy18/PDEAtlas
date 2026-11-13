/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactParametricIntegral.ContDiff
public import PDE.Analysis.Calculus.Gradient
public import PDE.Analysis.Calculus.Gradient.Hessian
public import PDE.Analysis.Calculus.Taylor.Quadratic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import CAS.IntegrationTactic

/-!
# The integral Hessian in Taylor's formula

Integrating the Hessian along a segment gives an exact quadratic
representation of a smooth function at a critical point. The resulting operator
field is smooth and self-adjoint, and equals the Hessian at the base point.

`integralHessian f p x` is the matrix `A(x)` of (48) in step 2 of Evans's proof of Lemma 3 of
§4.5.3(b), with base point `p` in place of `0`; `quadratic_taylor_integralHessian` is (48),
stated with the first-order term, and `integralHessian_self` is `A(0) = D²φ(0)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), step 2 of the proof of Lemma 3, (48),
  p. 224. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology Gradient RealInnerProductSpace

namespace PDE.Analysis.StationaryPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hessian averaged with the quadratic Taylor weight along a segment. -/
def integralHessian (f : E → ℝ) (p x : E) : E →L[ℝ] E :=
  ∫ t : Icc (0 : ℝ) 1,
    (2 * (1 - (t : ℝ))) • fderiv ℝ (∇ f) (p + (t : ℝ) • (x - p))
    ∂volume.comap Subtype.val

/-- A smooth phase has a smooth integral Hessian. -/
theorem contDiff_integralHessian {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (p : E) :
    ContDiff ℝ (⊤ : ℕ∞) (integralHessian f p) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (∇ f) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact PDE.Analysis.contDiffAt_gradient (by simpa using hf.contDiffAt (x := x))
  have hH : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (∇ f)) :=
    hg.fderiv_right (by simp)
  apply contDiff_infty.mpr
  intro k
  have hfamily : ContDiff ℝ k (fun y : E × ℝ ↦
      (2 * (1 - y.2)) • fderiv ℝ (∇ f) (p + y.2 • (y.1 - p))) :=
    (contDiff_const.mul (contDiff_const.sub contDiff_snd)).smul
      ((hH.of_le (by simp)).comp
        (contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))))
  exact contDiff_integral_compact_parametrization
    (μ := volume.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ))
    hfamily continuous_subtype_val

/-- The compact-index definition agrees with the usual interval integral. -/
theorem integralHessian_eq_intervalIntegral (f : E → ℝ) (p x : E) :
    integralHessian f p x =
      ∫ t in (0 : ℝ)..1,
        (2 * (1 - t)) • fderiv ℝ (∇ f) (p + t • (x - p)) := by
  rw [integralHessian, integral_subtype_comap measurableSet_Icc
    (fun t : ℝ ↦ (2 * (1 - t)) • fderiv ℝ (∇ f) (p + t • (x - p))),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- The integral Hessian agrees with the Hessian at the base point. -/
theorem integralHessian_self (f : E → ℝ) (p : E) :
    integralHessian f p p = fderiv ℝ (∇ f) p := by
  rw [integralHessian_eq_intervalIntegral]
  simp only [sub_self, smul_zero, add_zero]
  rw [intervalIntegral.integral_smul_const]
  have hw : (∫ t in (0 : ℝ)..1, 2 * (1 - t)) = 1 := by
    cas
  rw [hw, one_smul]

/-- Averaging Hessians preserves self-adjointness. -/
theorem star_integralHessian {f : E → ℝ} (hf : ContDiff ℝ 2 f) (p x : E) :
    star (integralHessian f p x) = integralHessian f p x := by
  let J : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E) := ContinuousLinearMap.adjoint
  change J (integralHessian f p x) = integralHessian f p x
  unfold integralHessian
  have hJ := J.toLinearIsometry.integral_comp_comm (μ := volume.comap Subtype.val)
    (fun t : Icc (0 : ℝ) 1 ↦
      (2 * (1 - (t : ℝ))) • fderiv ℝ (∇ f) (p + (t : ℝ) • (x - p)))
  change (∫ t : Icc (0 : ℝ) 1, J
    ((2 * (1 - (t : ℝ))) • fderiv ℝ (∇ f) (p + (t : ℝ) • (x - p)))
      ∂volume.comap Subtype.val) = J _ at hJ
  rw [← hJ]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul]
  congr 1
  exact (show (fderiv ℝ (∇ f) (p + (t : ℝ) • (x - p))).IsSymmetric from
    fun v w ↦ hf.contDiffAt.inner_fderiv_gradient_comm v w).clm_adjoint_eq

/-- Taylor's formula expressed through the integral Hessian operator. -/
theorem quadratic_taylor_integralHessian {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (p x : E) :
    f x = f p + fderiv ℝ f p (x - p) +
      inner ℝ (integralHessian f p x (x - p)) (x - p) / 2 := by
  let v := x - p
  have hg : ContDiff ℝ (⊤ : ℕ∞) (∇ f) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    exact PDE.Analysis.contDiffAt_gradient (by simpa using hf.contDiffAt (x := y))
  have hH : Continuous (fderiv ℝ (∇ f)) :=
    (hg.fderiv_right (m := 0) (by simp)).continuous
  have hfamily : Continuous
      (fun t : ℝ ↦ (2 * (1 - t)) • fderiv ℝ (∇ f) (p + t • v)) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).smul
        (hH.comp (continuous_const.add (continuous_id.smul continuous_const)))
  have hint := hfamily.intervalIntegrable (μ := volume) (a := 0) (b := 1)
  have hquad : inner ℝ (integralHessian f p x v) v =
      2 * ∫ t in (0 : ℝ)..1,
        (1 - t) * fderiv ℝ (fderiv ℝ f) (p + t • v) v v := by
    rw [real_inner_comm, integralHessian_eq_intervalIntegral,
      ContinuousLinearMap.intervalIntegral_apply hint]
    change (innerSL ℝ v) (∫ t in (0 : ℝ)..1,
      ((2 * (1 - t)) • fderiv ℝ (∇ f) (p + t • v)) v) = _
    rw [← (innerSL ℝ v).intervalIntegral_comp_comm
      ((hfamily.clm_apply (continuous_const (y := v))).intervalIntegrable 0 1)]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [smul_apply, real_inner_smul_right, innerSL_apply_apply]
    rw [real_inner_comm, PDE.Analysis.inner_fderiv_gradient_at
      (hf.contDiffAt.of_le (by simp))]
    ring
  have ht := PDE.Analysis.quadratic_taylor_integral
    (x := p) (h := v) (fun _ _ ↦ hf.contDiffAt.of_le (by simp))
  rw [show p + v = x by dsimp [v]; abel] at ht
  rw [hquad]
  convert ht using 1
  ring

end PDE.Analysis.StationaryPhase
