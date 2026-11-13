/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Higher regularity of compactly indexed integrals

A smooth ambient family remains smooth after integration over a compact continuous
parametrization. Applying the first-derivative theorem to each successive Fréchet derivative
gives every finite order. Compactness supplies local bounds, so no global derivative bound
is needed.
-/

@[expose] public noncomputable section

open MeasureTheory

universe u v

variable {E : Type u} {B T : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace T] [CompactSpace T]
  [MeasurableSpace T] [OpensMeasurableSpace T]
  {μ : Measure T} [IsFiniteMeasure μ]
  {η : T → B}

/-- Integrating successive parameter derivatives preserves every finite order
of smoothness. -/
private theorem contDiff_integral_compact_parametrization_nat
    {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : ℕ} {f : E × B → F} (hf : ContDiff ℝ k f) (hη : Continuous η) :
    ContDiff ℝ k (fun x ↦ ∫ t, f (x, η t) ∂μ) := by
  induction k generalizing F with
  | zero =>
    simp only [Nat.cast_zero, contDiff_zero]
    exact PDE.continuous_integral_of_compact
      (hf.continuous.comp (continuous_fst.prodMk (hη.comp continuous_snd)))
  | succ k ih =>
    let D : E × B → E →L[ℝ] F :=
      fun p ↦ (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E B)
    have hD : ContDiff ℝ k D :=
      (hf.fderiv_right (by simp)).clm_comp contDiff_const
    have hd (x : E) (t : T) :
        HasFDerivAt (fun y ↦ f (y, η t)) (D (x, η t)) x := by
      exact (hf.differentiable (by simp) (x, η t)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (η t) x))
    have hi (x : E) :=
      PDE.hasFDerivAt_integral_of_compact (μ := μ)
        (f := fun x t ↦ f (x, η t)) (D := fun x t ↦ D (x, η t))
        (hf.continuous.comp (continuous_fst.prodMk (hη.comp continuous_snd)))
        (hD.continuous.comp (continuous_fst.prodMk (hη.comp continuous_snd))) hd x
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun x ↦ (hi x).differentiableAt, by simp, ?_⟩
    have heq : fderiv ℝ (fun x ↦ ∫ t, f (x, η t) ∂μ) =
        fun x ↦ ∫ t, D (x, η t) ∂μ := funext fun x ↦ (hi x).fderiv
    rw [heq]
    exact ih hD

namespace PDE

/-- A smooth ambient family remains smooth after integration over a compact
continuous parametrization. Only the first variable is differentiated. Parameter
and codomain may lie in different universes, and no dimension bound is needed. -/
theorem contDiff_integral_compact_parametrization
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : ℕ} {f : E × B → F} (hf : ContDiff ℝ k f) (hη : Continuous η) :
    ContDiff ℝ k (fun x ↦ ∫ t, f (x, η t) ∂μ) := by
  let e : ULift.{u} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  have h := contDiff_integral_compact_parametrization_nat
    (μ := μ) (e.symm.toContinuousLinearEquiv.contDiff.comp hf) hη
  have h := e.toContinuousLinearEquiv.contDiff.comp h
  convert h using 1
  funext x
  simpa only [Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, e.apply_symm_apply] using
    e.toLinearIsometry.integral_comp_comm (fun t ↦ e.symm (f (x, η t)))

/-- The unit interval with the comap of Lebesgue measure is a finite measure space. -/
instance isFiniteMeasure_comap_val_Icc_zero_one :
    IsFiniteMeasure (volume.comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) := by
  have := IsFiniteMeasureOnCompacts.comap' (volume : Measure ℝ)
    (continuous_subtype_val : Continuous (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)
  infer_instance

end PDE
