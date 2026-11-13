/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Fourier.L1Reconstruction.Parametric

/-!
# Second joint derivatives of inverse Fourier integrals

Two applications of the joint first-derivative theorem give a joint C² field.
The second application takes values in continuous linear maps. The assumptions
require two spatial moments of the datum, one of its time derivative, and an
integrable bound for its second time derivative, locally uniformly in time.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped Topology

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

/-- The derivative frequency datum before multiplication by the inverse Fourier character. -/
def derivativeDatum (ξ : E) (v d : F) : (ℝ × E) →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ E).smulRight d +
    (2 * Real.pi * Complex.I) •
      ((innerSL ℝ ξ).comp (ContinuousLinearMap.snd ℝ ℝ E)).smulRight v

/-- At the spatial origin the inverse character equals one. -/
theorem derivativeDatum_eq_kernel (ξ : E) (v d : F) :
    derivativeDatum ξ v d = inverseKernelDerivative ξ (0, 0) v d := by
  simp [derivativeDatum, inverseKernelDerivative]

/-- One spatial derivative costs one frequency moment. -/
theorem norm_derivativeDatum_le (ξ : E) (v d : F) :
    ‖derivativeDatum ξ v d‖ ≤ ‖d‖ + (2 * Real.pi) * ‖ξ‖ * ‖v‖ := by
  rw [derivativeDatum_eq_kernel]
  exact norm_inverseKernelDerivative_le ξ (0, 0) v d

/-- Differentiating the derivative datum advances both time-dependent entries. -/
theorem hasDerivAt_derivativeDatum (ξ : E) {v d : ℝ → F} {v' d' : F} {t : ℝ}
    (hv : HasDerivAt v v' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun s ↦ derivativeDatum ξ (v s) (d s))
      (derivativeDatum ξ v' d') t := by
  have hd' := (ContinuousLinearMap.smulRightL ℝ (ℝ × E) F
    (ContinuousLinearMap.fst ℝ ℝ E)).hasFDerivAt.comp_hasDerivAt
      (E := (ℝ × E) →L[ℝ] F) t hd
  have hv' := (ContinuousLinearMap.smulRightL ℝ (ℝ × E) F
    ((innerSL ℝ ξ).comp (ContinuousLinearMap.snd ℝ ℝ E))).hasFDerivAt.comp_hasDerivAt
      (E := (ℝ × E) →L[ℝ] F) t hv
  simpa only [derivativeDatum, Function.comp_def, Pi.add_def, Pi.smul_def,
    ContinuousLinearMap.smulRightL_apply_apply] using
    hd'.add (hv'.const_smul (2 * Real.pi * Complex.I))

/-- Joint continuity of the derivative datum in frequency and its two values. -/
theorem continuous_derivativeDatum {X : Type*} [TopologicalSpace X]
    {ξ : X → E} {v d : X → F} (hξ : Continuous ξ) (hv : Continuous v)
    (hd : Continuous d) : Continuous (fun x ↦ derivativeDatum (ξ x) (v x) (d x)) := by
  simpa only [derivativeDatum_eq_kernel] using
    continuous_inverseKernelDerivative hξ (continuous_const (y := (0, 0))) hv hd

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The second derivative takes values in operators with their operator norm. -/
local instance instNormedAddCommGroupJointDerivative :
    NormedAddCommGroup ((ℝ × E) →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Use the given real scalar action on the derivative's values in the second
application of the parameter integral theorem. -/
local instance instNormedSpaceJointDerivative :
    NormedSpace ℝ ((ℝ × E) →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

/-- Use the operator norm when integrating the joint first derivative. -/
local instance instContinuousENormFirstDerivative :
    ContinuousENorm ((ℝ × E) →L[ℝ] F) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid ((ℝ × E) →L[ℝ] F) inferInstance).toContinuousENorm

/-- The Hessian integral uses the iterated operator norm. -/
local instance instContinuousENormSecondDerivative :
    ContinuousENorm ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] F) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] F) inferInstance).toContinuousENorm

/-- A second joint derivative needs two spatial moments and two time derivatives. -/
theorem contDiff_two_fourierInv_family
    (v d e : ℝ → E → F)
    (hv : ∀ t, AEStronglyMeasurable (v t) volume)
    (hd : ∀ t, AEStronglyMeasurable (d t) volume)
    (he : ∀ t, AEStronglyMeasurable (e t) volume)
    (hvd : ∀ ξ t, HasDerivAt (fun s ↦ v s ξ) (d t ξ) t)
    (hde : ∀ ξ t, HasDerivAt (fun s ↦ d s ξ) (e t ξ) t)
    (hec : ∀ ξ, Continuous (fun t ↦ e t ξ))
    (hbound : ∀ T : ℝ, 0 ≤ T → ∃ b c a : E → ℝ,
      Integrable b ∧ Integrable (fun ξ ↦ ‖ξ‖ * b ξ) ∧
      Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * b ξ) ∧
      Integrable c ∧ Integrable (fun ξ ↦ ‖ξ‖ * c ξ) ∧ Integrable a ∧
      ∀ t, |t| ≤ T → ∀ ξ, ‖v t ξ‖ ≤ b ξ ∧ ‖d t ξ‖ ≤ c ξ ∧ ‖e t ξ‖ ≤ a ξ) :
    ContDiff ℝ 2 (fun p : ℝ × E ↦ 𝓕⁻ (v p.1) p.2) ∧
      ∀ p : ℝ × E,
        Integrable (fun ξ ↦ inverseKernelDerivative ξ p (v p.1 ξ) (d p.1 ξ)) ∧
        HasFDerivAt (fun q : ℝ × E ↦ 𝓕⁻ (v q.1) q.2)
          (∫ ξ, inverseKernelDerivative ξ p (v p.1 ξ) (d p.1 ξ)) p ∧
        Integrable (fun ξ ↦ inverseKernelDerivative ξ p
          (derivativeDatum ξ (v p.1 ξ) (d p.1 ξ))
          (derivativeDatum ξ (d p.1 ξ) (e p.1 ξ))) ∧
        HasFDerivAt (fderiv ℝ (fun q : ℝ × E ↦ 𝓕⁻ (v q.1) q.2))
        (∫ ξ, inverseKernelDerivative ξ p
          (derivativeDatum ξ (v p.1 ξ) (d p.1 ξ))
          (derivativeDatum ξ (d p.1 ξ) (e p.1 ξ))) p := by
  have hdc (ξ : E) : Continuous (fun t ↦ d t ξ) :=
    continuous_iff_continuousAt.mpr fun t ↦ (hde ξ t).continuousAt
  have hfirst := contDiff_one_fourierInv_family v d hv hd hvd hdc (by
    intro T hT
    obtain ⟨b, c, a, hb, hb₁, _, hc, _, _, hbca⟩ := hbound T hT
    exact ⟨b, c, hb, hb₁, hc, fun t ht ξ ↦ ⟨(hbca t ht ξ).1, (hbca t ht ξ).2.1⟩⟩)
  let A (t : ℝ) (ξ : E) := derivativeDatum ξ (v t ξ) (d t ξ)
  let B (t : ℝ) (ξ : E) := derivativeDatum ξ (d t ξ) (e t ξ)
  have hAm (t : ℝ) : AEStronglyMeasurable (A t) volume := by
    have hc : Continuous (fun q : E × F × F ↦ derivativeDatum q.1 q.2.1 q.2.2) :=
      continuous_derivativeDatum continuous_fst continuous_snd.fst continuous_snd.snd
    exact hc.comp_aestronglyMeasurable
      (aestronglyMeasurable_id.prodMk ((hv t).prodMk (hd t)))
  have hBm (t : ℝ) : AEStronglyMeasurable (B t) volume := by
    have hc : Continuous (fun q : E × F × F ↦ derivativeDatum q.1 q.2.1 q.2.2) :=
      continuous_derivativeDatum continuous_fst continuous_snd.fst continuous_snd.snd
    exact hc.comp_aestronglyMeasurable
      (aestronglyMeasurable_id.prodMk ((hd t).prodMk (he t)))
  have hAB (ξ : E) (t : ℝ) : HasDerivAt (fun s ↦ A s ξ) (B t ξ) t :=
    hasDerivAt_derivativeDatum ξ (hvd ξ t) (hde ξ t)
  have hBc (ξ : E) : Continuous (fun t ↦ B t ξ) :=
    continuous_derivativeDatum continuous_const (hdc ξ) (hec ξ)
  have hsecond := contDiff_one_fourierInv_family A B hAm hBm hAB hBc (by
    intro T hT
    obtain ⟨b, c, a, hb, hb₁, hb₂, hc, hc₁, ha, hbca⟩ := hbound T hT
    refine ⟨fun ξ ↦ c ξ + (2 * Real.pi) * (‖ξ‖ * b ξ),
      fun ξ ↦ a ξ + (2 * Real.pi) * (‖ξ‖ * c ξ),
      hc.add (hb₁.const_mul _), ?_, ha.add (hc₁.const_mul _), ?_⟩
    · convert hc₁.add (hb₂.const_mul (2 * Real.pi)) using 1
      ext ξ
      dsimp only [Pi.add_apply]
      ring
    · intro t ht ξ
      obtain ⟨hvb, hdc', hea⟩ := hbca t ht ξ
      constructor
      · exact (norm_derivativeDatum_le ξ _ _).trans (by
          dsimp only [A]
          nlinarith [mul_le_mul_of_nonneg_left hvb
            (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (norm_nonneg ξ))])
      · exact (norm_derivativeDatum_le ξ _ _).trans (by
          dsimp only [B]
          nlinarith [mul_le_mul_of_nonneg_left hdc'
            (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (norm_nonneg ξ))]))
  have hDf : fderiv ℝ (fun p : ℝ × E ↦ 𝓕⁻ (v p.1) p.2) =
      fun p : ℝ × E ↦ 𝓕⁻ (A p.1) p.2 := by
    funext p
    rw [(hfirst.2 p).2.fderiv]
    simp only [Real.fourierInv_eq, Circle.smul_def, A, derivativeDatum,
      inverseKernelDerivative]
    congr 1
    exact (NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ)).symm
  constructor
  · apply (contDiff_succ_iff_fderiv (n := 1)).mpr
    refine ⟨hfirst.1.differentiable one_ne_zero, ?_, ?_⟩
    · simp
    · rw [hDf]
      exact hsecond.1
  · intro p
    refine ⟨(hfirst.2 p).1, (hfirst.2 p).2, ?_⟩
    rw [hDf]
    exact hsecond.2 p

end PDE.Analysis.Fourier
