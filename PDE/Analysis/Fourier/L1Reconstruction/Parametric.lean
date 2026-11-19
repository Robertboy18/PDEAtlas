/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ParametricIntegral.ContinuousDerivative
public import PDE.Analysis.Fourier.L1Reconstruction

/-!
# Joint derivatives of a parameter-dependent inverse Fourier integral

The derivative splits into the derivative of the Fourier datum and the first
frequency moment from differentiating the inverse character. All formulas use
Mathlib's phase `exp(2πi⟨ξ,x⟩)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory FourierTransform
open scoped Topology

namespace PDE.Analysis.Fourier

section Kernel

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

/-- The joint time-space derivative of a single inverse Fourier integrand.
Its two inputs are the Fourier value and its time derivative. -/
def inverseKernelDerivative (ξ : E) (p : ℝ × E) (v d : F) :
    (ℝ × E) →L[ℝ] F :=
  (Real.fourierChar (inner ℝ ξ p.2) : ℂ) •
    ((ContinuousLinearMap.fst ℝ ℝ E).smulRight d +
      (2 * Real.pi * Complex.I) •
        ((innerSL ℝ ξ).comp (ContinuousLinearMap.snd ℝ ℝ E)).smulRight v)

/-- Evaluation separates the time and spatial components of the derivative. -/
@[simp]
theorem inverseKernelDerivative_apply (ξ : E) (p q : ℝ × E) (v d : F) :
    inverseKernelDerivative ξ p v d q =
      (Real.fourierChar (inner ℝ ξ p.2) : ℂ) •
        (q.1 • d + (2 * Real.pi * Complex.I) • (inner ℝ ξ q.2 • v)) := rfl

/-- The kernel derivative depends continuously on frequency, position, value,
and time derivative. -/
theorem continuous_inverseKernelDerivative {X : Type*} [TopologicalSpace X]
    {ξ : X → E} {p : X → ℝ × E} {v d : X → F}
    (hξ : Continuous ξ) (hp : Continuous p) (hv : Continuous v) (hd : Continuous d) :
    Continuous (fun x ↦ inverseKernelDerivative (ξ x) (p x) (v x) (d x)) := by
  have hphase : Continuous (fun x ↦
      (Real.fourierChar (inner ℝ (ξ x) (p x).2) : ℂ)) := by fun_prop
  have htime : Continuous (fun x ↦
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight
        ((Real.fourierChar (inner ℝ (ξ x) (p x).2) : ℂ) • d x)) :=
    isBoundedBilinearMap_smulRight.continuous.comp
      (continuous_const.prodMk (hphase.smul hd))
  have hspace : Continuous (fun x ↦
      ((innerSL ℝ (ξ x)).comp (ContinuousLinearMap.snd ℝ ℝ E)).smulRight
        (((Real.fourierChar (inner ℝ (ξ x) (p x).2) : ℂ) *
          (2 * Real.pi * Complex.I)) • v x)) :=
    isBoundedBilinearMap_smulRight.continuous.comp
      ((((innerSL ℝ).continuous.comp hξ).clm_comp continuous_const).prodMk
        ((hphase.mul continuous_const).smul hv))
  convert htime.add hspace using 1
  funext x
  apply ContinuousLinearMap.ext
  intro q
  change (Real.fourierChar (inner ℝ (ξ x) (p x).2) : ℂ) •
      (q.1 • d x + (2 * Real.pi * Complex.I) • (inner ℝ (ξ x) q.2 • v x)) =
    q.1 • ((Real.fourierChar (inner ℝ (ξ x) (p x).2) : ℂ) • d x) +
      inner ℝ (ξ x) q.2 •
        (((Real.fourierChar (inner ℝ (ξ x) (p x).2) : ℂ) *
          (2 * Real.pi * Complex.I)) • v x)
  module

/-- Differentiating a Fourier integrand gives the joint Fréchet
derivative, including its time component. -/
theorem hasFDerivAt_inverseKernel
    (v : ℝ → F) (ξ : E) (p : ℝ × E) {d : F}
    (hv : HasDerivAt v d p.1) :
    HasFDerivAt (fun q : ℝ × E ↦
      (Real.fourierChar (inner ℝ ξ q.2) : ℂ) • v q.1)
      (inverseKernelDerivative ξ p (v p.1) d) p := by
  have hphase := (Real.hasDerivAt_fourierChar (inner ℝ ξ p.2)).hasFDerivAt.comp p
    ((innerSL ℝ ξ).hasFDerivAt.comp p hasFDerivAt_snd)
  have htime := hv.hasFDerivAt.comp p hasFDerivAt_fst
  convert hphase.smul htime using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro q
  simp only [inverseKernelDerivative, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply,
    Function.comp_apply]
  simp only [smul_add, smul_smul, Complex.real_smul]
  module

/-- The joint derivative costs one frequency moment and one time derivative. -/
theorem norm_inverseKernelDerivative_le (ξ : E) (p : ℝ × E) (v d : F) :
    ‖inverseKernelDerivative ξ p v d‖ ≤ ‖d‖ + (2 * Real.pi) * ‖ξ‖ * ‖v‖ := by
  let D₀ : (ℝ × E) →L[ℝ] F :=
    (ContinuousLinearMap.fst ℝ ℝ E).smulRight d +
      (2 * Real.pi * Complex.I) •
        ((innerSL ℝ ξ).comp (ContinuousLinearMap.snd ℝ ℝ E)).smulRight v
  change ‖(Real.fourierChar (inner ℝ ξ p.2) : ℂ) • D₀‖ ≤ _
  refine (ContinuousLinearMap.opNorm_smul_le
    (Real.fourierChar (inner ℝ ξ p.2) : ℂ) D₀).trans ?_
  rw [Circle.norm_coe, one_mul]
  dsimp only [D₀]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.norm_fst_le ℝ ℝ E)
  · refine (ContinuousLinearMap.opNorm_smul_le (2 * Real.pi * Complex.I : ℂ)
      (((innerSL ℝ ξ).comp (ContinuousLinearMap.snd ℝ ℝ E)).smulRight v)).trans ?_
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp
    rw [hnorm]
    have hinner : ‖(innerSL ℝ ξ).comp (ContinuousLinearMap.snd ℝ ℝ E)‖ ≤ ‖ξ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _)
          (ContinuousLinearMap.norm_snd_le ℝ ℝ E)).trans_eq (innerSL_apply_norm ℝ ξ))
    nlinarith [mul_le_mul_of_nonneg_right hinner (norm_nonneg v), Real.pi_pos,
      norm_nonneg v, norm_nonneg ξ]

end Kernel

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [hF : NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

/-- The joint derivative uses the norm topology on its space of continuous
linear maps when applying the Bochner integration lemmas. -/
local instance instContinuousENormJointDerivative : ContinuousENorm ((ℝ × E) →L[ℝ] F) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid ((ℝ × E) →L[ℝ] F) inferInstance).toContinuousENorm

/-- Uniform integrable bounds on bounded time intervals give one jointly `C¹`
inverse Fourier integral and its joint derivative. The bound for the value
must have one integrable spatial moment; the time derivative needs no extra moment. -/
theorem contDiff_one_fourierInv_family
    (v d : ℝ → E → F)
    (hv : ∀ t, AEStronglyMeasurable (v t) volume)
    (hd : ∀ t, AEStronglyMeasurable (d t) volume)
    (hder : ∀ ξ t, HasDerivAt (fun u ↦ v u ξ) (d t ξ) t)
    (hcont : ∀ ξ, Continuous (fun t ↦ d t ξ))
    (hbound : ∀ T : ℝ, 0 ≤ T → ∃ b c : E → ℝ,
      Integrable b ∧ Integrable (fun ξ ↦ ‖ξ‖ * b ξ) ∧ Integrable c ∧
        ∀ t : ℝ, |t| ≤ T → ∀ ξ, ‖v t ξ‖ ≤ b ξ ∧ ‖d t ξ‖ ≤ c ξ) :
    ContDiff ℝ 1 (fun p : ℝ × E ↦ 𝓕⁻ (v p.1) p.2) ∧
      ∀ p : ℝ × E,
        Integrable (fun ξ ↦ inverseKernelDerivative ξ p (v p.1 ξ) (d p.1 ξ)) ∧
          HasFDerivAt (fun q : ℝ × E ↦ 𝓕⁻ (v q.1) q.2)
            (∫ ξ, inverseKernelDerivative ξ p (v p.1 ξ) (d p.1 ξ)) p := by
  have hreal : NormedSpace.complexToReal (E := F) = hF :=
    NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ)
  cases hreal
  let K (p : ℝ × E) (ξ : E) :=
    (Real.fourierChar (inner ℝ ξ p.2) : ℂ) • v p.1 ξ
  let D (p : ℝ × E) (ξ : E) :=
    inverseKernelDerivative ξ p (v p.1 ξ) (d p.1 ξ)
  have hKm (p : ℝ × E) : AEStronglyMeasurable (K p) volume :=
    ((Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable.fun_smul (hv p.1))
  have hKi (p : ℝ × E) : Integrable (K p) := by
    obtain ⟨b, c, hb, _, _, hbc⟩ := hbound |p.1| (abs_nonneg _)
    refine hb.mono' (hKm p) (Eventually.of_forall fun ξ ↦ ?_)
    dsimp only [K]
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact (hbc p.1 le_rfl ξ).1
  have hDm (p : ℝ × E) : AEStronglyMeasurable (D p) volume := by
    have h : Continuous (fun q : E × F × F ↦
        inverseKernelDerivative q.1 p q.2.1 q.2.2) :=
      continuous_inverseKernelDerivative continuous_fst continuous_const
        continuous_snd.fst continuous_snd.snd
    exact h.comp_aestronglyMeasurable
      (aestronglyMeasurable_id.prodMk ((hv p.1).prodMk (hd p.1)))
  have hDc : ∀ᵐ ξ, Continuous (fun p ↦ D p ξ) :=
    Eventually.of_forall fun ξ ↦
      continuous_inverseKernelDerivative continuous_const continuous_id
        ((continuous_iff_continuousAt.mpr fun t ↦ (hder ξ t).continuousAt).comp
          continuous_fst)
        ((hcont ξ).comp continuous_fst)
  have hDf : ∀ᵐ ξ, ∀ p, HasFDerivAt (fun q ↦ K q ξ) (D p ξ) p :=
    Eventually.of_forall fun ξ p ↦ hasFDerivAt_inverseKernel
      (fun t ↦ v t ξ) ξ p (hder ξ p.1)
  have hDb (p : ℝ × E) : ∃ s ∈ 𝓝 p, ∃ b : E → ℝ,
      Integrable b ∧ ∀ᵐ ξ, ∀ q ∈ s, ‖D q ξ‖ ≤ b ξ := by
    obtain ⟨b, c, hb, hxb, hc, hbc⟩ :=
      hbound (|p.1| + 1) (by positivity)
    refine ⟨{q : ℝ × E | |q.1| < |p.1| + 1},
      (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simp),
      fun ξ ↦ c ξ + (2 * Real.pi) * (‖ξ‖ * b ξ),
      hc.add (hxb.const_mul _), Eventually.of_forall fun ξ q hq ↦ ?_⟩
    refine (norm_inverseKernelDerivative_le ξ q _ _).trans ?_
    obtain ⟨hvq, hdq⟩ := hbc q.1 (le_of_lt hq) ξ
    have hmul := mul_le_mul_of_nonneg_left hvq
      (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (norm_nonneg ξ))
    nlinarith
  constructor
  · simpa only [Real.fourierInv_eq, Circle.smul_def, K] using
      contDiff_one_integral_of_locally_dominated hKi hDm hDf hDc hDb
  · intro p
    have hDi : Integrable (D p) := by
      obtain ⟨s, hs, b, hb, hDb⟩ := hDb p
      apply hb.mono' (f := D p) (hDm p)
      exact hDb.mono fun ξ hξ ↦ hξ p (mem_of_mem_nhds hs)
    refine ⟨hDi, ?_⟩
    simpa only [Real.fourierInv_eq, Circle.smul_def, K, D] using
      hasFDerivAt_integral_of_locally_dominated hKi hDm hDf hDb p

end PDE.Analysis.Fourier
