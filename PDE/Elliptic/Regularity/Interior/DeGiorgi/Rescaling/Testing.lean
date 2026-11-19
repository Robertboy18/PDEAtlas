/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Geometry
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.DistributionTheory.TestFunction.ProperPrecomposition

/-!
# Smooth tests for affine transport of the interior weak equation

The H¹–H¹₀ weak predicate is equivalent to its smooth test identity
by density. Smooth proper precomposition transports the tests between balls,
and the classical chain rule supplies the inverse spatial factor.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Evaluate the interior bilinear form on a supported smooth test. -/
theorem interiorVariableCoeffForm_testFunction_eq_integral
    (A : Fin n → Fin n → DerivLp n ∞ Ω) (u : H¹(Ω)) (φ : TestFunctionOn n Ω) :
    interiorVariableCoeffForm (multiplicationCoefficientOperator A) u (testFunctionToH10 φ) =
      ∑ i, ∑ j, ∫ x, A i j x * wkpCoordinateCLM (singleDerivIndex n j) u x *
        (∂[i] φ.1.toFun) x ∂domainMeasure n Ω := by
  rw [interiorVariableCoeffForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplicationCoefficientOperator_apply_ae A i j
    (wkpCoordinateCLM (singleDerivIndex n j) u),
    derivCoordCLM_testFunction_apply_ae i φ] with x hx hφ
  rw [hx, hφ]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Smooth testing characterizes the interior weak solution predicate.
Density extends the displayed integral identity to every H¹₀ test. -/
theorem isInteriorWeakDivergenceSolution_iff_testFunctions
    (hΩ : IsOpen Ω) (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω) (u : H¹(Ω)) :
    IsInteriorWeakDivergenceSolution A f u ↔
      ∀ φ : TestFunctionOn n Ω,
        (∑ i, ∑ j, ∫ x, A i j x * wkpCoordinateCLM (singleDerivIndex n j) u x *
          (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) =
            ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω := by
  constructor
  · intro hu φ
    have h := hu.equation (testFunctionToH10 φ)
    simpa only [interiorVariableCoeffForm_testFunction_eq_integral, loadFunctional_apply,
      inner_base_testFunction_eq_integral] using h
  · intro h
    refine ⟨hΩ, ?_⟩
    have heq :
        (interiorVariableCoeffForm (multiplicationCoefficientOperator A) u : H¹₀(Ω) → ℝ) ∘
            testFunctionToH10Linear =
          (loadFunctional f : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear := by
      funext φ
      change interiorVariableCoeffForm (multiplicationCoefficientOperator A) u
          (testFunctionToH10 φ) = loadFunctional f (testFunctionToH10 φ)
      simpa only [interiorVariableCoeffForm_testFunction_eq_integral, loadFunctional_apply,
        inner_base_testFunction_eq_integral] using h φ
    exact fun v ↦ congrFun (denseRange_testFunctionToH10Linear.equalizer
      (interiorVariableCoeffForm (multiplicationCoefficientOperator A) u).continuous
      (loadFunctional f).continuous heq) v

namespace MeanScaling

/-- Transport a smooth test from a centred ball to its affine image. -/
def scaledBallTestFunction (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (φ : TestFunctionOn n (ball (0 : ℝ^n) r)) : TestFunctionOn n (ball z (a * r)) :=
  ⟨TestFunction.precompProper (ballHomeomorph z ha).symm
      (contDiff_scaledBallChart_symm z ha r ⊤)
      (ballHomeomorph z ha).symm.isProperMap φ.1, by
    intro x hx
    have hφ := φ.2 (tsupport_comp_subset_preimage φ.1
      (ballHomeomorph z ha).symm.continuous hx)
    have h := (image_ball_mul z ha r).subset ⟨(ballHomeomorph z ha).symm x, hφ, rfl⟩
    simpa only [Homeomorph.apply_symm_apply] using h⟩

/-- The transported test recovers its original value after the affine map. -/
theorem scaledBallTestFunction_apply (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (φ : TestFunctionOn n (ball (0 : ℝ^n) r)) (y : ℝ^n) :
    (scaledBallTestFunction z ha r φ).1 (ballHomeomorph z ha y) = φ.1 y := by
  change φ.1 ((ballHomeomorph z ha).symm (ballHomeomorph z ha y)) = _
  rw [Homeomorph.symm_apply_apply]

/-- Derivatives of the transported test carry the reciprocal spatial scale. -/
theorem partialDeriv_scaledBallTestFunction (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (φ : TestFunctionOn n (ball (0 : ℝ^n) r)) (i : Fin n) (y : ℝ^n) :
    (∂[i] (scaledBallTestFunction z ha r φ).1.toFun) (ballHomeomorph z ha y) =
      a⁻¹ * (∂[i] φ.1.toFun) y := by
  let T := ballHomeomorph z ha
  have hi : HasFDerivAt (fun x ↦ T.symm x)
      (a⁻¹ • ContinuousLinearMap.id ℝ (ℝ^n)) (T y) := by
    simp only [T, ballHomeomorph_symm_apply]
    exact ((hasFDerivAt_id (ballHomeomorph z ha y)).sub_const z).const_smul a⁻¹
  have hφ := (φ.1.contDiff.differentiable (by simp)).differentiableAt
    (x := T.symm (T y)) |>.hasFDerivAt
  have hc := hφ.comp (T y) hi
  change fderiv ℝ (⇑φ.1 ∘ ⇑T.symm) (T y) (EuclideanSpace.single i 1) = _
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  simp only [T, Homeomorph.symm_apply_apply, PDE.partialDeriv]
  rfl

end MeanScaling
end SobolevSpace.GraphSpace
