/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Sobolev
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Testing

/-!
# Affine transport of the weak divergence equation

Transporting a smooth test by the inverse affine map gives one inverse
derivative factor. The Sobolev chain rule gives the other derivative factor,
and change of variables gives the Jacobian. The resulting common scalar
cancels from the homogeneous equation. Density then recovers all H¹₀ tests.

The construction preserves the coefficient bounds and ellipticity constant,
so De Giorgi's contraction can be used uniformly at every interior scale.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- The affine pullbacks of the coefficients and weak derivatives satisfy the
transported homogeneous equation. This form also preserves specified
representatives, such as a constant comparison matrix. -/
theorem isInteriorWeakDivergenceSolution_of_scaledBall_representatives
    (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (A : Fin n → Fin n → DerivLp n ∞ (ball z (a * r)))
    (u : H¹(ball z (a * r))) (hu : IsInteriorWeakDivergenceSolution A 0 u)
    (B : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) r))
    (v : H¹(ball (0 : ℝ^n) r))
    (hB : ∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
      fun y ↦ A i j (ballHomeomorph z ha y))
    (hv : ∀ i, (wkpCoordinateCLM (singleDerivIndex n i) v : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball 0 r)]
        fun y ↦ a * wkpCoordinateCLM (singleDerivIndex n i) u
          (ballHomeomorph z ha y)) :
    IsInteriorWeakDivergenceSolution B 0 v := by
  apply (isInteriorWeakDivergenceSolution_iff_testFunctions isOpen_ball B 0 v).mpr
  intro φ
  let ψ := scaledBallTestFunction z ha r φ
  have horig : (∑ i, ∑ j, ∫ x, A i j x *
      wkpCoordinateCLM (singleDerivIndex n j) u x *
        (∂[i] ψ.1.toFun) x ∂domainMeasure n (ball z (a * r))) = 0 := by
    have h := hu.equation (testFunctionToH10 ψ)
    simpa only [interiorVariableCoeffForm_testFunction_eq_integral,
      loadFunctional_apply, inner_zero_left] using h
  have hterm (i j : Fin n) :
      (∫ y, B i j y * wkpCoordinateCLM (singleDerivIndex n j) v y *
        (∂[i] φ.1.toFun) y ∂domainMeasure n (ball 0 r)) =
      (a ^ 2 * (a ^ n)⁻¹) *
        ∫ x, A i j x * wkpCoordinateCLM (singleDerivIndex n j) u x *
          (∂[i] ψ.1.toFun) x ∂domainMeasure n (ball z (a * r)) := by
    calc
      _ = a ^ 2 * ∫ y in ball (0 : ℝ^n) r,
          A i j (ballHomeomorph z ha y) *
            wkpCoordinateCLM (singleDerivIndex n j) u (ballHomeomorph z ha y) *
            (∂[i] ψ.1.toFun) (ballHomeomorph z ha y) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hB i j, hv j] with y hb hd
        rw [hb, hd, partialDeriv_scaledBallTestFunction]
        field_simp [ha.ne']
      _ = _ := by
        rw [integral_comp_ballHomeomorph_mul z ha r (fun x ↦
          A i j x * wkpCoordinateCLM (singleDerivIndex n j) u x *
            (∂[i] ψ.1.toFun) x)]
        exact (mul_assoc _ _ _).symm
  rw [← inner_base_testFunction_eq_integral, inner_zero_left]
  simp only [hterm, ← Finset.mul_sum, horig, mul_zero]

/-- Rescale an H¹ homogeneous weak solution between corresponding
balls. The constructed solution satisfies the same weak predicate, with
unchanged essential coefficient bounds and ellipticity constant. -/
theorem exists_scaledBallWeakSolution
    (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (A : Fin n → Fin n → DerivLp n ∞ (ball z (a * r))) {α Λ : ℝ}
    (hA : AEUniformlyElliptic A α) (hΛ : ∀ i j, ‖A i j‖ ≤ Λ)
    (u : H¹(ball z (a * r))) (hu : IsInteriorWeakDivergenceSolution A 0 u) :
    ∃ (B : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) r))
      (v : H¹(ball (0 : ℝ^n) r)),
      AEUniformlyElliptic B α ∧ (∀ i j, ‖B i j‖ ≤ Λ) ∧
      IsInteriorWeakDivergenceSolution B 0 v ∧
      (wkpBaseCoordinateCLM v : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
        fun y ↦ wkpBaseCoordinateCLM u (ballHomeomorph z ha y) := by
  obtain ⟨v, hvbase, hv⟩ := exists_scaledBallSobolevPullback z ha r u
  obtain ⟨B, hB, hBΛ, hrep⟩ := exists_scaledBallCoefficientPullback z ha r A hA hΛ
  exact ⟨B, v, hB, hBΛ,
    isInteriorWeakDivergenceSolution_of_scaledBall_representatives z ha r A u hu B v hrep hv,
    hvbase⟩

end SobolevSpace.GraphSpace.MeanScaling
