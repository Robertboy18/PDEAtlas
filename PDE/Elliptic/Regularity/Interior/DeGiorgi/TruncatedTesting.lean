/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Elliptic.Regularity.Localization.CutoffEquation.ZeroBoundaryCutoff
public import PDE.Spaces.Sobolev.Calculus.Composition.PositivePart.Domain
public import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore

/-!
# Testing a weak elliptic equation with a superlevel truncation

The weak derivative of the positive part is the original derivative on its
positive set and zero elsewhere. Consequently, when testing with a smooth
cutoff times the positive part, the principal form only sees the truncated
gradient. Subtracting a constant gives the same identity at every superlevel.

This is the testing step in the De Giorgi energy argument. The state belongs
only to `H¹`; its continuity and any regularity of the coefficients are unnecessary.
The domain extension atlas is used by the positive-part chain rule.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal InnerProductSpace Distributions

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- A cutoff of the positive part only tests the gradient on the positive set.
No ellipticity or weak equation is needed for this identity. -/
theorem interiorVariableCoeffForm_posPart_cutoff
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (u : H¹(Ω))
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part u
    let v := cutoffH1ToH10 hΩ.isOpen η hη T
    interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) T v := by
  classical
  dsimp only
  let T : H¹(Ω) := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part u
  let v : H¹₀(Ω) := cutoffH1ToH10 hΩ.isOpen η hη T
  change interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
    interiorVariableCoeffForm (multiplicationCoefficientOperator a) T v
  simp only [interiorVariableCoeffForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hv :
      (derivCoordCLM i v : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        η.toFun x * wkpCoordinateCLM (singleDerivIndex n i) T x +
          iteratedPartialDeriv [i] η.toFun x * wkpBaseCoordinateCLM T x :=
    cutoffCLM_singleDeriv_apply_ae η T i
  filter_upwards [
    multiplicationCoefficientOperator_apply_ae a i j
      (wkpCoordinateCLM (singleDerivIndex n j) u),
    multiplicationCoefficientOperator_apply_ae a i j
      (wkpCoordinateCLM (singleDerivIndex n j) T),
    lipschitzCompositionOn_posPart_derivative_ae u i,
    lipschitzCompositionOn_posPart_derivative_ae u j,
    lipschitzCompositionOn_posPart_coordinate_ae u (baseIndex n 1), hv]
      with x hleft hright hi hj hbase htest
  change wkpCoordinateCLM (singleDerivIndex n i) T x =
    (if 0 < wkpBaseCoordinateCLM u x then
      wkpCoordinateCLM (singleDerivIndex n i) u x else 0) at hi
  change wkpCoordinateCLM (singleDerivIndex n j) T x =
    (if 0 < wkpBaseCoordinateCLM u x then
      wkpCoordinateCLM (singleDerivIndex n j) u x else 0) at hj
  change wkpBaseCoordinateCLM T x =
    (if 0 < wkpBaseCoordinateCLM u x then wkpBaseCoordinateCLM u x else 0) at hbase
  by_cases hx : 0 < wkpBaseCoordinateCLM u x
  · simp only [ite_eq_left hx] at hj
    rw [hleft, hright, hj]
  · simp only [ite_eq_right hx] at hi hj hbase
    simp only [hi, hbase, mul_zero, add_zero] at htest
    simp only [htest, inner_zero_right]

/-- Every superlevel truncation is an admissible cutoff test in the weak
equation. The equality uses its own gradient in the principal form. It does not
claim that the truncation solves the original equation against arbitrary tests. -/
theorem IsInteriorWeakDivergenceSolution.superlevel_cutoff_equation
    [IsFiniteMeasure (domainMeasure n Ω)]
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (f : DerivLp n 2 Ω) (u : H¹(Ω))
    (hu : IsInteriorWeakDivergenceSolution a f u) (k : ℝ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
      (u - wkpConstant k)
    let v := cutoffH1ToH10 hΩ.isOpen η hη T
    interiorVariableCoeffForm (multiplicationCoefficientOperator a) T v =
      loadFunctional f v := by
  let U : H¹(Ω) := u - wkpConstant k
  let T : H¹(Ω) := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U
  let v : H¹₀(Ω) := cutoffH1ToH10 hΩ.isOpen η hη T
  have hD (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n j) U =
        wkpCoordinateCLM (singleDerivIndex n j) u := by
    have hc : wkpCoordinateCLM (singleDerivIndex n j)
        (wkpConstant (n := n) (p := 2) (Ω := Ω) k) = 0 :=
      Lp.ext ((wkpConstant_deriv_ae k j).trans
        (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)).symm)
    simp only [U, map_sub, hc, sub_zero]
  change interiorVariableCoeffForm (multiplicationCoefficientOperator a) T v = _
  calc
    _ = interiorVariableCoeffForm (multiplicationCoefficientOperator a) U v :=
      (interiorVariableCoeffForm_posPart_cutoff a U η hη).symm
    _ = interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v := by
      simp only [interiorVariableCoeffForm_apply, hD]
    _ = _ := hu.equation v

end SobolevSpace.GraphSpace
