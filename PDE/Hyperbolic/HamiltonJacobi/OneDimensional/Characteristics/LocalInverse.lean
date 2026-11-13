/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Characteristics
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.ExactTactic

/-!
# Local Hamilton–Jacobi characteristics from the inverse function theorem

For the one-dimensional Hamilton–Jacobi equation

`u_t + H(u_x) = 0`, `u(0, x) = φ(x)`,

the characteristic map is

`(t, ξ) ↦ (t, ξ + t H'(φ'(ξ)))`.

At every point of the initial line its derivative is invertible. The inverse
function theorem therefore supplies a local `C¹` footpoint map. After
restricting to the open set where the characteristic Jacobian is nonzero, the
general calculations in `OneDimensional.Characteristics` produce a local
classical solution with the prescribed initial trace.

The local inversion is Lemma 2 (local invertibility) of Evans, §3.2.4, on the initial line
`t = 0`, where the noncharacteristic condition (35) holds automatically. The local solution is
Theorem 2 there.

## Main results

* `characteristicMap`, `hasFDerivAt_characteristicMap`: the map
  `(t, ξ) ↦ (t, ξ + t H'(φ'(ξ)))` and its derivative, whose determinant is
  the characteristic Jacobian `1 + t H''(φ'(ξ)) φ''(ξ)`.
* `exists_local_footpoint_of_jacobian_ne_zero`: a local `C¹` inverse at any
  nondegenerate characteristic point for `C²` data `H` and `φ`.
* `exists_local_characteristic_solution`: on that neighborhood the
  characteristic candidate is differentiable, solves `u_t + H(u_x) = 0`, and
  equals `φ` on the initial line.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.4, Lemma 2 and Theorem 2; §3.2.5(c), Example 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi1D

noncomputable section

open PDE.Common

open scoped Topology

/-! ## The characteristic map -/

/-- The spacetime characteristic map `(t, ξ) ↦ (t, ξ + t H'(φ'(ξ)))`. -/
def characteristicMap (H φ : ℝ → ℝ) : ℝ^2 → ℝ^2 :=
  fun p ↦ !₂[p 0, p 1 + p 0 * deriv H (deriv φ (p 1))]

/-- The derivative of the spatial characteristic map with respect to its footpoint. -/
def characteristicMapJacobian (H φ : ℝ → ℝ) (p : ℝ^2) : ℝ :=
  1 + p 0 * deriv (deriv H) (deriv φ (p 1)) * deriv (deriv φ) (p 1)

/-- The Fréchet derivative of `characteristicMap`, written as a continuous linear map. -/
def characteristicMapFDeriv
    (H φ : ℝ → ℝ) (p : ℝ^2) : ℝ^2 →L[ℝ] ℝ^2 :=
  (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi ![
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2),
      characteristicMapJacobian H φ p • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) +
        deriv H (deriv φ (p 1)) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)]

private def characteristicMapFDerivEquiv
    (H φ : ℝ → ℝ) (p : ℝ^2)
    (hjac : characteristicMapJacobian H φ p ≠ 0) :
    ℝ^2 ≃L[ℝ] ℝ^2 :=
  let e : ℝ^2 ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  e.trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).skewProd
      (ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 (characteristicMapJacobian H φ p) hjac))
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv H (deriv φ (p 1))))).trans e.symm)

private theorem coe_characteristicMapFDerivEquiv (H φ : ℝ → ℝ) (p : ℝ^2)
    (hjac : characteristicMapJacobian H φ p ≠ 0) :
    ((characteristicMapFDerivEquiv H φ p hjac : ℝ^2 ≃L[ℝ] ℝ^2) : ℝ^2 →L[ℝ] ℝ^2) =
      characteristicMapFDeriv H φ p := by
  ext v i
  fin_cases i <;> simp [characteristicMapFDerivEquiv, characteristicMapFDeriv,
      ContinuousLinearEquiv.unitsEquivAut_apply, EuclideanSpace.equiv, mul_comm]

/-- The displayed map is the Fréchet derivative of `characteristicMap`. -/
theorem hasFDerivAt_characteristicMap {H φ : ℝ → ℝ} (hH' : Differentiable ℝ (deriv H))
    (hφ' : Differentiable ℝ (deriv φ)) (p : ℝ^2) :
    HasFDerivAt (characteristicMap H φ) (characteristicMapFDeriv H φ p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  refine HasFDerivAt.hasFDerivWithinAt ?_
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.congr_fderiv
      (by ext v; simp [characteristicMapFDeriv])
  · have hξ := (hφ' _).hasDerivAt.comp_hasFDerivAt p
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
    have h := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.add
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.mul
        ((hH' _).hasDerivAt.comp_hasFDerivAt p hξ))
    refine h.congr_fderiv ?_
    ext v
    simp only [Fin.isValue, PiLp.proj_apply, EuclideanSpace.coe_proj, Function.comp_apply,
      add_apply, smul_apply, smul_eq_mul, Fin.mk_one, characteristicMapFDeriv,
      characteristicMapJacobian, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_pi',
      ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    ring

/-! ## Local inversion -/

private theorem contDiff_characteristicMap
    {H φ : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (characteristicMap H φ) := by
  have hH' : ContDiff ℝ 1 (deriv H) := by simpa using hH.deriv' (n := 1)
  have hφ' : ContDiff ℝ 1 (deriv φ) := by simpa using hφ.deriv' (n := 1)
  refine (contDiff_piLp (p := (2 : ENNReal))).2 fun i ↦ ?_
  have ht : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 0) := by cas
  have hx : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 1) := by cas
  fin_cases i
  · exact ht
  · exact hx.add (ht.mul (hH'.comp (hφ'.comp hx)))

private theorem continuous_characteristicMapJacobian
    {H φ : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 2 φ) :
    Continuous (characteristicMapJacobian H φ) := by
  have ht : Continuous (fun p : ℝ^2 ↦ p 0) := (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous
  have hx : Continuous (fun p : ℝ^2 ↦ p 1) := (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  have hH' : ContDiff ℝ 1 (deriv H) := by simpa using hH.deriv' (n := 1)
  have hφ' : ContDiff ℝ 1 (deriv φ) := by simpa using hφ.deriv' (n := 1)
  exact continuous_const.add ((ht.mul (hH'.continuous_deriv_one.comp
    ((hφ.continuous_deriv (hn := by simp)).comp hx))).mul (hφ'.continuous_deriv_one.comp hx))

/-- A nondegenerate characteristic point has a local `C¹` footpoint map. -/
theorem exists_local_footpoint_of_jacobian_ne_zero (H φ : ℝ → ℝ) (p0 : ℝ^2) (hH : ContDiff ℝ 2 H)
    (hφ : ContDiff ℝ 2 φ) (hp0Jac : characteristicMapJacobian H φ p0 ≠ 0) :
    ∃ U : Set ℝ^2, IsOpen U ∧ characteristicMap H φ p0 ∈ U ∧ ∃ ξ : ℝ^2 → ℝ, IsFootpointOn H φ ξ U ∧
      (∀ x ∈ U, ContDiffAt ℝ 1 ξ x) ∧ (∀ x ∈ U, footpointJacobian H φ ξ x ≠ 0) := by
  have hMap : ContDiff ℝ 1 (characteristicMap H φ) := contDiff_characteristicMap hH hφ
  have hD (p) (hp : characteristicMapJacobian H φ p ≠ 0) : HasFDerivAt (characteristicMap H φ)
      ((characteristicMapFDerivEquiv H φ p hp : ℝ^2 ≃L[ℝ] ℝ^2) : ℝ^2 →L[ℝ] ℝ^2) p := by
    simpa only [coe_characteristicMapFDerivEquiv] using hasFDerivAt_characteristicMap
      (ContDiff.differentiable_deriv_two hH) (ContDiff.differentiable_deriv_two hφ) p
  -- The inverse-function chart, restricted to the points with nonzero Jacobian.
  let e : OpenPartialHomeomorph ℝ^2 ℝ^2 :=
    (hMap.contDiffAt.toOpenPartialHomeomorph _ (hD p0 hp0Jac) one_ne_zero).restrOpen
      {p | characteristicMapJacobian H φ p ≠ 0}
      (isOpen_ne_fun (continuous_characteristicMapJacobian hH hφ) continuous_const)
  have hreg {x} (hx : x ∈ e.target) : characteristicMapJacobian H φ (e.symm x) ≠ 0 :=
    (e.map_target hx).2
  have hinv {x} (hx : x ∈ e.target) : characteristicMap H φ (e.symm x) = x := e.right_inv hx
  have htime {x} (hx : x ∈ e.target) : (e.symm x) 0 = x 0 := by
    simpa [characteristicMap] using congrArg (· 0) (hinv hx)
  refine ⟨e.target, e.open_target, e.map_source
    ⟨hMap.contDiffAt.mem_toOpenPartialHomeomorph_source (hD p0 hp0Jac) one_ne_zero, hp0Jac⟩,
    fun x ↦ (e.symm x) 1, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · simpa [characteristicMap, htime hx] using (congrArg (· 1) (hinv hx)).symm
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffAt.comp x
      (e.contDiffAt_symm hx (hD _ (hreg hx)) hMap.contDiffAt)
  · simpa [footpointJacobian, characteristicMapJacobian, htime hx] using hreg hx

/-- A nondegenerate characteristic point has a local classical Hamilton–Jacobi solution. -/
theorem exists_local_characteristic_solution_of_jacobian_ne_zero (H φ : ℝ → ℝ) (p0 : ℝ^2)
    (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 2 φ) (hjac : characteristicMapJacobian H φ p0 ≠ 0) :
    ∃ U : Set ℝ^2, IsOpen U ∧ characteristicMap H φ p0 ∈ U ∧
      ∃ ξ : ℝ^2 → ℝ,
        (∀ x ∈ U,
          DifferentiableAt ℝ (characteristicSolution H φ ξ) x) ∧
        (∀ x ∈ U,
          (∂[(0 : Fin 2)] (characteristicSolution H φ ξ)) x +
            H ((∂[(1 : Fin 2)] (characteristicSolution H φ ξ)) x) = 0) ∧
        Set.EqOn (characteristicSolution H φ ξ)
          (fun x ↦ φ (x 1)) (U ∩ initialTimeSlice) := by
  obtain ⟨U, hU, hx₀, ξ, hrel, hξ, _⟩ :=
    exists_local_footpoint_of_jacobian_ne_zero H φ p0 hH hφ hjac
  have hH0 : Differentiable ℝ H := hH.differentiable (by simp)
  have hφ0 : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hH1 := ContDiff.differentiable_deriv_two hH
  have hφ1 := ContDiff.differentiable_deriv_two hφ
  have hξDiff : ∀ x ∈ U, DifferentiableAt ℝ ξ x := fun x hx ↦ (hξ x hx).differentiableAt (by simp)
  exact ⟨U, hU, hx₀, ξ, fun x hx ↦ differentiableAt_characteristicSolution hH0 hH1 hφ0 hφ1
    (hξDiff x hx), characteristicSolution_residual_on hH0 hH1 hφ0 hφ1 hU hξDiff hrel,
    characteristicSolution_initial_on hrel⟩

/-- Before the first characteristic degeneracy, a local classical solution exists near
every point of the characteristic flow. -/
theorem exists_local_characteristic_solution_before_degeneracyTime (H φ : ℝ → ℝ) (p0 : ℝ^2)
    (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 2 φ) (ht0 : 0 ≤ p0 0)
    (ht : (p0 0 : WithTop ℝ) < firstCharacteristicDegeneracyTime H φ) :
    ∃ U : Set ℝ^2, IsOpen U ∧ characteristicMap H φ p0 ∈ U ∧
      ∃ ξ : ℝ^2 → ℝ,
        (∀ x ∈ U, DifferentiableAt ℝ (characteristicSolution H φ ξ) x) ∧
        (∀ x ∈ U,
          (∂[(0 : Fin 2)] (characteristicSolution H φ ξ)) x +
            H ((∂[(1 : Fin 2)] (characteristicSolution H φ ξ)) x) = 0) ∧
        Set.EqOn (characteristicSolution H φ ξ)
          (fun x ↦ φ (x 1)) (U ∩ initialTimeSlice) :=
  exists_local_characteristic_solution_of_jacobian_ne_zero H φ p0 hH hφ
    (characteristicJacobian_ne_zero_of_lt_firstDegeneracyTime H φ ht0 ht (p0 1))

/-- Near each point of the initial line there is a local classical solution with trace `φ`. -/
theorem exists_local_characteristic_solution (H φ : ℝ → ℝ) (x₀ : ℝ) (hH : ContDiff ℝ 2 H)
    (hφ : ContDiff ℝ 2 φ) :
    ∃ U : Set ℝ^2, IsOpen U ∧ !₂[0, x₀] ∈ U ∧
      ∃ ξ : ℝ^2 → ℝ,
        (∀ x ∈ U, DifferentiableAt ℝ (characteristicSolution H φ ξ) x) ∧
        (∀ x ∈ U,
          (∂[(0 : Fin 2)] (characteristicSolution H φ ξ)) x +
            H ((∂[(1 : Fin 2)] (characteristicSolution H φ ξ)) x) = 0) ∧
        Set.EqOn (characteristicSolution H φ ξ)
          (fun x ↦ φ (x 1)) (U ∩ initialTimeSlice) := by
  simpa [characteristicMap] using
    exists_local_characteristic_solution_of_jacobian_ne_zero H φ !₂[0, x₀] hH hφ
      (by simp [characteristicMapJacobian])

end

end HamiltonJacobi1D
