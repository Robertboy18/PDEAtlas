/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics
public import PDE.Problem.Equation.Satisfaction
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.ExactTactic

/-!
# Local characteristic solutions of scalar conservation laws

The characteristic map `(t, ξ) ↦ (t, ξ + t * a(u₀(ξ)))` has a local differentiable
inverse wherever its Jacobian is nonzero. Composing the inverse footpoint with `u₀`
gives a solution of `u_t + a(u) u_x = 0` on an open spacetime neighborhood.

Before `conservationShockTime`, every characteristic point is nondegenerate. The result constructs a
local branch through each such point.

This is Evans, §3.2.5, Example 5, made local: the inverse footpoint gives the implicit formula
(61), and the Jacobian is the expression `1 + t g'(x - tF'(u)) F''(u)` whose nonvanishing Evans
requires there, with `a = F'` and `u₀ = g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.5, Example 5, equations (58)-(61).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

noncomputable section

open PDE.Common

open scoped Topology

/-!
## Characteristic map and its derivative

We consider the characteristic map in spacetime coordinates

`(t, ξ) ↦ (t, ξ + t * a(u₀(ξ)))`.

Its Jacobian is lower-triangular with diagonal entry

`1 + t * a'(u₀(ξ)) * u₀'(ξ)`.
-/

/-- Characteristic map `(t,ξ) ↦ (t, ξ + t * a(u₀(ξ)))` as a map `ℝ^2 → ℝ^2`. -/
noncomputable def conservationCharMap (a u₀ : ℝ → ℝ) : ℝ^2 → ℝ^2 :=
  fun p ↦ !₂[p 0, p 1 + p 0 * a (u₀ (p 1))]

/-- The Jacobian diagonal entry `1 + t * a'(u₀(ξ)) * u₀'(ξ)` for `conservationCharMap`. -/
noncomputable def conservationCharDenom (a u₀ : ℝ → ℝ) (p : ℝ^2) : ℝ :=
  1 + p 0 * deriv a (u₀ (p 1)) * deriv u₀ (p 1)

/-- The Fréchet derivative of `conservationCharMap` at `p`, as a continuous linear map. -/
noncomputable def conservationCharDeriv (a u₀ : ℝ → ℝ) (p : ℝ^2) : ℝ^2 →L[ℝ] ℝ^2 :=
  (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi ![
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2),
      conservationCharDenom a u₀ p • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) +
        a (u₀ (p 1)) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)]

/-- `HasFDerivAt` for `conservationCharMap`. -/
theorem hasFDerivAt_conservationCharMap {a u₀ : ℝ → ℝ} (ha : Differentiable ℝ a)
    (hu₀ : Differentiable ℝ u₀) (p : ℝ^2) :
    HasFDerivAt (conservationCharMap a u₀) (conservationCharDeriv a u₀ p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  refine HasFDerivAt.hasFDerivWithinAt ?_
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.congr_fderiv
      (by ext v; simp [conservationCharDeriv])
  · have hu := (hu₀ _).hasDerivAt.comp_hasFDerivAt p
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
    have h := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.add
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.mul
        ((ha _).hasDerivAt.comp_hasFDerivAt p hu))
    refine h.congr_fderiv ?_
    ext v
    simp only [Fin.isValue, PiLp.proj_apply, EuclideanSpace.coe_proj, Function.comp_apply,
      add_apply, smul_apply, smul_eq_mul, Fin.mk_one, conservationCharDeriv, conservationCharDenom,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_pi', ContinuousLinearEquiv.coe_coe,
      PiLp.continuousLinearEquiv_symm_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

/-!
## Local inverse and the footpoint map
-/

private theorem contDiff_conservationCharMap {a u₀ : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hu₀ : ContDiff ℝ 1 u₀) :
    ContDiff ℝ 1 (conservationCharMap a u₀) := by
  refine (contDiff_piLp (p := (2 : ENNReal))).2 fun i ↦ ?_
  have ht : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 0) := by cas
  have hx : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 1) := by cas
  fin_cases i
  · exact ht
  · exact hx.add (ht.mul (ha.comp (hu₀.comp hx)))

private theorem conservationCharDenom_continuous {a u₀ : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hu₀ : ContDiff ℝ 1 u₀) :
    Continuous (conservationCharDenom a u₀) := by
  have hx : Continuous (fun p : ℝ^2 ↦ p 1) := (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  exact continuous_const.add (((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.mul
    (ha.continuous_deriv_one.comp (hu₀.continuous.comp hx))).mul (hu₀.continuous_deriv_one.comp hx))

/-- A nonzero characteristic Jacobian gives a local C¹ inverse through the
specified characteristic point. -/
theorem exists_local_contDiff_footpointMap_of_denom_ne_zero (a u₀ : ℝ → ℝ) (p0 : ℝ^2)
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) (hnonzero : conservationCharDenom a u₀ p0 ≠ 0) :
    ∃ U : Set ℝ^2, IsOpen U ∧ conservationCharMap a u₀ p0 ∈ U ∧ ∃ ξ : ℝ^2 → ℝ,
      ξ (conservationCharMap a u₀ p0) = p0 1 ∧ ConservationFootRelationOn a u₀ ξ U ∧
      (∀ x ∈ U, ContDiffAt ℝ 1 ξ x) := by
  have hMap := contDiff_conservationCharMap ha hu₀
  let eCoord : ℝ^2 ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let eDeriv (p : ℝ^2) (hp : conservationCharDenom a u₀ p ≠ 0) : ℝ^2 ≃L[ℝ] ℝ^2 :=
    eCoord.trans (((ContinuousLinearEquiv.refl ℝ ℝ).skewProd
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hp))
      (ContinuousLinearMap.toSpanSingleton ℝ (a (u₀ (p 1))))).trans eCoord.symm)
  have hD (p) (hp : conservationCharDenom a u₀ p ≠ 0) :
      HasFDerivAt (conservationCharMap a u₀) (eDeriv p hp : ℝ^2 →L[ℝ] ℝ^2) p := by
    refine (hasFDerivAt_conservationCharMap (ha.differentiable one_ne_zero)
      (hu₀.differentiable one_ne_zero) p).congr_fderiv ?_
    ext v i
    fin_cases i <;> simp [conservationCharDeriv, eDeriv, eCoord,
      ContinuousLinearEquiv.unitsEquivAut_apply, EuclideanSpace.equiv, mul_comm]
  -- The inverse-function chart, restricted to the points with nonzero Jacobian.
  let e : OpenPartialHomeomorph ℝ^2 ℝ^2 :=
    (hMap.contDiffAt.toOpenPartialHomeomorph _ (hD p0 hnonzero) one_ne_zero).restrOpen
      {p | conservationCharDenom a u₀ p ≠ 0}
      (isOpen_ne_fun (conservationCharDenom_continuous ha hu₀) continuous_const)
  have hp0 : p0 ∈ e.source :=
    ⟨hMap.contDiffAt.mem_toOpenPartialHomeomorph_source (hD p0 hnonzero) one_ne_zero, hnonzero⟩
  have hinv {x} (hx : x ∈ e.target) : conservationCharMap a u₀ (e.symm x) = x := e.right_inv hx
  refine ⟨e.target, e.open_target, e.map_source hp0, fun x ↦ (e.symm x) 1,
    congrArg (· 1) (e.left_inv hp0), fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have htime : (e.symm x) 0 = x 0 := by
      simpa [conservationCharMap] using congrArg (· 0) (hinv hx)
    simpa [conservationCharMap, htime] using (congrArg (· 1) (hinv hx)).symm
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffAt.comp x
      (e.contDiffAt_symm hx (hD _ (e.map_target hx).2) hMap.contDiffAt)

/-- A nonzero characteristic Jacobian gives a local differentiable inverse through the
specified characteristic point. -/
theorem exists_local_footpointMap_of_denom_ne_zero (a u₀ : ℝ → ℝ) (p0 : ℝ^2) (ha : ContDiff ℝ 1 a)
    (hu₀ : ContDiff ℝ 1 u₀) (hnonzero : conservationCharDenom a u₀ p0 ≠ 0) :
    ∃ U : Set ℝ^2, IsOpen U ∧ conservationCharMap a u₀ p0 ∈ U ∧ ∃ ξ : ℝ^2 → ℝ,
      ξ (conservationCharMap a u₀ p0) = p0 1 ∧ ConservationFootRelationOn a u₀ ξ U ∧
      (∀ x ∈ U, DifferentiableAt ℝ ξ x) := by
  obtain ⟨U, hU, hp, ξ, hξ, hrel, hC⟩ :=
    exists_local_contDiff_footpointMap_of_denom_ne_zero a u₀ p0 ha hu₀ hnonzero
  exact ⟨U, hU, hp, ξ, hξ, hrel, fun x hx ↦ (hC x hx).differentiableAt_one⟩

/-!
## Local PDEProblem residual witness near `t = 0`

Using the IFT footpoint map, we obtain a local `SatisfiesPDEProblem` witness

`u(t,x) = u₀(ξ(t,x))`

for `u_t + a(u) u_x = 0` on the neighborhood `U`, together with differentiability of the
returned footpoint map on `U`.
-/

/-- Local IVP restricted to a spacetime set `U`. -/
noncomputable def conservationLocalIVP (a u₀ : ℝ → ℝ) (U : Set ℝ^2) :
  PDEProblem ℝ^2 ℝ :=
  { eqns := [
      { Output := ℝ
        operator := fun u x ↦ (∂[(0 : Fin 2)] u) x + a (u x) * (∂[(1 : Fin 2)] u) x
        rhs := fun _ ↦ 0
        domain := U }
    ]
    sideConditions := [
      { Output := ℝ
        operator := id
        rhs := fun x ↦ u₀ (x 1)
        domain := U ∩ initialTimeSlice }
    ] }

/-- A nondegenerate characteristic point has a local conservation-law solution with
initial trace `u₀` on the part of the neighborhood at time zero. -/
theorem exists_local_solution_of_denom_ne_zero (a u₀ : ℝ → ℝ) (p0 : ℝ^2) (ha : ContDiff ℝ 1 a)
    (hu₀ : ContDiff ℝ 1 u₀) (hnonzero : conservationCharDenom a u₀ p0 ≠ 0) :
    ∃ U : Set ℝ^2, IsOpen U ∧ conservationCharMap a u₀ p0 ∈ U ∧
      ∃ ξ : ℝ^2 → ℝ,
        ξ (conservationCharMap a u₀ p0) = p0 1 ∧
        ConservationFootRelationOn a u₀ ξ U ∧
        (∀ x ∈ U, DifferentiableAt ℝ ξ x) ∧
        SatisfiesPDEProblem (conservationLocalIVP a u₀ U)
          (conservationSolutionFromFoot u₀ ξ) := by
  obtain ⟨U, hU, hp0, ξ, hbase, hrel, hξ⟩ :=
    exists_local_footpointMap_of_denom_ne_zero a u₀ p0 ha hu₀ hnonzero
  refine ⟨U, hU, hp0, ξ, hbase, hrel, hξ, fun eqn heqn x hx ↦ ?_⟩
  simp only [conservationLocalIVP, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at heqn
  rcases heqn with rfl | rfl
  · exact hrel.satisfies_pde_at hU (ha.differentiable one_ne_zero)
      (hu₀.differentiable one_ne_zero) hx (hξ x hx)
  · exact conservationSolutionFromFoot_initial x hx.2 (hrel x hx.1)

/-- Before the first characteristic degeneracy, a local conservation-law solution exists
through every characteristic point. The footpoint at the central point is the prescribed label. -/
theorem exists_local_solution_before_shockTime (a u₀ : ℝ → ℝ) (p0 : ℝ^2)
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) (ht0 : 0 ≤ p0 0)
    (hlt : (p0 0 : WithTop ℝ) < conservationShockTime a u₀) :
    ∃ U : Set ℝ^2, IsOpen U ∧ conservationCharMap a u₀ p0 ∈ U ∧
      ∃ ξ : ℝ^2 → ℝ,
        ξ (conservationCharMap a u₀ p0) = p0 1 ∧
        ConservationFootRelationOn a u₀ ξ U ∧
        (∀ x ∈ U, DifferentiableAt ℝ ξ x) ∧
        SatisfiesPDEProblem (conservationLocalIVP a u₀ U)
          (conservationSolutionFromFoot u₀ ξ) :=
  exists_local_solution_of_denom_ne_zero a u₀ p0 ha hu₀
    (conservationDenom_ne_zero_of_lt_shockTime a u₀ ht0 hlt (p0 1))

/-- Near every point of the initial line, the characteristic construction gives a local
solution with initial data `u₀`. -/
theorem exists_local_solution_witness (a u₀ : ℝ → ℝ) (x₀ : ℝ)
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) :
    ∃ U : Set ℝ^2, IsOpen U ∧ !₂[0, x₀] ∈ U ∧ ∃ ξ : ℝ^2 → ℝ, ConservationFootRelationOn a u₀ ξ U ∧
      (∀ x ∈ U, DifferentiableAt ℝ ξ x) ∧
      SatisfiesPDEProblem (conservationLocalIVP a u₀ U) (conservationSolutionFromFoot u₀ ξ) := by
  obtain ⟨U, hU, hp0, ξ, _, hrel, hξ, hu⟩ :=
    exists_local_solution_of_denom_ne_zero a u₀ !₂[0, x₀] ha hu₀
      (by simp [conservationCharDenom])
  exact ⟨U, hU, by simpa [conservationCharMap] using hp0, ξ, hrel, hξ, hu⟩

end

end PDE.Hyperbolic.ConservationLaw.Scalar
