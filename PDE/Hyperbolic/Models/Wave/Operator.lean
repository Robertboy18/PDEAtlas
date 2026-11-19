/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Problem.Equation.Satisfaction
public import PDE.FDeriv.PartialDeriv

/-!
# Wave operator and residual equations

We define the coordinate wave operator and the homogeneous and
nonhomogeneous residual problems.
The propagation speed is normalized to `c = 1`, so the operator is `u_tt - Δu`.

The operator is `□u` of Evans, §2.4, and the two problems are the wave equation (1) and the
nonhomogeneous wave equation (2) there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4, equations (1)-(2) and the notation `□u`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (PDEEquation PDEProblem SatisfiesPDEProblem)

namespace WaveEquation

variable {n : ℕ}

/-- The wave-operator expression: second time derivative minus the spatial Laplacian.

This is a total Lean expression built from total derivative operators; classical use requires the
corresponding second differentiability hypotheses. -/
noncomputable def waveOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ^(n + 1) → E) (xt : ℝ^(n + 1)) : E :=
  (∂[0] (fun p ↦ (∂[0] u) p)) xt -
    ∑ i : Fin n, (∂[i.succ] (fun p ↦ (∂[i.succ] u) p)) xt

/-- Constants are annihilated by the wave operator: both second derivatives vanish. -/
@[simp]
theorem waveOperator_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E)
    (xt : ℝ^(n + 1)) :
    waveOperator (n := n) (fun _ ↦ c) xt = 0 := by
  simp [waveOperator]

/-- The non-homogeneous wave-equation residual equation, `u_tt - Δu = f`. -/
noncomputable def nonhomogeneousWaveEquation
    (U : Set (ℝ^(n + 1)))
    (f : ℝ^(n + 1) → ℝ) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  { eqns := [
      { Output := ℝ
        operator := fun u x ↦ waveOperator u x
        rhs := f
        domain := U
      }
    ],
    sideConditions := []
  }

/-- Projection from the bundled nonhomogeneous wave equation to the residual
`u_tt - Δu = f` on `U`. -/
theorem nonhomogeneousWaveEquation.residual_eq {U : Set (ℝ^(n + 1))} {f u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u) {x : ℝ^(n + 1)}
    (hx : x ∈ U) :
    waveOperator (n := n) u x = f x := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := fun u x ↦ waveOperator (n := n) u x
      rhs := f
      domain := U }
  have heqn : eqn ∈ (nonhomogeneousWaveEquation (n := n) U f).eqns := by
    simp [eqn, nonhomogeneousWaveEquation]
  have h := PDE.SatisfiesPDEProblem.eqn
      (pde := nonhomogeneousWaveEquation (n := n) U f) (u := u) hu heqn hx
  simpa [eqn] using h

/-- Constructor for the bundled nonhomogeneous wave equation from the residual. -/
theorem nonhomogeneousWaveEquation.of_residual {U : Set (ℝ^(n + 1))} {f u : ℝ^(n + 1) → ℝ}
    (hres : ∀ x ∈ U, waveOperator (n := n) u x = f x) :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u := by
  refine PDE.SatisfiesPDEProblem.mk ?_ ?_
  · intro eqn heqn x hx
    simp only [nonhomogeneousWaveEquation, List.mem_singleton] at heqn
    subst heqn
    simpa using hres x hx
  · intro eqn heqn
    simp [nonhomogeneousWaveEquation] at heqn

/-- The bundled nonhomogeneous wave equation is exactly its residual equation on `U`. -/
theorem nonhomogeneousWaveEquation_iff {U : Set (ℝ^(n + 1))} {f u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (nonhomogeneousWaveEquation (n := n) U f) u ↔
      ∀ x ∈ U, waveOperator (n := n) u x = f x := by
  constructor
  · exact fun hu x hx ↦ nonhomogeneousWaveEquation.residual_eq (n := n) hu hx
  · exact fun hres ↦ nonhomogeneousWaveEquation.of_residual (n := n) hres

/-- The wave operator of a `C²` field is continuous. -/
theorem continuous_waveOperator_of_contDiff_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ^(n + 1) → E} (hu : ContDiff ℝ 2 u) :
    Continuous (waveOperator (n := n) u) := by
  have hsecond (i : Fin (n + 1)) : Continuous (fun p ↦
          (∂[i] (fun q ↦ (∂[i] u) q)) p) := by
    exact (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i)
        (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hu)).continuous
  unfold waveOperator
  exact (hsecond 0).sub (continuous_finsetSum Finset.univ fun i _ ↦ hsecond i.succ)

/-- The homogeneous wave equation is the forced equation with zero source. -/
noncomputable def waveEquation (U : Set (ℝ^(n + 1))) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  nonhomogeneousWaveEquation U (fun _ ↦ 0)

end WaveEquation
