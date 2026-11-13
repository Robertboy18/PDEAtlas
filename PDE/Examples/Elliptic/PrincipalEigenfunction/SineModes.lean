/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.ClassicalDirichlet
public import PDE.Spaces.Sobolev.Boundary.Atlas.Interval.Graph
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Dirichlet sine modes with a nonzero drift

On `(0, π)` the operator `-u'' + 2u'` has the Dirichlet eigenfunctions
`exp(x) sin(x)` and `exp(x) sin(2x)`, with eigenvalues `2` and `5`. Classically
`-u'' + 2u' = (1 + k²) u` for `u = exp(x) sin(kx)` (`classicalLoad_mode`), and
`exists_eigenfunction_of_classicalLoad_eq` makes the modes with `k = 1, 2` weak
eigenfunctions in `H¹₀` (`exists_native_mode`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Elliptic.PrincipalEigenfunction

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace ContDiff Sobolev

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

/-- The interval on which both sine modes have zero boundary values. -/
def domain : Set (ℝ^1) := {x | 0 < x 0 ∧ x 0 < Real.pi}

/-- The interval is open. -/
theorem domain_open : IsOpen domain :=
  isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous

/-- The interval is bounded. -/
theorem domain_bounded : Bornology.IsBounded domain := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.pi, fun x hx ↦ ?_⟩
  have hnorm : ‖x‖ = |x 0| := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_one, Real.norm_eq_abs]
    simpa using Real.sqrt_sq_eq_abs |x (0 : Fin 1)|
  rw [hnorm, abs_of_pos hx.1]
  exact hx.2.le

/-- The interval has `C^k` graph boundary for every `k`. -/
theorem domain_graph (k : ℕ) : Boundary.HasContDiffGraphBoundary k domain :=
  Boundary.Atlas.Interval.hasContDiffGraphBoundary_Ioo Real.pi_pos k

/-- Constant principal coefficient one, drift two, and potential zero. -/
def coefficients : SmoothFullCoefficients 1 domain where
  principal := fun _ _ _ ↦ 1
  drift := fun _ _ ↦ 2
  potential := fun _ ↦ 0
  principal_smooth := fun _ _ _ ↦ ContDiffUpToBoundary.const 1
  drift_smooth := fun _ _ ↦ ContDiffUpToBoundary.const 2
  potential_smooth := fun _ ↦ ContDiffUpToBoundary.const 0

/-- The function `exp(x) sin(kx)`. -/
def mode (k : ℝ) (x : ℝ^1) : ℝ := Real.exp (x 0) * Real.sin (k * x 0)

/-- The modes are smooth on all of `ℝ`. -/
theorem mode_contDiff (k : ℝ) : ContDiff ℝ ∞ (mode k) := by
  unfold mode
  cas

/-- The modes are `C^j` up to the boundary of the interval. -/
theorem mode_regular (k : ℝ) (j : ℕ) : ContDiffUpToBoundary j (mode k) domain :=
  contDiffUpToBoundary_of_contDiffOn isOpen_univ
    (((mode_contDiff k).of_le (by simp)).contDiffOn)
    domain_bounded.isCompact_closure (subset_univ _)

/-- The derivative of `exp(x) sin(kx)` is `exp(x) (sin(kx) + k cos(kx))`. -/
theorem partialDeriv_mode (k : ℝ) (x : ℝ^1) :
    (∂[(0 : Fin 1)] (mode k)) x =
      Real.exp (x 0) * (Real.sin (k * x 0) + k * Real.cos (k * x 0)) := by
  unfold mode
  cas

/-- `-u'' + 2u' = (1 + k²) u` for `u = mode k`. -/
theorem classicalLoad_mode (k : ℝ) (x : ℝ^1) :
    coefficients.classicalLoad (mode k) x = (1 + k ^ 2) * mode k x := by
  unfold SmoothFullCoefficients.classicalLoad coefficients
  simp only [Fintype.sum_unique, Fin.default_eq_zero, one_mul, zero_mul, add_zero]
  have hfirst : ∂[(0 : Fin 1)] (mode k) =
      fun y ↦ Real.exp (y 0) * (Real.sin (k * y 0) + k * Real.cos (k * y 0)) :=
    funext (partialDeriv_mode k)
  rw [hfirst]
  have hsecond : (∂[(0 : Fin 1)]
      (fun y : ℝ^1 ↦ Real.exp (y 0) *
        (Real.sin (k * y 0) + k * Real.cos (k * y 0)))) x =
      Real.exp (x 0) * ((1 - k ^ 2) * Real.sin (k * x 0) +
        2 * k * Real.cos (k * x 0)) := by
    cas
  rw [hsecond]
  unfold mode
  cas

/-- The first mode has strictly positive interior values. -/
theorem mode_one_pos (x : ℝ^1) (hx : x ∈ domain) : 0 < mode 1 x := by
  simpa only [mode, one_mul] using
    mul_pos (Real.exp_pos (x 0)) (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)

/-- For `k = 1, 2` the mode vanishes at both endpoints. -/
theorem mode_boundary (k : ℝ) (hk : k = 1 ∨ k = 2) :
    ∀ x ∈ frontier domain, mode k x = 0 := by
  intro x hx
  obtain hzero | hpi := Boundary.Atlas.Interval.eq_endpoint_of_mem_frontier_Ioo hx
  · simp [mode, hzero]
  · obtain rfl | rfl := hk
    · simp [mode, hpi]
    · simp [mode, hpi, Real.sin_two_mul]

/-- The classical modes are weak Dirichlet eigenfunctions in `H¹₀`, tested against
every `H¹₀` function. -/
theorem exists_native_mode (k : ℝ) (hk : k = 1 ∨ k = 2) :
    ∃ u : H¹₀(domain),
      (baseCoordCLM u : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 domain] mode k ∧
      ∀ v : H¹₀(domain),
        coefficients.form domain_open domain_bounded u v =
          (1 + k ^ 2) * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ :=
  coefficients.exists_eigenfunction_of_classicalLoad_eq domain_open domain_bounded
    ((domain_graph 1).hasC1GraphBoundary le_rfl) (mode_regular k 2)
    (mode_contDiff k).continuous.continuousOn (mode_boundary k hk) (1 + k ^ 2)
    (fun x _ ↦ classicalLoad_mode k x)

end PDE.Examples.Elliptic.PrincipalEigenfunction
