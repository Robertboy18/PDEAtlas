/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FirstVariation.LocalMinimizer

/-!
# Local minima in a uniform C¹ neighborhood

A classical local minimum compares the action with all sufficiently small
zero-boundary `C²` perturbations, measured uniformly in both value and Jacobian
on the closure of the domain. On a bounded domain this implies local minimality
along every classical zero-boundary variation. The size of the parameter interval
may depend on the variation.

Consequently the coupled Euler–Lagrange system holds pointwise under the same
regularity hypotheses as the classical first-variation theorem. The neighborhood is
the classical uniform `C¹` one, not a Sobolev neighborhood. Evans, §8.1.4(a), derives the
same system (16) for smooth minimizers.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(a).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Elementwise ContDiff

namespace PDE.CalculusOfVariations

open Analysis SobolevSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u v : ℝ^n → ℝ^m}

/-- A local minimum with respect to a uniform `C¹` neighborhood of classical
zero-boundary perturbations. The matrix norm is the elementwise supremum norm.
The radius controls values and Jacobians together on the closure of the domain. -/
def IsC1LocalMinimizer (Ω : Set (ℝ^n))
    (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ) (u : ℝ^n → ℝ^m) : Prop :=
  ∃ ε > 0, ∀ v : ℝ^n → ℝ^m, ContDiff ℝ 2 v →
    (∀ x ∈ frontier Ω, v x = 0) →
    (∀ x ∈ closure Ω, ‖v x‖ + ‖jacobianMatrix v x‖ < ε) →
    lagrangianAction Ω L u ≤ lagrangianAction Ω L (fun x ↦ u x + v x)

/-- Uniform `C¹` local minimality implies the local minimum along any classical
zero-boundary variation. Compactness bounds its value and Jacobian, so sufficiently
small scalar multiples lie in the prescribed neighborhood. -/
theorem IsC1LocalMinimizer.isLocalMin
    (hmin : IsC1LocalMinimizer Ω L u) (hbounded : Bornology.IsBounded Ω)
    (hv : ContDiff ℝ 2 v) (hzero : ∀ x ∈ frontier Ω, v x = 0) :
    IsLocalMin (fun t : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + t • v x)) 0 := by
  obtain ⟨ε, hε, hmin⟩ := hmin
  have hc : Continuous (fun x ↦ ‖v x‖ + ‖jacobianMatrix v x‖) :=
    hv.continuous.norm.add (contDiff_jacobianMatrix hv).continuous.norm
  obtain ⟨B, hB⟩ := hbounded.isCompact_closure.exists_bound_of_continuousOn hc.continuousOn
  have ht : ∀ᶠ t : ℝ in nhds 0, ‖t‖ * B < ε :=
    (continuous_norm.mul continuous_const).continuousAt.eventually_lt_const
      (by simpa using hε)
  filter_upwards [ht] with t ht
  have htv : ContDiff ℝ 2 (fun x ↦ t • v x) := hv.const_smul t
  have htvzero : ∀ x ∈ frontier Ω, t • v x = 0 := by
    intro x hx
    rw [hzero x hx, smul_zero]
  have hsmall : ∀ x ∈ closure Ω,
      ‖t • v x‖ + ‖jacobianMatrix (fun y ↦ t • v y) x‖ < ε := by
    intro x hx
    rw [jacobianMatrix_const_smul, norm_smul, norm_smul, ← mul_add]
    exact (mul_le_mul_of_nonneg_left
      ((Real.le_norm_self _).trans (hB x hx)) (norm_nonneg t)).trans_lt ht
  simpa only [zero_smul, add_zero] using hmin _ htv htvzero hsmall

/-- A uniform `C¹` local minimizer satisfies the full coupled Euler–Lagrange
system at every interior point. Smooth compactly supported tests have zero boundary
values, and their scalar multiples eventually lie in the minimizing neighborhood. -/
theorem IsC1LocalMinimizer.classicalEulerLagrange_eq_zero
    (hmin : IsC1LocalMinimizer Ω L u)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) :
    ∀ x ∈ Ω, ∀ k, classicalEulerLagrange L u x k = 0 := by
  apply classicalEulerLagrange_eq_zero_of_isLocalMin hopen hbounded hgraph hL hu
  intro v hv _ hvs
  apply hmin.isLocalMin hbounded (hv.of_le (by simp))
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  exact fun h ↦ (hopen.frontier_eq ▸ hx).2 (hvs h)

end PDE.CalculusOfVariations
