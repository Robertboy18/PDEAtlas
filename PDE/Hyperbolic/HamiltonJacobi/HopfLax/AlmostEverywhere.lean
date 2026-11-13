/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Hamiltonian
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# The Hopf–Lax equation almost everywhere

Lipschitz initial data give a Lipschitz value function on the whole forward
spacetime half-space. Mathlib's Rademacher theorem supplies differentiability
almost everywhere. The two contact inequalities then give the equation at
those points.

The last theorem starts with a prescribed convex superlinear Hamiltonian and
uses double duality to recover that same Hamiltonian in the equation. With the Lipschitz
estimate this is Theorem 6 of Evans, §3.3.2, where the Lipschitz datum may also be unbounded.
The initial identity is `value_zero`; the quantitative initial trace and
spacetime Lipschitz estimate are in `HopfLax.Regularity`.

An almost-everywhere equation alone does not give uniqueness (Evans, §3.3.3(a), Example (33)).
Evans adds a semiconcavity condition; see `HopfLax.WeakWellPosedness`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorems 5 and 6; §3.3.3(a), Example (33).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

open Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]
    {L g : E → ℝ} (hL : Superlinear L) (hconv : ConvexOn ℝ Set.univ L)
    {K : NNReal} (hg : LipschitzWith K g)

include hL hconv hg

/-- The Hopf–Lax value is differentiable almost everywhere at positive times,
for arbitrary Lipschitz initial data. -/
theorem ae_differentiableAt_value :
    ∀ᵐ z ∂μ.restrict positiveTimeDomain,
      DifferentiableAt ℝ (fun w : E × ℝ ↦ value L g w.2 w.1) z := by
  have hcont : Continuous L := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨C, hC, hLC, hbound⟩ := exists_trace_constant hL K
  have hLip := lipschitzOnWith_forward hcont hL hconv hg hC hLC hbound
  apply (ae_restrict_iff' isOpen_positiveTimeDomain.measurableSet).2
  filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := μ)] with z hz ht
  apply (hz (show 0 ≤ z.2 from (show 0 < z.2 from ht).le)).differentiableAt
  exact mem_of_superset (isOpen_positiveTimeDomain.mem_nhds ht)
    fun w hw ↦ show 0 ≤ w.2 from (show 0 < w.2 from hw).le

/-- The Hopf–Lax value satisfies the Hamilton–Jacobi equation almost everywhere
in positive spacetime. The initial datum may be unbounded. -/
theorem ae_residual_eq_zero :
    ∀ᵐ z ∂μ.restrict positiveTimeDomain, fderiv ℝ (fun w : E × ℝ ↦ value L g w.2 w.1) z (0, 1) +
      hamiltonian L (∇ (value L g z.2) z.1) = 0 := by
  have hcont : Continuous L := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hlower : ∀ y, -(-g 0) - (K : ℝ) * ‖y‖ ≤ g y := by
    intro y
    have h := hg.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right] at h
    linarith [(neg_le_abs (g y - g 0)).trans h]
  filter_upwards [ae_differentiableAt_value hL hconv hg (μ := μ),
    ae_restrict_mem isOpen_positiveTimeDomain.measurableSet] with z hdiff ht
  exact residual_eq_zero_of_differentiableAt hcont hL hconv hg.continuous hlower ht hdiff

omit hL hconv in
/-- Starting with a convex superlinear Hamiltonian, the Hopf–Lax formula
formed from its Legendre transform solves the original equation almost everywhere.
Double duality identifies the Hamiltonian without any differentiability assumption. -/
theorem ae_residual_eq_zero_of_convex
    {H : E → ℝ} (hH : Superlinear H) (hHconv : ConvexOn ℝ Set.univ H) :
    ∀ᵐ z ∂μ.restrict positiveTimeDomain, fderiv ℝ (fun w : E × ℝ ↦ value (hamiltonian H) g w.2 w.1)
      z (0, 1) + H (∇ (value (hamiltonian H) g z.2) z.1) = 0 := by
  have hcont : Continuous H := continuousOn_univ.mp (hHconv.continuousOn isOpen_univ)
  filter_upwards [ae_residual_eq_zero (superlinear_hamiltonian hH hcont)
    (convexOn_hamiltonian hH) hg (μ := μ)] with z hz
  rwa [biconjugate_eq hH hHconv] at hz

end HamiltonJacobi.HopfLax
