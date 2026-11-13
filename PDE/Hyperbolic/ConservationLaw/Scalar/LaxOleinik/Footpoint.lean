/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Potential
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.Congruence
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Footpoint.AlmostEverywhere

/-!
# Conservation laws from minimizing footpoints

The minimizing footpoint need not be chosen measurably. Joint almost-everywhere
identification with the derivative of a Lipschitz potential supplies
measurability and the weak initial identity. A separate slice theorem gives
the spatial derivative at every fixed positive time.

The solution is extended by zero to nonpositive times. Its initial datum
appears in the boundary term, so this convention imposes no pointwise initial
representative condition.

`costSolution` is the Lax–Oleinik formula (29) of Evans, §3.4.2, Theorem 1, with `L'` in
place of `G = (F')⁻¹`; the two agree when `L = F*` for a uniformly convex flux `F`, as in Evans.
`costSolution_spec` is Theorem 2 there: the formula gives an integral solution. We assume only
a convex, superlinear, differentiable cost `L` and bounded data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, Theorems 1-2, equations (28)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax HamiltonJacobi1D
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The Lax–Oleinik footpoint construction for a differentiable cost. The
primitive is the interval integral of the supplied datum. -/
def costSolution (L g : ℝ → ℝ) (p : ℝ^2) : ℝ :=
  if 0 < p 0 then
    deriv L ((p 1 - minimizingFootpoint L (fun x ↦ ∫ s in (0 : ℝ)..x, g s)
      (p 0) (p 1)) / p 0)
  else 0

/-- The footpoint formula agrees jointly almost everywhere with the
measurable spatial derivative, restricted to positive time. -/
theorem costSolution_ae_eq_indicator_potentialDerivative {L g : ℝ → ℝ} (hL : Superlinear L)
    (hconv : ConvexOn ℝ univ L) (hD : Differentiable ℝ L) (hg : MemLp g ∞ volume) :
    costSolution L g =ᵐ[volume]
      (forwardHalfSpace : Set ℝ^2).indicator (potentialDerivative L g) := by
  obtain ⟨K, hh⟩ := exists_lipschitzWith_intervalIntegral_of_memLp_top hg 0
  have hAE := ae_spatial_fderiv_eq_deriv_cost_of_fixed_footpoint hL hconv hD hh
  have hnative := measurePreserving_scalarSpaceTimeEquiv.quasiMeasurePreserving.ae hAE
  filter_upwards [hnative] with p hp
  by_cases ht : 0 < p 0
  · have hmin := minimizingFootpoint_spec hD.continuous hL hh ht (p 1)
    have heq := hp (by simpa only [scalarSpaceTimeEquiv_apply] using ht) _ hmin
    have hpU : p ∈ (forwardHalfSpace : Set ℝ^2) := ht
    simpa only [costSolution, ite_eq_left ht, Set.indicator_of_mem hpU,
      potentialDerivative, scalarSpaceTimeEquiv_apply] using heq.symm
  · have hpU : p ∉ (forwardHalfSpace : Set ℝ^2) := ht
    simp only [costSolution, ite_eq_right ht, Set.indicator_of_notMem hpU]

/-- For each fixed positive time, the footpoint formula is the
spatial derivative of the value almost everywhere. -/
theorem costSolution_ae_eq_deriv_value {L g : ℝ → ℝ} (hL : Superlinear L) (hD : Differentiable ℝ L)
    (hg : MemLp g ∞ volume) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x : ℝ, costSolution L g !₂[t, x] = deriv (value L (fun y ↦ ∫ s in (0 : ℝ)..y, g s) t) x := by
  obtain ⟨K, hh⟩ := exists_lipschitzWith_intervalIntegral_of_memLp_top hg 0
  filter_upwards [ae_deriv_value_eq_deriv_cost_of_fixed_footpoint hL hD hh ht] with x hx
  have heq := hx _ (minimizingFootpoint_spec hD.continuous hL hh ht x)
  simpa [costSolution, ht] using heq.symm

/-- The minimizing-footpoint construction solves the full weak
initial problem and is globally essentially bounded. Neither a measurable
minimizer selection nor an initial trace is an input. -/
theorem costSolution_spec {L g : ℝ → ℝ} (hL : Superlinear L) (hconv : ConvexOn ℝ univ L)
    (hD : Differentiable ℝ L) (hg : MemLp g ∞ volume) :
    IsWeakInitialValueSolution (hamiltonian L) g (costSolution L g) ∧
      MemLp (costSolution L g) ∞ volume := by
  obtain ⟨hweak, hbounded⟩ := potentialDerivative_spec hL hconv hg
  have heq := costSolution_ae_eq_indicator_potentialDerivative hL hconv hD hg
  have hR : potentialDerivative L g =ᵐ[volume.restrict forwardHalfSpace]
      costSolution L g := by
    filter_upwards [ae_restrict_of_ae heq,
      ae_restrict_mem forwardHalfSpace.isOpen.measurableSet] with p hp hpU
    simpa only [Set.indicator_of_mem hpU] using hp.symm
  exact ⟨hweak.congr_ae_restrict hR Filter.EventuallyEq.rfl,
    (hbounded.indicator forwardHalfSpace.isOpen.measurableSet.nullMeasurableSet).ae_eq heq.symm⟩

/-- Every essential bound for the datum is preserved by the footpoint
solution. The bound may be zero and is independent of the flux's time modulus. -/
theorem ae_norm_costSolution_le {L g : ℝ → ℝ} (hL : Superlinear L) (hconv : ConvexOn ℝ univ L)
    (hD : Differentiable ℝ L) (hg : MemLp g ∞ volume) {K : ℝ≥0} (hK : ∀ᵐ x : ℝ, ‖g x‖ ≤ K) :
    ∀ᵐ p : ℝ^2, ‖costSolution L g p‖ ≤ K := by
  have hh := lipschitzWith_intervalIntegral_of_ae_bound
    (hg.locallyIntegrable (by simp)) hK 0
  filter_upwards [costSolution_ae_eq_indicator_potentialDerivative hL hconv hD hg] with p hp
  rw [hp]
  by_cases hpU : p ∈ (forwardHalfSpace : Set ℝ^2)
  · rw [Set.indicator_of_mem hpU]
    exact norm_spatial_fderiv_forwardValue_le hL hh (scalarSpaceTimeEquiv p)
  · simp only [Set.indicator_of_notMem hpU, norm_zero, NNReal.coe_nonneg]

/-- The footpoint solution satisfies the sharp data-only bound by
the essential supremum of its initial datum. -/
theorem ae_norm_costSolution_le_eLpNorm {L g : ℝ → ℝ} (hL : Superlinear L)
    (hconv : ConvexOn ℝ univ L) (hD : Differentiable ℝ L) (hg : MemLp g ∞ volume) :
    ∀ᵐ p : ℝ^2, ‖costSolution L g p‖ ≤ (eLpNorm g ∞ volume).toReal := by
  have hh := lipschitzWith_intervalIntegral_of_memLp_top hg 0
  filter_upwards [costSolution_ae_eq_indicator_potentialDerivative hL hconv hD hg] with p hp
  rw [hp]
  by_cases hpU : p ∈ (forwardHalfSpace : Set ℝ^2)
  · rw [Set.indicator_of_mem hpU]
    simpa only [potentialDerivative, ENNReal.coe_toNNReal_eq_toReal] using
      norm_spatial_fderiv_forwardValue_le hL hh (scalarSpaceTimeEquiv p)
  · simp only [Set.indicator_of_notMem hpU, norm_zero, ENNReal.toReal_nonneg]

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
