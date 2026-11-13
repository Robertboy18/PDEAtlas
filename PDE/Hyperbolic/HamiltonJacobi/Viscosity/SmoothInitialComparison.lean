/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialComparison
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SmoothTests
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SpatialInitialComparison

/-!
# Initial-value comparison from smooth viscosity tests

The smooth-test hypotheses use functions smooth on the open
positive-time domain, as in the definition of viscosity solution in Evans, §10.1.1.
Slab uniform continuity gives the semicontinuity needed to pass from these
tests to the local `C¹` predicates.

For an autonomous Hamiltonian, continuity suffices. For a position-dependent Hamiltonian, the
uniform momentum Lipschitz bound and the spatial bound `Cx * ‖x-y‖ * (1+‖p‖)`, condition (3) of
Evans, §10.2, with two constants, imply joint continuity and allow the spatial comparison theorem
to apply. The conclusion propagates the given initial ordering; with equal initial data it is
Theorem 1 of Evans, §10.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.1.1, definition of viscosity solution, (16)-(17);
  §10.2, condition (3) and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem continuousOn_positiveTimeDomain_of_slabs
    {u : E × ℝ → ℝ} (hu : IsBoundedUniformContinuousOnSlabs u) :
    ContinuousOn u positiveTimeDomain := by
  intro z hz
  change 0 < z.2 at hz
  have hT : 0 < z.2 + 1 := by linarith
  have hslab : closedTimeSlab (z.2 + 1) ∈ 𝓝 z := by
    have hlower : ∀ᶠ w : E × ℝ in 𝓝 z, 0 < w.2 :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hz
    have hupper : ∀ᶠ w : E × ℝ in 𝓝 z, w.2 < z.2 + 1 := (isOpen_lt continuous_snd
        (continuous_const : Continuous (fun _ : E × ℝ ↦ z.2 + 1))).mem_nhds
          (by change z.2 < z.2 + 1; linarith)
    filter_upwards [hlower, hupper] with w hw₀ hwT using ⟨hw₀.le, hwT.le⟩
  exact ((hu (z.2 + 1) hT).2.continuousOn.continuousAt hslab).continuousWithinAt

/-- Smooth upper and lower tests on the positive half-space, bounded uniform continuity on
every slab, and ordered initial values imply comparison at all nonnegative times for a continuous
autonomous Hamiltonian. -/
theorem le_of_initial_le_of_smooth_tests {H : E → ℝ} {u v : E × ℝ → ℝ} (hH : Continuous H)
    (hub : IsBoundedUniformContinuousOnSlabs u) (hvb : IsBoundedUniformContinuousOnSlabs v)
    (husub : ∀ z ∈ positiveTimeDomain, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ positiveTimeDomain →
      IsLocalMaxOn (fun y ↦ u y - φ y) positiveTimeDomain z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) ≤ 0)
    (hvsuper : ∀ z ∈ positiveTimeDomain, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ positiveTimeDomain →
      IsLocalMinOn (fun y ↦ v y - φ y) positiveTimeDomain z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1))
    (hinit : ∀ x, u (x, 0) ≤ v (x, 0)) {z : E × ℝ} (hz : 0 ≤ z.2) :
    u z ≤ v z := by
  have hcont : Continuous (fun q : E × E ↦ H q.1) := hH.comp continuous_fst
  have hu := (isSpatialViscositySubsolution_iff_smooth_tests (H := fun p _ ↦ H p)
    isOpen_positiveTimeDomain
    (continuousOn_positiveTimeDomain_of_slabs hub).upperSemicontinuousOn hcont).mpr husub
  have hv := (isSpatialViscositySupersolution_iff_smooth_tests (H := fun p _ ↦ H p)
    isOpen_positiveTimeDomain
    (continuousOn_positiveTimeDomain_of_slabs hvb).lowerSemicontinuousOn hcont).mpr hvsuper
  exact hu.le_of_initial_le hv hH hub hvb hinit hz

/-- Comparison at all nonnegative times from smooth tests on the positive half-space, for a
position-dependent Hamiltonian. The two coefficient bounds imply the joint continuity needed for
smooth-test closure. -/
theorem le_of_initial_le_of_smooth_tests_of_lipschitz {H : E → E → ℝ} {u v : E × ℝ → ℝ}
    {Cp Cx : NNReal} (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : IsBoundedUniformContinuousOnSlabs u) (hvb : IsBoundedUniformContinuousOnSlabs v)
    (husub : ∀ z ∈ positiveTimeDomain, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ positiveTimeDomain →
      IsLocalMaxOn (fun y ↦ u y - φ y) positiveTimeDomain z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0)
    (hvsuper : ∀ z ∈ positiveTimeDomain, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ positiveTimeDomain →
      IsLocalMinOn (fun y ↦ v y - φ y) positiveTimeDomain z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1)
    (hinit : ∀ x, u (x, 0) ≤ v (x, 0)) {z : E × ℝ} (hz : 0 ≤ z.2) :
    u z ≤ v z := by
  have hcont := continuous_hamiltonian_of_lipschitz hp hx
  have hu := (isSpatialViscositySubsolution_iff_smooth_tests isOpen_positiveTimeDomain
    (continuousOn_positiveTimeDomain_of_slabs hub).upperSemicontinuousOn hcont).mpr husub
  have hv := (isSpatialViscositySupersolution_iff_smooth_tests isOpen_positiveTimeDomain
    (continuousOn_positiveTimeDomain_of_slabs hvb).lowerSemicontinuousOn hcont).mpr hvsuper
  exact hu.le_of_initial_le_of_lipschitz hv hp hx hub hvb hinit hz

end HamiltonJacobi

end
