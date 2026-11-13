/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.Autonomous
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.Spatial
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SmoothTests

/-!
# Finite-horizon comparison from smooth touching tests

These theorems use the smooth tests and finite closed slab of Evans, §10.2,
Theorem 1. Uniform continuity on this slab supplies the semicontinuity needed
by the smooth-test equivalence. The equation is tested only for
`0 < t < T`; comparison at `t = T` follows from continuity.

For a position-dependent Hamiltonian, the two bounds of condition (3) assumed by Evans imply
joint continuity. For an autonomous Hamiltonian, continuity alone suffices.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, condition (3) and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Smooth upper and lower tests on the open slab `0 < t < T`, bounded uniform continuity on
the closed slab, and ordered initial values imply comparison on the closed slab for a continuous
autonomous Hamiltonian. -/
theorem le_on_slab_of_initial_le_of_smooth_tests {H : E → ℝ} {u v : E × ℝ → ℝ} {T : ℝ}
    (hH : Continuous H)
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (husub : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) ≤ 0)
    (hvsuper : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ v y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1))
    (hinit : ∀ x, u (x, 0) ≤ v (x, 0)) (hT : 0 < T) {z : E × ℝ} (hz : z ∈ closedTimeSlab T) :
    u z ≤ v z := by
  have hcont : Continuous (fun q : E × E ↦ H q.1) := hH.comp continuous_fst
  have hu := (isSpatialViscositySubsolution_iff_smooth_tests (H := fun p _ ↦ H p)
    (isOpen_openTimeSlab T)
    (hub.2.continuousOn.mono (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)).upperSemicontinuousOn hcont).mpr husub
  have hv := (isSpatialViscositySupersolution_iff_smooth_tests (H := fun p _ ↦ H p)
    (isOpen_openTimeSlab T)
    (hvb.2.continuousOn.mono (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)).lowerSemicontinuousOn
      hcont).mpr hvsuper
  exact hu.le_of_initial_le_on_slab hv Subset.rfl Subset.rfl hH hub hvb hinit hT hz

/-- Comparison on the closed slab `0 ≤ t ≤ T` from smooth tests on the open slab, for a
position-dependent Hamiltonian. The two coefficient bounds imply the joint continuity needed for
smooth-test closure. -/
theorem le_on_slab_of_initial_le_of_smooth_tests_of_lipschitz {H : E → E → ℝ} {u v : E × ℝ → ℝ}
    {T : ℝ} {Cp Cx : NNReal} (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (husub : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0)
    (hvsuper : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ v y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1)
    (hinit : ∀ x, u (x, 0) ≤ v (x, 0)) (hT : 0 < T) {z : E × ℝ} (hz : z ∈ closedTimeSlab T) :
    u z ≤ v z := by
  have hcont := continuous_hamiltonian_of_lipschitz hp hx
  have hu := (isSpatialViscositySubsolution_iff_smooth_tests (isOpen_openTimeSlab T)
    (hub.2.continuousOn.mono (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)).upperSemicontinuousOn hcont).mpr husub
  have hv := (isSpatialViscositySupersolution_iff_smooth_tests (isOpen_openTimeSlab T)
    (hvb.2.continuousOn.mono (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)).lowerSemicontinuousOn
      hcont).mpr hvsuper
  exact hu.le_of_initial_le_on_slab_of_lipschitz hv Subset.rfl Subset.rfl hp hx hub hvb hinit hT hz

/-- Evans's finite-horizon uniqueness in the original smooth-test class.
Only bounded uniform continuity on `[0,T]`, initial equality, and the two
Hamiltonian bounds are required; equality includes both time endpoints. -/
theorem eqOn_closedTimeSlab_of_smooth_tests_of_lipschitz {H : E → E → ℝ} {u v : E × ℝ → ℝ}
    {Cp Cx : NNReal} {T : ℝ} (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (husub : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0)
    (husuper : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ u y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1)
    (hvsub : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ v y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0)
    (hvsuper : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ v y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1)
    (hinit : ∀ x, u (x, 0) = v (x, 0)) (hT : 0 < T) :
    EqOn u v (closedTimeSlab T) := by
  intro z hz
  exact le_antisymm
    (le_on_slab_of_initial_le_of_smooth_tests_of_lipschitz hp hx hub hvb husub hvsuper
      (fun x ↦ (hinit x).le) hT hz)
    (le_on_slab_of_initial_le_of_smooth_tests_of_lipschitz hp hx hvb hub hvsub husuper
      (fun x ↦ (hinit x).ge) hT hz)

end HamiltonJacobi

end
