/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Hamiltonian
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SmoothTests

/-!
# Hopf–Lax uniqueness against finite-horizon competitors

The Hopf–Lax construction gives a solution for all positive times.
An arbitrary competitor here is required to solve the equation only on `0 < t < T`
and to be bounded and uniformly continuous only on `[0,T]`.

For a prescribed convex superlinear Hamiltonian, the Lagrangian is its
Legendre transform. The biconjugacy theorem identifies the PDE with the
original Hamiltonian, without smoothness or uniform convexity assumptions.
Continuous autonomous comparison applies even though the Hamiltonian need not be
globally Lipschitz.

This supplies the finite-horizon uniqueness clause of Evans, §10.3.4, Theorem 3,
including equality at the terminal time, for bounded uniformly continuous initial data; Evans
assumes the datum bounded and Lipschitz. His uniqueness comes from Theorem 1 of §10.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.4, (43)-(44) and Theorem 3; §10.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every finite-horizon viscosity competitor for the dual Hamiltonian agrees with
the Hopf–Lax value on the entire closed slab, including both endpoints. -/
theorem eqOn_value_on_slab {L g : E → ℝ} {u : E × ℝ → ℝ} {T : ℝ} (hL : Superlinear L)
    (hconv : ConvexOn ℝ univ L) (hg : UniformContinuous g) (hgb : Bornology.IsBounded (range g))
    (hu : IsSpatialViscositySolution (fun p _ ↦ hamiltonian L p) (openTimeSlab T) u)
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hinit : ∀ x, u (x, 0) = g x) (hT : 0 < T) :
    EqOn u (fun z : E × ℝ ↦ value L g z.2 z.1) (closedTimeSlab T) := by
  have hv := isViscosityInitialSolution hL hconv hg hgb
  exact fun z hz ↦ le_antisymm (hu.1.le_of_initial_le_on_slab hv.2.1.2 Subset.rfl (fun _ hw ↦ hw.1)
      (continuous_hamiltonian hL) hub (hv.1 T hT)
      (fun x ↦ by rw [hinit x, value_zero]) hT hz)
    (hv.2.1.1.le_of_initial_le_on_slab hu.2 (fun _ hw ↦ hw.1) Subset.rfl
      (continuous_hamiltonian hL) (hv.1 T hT) hub
      (fun x ↦ by rw [hinit x, value_zero]) hT hz)

/-- Finite-horizon uniqueness for a prescribed convex superlinear Hamiltonian.
The Lagrangian is its Legendre transform; the competitor satisfies the equation
for the original Hamiltonian only in the open slab. -/
theorem eqOn_value_on_slab_of_convex {H g : E → ℝ} {u : E × ℝ → ℝ} {T : ℝ} (hH : Superlinear H)
    (hconv : ConvexOn ℝ univ H) (hg : UniformContinuous g) (hgb : Bornology.IsBounded (range g))
    (hu : IsSpatialViscositySolution (fun p _ ↦ H p) (openTimeSlab T) u)
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hinit : ∀ x, u (x, 0) = g x) (hT : 0 < T) :
    EqOn u (fun z : E × ℝ ↦ value (hamiltonian H) g z.2 z.1) (closedTimeSlab T) := by
  have hcont : Continuous H := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have heq : hamiltonian (hamiltonian H) = H := funext fun _ ↦ biconjugate_eq hH hconv
  apply eqOn_value_on_slab (superlinear_hamiltonian hH hcont)
    (convexOn_hamiltonian hH) hg hgb ?_ hub hinit hT
  rwa [heq]

/-- The Hopf–Lax formula is the unique solution in Evans's finite-horizon
smooth-test class. Bounded uniform continuity is required only on `[0,T]`. -/
theorem eqOn_value_on_slab_of_convex_of_smooth_tests {H g : E → ℝ} {u : E × ℝ → ℝ} {T : ℝ}
    (hH : Superlinear H) (hconv : ConvexOn ℝ univ H) (hg : UniformContinuous g)
    (hgb : Bornology.IsBounded (range g))
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (husub : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) ≤ 0)
    (husuper : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ u y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1))
    (hinit : ∀ x, u (x, 0) = g x) (hT : 0 < T) :
    EqOn u (fun z : E × ℝ ↦ value (hamiltonian H) g z.2 z.1) (closedTimeSlab T) := by
  have hcont : Continuous H := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hcontU : ContinuousOn u (openTimeSlab T) :=
    hub.2.continuousOn.mono (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)
  have hsub := (isSpatialViscositySubsolution_iff_smooth_tests (H := fun p _ ↦ H p)
    (isOpen_openTimeSlab T) hcontU.upperSemicontinuousOn (hcont.comp continuous_fst)).mpr husub
  have hsuper := (isSpatialViscositySupersolution_iff_smooth_tests (H := fun p _ ↦ H p)
    (isOpen_openTimeSlab T) hcontU.lowerSemicontinuousOn (hcont.comp continuous_fst)).mpr husuper
  exact eqOn_value_on_slab_of_convex hH hconv hg hgb ⟨hsub, hsuper⟩ hub hinit hT

end HamiltonJacobi.HopfLax

end
