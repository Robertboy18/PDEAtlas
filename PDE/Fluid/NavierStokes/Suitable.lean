/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.LerayHopf

/-!
# Suitable Leray–Hopf solutions

The local energy inequality is tested against nonnegative smooth functions
supported inside the open physical time slab. It retains pressure, uses the
stored weak spatial gradient, and records integrability of each pairing.
This is the distributional inequality (1.2) in Remark 1 of Hou, Wang and Yang, with viscosity
and forcing restored. The name comes from the suitable weak solutions of Caffarelli, Kohn and
Nirenberg.

`SuitableLerayHopfSolution` adds local velocity and pressure integrability and
this inequality to the existing pressure-retaining energy-class interface.
The limit theorem `LocalEnergyInequality.of_tendsto` takes convergence of the energy input and
lower semicontinuity of the tested dissipation as hypotheses; it does not assume strong
convergence of the gradients.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 1.1, Remark 1 and (1.2),
  p. 2.
  <https://arxiv.org/abs/2509.25116v2>
* L. Caffarelli, R. Kohn, and L. Nirenberg, "Partial regularity of suitable weak solutions of the
  Navier–Stokes equations", *Comm. Pure Appl. Math.* 35 (1982), no. 6, 771-831.
  <https://doi.org/10.1002/cpa.3160350604>
-/

@[expose] public section

open PDE (spatialGradient)

namespace NavierStokes

open EuclideanSpace MeasureTheory Filter
open scoped Topology

set_option linter.missingDocs true

/-- A nonnegative smooth test supported strictly inside the physical time slab. -/
def IsLocalEnergyTest {n : ℕ} (T : ℝ) (φ : ℝ^(n + 1) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ IncompressibleFlow.finiteTimeDomain n T ∧ ∀ z, 0 ≤ φ z

/-- Tested viscous dissipation with the distributional spatial-gradient witness. -/
noncomputable def localEnergyDissipationDensity {n : ℕ} (nse : Problem n)
    (Du : IncompressibleFlow.SpatialGradientField n) (φ : ℝ^(n + 1) → ℝ)
    (z : ℝ^(n + 1)) : ℝ :=
  nse.kinematicViscosity * ‖Du z‖ ^ 2 * φ z

/-- Energy paired with the time derivative and spatial Laplacian of the test. -/
noncomputable def localEnergyDiffusionDensity {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (φ : ℝ^(n + 1) → ℝ)
    (z : ℝ^(n + 1)) : ℝ :=
  IncompressibleFlow.specificKineticEnergy u z *
    ((∂[0] φ) z + nse.kinematicViscosity *
      IncompressibleFlow.spatialLaplacian n φ z)

/-- The kinetic and pressure energy flux paired with the spatial test gradient. -/
noncomputable def localEnergyFluxDensity {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (p φ : ℝ^(n + 1) → ℝ)
    (z : ℝ^(n + 1)) : ℝ :=
  (IncompressibleFlow.specificKineticEnergy u z + p z) *
    inner ℝ (u z) (spatialGradient φ z)

/-- Work of the force localized by the scalar test. -/
noncomputable def localEnergyForceDensity {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (φ : ℝ^(n + 1) → ℝ)
    (z : ℝ^(n + 1)) : ℝ :=
  inner ℝ (nse.forcing z) (u z) * φ z

/-- Integrability of the four local-energy pairings, separately. -/
def LocalEnergyIntegrable {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (Du : IncompressibleFlow.SpatialGradientField n) (φ : ℝ^(n + 1) → ℝ) : Prop :=
  Integrable (localEnergyDissipationDensity nse Du φ) ∧
    Integrable (localEnergyDiffusionDensity nse u φ) ∧
    Integrable (localEnergyFluxDensity u p φ) ∧
    Integrable (localEnergyForceDensity nse u φ)

/-- Localized spacetime dissipation. -/
noncomputable def localEnergyDissipation {n : ℕ} (nse : Problem n)
    (Du : IncompressibleFlow.SpatialGradientField n) (φ : ℝ^(n + 1) → ℝ) : ℝ :=
  ∫ z, localEnergyDissipationDensity nse Du φ z

/-- Energy input from test derivatives, energy flux, and localized force work. -/
noncomputable def localEnergyInput {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p φ : ℝ^(n + 1) → ℝ) : ℝ :=
  (∫ z, localEnergyDiffusionDensity nse u φ z) +
    (∫ z, localEnergyFluxDensity u p φ z) +
    ∫ z, localEnergyForceDensity nse u φ z

/-- The distributional local energy inequality, including genuine integrability. -/
def LocalEnergyInequality {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (Du : IncompressibleFlow.SpatialGradientField n) (T : ℝ) : Prop :=
  ∀ φ, IsLocalEnergyTest T φ → LocalEnergyIntegrable nse u p Du φ ∧
    localEnergyDissipation nse Du φ ≤ localEnergyInput nse u p φ

/-- Local `Lᵖ` membership on every compact subset of an open spacetime slab. -/
def LocalEnergyMemLp {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : ℝ^(n + 1) → E) (p : ENNReal) (T : ℝ) : Prop :=
  ∀ K : Set (ℝ^(n + 1)), IsCompact K → K ⊆ IncompressibleFlow.finiteTimeDomain n T →
    MemLp f p (volume.restrict K)

/-- A suitable pressure-retaining Leray–Hopf solution.

Local `L³` velocity and `L^(3/2)` pressure ensure that the energy flux has its
usual distributional meaning. The explicit tested integrability fields also
cover the force and weak-gradient representatives. -/
structure SuitableLerayHopfSolution {n : ℕ} (nse : Problem n)
    extends PressureRepresentativeLerayHopfSolution nse where
  /-- The velocity is locally cubic-integrable in the interior slab. -/
  velocity_local_memLp_three : LocalEnergyMemLp u 3 T
  /-- The pressure has the local exponent used in the suitable energy flux. -/
  pressure_local_memLp_three_halves : LocalEnergyMemLp p (3 / 2) T
  /-- The solution satisfies the distributional local energy inequality. -/
  local_energy_inequality : LocalEnergyInequality nse u p Du T

/-- Localized dissipation is nonnegative for nonnegative tests. -/
theorem localEnergyDissipation_nonneg {n : ℕ} (nse : Problem n)
    (Du : IncompressibleFlow.SpatialGradientField n) {φ : ℝ^(n + 1) → ℝ}
    (hφ : ∀ z, 0 ≤ φ z) : 0 ≤ localEnergyDissipation nse Du φ := by
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg nse.kinematicViscosity.property.le (sq_nonneg _)) (hφ z)

/-- A local energy inequality passes to limits with convergent energy input
and lower semicontinuous tested dissipation. Only eventual inequalities are needed. -/
theorem LocalEnergyInequality.of_tendsto {n : ℕ} {nse : Problem n}
    {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ}
    {Du : IncompressibleFlow.SpatialGradientField n} {T : ℝ}
    (U : ι → ℝ^(n + 1) → ℝ^n) (P : ι → ℝ^(n + 1) → ℝ)
    (D : ι → IncompressibleFlow.SpatialGradientField n)
    (hint : ∀ φ, IsLocalEnergyTest T φ → LocalEnergyIntegrable nse u p Du φ)
    (hineq : ∀ φ, IsLocalEnergyTest T φ → ∀ᶠ k in l,
      localEnergyDissipation nse (D k) φ ≤ localEnergyInput nse (U k) (P k) φ)
    (hinput : ∀ φ, IsLocalEnergyTest T φ →
      Tendsto (fun k ↦ localEnergyInput nse (U k) (P k) φ) l
        (𝓝 (localEnergyInput nse u p φ)))
    (hdiss : ∀ φ, IsLocalEnergyTest T φ → ∀ a : ℝ,
      a < localEnergyDissipation nse Du φ → ∀ᶠ k in l,
        a ≤ localEnergyDissipation nse (D k) φ) :
    LocalEnergyInequality nse u p Du T := by
  intro φ hφ
  refine ⟨hint φ hφ, le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_⟩
  apply ge_of_tendsto (hinput φ hφ)
  filter_upwards [hdiss φ hφ a ha, hineq φ hφ] with k hlower hupper
  exact hlower.trans hupper

end NavierStokes
