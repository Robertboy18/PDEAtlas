/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.EigenTests
public import PDE.Fluid.NavierStokes.Stationary.SolenoidalDensity

/-!
# A weak eigenvalue equation known against the tests orthogonal to a field

Suppose a weak eigenvalue equation is known against the odd divergence-free test fields that are
orthogonal in `L²` to a fixed field `w`. Then it holds against every odd divergence-free test
field up to a multiple of `w`: the density integrates to `c ⟨φ, w⟩`, with one number `c` for all
`φ`. The value of `c` is not computed here; it is zero exactly when the equation holds against
one test field `ψ` with `⟨ψ, w⟩ ≠ 0`. In Proposition 2 of Hou, Wang and Yang, `w` is the
approximate eigenfunction `v̄`, and the equation of the eigenfunction holds up to a multiple of
`v̄`.

## Main results

* `integral_weakEigenDensity_eq_mul_of_orthogonal_tests`: for every profile in `L²_loc` and every
  field of `H¹(ℝ³)³`, the weak eigenvalue density integrates to `c ⟨φ, w⟩` against every odd
  divergence-free test field `φ`, where `c` is its integral against `ψ` divided by `⟨ψ, w⟩`.

## How it works

The integral of the weak eigenvalue density is linear in the test field
(`Symmetry.weakEigenDensity_eq_jetDensity`, `Symmetry.jetDensity_add`,
`Symmetry.jetDensity_smul`). Fix one odd divergence-free test field `ψ` with `⟨ψ, w⟩ ≠ 0`. Every
odd divergence-free test field `φ` is `φ - a ψ` plus `a ψ`, with `a = ⟨φ, w⟩ / ⟨ψ, w⟩`, and
`φ - a ψ` is orthogonal to `w`.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Proposition 2.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace NavierStokes.Symmetry
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert ContDiff

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- **The equation up to a multiple of `w`.** Let the weak eigenvalue density of `v` at the
profile `U` integrate to zero against every odd divergence-free test field that is orthogonal
to `w` in `L²`, and let `ψ` be an odd divergence-free test field with `⟨ψ, w⟩ ≠ 0`. Then
against every odd divergence-free test field `φ` the density integrates to `c ⟨φ, w⟩`, with
the one number `c = (∫ density against ψ) / ⟨ψ, w⟩`. In particular the equation holds against
all of them as soon as it holds against `ψ`. -/
theorem integral_weakEigenDensity_eq_mul_of_orthogonal_tests {U : ℝ^3 → ℝ^3} {μ : ℝ} {v : H}
    (w : H) (hUm : AEStronglyMeasurable U volume)
    (hU2 : LocallyIntegrable (fun x ↦ ‖U x‖ ^ 2) volume)
    (horth : ∀ φ (hφ : IsSolenoidalTestField φ), IsOddAxisymmetric φ →
      ⟪Stationary.massCLM (Stationary.testFieldH1 φ hφ.1 hφ.2.1), Stationary.massCLM w⟫ = 0 →
      ∫ x, weakEigenDensity U μ v φ x = 0)
    {ψ : ℝ^3 → ℝ^3} (hψ : IsSolenoidalTestField ψ) (hψodd : IsOddAxisymmetric ψ)
    (hψw : ⟪Stationary.massCLM (Stationary.testFieldH1 ψ hψ.1 hψ.2.1),
      Stationary.massCLM w⟫ ≠ 0)
    (φ : ℝ^3 → ℝ^3) (hφ : IsSolenoidalTestField φ) (hφodd : IsOddAxisymmetric φ) :
    ∫ x, weakEigenDensity U μ v φ x =
      (∫ x, weakEigenDensity U μ v ψ x) /
          ⟪Stationary.massCLM (Stationary.testFieldH1 ψ hψ.1 hψ.2.1), Stationary.massCLM w⟫ *
        ⟪Stationary.massCLM (Stationary.testFieldH1 φ hφ.1 hφ.2.1), Stationary.massCLM w⟫ := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c * ⟪Stationary.massCLM (Stationary.testFieldH1 ψ hψ.1 hψ.2.1),
      Stationary.massCLM w⟫ = ⟪Stationary.massCLM (Stationary.testFieldH1 φ hφ.1 hφ.2.1),
        Stationary.massCLM w⟫ := ⟨_, div_mul_cancel₀ _ hψw⟩
  have hcψ : IsSolenoidalTestField ((-c) • ψ) := hψ.smul (-c)
  have hφ' : IsSolenoidalTestField (φ + (-c) • ψ) := hφ.add hcψ
  have hT : Stationary.testFieldH1 (φ + (-c) • ψ) hφ'.1 hφ'.2.1 =
      Stationary.testFieldH1 φ hφ.1 hφ.2.1 + (-c) • Stationary.testFieldH1 ψ hψ.1 hψ.2.1 := by
    rw [Stationary.testFieldH1_add hφ.1 hφ.2.1 hcψ.1 hcψ.2.1 hφ'.1 hφ'.2.1,
      Stationary.testFieldH1_smul (-c) hψ.1 hψ.2.1 hcψ.1 hcψ.2.1]
  have h0 := horth _ hφ' (hφodd.add (hψodd.smul (-c))) (by
    rw [hT, map_add, map_smul, inner_add_left, real_inner_smul_left, neg_mul, hc,
      add_neg_cancel])
  -- The density is linear in the test field.
  have hJ := isLocallyIntegrableJet_eigen μ v hUm hU2
  have hdens (χ : ℝ^3 → ℝ^3) (hχ : IsSolenoidalTestField χ) : weakEigenDensity U μ v χ =
      jetDensity (eigenZeroth U μ v) (eigenFirst U v) 0 χ :=
    funext fun x ↦ weakEigenDensity_eq_jetDensity U μ v ((hχ.1.differentiable (by simp)) x)
  have hlin : weakEigenDensity U μ v (φ + (-c) • ψ) = fun x ↦
      weakEigenDensity U μ v φ x + -c * weakEigenDensity U μ v ψ x := by
    rw [hdens _ hφ', hdens φ hφ, hdens ψ hψ]
    funext x
    rw [jetDensity_add (hφ.1.of_le (by simp)) (hcψ.1.of_le (by simp)) x,
      jetDensity_smul (-c) (hψ.1.of_le (by simp)) x]
  have hiφ : Integrable (weakEigenDensity U μ v φ) := by
    rw [hdens φ hφ]
    exact integrable_jetDensity hJ hφ.1 hφ.2.1
  have hiψ : Integrable (weakEigenDensity U μ v ψ) := by
    rw [hdens ψ hψ]
    exact integrable_jetDensity hJ hψ.1 hψ.2.1
  rw [hlin] at h0
  have h1 := (integral_add hiφ (hiψ.const_mul (-c))).symm.trans h0
  rw [integral_const_mul] at h1
  rw [← hc, mul_left_comm, div_mul_cancel₀ _ hψw]
  linarith

end NavierStokes.Nonuniqueness
