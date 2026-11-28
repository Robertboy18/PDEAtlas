/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.FiniteRankCorrection
public import PDE.Fluid.NavierStokes.CompensatedSimilarityForm

/-!
# Coercivity of the similarity form after a finite-rank capture of the compensation

Once a matrix field `Q` compensates the gradient of a divergence-free background `b` up to
`η₁`, the stationary similarity form at `b` is at least `((n - 2) / 4 - η₁) ‖u‖² + ‖∇u‖²`
(`similarityPrincipalForm_lower_bound`). The form that one solves with has no `Q`. The
compensation is replaced by a finite-rank term `∑ⱼ ⟪qⱼ, u⟫ ⟪fⱼ, v⟫`. How much coercivity is
left? This module answers for every field `u` at which the finite-rank term captures the
compensation up to `M₁ ‖∇u‖² + M₂ ‖u‖²`: the form without `Q` plus the finite-rank term is at
least `((n - 2) / 4 - η₁ - M₂) ‖u‖² + (1 - M₁) ‖∇u‖²`. The capture bound is a hypothesis on the
field. For the finite-rank approximation of Hou, Wang and Yang it is their Lemma 3.

## Main results

* `similarityPrincipalForm_zero_add_finiteRank_ge`: the lower bound
  `((n - 2) / 4 - η₁ - M₂) ‖u‖² + (1 - M₁) ‖∇u‖²` for the form without compensation plus the
  finite-rank term, at every solenoidal zero-boundary field `u` that satisfies the capture
  bound, for all bounded open sets, backgrounds and finite families `q`, `f`.

## How it works

The similarity form is affine in the compensation (`similarityPrincipalForm_apply_eq_add`, from
`CompensatedSimilarityForm`), so the
form without `Q` is the compensated form minus `⟨Q u, u⟩`. Subtracting the capture bound from
the lower bound of the compensated form leaves the stated coercivity.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.1, (4.1)-(4.3),
  p. 24, Section 4.2.2, Lemma 3, and Section 4.3, (4.20), p. 28.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev RealInnerProductSpace

set_option linter.missingDocs true

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "Vσ" => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω))

/-- **Coercivity after a finite-rank capture** (Hou, Wang and Yang, (4.20)). Let `Q` compensate
the gradient of a divergence-free background `b` up to `η₁`, as in their (4.3), and let `u` be a
solenoidal zero-boundary field for which the finite-rank term captures the compensation:

`⟨Q u, u⟩ - ∑ⱼ ⟪qⱼ, u⟫ ⟪fⱼ, u⟫ ≤ M₁ ‖∇u‖² + M₂ ‖u‖²`.

Then the similarity form without compensation, plus the finite-rank term, is at least
`((n - 2) / 4 - η₁ - M₂) ‖u‖² + (1 - M₁) ‖∇u‖²` at `u`. -/
theorem similarityPrincipalForm_zero_add_finiteRank_ge {F : Type*} [Fintype F] (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω)
    (η₁ : ℝ) (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η₁ * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) + Q k j) x * v j * v k)
    (q f : F → PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Ω)) {M₁ M₂ : ℝ} (u : Vσ)
    (hcapture : (∑ k, ∑ j, ⟪Q k j • baseCoordCLM ((u : H¹₀(Ω; ℝ^n)) j),
        baseCoordCLM ((u : H¹₀(Ω; ℝ^n)) k)⟫) -
      ∑ j, ⟪q j, solenoidalMassCoordinates u⟫ * ⟪f j, solenoidalMassCoordinates u⟫ ≤
        M₁ * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
          M₂ * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2) :
    (((n : ℝ) - 2) / 4 - η₁ - M₂) * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        (1 - M₁) * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤
      similarityPrincipalForm hΩ hb b 0 (u : H¹₀(Ω; ℝ^n)) (u : H¹₀(Ω; ℝ^n)) +
        ∑ j, ⟪q j, solenoidalMassCoordinates u⟫ * ⟪f j, solenoidalMassCoordinates u⟫ := by
  have hlower := similarityPrincipalForm_lower_bound hΩ hb b Q η₁ hdiv hcompensation
    (u : H¹₀(Ω; ℝ^n))
  rw [similarityPrincipalForm_apply_eq_add] at hlower
  linarith

end NavierStokes
