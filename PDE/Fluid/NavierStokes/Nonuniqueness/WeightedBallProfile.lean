/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileWeakLimit
public import PDE.Fluid.NavierStokes.WeightedCorrection
public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Closed

/-!
# The exact profile from finite-rank data, in a weighted energy ball

Given an approximate self-similar profile `B` with a small residual and a finite-rank
approximate inverse of the compact part of its linearization, there is an exact profile nearby,
and the correction lies in the ball `η ‖w‖² + ‖∇w‖² ≤ r²` of the weighted energy. This is the
proof of Proposition 1 of Hou, Wang and Yang, for all data with the stated certificates. The ball
data (the restrictions of the whole-space fields, the reconstruction maps, the profile forms) and
the coercivity are hypotheses on every ball.

## Main results

* `exists_weakProfileEquation_of_weighted_ball`: for every even background and all finite-rank
  data with the stated certificates, the exact profile, with the correction in the weighted ball
  and with every bound that the ball solutions share.

## How it works

On each ball `B(0, ρ)` the semi-implicit map has a fixed point in the weighted ball
(`exists_solenoidal_weighted_transport_correction_of_finiteRank_on`), because the invariance
inequality `ε + (M₃ / η) r² ≤ b √η r` does not involve `ρ`. The zero extensions of the fixed
points are bounded in `H¹(ℝ³)`, so they have a weak limit, and the limit solves the weak profile
equation (`exists_weakProfileEquation_of_ball_corrections_of_bound`). The bound passed through
the limit is the supremum of `p ‖u‖ + q ‖∇u‖` over the fixed points, so every bound of such a
combination that holds at all of them holds at the limit. The weighted ball is one such family of
bounds, through its support function.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.3: Proposition 1, the
  fixed points (4.39) on the balls and their weak limit.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
open scoped Topology Distributions Matrix

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

open NavierStokes.Symmetry

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))
local notation "M" => PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 univ)
local notation "Vb" ρ => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))

variable {F : Type*} [Fintype F]

/-- **The exact profile from finite-rank data, in a weighted energy ball** (Hou–Wang–Yang,
Section 4.3: the fixed points (4.39) on the balls and their weak limit). The data are those of
`exists_weakProfileEquation_of_ball_corrections_of_bound`, and on every ball `B(0, ρ)`, `ρ ≥ ρ₀`,
those of `exists_solenoidal_weighted_transport_correction_of_finiteRank_on` in the even sector:
the compact `L⁴` inclusion, the advecting field, the coercivity margins `a`, `b` of the profile
form, the residual bound `ε`, and the three certificates `g`, `A`, `I` of the finite-rank
reconstruction. For a weight `η > 0` with `η b ≤ a` and a radius `r` with

`ε + (M₃ / η) r² ≤ b √η r`,  `M₃ = √g A + g I`,

there is an even solenoidal whole-space `w` with `η ‖w‖² + ‖∇w‖² ≤ r²` such that
`B + w + ∑ⱼ ⟪qⱼ, w⟫ Φⱼ` is an even axisymmetric weak profile. Moreover every bound of
`p ‖u‖ + q ‖∇u‖`, `p, q ≥ 0`, that all solutions of the ball problems in the weighted ball
share holds for `w`. -/
theorem exists_weakProfileEquation_of_weighted_ball {B E : ℝ^3 → ℝ^3}
    (hB : IsEvenAxisymmetric B) (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume)
    (hE : ∀ φ, IsSolenoidalTestField φ → IsEvenAxisymmetric φ →
      ∫ x, weakProfileDensity B φ x = ∫ x, ⟪E x, φ x⟫)
    (q : F → M) (Φ : F → H) (f : F → ℝ^3 → ℝ^3)
    (hΦ : ∀ j, Stationary.divergenceCLM (Φ j) = 0) (hΦe : ∀ j, Φ j ∈ evenSectorH1)
    (hΦeq : ∀ j φ, IsSolenoidalTestField φ → IsEvenAxisymmetric φ →
      ∫ x, ⟪Stationary.representative (Φ j) x, profileAdjoint B φ x⟫ = ∫ x, ⟪f j x, φ x⟫)
    (ρ₀ : ℝ) (bg : ∀ ρ : ℝ, Fin 3 → W^{1,∞}(Metric.ball (0 : ℝ^3) ρ))
    (hbg : ∀ ρ, ρ₀ ≤ ρ → ∀ i, (((bg ρ i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
      (baseIndex 3 1) : DerivLp 3 ∞ (Metric.ball (0 : ℝ^3) ρ)) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ B x i)
    (hbgdiv : ∀ ρ, ρ₀ ≤ ρ → ∑ i, (bg ρ i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
      (singleDerivIndex 3 i) = 0)
    (J : ∀ ρ : ℝ, H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hJ : ∀ ρ, ρ₀ ≤ ρ → ∀ u, (J ρ u : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (baseCoordCLM u : ℝ^3 → ℝ))
    (R : ∀ ρ : ℝ, PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)) →L[ℝ]
      PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)))
    (S : ∀ ρ : ℝ, PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)) →L[ℝ]
      PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (profileForm : ∀ ρ : ℝ, (Vb ρ) →L[ℝ] StrongDual ℝ (Vb ρ))
    (qB φB fB : ∀ ρ : ℝ, F → PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (D₂ : ∀ ρ : ℝ, F → PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (hq : ∀ ρ, ρ₀ ≤ ρ → ∀ j i, (qB ρ j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] (q j i : ℝ^3 → ℝ))
    (hφB : ∀ ρ, ρ₀ ≤ ρ → ∀ j i, (φB ρ j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ Stationary.representative (Φ j) x i)
    (hD₂ : ∀ ρ, ρ₀ ≤ ρ → ∀ j k i, (D₂ ρ j (k, i) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ Stationary.gradientRepresentative (Φ j) x k i)
    (hfB : ∀ ρ, ρ₀ ≤ ρ → ∀ j i, (fB ρ j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ f j x i)
    (hR : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ, ∀ i,
      (R ρ (solenoidalL4Embedding (J ρ) u) i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] ((solenoidalMassCoordinates u +
          ∑ j, ⟪qB ρ j, solenoidalMassCoordinates u⟫ • φB ρ j) i : ℝ^3 → ℝ))
    (hS : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ, S ρ (solenoidalL4Embedding (J ρ) u) =
      ∑ j, ⟪qB ρ j, solenoidalMassCoordinates u⟫ • D₂ ρ j)
    (hprofile : ∀ ρ, ρ₀ ≤ ρ → ∀ u v, profileForm ρ u v =
      similarityPrincipalForm Metric.isOpen_ball Metric.isBounded_ball (bg ρ) 0
        (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ∑ j, ⟪qB ρ j, solenoidalMassCoordinates u⟫ * ⟪fB ρ j, solenoidalMassCoordinates v⟫)
    (hinj : ∀ ρ, ρ₀ ≤ ρ → Function.Injective (J ρ))
    (hcompact : ∀ ρ, ρ₀ ≤ ρ → IsCompactOperator (J ρ))
    (adv : ∀ ρ : ℝ, (Vb ρ) → Fin 3 → H¹(Metric.ball (0 : ℝ^3) ρ))
    (hA : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ, ∀ i,
      (R ρ (solenoidalL4Embedding (J ρ) u) i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] (wkpBaseCoordinateCLM (adv ρ u i) : ℝ^3 → ℝ))
    (hadv : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ, negativeDivergence (adv ρ u) = 0)
    (Dtop : ∀ ρ : ℝ, F → PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 ∞ (Metric.ball (0 : ℝ^3) ρ)))
    (hDtop : ∀ ρ, ρ₀ ≤ ρ → ∀ j ki, (D₂ ρ j ki : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] Dtop ρ j ki)
    (ell : ∀ ρ : ℝ, StrongDual ℝ (Vb ρ))
    (hellEq : ∀ ρ, ρ₀ ≤ ρ → ∀ v : Vb ρ, ell ρ v =
      -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x, (ZeroBoundaryVectorSpace.toLp
        (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3) x⟫)
    {a b η r ε g A I : ℝ} (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hηb : η * b ≤ a)
    (hr : 0 ≤ r) (hg : 0 ≤ g) (hAn : 0 ≤ A) (hIn : 0 ≤ I)
    (hgram : ∀ ρ, ρ₀ ≤ ρ → ∀ c : F → ℝ,
      c ⬝ᵥ (Matrix.gram ℝ (qB ρ)) *ᵥ c ≤ g * ∑ j, c j ^ 2)
    (hoperator : ∀ ρ, ρ₀ ≤ ρ →
      ∑ j, ‖ContinuousLinearMap.l2MatrixTransport (Dtop ρ j)‖ ^ 2 ≤ A ^ 2)
    (hinteraction : ∀ ρ, ρ₀ ≤ ρ → ∑ i, ∑ j,
      ‖ContinuousLinearMap.l2MatrixTransport (Dtop ρ j) (φB ρ i)‖ ^ 2 ≤ I ^ 2)
    (hcoercive : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ,
      a * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
        b * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 ≤
          profileForm ρ u u)
    (hell : ∀ ρ, ρ₀ ≤ ρ → ∀ v ∈ evenSector ρ,
      |ell ρ v| ≤ ε * ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖)
    (hbudget : ε + (√g * A + g * I) / η * r ^ 2 ≤ b * √η * r) :
    ∃ w ∈ evenSectorH1,
      η * ‖Stationary.massCLM w‖ ^ 2 + ‖Stationary.gradientCLM w‖ ^ 2 ≤ r ^ 2 ∧
      (∀ bound : ℝ → ℝ → ℝ,
        (∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ,
          η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
            ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 ≤ r ^ 2 →
          (∀ v ∈ evenSector ρ, profileForm ρ u v +
        IncompressibleFlow.l4Convection (J ρ) (R ρ (solenoidalL4Embedding (J ρ) u))
          (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ContinuousLinearMap.transportPairing (R ρ (solenoidalL4Embedding (J ρ) u))
          (S ρ (solenoidalL4Embedding (J ρ) u)) (solenoidalL4Embedding (J ρ) v) =
        -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x, (ZeroBoundaryVectorSpace.toLp
          (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3) x⟫) →
          ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
            p * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ +
              q * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ≤
                bound p q) →
        ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
          p * ‖Stationary.massCLM w‖ + q * ‖Stationary.gradientCLM w‖ ≤ bound p q) ∧
      Stationary.divergenceCLM w = 0 ∧
      IsEvenAxisymmetric (B + Stationary.representative (w + finiteRankCorrection q Φ w)) ∧
      WeakProfileEquation (B + Stationary.representative (w + finiteRankCorrection q Φ w)) := by
  classical
  -- A solution of the ball problem in the weighted ball, for every admissible radius.
  have hexists (ρ : ℝ) (hρ : ρ₀ ≤ ρ) : ∃ u ∈ evenSector ρ,
      η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 ≤ r ^ 2 ∧
      ∀ v ∈ evenSector ρ, profileForm ρ u v +
        IncompressibleFlow.l4Convection (J ρ) (R ρ (solenoidalL4Embedding (J ρ) u))
          (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ContinuousLinearMap.transportPairing (R ρ (solenoidalL4Embedding (J ρ) u))
          (S ρ (solenoidalL4Embedding (J ρ) u)) (solenoidalL4Embedding (J ρ) v) =
        -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x, (ZeroBoundaryVectorSpace.toLp
          (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3) x⟫ := by
    obtain ⟨u, hu, hub, hueq⟩ :=
      exists_solenoidal_weighted_transport_correction_of_finiteRank_on (evenSector ρ)
        (evenSector_isClosed ρ) (J ρ) (hJ ρ hρ) (hinj ρ hρ) (hcompact ρ hρ) (profileForm ρ)
        (R ρ) (S ρ) (adv ρ) (hA ρ hρ) (hadv ρ hρ) (qB ρ) (φB ρ) (D₂ ρ) (Dtop ρ) (hR ρ hρ)
        (hS ρ hρ) (hDtop ρ hρ) (ell ρ) ha hb hη hηb hr hg hAn hIn (hgram ρ hρ)
        (hoperator ρ hρ) (hinteraction ρ hρ) (hcoercive ρ hρ) (hell ρ hρ) hbudget
    exact ⟨u, hu, hub, fun v hv ↦ by rw [hueq v hv, hellEq ρ hρ]⟩
  -- The values of `p ‖u‖ + q ‖∇u‖` over all ball solutions, and their supremum.
  let vals : ℝ → ℝ → Set ℝ := fun p q ↦ {t | ∃ ρ, ρ₀ ≤ ρ ∧ ∃ u ∈ evenSector ρ,
    η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 ≤ r ^ 2 ∧
    (∀ v ∈ evenSector ρ, profileForm ρ u v +
        IncompressibleFlow.l4Convection (J ρ) (R ρ (solenoidalL4Embedding (J ρ) u))
          (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ContinuousLinearMap.transportPairing (R ρ (solenoidalL4Embedding (J ρ) u))
          (S ρ (solenoidalL4Embedding (J ρ) u)) (solenoidalL4Embedding (J ρ) v) =
        -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x, (ZeroBoundaryVectorSpace.toLp
          (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3) x⟫) ∧
    t = p * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ +
      q * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖}
  have hvals (p q : ℝ) : BddAbove (vals p q) := by
    refine ⟨r * √(p ^ 2 / η + q ^ 2), ?_⟩
    rintro t ⟨ρ, -, u, -, hub, -, rfl⟩
    exact PDE.Analysis.Variational.mul_add_mul_le_of_weighted_energy_le hη hr hub p q
  obtain ⟨w, hwS, hwb, hwdiv, heven, heq⟩ :=
    exists_weakProfileEquation_of_ball_corrections_of_bound hB hBm hB2 hE q Φ f hΦ hΦe hΦeq ρ₀ bg
      hbg hbgdiv J hJ R S profileForm qB φB fB D₂ hq hφB hD₂ hfB hR hS hprofile
      (fun p q ↦ sSup (vals p q)) (fun ρ hρ ↦ by
        obtain ⟨u, hu, hub, hueq⟩ := hexists ρ hρ
        exact ⟨u, hu, fun p q _ _ ↦ le_csSup (hvals p q) ⟨ρ, hρ, u, hu, hub, hueq, rfl⟩, hueq⟩)
  have hfamily (bound : ℝ → ℝ → ℝ)
      (hbound : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ,
        η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
          ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 ≤ r ^ 2 →
        (∀ v ∈ evenSector ρ, profileForm ρ u v +
        IncompressibleFlow.l4Convection (J ρ) (R ρ (solenoidalL4Embedding (J ρ) u))
          (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ContinuousLinearMap.transportPairing (R ρ (solenoidalL4Embedding (J ρ) u))
          (S ρ (solenoidalL4Embedding (J ρ) u)) (solenoidalL4Embedding (J ρ) v) =
        -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x, (ZeroBoundaryVectorSpace.toLp
          (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3) x⟫) →
        ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
          p * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ +
            q * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ≤
              bound p q) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
      p * ‖Stationary.massCLM w‖ + q * ‖Stationary.gradientCLM w‖ ≤ bound p q := by
    refine (hwb p q hp hq).trans (csSup_le ?_ ?_)
    · obtain ⟨u, hu, hub, hueq⟩ := hexists ρ₀ le_rfl
      exact ⟨_, ρ₀, le_rfl, u, hu, hub, hueq, rfl⟩
    · rintro t ⟨ρ, hρ, u, hu, hub, hueq, rfl⟩
      exact hbound ρ hρ u hu hub hueq p q hp hq
  refine ⟨w, hwS, ?_, hfamily, hwdiv, heven, heq⟩
  exact PDE.Analysis.Variational.weighted_energy_le_of_forall_mul_add_mul_le hη hr
    (norm_nonneg _) (norm_nonneg _)
    (hfamily (fun p q ↦ r * √(p ^ 2 / η + q ^ 2)) fun ρ _ u _ hub _ p q _ _ ↦
      PDE.Analysis.Variational.mul_add_mul_le_of_weighted_energy_le hη hr hub p q)

end NavierStokes.Nonuniqueness
