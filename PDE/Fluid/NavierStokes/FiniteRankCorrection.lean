/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.FiniteRankTransport
public import PDE.Fluid.NavierStokes.SimilarityCorrection

/-!
# Stationary fluid corrections from finite-rank basis certificates

Let the unknown `u` of the bounded-domain solenoidal correction be reconstructed as
`u + ∑ⱼ ⟪qⱼ, u⟫ φⱼ`, with derivative part `∑ⱼ ⟪qⱼ, u⟫ Dⱼ` for essentially bounded matrices `Dⱼ`.
Three finite certificates then replace the nonlinear mass estimate of
`exists_solenoidal_transport_correction_on`: a Gram bound `g` for the `qⱼ`, a bound `A` for the
operator norms of the `Dⱼ` and a bound `I` for the pairwise interactions `Dⱼ φᵢ`. Under the budgets
`ε + (√g A + g I) r₀² ≤ a r₀` and `a r₀² ≤ 4 b r₁²` there is a correction `u` in a closed subspace
`S`, such as the even symmetry sector, with mass at most `r₀` and gradient at most `r₁` that solves
the corrected equation against the test fields of `S`
(`exists_solenoidal_transport_correction_of_finiteRank_on`;
`exists_solenoidal_transport_correction_of_finiteRank` is the case of the whole solenoidal space).
The coercivity and residual bounds stay explicit hypotheses, required only on `S`, and the
correction basis need not have zero trace on the artificial boundary.

## How it works

We apply `exists_solenoidal_transport_correction_on` and supply its nonlinear mass estimate from
`ContinuousLinearMap.abs_transportPairing_finiteRank_le`, which bounds the transport pairing of the
reconstructed field and the finite-rank derivative by `(√g A + g I) ‖u‖² ‖v‖`. That bound is proved
the way Hou, Wang and Yang prove their bound (4.28) for the modified fixed-point map (4.24): a Gram
bound for the coefficients, then the Cauchy–Schwarz inequality against the basis derivatives and the
pairwise basis interactions. The scalar mass coordinates `solenoidalMassCoordinates` connect the two
statements: they have the norm of the `L²` inclusion (`norm_solenoidalMassCoordinates`) and agree
almost everywhere with the faithful `L⁴` inclusion (`solenoidalL4Embedding_eq_massCoordinates`).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.24)-(4.28) and the
  proof of (4.28), pp. 28-30.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory Matrix SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev BigOperators RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "Vσ" => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω))

/-- Scalar `L²` coordinates of a solenoidal energy field, with their finite
Hilbert norm. This is the same mass norm as the Euclidean-valued inclusion. -/
def solenoidalMassCoordinates (u : Vσ) : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Ω) :=
  WithLp.toLp 2 (fun i ↦ baseCoordCLM ((u : H¹₀(Ω; ℝ^n)) i))

/-- Coordinate evaluation of the solenoidal mass realization. -/
theorem solenoidalMassCoordinates_apply (u : Vσ) (i : Fin n) :
    solenoidalMassCoordinates u i = baseCoordCLM ((u : H¹₀(Ω; ℝ^n)) i) := rfl

/-- The scalar-coordinate mass norm equals the Euclidean-valued `L²` norm. -/
theorem norm_solenoidalMassCoordinates (u : Vσ) :
    ‖solenoidalMassCoordinates u‖ = ‖ZeroBoundaryVectorSpace.toLp
      (u : H¹₀(Ω; ℝ^n))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, ZeroBoundaryVectorSpace.norm_toLp_sq]
  rfl

/-- A faithful scalar `L⁴` inclusion agrees with the mass realization almost
everywhere, without a choice of pointwise Sobolev representatives. -/
theorem solenoidalL4Embedding_eq_massCoordinates
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (baseCoordCLM u : ℝ^n → ℝ)) (u : Vσ) (i : Fin n) :
    (solenoidalL4Embedding J u i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      solenoidalMassCoordinates u i :=
  hJ ((u : H¹₀(Ω; ℝ^n)) i)

/-- Finite-rank Gram and basis certificates supply the nonlinear mass estimate for a
solenoidal stationary correction in a closed subspace `S`, such as a symmetry sector. The
reconstruction and advecting-field identities, coercivity and residual bounds are required
only on `S`, and the equation holds against the test fields of `S`. All radius and norm
conventions are those of `exists_solenoidal_transport_correction`. -/
theorem exists_solenoidal_transport_correction_of_finiteRank_on {F : Type*} [Fintype F]
    (S : Submodule ℝ Vσ) (hS : IsClosed (S : Set Vσ))
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (baseCoordCLM u : ℝ^n → ℝ))
    (hinj : Function.Injective J) (hcompact : IsCompactOperator J)
    (B : Vσ →L[ℝ] StrongDual ℝ Vσ)
    (R : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ]
      PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω))
    (S' : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ]
      PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n 2 Ω))
    (adv : Vσ → Fin n → H¹(Ω))
    (hA : ∀ u ∈ S, ∀ i, (R (solenoidalL4Embedding J u) i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (adv u i) : ℝ^n → ℝ))
    (hadv : ∀ u ∈ S, negativeDivergence (adv u) = 0)
    (q φ : F → PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Ω))
    (D₂ : F → PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n 2 Ω))
    (Dtop : F → PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ Ω))
    (hR : ∀ u ∈ S, ∀ i, (R (solenoidalL4Embedding J u) i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (solenoidalMassCoordinates u +
        ∑ j, ⟪q j, solenoidalMassCoordinates u⟫ • φ j) i)
    (hS' : ∀ u ∈ S, S' (solenoidalL4Embedding J u) =
      ∑ j, ⟪q j, solenoidalMassCoordinates u⟫ • D₂ j)
    (hD : ∀ j ki, (D₂ j ki : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] Dtop j ki)
    (ell : StrongDual ℝ Vσ) {a b r₀ r₁ ε g A I : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hg : 0 ≤ g) (hAn : 0 ≤ A) (hIn : 0 ≤ I)
    (hgram : ∀ c : F → ℝ,
      c ⬝ᵥ (Matrix.gram ℝ q) *ᵥ c ≤ g * ∑ j, c j ^ 2)
    (hoperator : ∑ j, ‖ContinuousLinearMap.l2MatrixTransport (Dtop j)‖ ^ 2 ≤ A ^ 2)
    (hinteraction : ∑ i, ∑ j,
      ‖ContinuousLinearMap.l2MatrixTransport (Dtop j) (φ i)‖ ^ 2 ≤ I ^ 2)
    (hcoercive : ∀ u ∈ S,
      a * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        b * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ B u u)
    (hell : ∀ v ∈ S,
      |ell v| ≤ ε * ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hbudget : ε + (Real.sqrt g * A + g * I) * r₀ ^ 2 ≤ a * r₀)
    (hgradient : a * r₀ ^ 2 ≤ 4 * b * r₁ ^ 2) :
    ∃ u ∈ S, ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀ ∧
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁ ∧ ∀ v ∈ S,
      B u v + IncompressibleFlow.l4Convection J (R (solenoidalL4Embedding J u))
        (u : H¹₀(Ω; ℝ^n)) (v : H¹₀(Ω; ℝ^n)) +
        ContinuousLinearMap.transportPairing
          (R (solenoidalL4Embedding J u)) (S' (solenoidalL4Embedding J u))
          (solenoidalL4Embedding J v) = ell v := by
  apply exists_solenoidal_transport_correction_on S hS J hJ hinj hcompact B R S' adv hA hadv
    ell ha hb hr₀ hr₁ (by positivity) hcoercive hell _ hbudget hgradient
  intro u hu _ _ v _
  rw [hS' u hu]
  simpa only [norm_solenoidalMassCoordinates] using
    ContinuousLinearMap.abs_transportPairing_finiteRank_le q φ D₂ Dtop
      (solenoidalMassCoordinates u) (solenoidalMassCoordinates v)
      (R (solenoidalL4Embedding J u)) (solenoidalL4Embedding J v) (hR u hu) hD
      (solenoidalL4Embedding_eq_massCoordinates J hJ v) hg hAn hIn hgram hoperator hinteraction

/-- Finite-rank Gram and basis certificates supply the nonlinear mass estimate
for a solenoidal stationary correction. All radius and norm conventions are
those of `exists_solenoidal_transport_correction`. -/
theorem exists_solenoidal_transport_correction_of_finiteRank {F : Type*} [Fintype F]
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (baseCoordCLM u : ℝ^n → ℝ))
    (hinj : Function.Injective J) (hcompact : IsCompactOperator J)
    (B : Vσ →L[ℝ] StrongDual ℝ Vσ)
    (R : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ]
      PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω))
    (S : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ]
      PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n 2 Ω))
    (adv : Vσ → Fin n → H¹(Ω))
    (hA : ∀ u i, (R (solenoidalL4Embedding J u) i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (adv u i) : ℝ^n → ℝ))
    (hadv : ∀ u, negativeDivergence (adv u) = 0)
    (q φ : F → PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Ω))
    (D₂ : F → PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n 2 Ω))
    (Dtop : F → PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n ∞ Ω))
    (hR : ∀ u i, (R (solenoidalL4Embedding J u) i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (solenoidalMassCoordinates u +
        ∑ j, ⟪q j, solenoidalMassCoordinates u⟫ • φ j) i)
    (hS : ∀ u, S (solenoidalL4Embedding J u) =
      ∑ j, ⟪q j, solenoidalMassCoordinates u⟫ • D₂ j)
    (hD : ∀ j ki, (D₂ j ki : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] Dtop j ki)
    (ell : StrongDual ℝ Vσ) {a b r₀ r₁ ε g A I : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hg : 0 ≤ g) (hAn : 0 ≤ A) (hIn : 0 ≤ I)
    (hgram : ∀ c : F → ℝ,
      c ⬝ᵥ (Matrix.gram ℝ q) *ᵥ c ≤ g * ∑ j, c j ^ 2)
    (hoperator : ∑ j, ‖ContinuousLinearMap.l2MatrixTransport (Dtop j)‖ ^ 2 ≤ A ^ 2)
    (hinteraction : ∑ i, ∑ j,
      ‖ContinuousLinearMap.l2MatrixTransport (Dtop j) (φ i)‖ ^ 2 ≤ I ^ 2)
    (hcoercive : ∀ u : Vσ,
      a * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        b * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ B u u)
    (hell : ∀ v : Vσ,
      |ell v| ≤ ε * ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hbudget : ε + (Real.sqrt g * A + g * I) * r₀ ^ 2 ≤ a * r₀)
    (hgradient : a * r₀ ^ 2 ≤ 4 * b * r₁ ^ 2) :
    ∃ u : Vσ, ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀ ∧
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁ ∧ ∀ v : Vσ,
      B u v + IncompressibleFlow.l4Convection J (R (solenoidalL4Embedding J u))
        (u : H¹₀(Ω; ℝ^n)) (v : H¹₀(Ω; ℝ^n)) +
        ContinuousLinearMap.transportPairing
          (R (solenoidalL4Embedding J u)) (S (solenoidalL4Embedding J u))
          (solenoidalL4Embedding J v) = ell v := by
  obtain ⟨u, -, hu₀, hu₁, heq⟩ := exists_solenoidal_transport_correction_of_finiteRank_on ⊤
    (by simp only [Submodule.top_coe, isClosed_univ]) J hJ hinj hcompact B R S adv
    (fun u _ ↦ hA u) (fun u _ ↦ hadv u) q φ D₂ Dtop (fun u _ ↦ hR u) (fun u _ ↦ hS u) hD ell
    ha hb hr₀ hr₁ hg hAn hIn hgram hoperator hinteraction (fun u _ ↦ hcoercive u)
    (fun v _ ↦ hell v) hbudget hgradient
  exact ⟨u, hu₀, hu₁, fun v ↦ heq v Submodule.mem_top⟩

end NavierStokes
