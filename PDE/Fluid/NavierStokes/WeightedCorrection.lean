/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.FiniteRankCorrection
public import PDE.Analysis.Variational.WeightedEnergyBall

/-!
# Stationary fluid corrections in a weighted energy ball

On a bounded domain, the correction of an approximate self-similar profile solves a coercive
equation with a transport term and a quadratic load built from a finite-rank reconstruction. We
find a solution in one ball of the weighted energy `η ‖u‖² + ‖∇u‖²`, from the two coercivity
margins, the residual and three finite certificates of the reconstruction. This is the fixed
point of Section 4.3 of Hou, Wang and Yang in its weighted-ball form; the versions with separate
value and gradient radii are `NavierStokes.exists_solenoidal_transport_correction_on` and
`NavierStokes.exists_solenoidal_transport_correction_of_finiteRank_on`. The coercivity and the
residual bound stay hypotheses. In the application they come from the compensation of the
background gradient and from the finite-rank capture.

## Main results

* `exists_solenoidal_weighted_transport_correction_on`: on any bounded domain, a correction in
  the weighted ball of a closed subspace of the solenoidal space, such as a symmetry sector, for
  a supplied load bound `M`.
* `exists_solenoidal_weighted_transport_correction_of_finiteRank_on`: the same with the load
  bound `M = √g A + g I` from the three certificates.

## How it works

The solenoidal zero-boundary space embeds compactly in `L⁴`. The transport term is skew, so it
does not change coercivity, and the quadratic load is Lipschitz for the `L⁴` norm on every ball
(`exists_norm_correctionLoad_sub_le_of_norm_le`). With a coercivity `a ‖u‖² + b ‖∇u‖²`, a
residual of size `ε` and a load of size `M ‖u‖²`, both in the `L²` norm, the weighted ball of
radius `r` is invariant as soon as `η b ≤ a` and `ε + (M / η) r² ≤ b √η r`. Then Schauder's
fixed point theorem applies, in the form
`PDE.Analysis.Variational.exists_solution_of_weighted_energy_transport_on_submodule`. For a
finite-rank reconstruction `u + ∑ⱼ ⟪qⱼ, u⟫ φⱼ` the constant is `M = √g A + g I`, with `g` a Gram
bound of the `qⱼ`, `A` a bound of the derivatives of the `φⱼ` and `I` a bound of their pairwise
interactions.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.3, the map (4.27), the
  estimates (4.30) to (4.33), Assumption 6 with (4.34), (4.35) and the weighted energy ball, the
  continuity estimate (4.36) to (4.38) and the fixed point (4.39).
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory Matrix SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev BigOperators RealInnerProductSpace

set_option linter.missingDocs true

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "Vσ" => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω))

-- The cached norms of `SimilarityTransport`, before the mixed Lebesgue operator spaces.
attribute [local instance] innerProductSpaceSolenoidal normedSpaceSolenoidal
  completeSpaceSolenoidal normedAddCommGroupSolenoidal seminormedAddCommGroupSolenoidal
  normedAddCommGroupL4Field normedSpaceL4Field seminormedAddCommGroupL4Field
  normedAddCommGroupSolenoidalDual seminormedAddCommGroupSolenoidalDual
  normedAddCommGroupL4FieldToSolenoidalDual seminormedAddCommGroupL4FieldToSolenoidalDual

/-- **The bounded-domain correction in a weighted energy ball** (Hou–Wang–Yang, Section 4.3,
the fixed point (4.39)). In a closed subspace `S` of the solenoidal space, such as a symmetry
sector, let the form `B` have the coercivity margins `a`, `b`, the residual `ell` size `ε` and
the transport load size `M ‖u‖²` on the ball, both in the `L²` norm. For a weight `η > 0` with
`η b ≤ a` and a radius `r ≥ 0` with `ε + (M / η) r² ≤ b √η r` there is a solution `u ∈ S` with
`η ‖u‖² + ‖∇u‖² ≤ r²`, tested by the fields of `S`. -/
theorem exists_solenoidal_weighted_transport_correction_on (S : Submodule ℝ Vσ)
    (hS : IsClosed (S : Set Vσ))
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
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
    (ell : StrongDual ℝ Vσ) {a b η r ε M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hηb : η * b ≤ a) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hcoercive : ∀ u ∈ S,
      a * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        b * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ B u u)
    (hell : ∀ v ∈ S,
      |ell v| ≤ ε * ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hN : ∀ u ∈ S, η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ r ^ 2 → ∀ v ∈ S,
      |ContinuousLinearMap.transportPairing
        (R (solenoidalL4Embedding J u)) (S' (solenoidalL4Embedding J u))
        (solenoidalL4Embedding J v)| ≤
          M * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 *
            ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hbudget : ε + M / η * r ^ 2 ≤ b * √η * r) :
    ∃ u ∈ S, η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ r ^ 2 ∧ ∀ v ∈ S,
      B u v + IncompressibleFlow.l4Convection J (R (solenoidalL4Embedding J u))
        (u : H¹₀(Ω; ℝ^n)) (v : H¹₀(Ω; ℝ^n)) +
        ContinuousLinearMap.transportPairing
          (R (solenoidalL4Embedding J u)) (S' (solenoidalL4Embedding J u))
          (solenoidalL4Embedding J v) = ell v := by
  let inc := (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω)).ker.subtypeL
  let e := solenoidalL4Embedding J
  let mass := ZeroBoundaryVectorSpace.toLp.comp inc
  let gradient := ZeroBoundaryVectorSpace.gradient.comp inc
  let T := PDE.Analysis.ContinuousTrilinearForm.restrict
    (IncompressibleFlow.l4Convection J) (R.comp e) inc inc
  let P := PDE.Analysis.ContinuousTrilinearForm.restrict
    ContinuousLinearMap.transportPairing R S' e
  have he : Function.Injective e := by
    intro u v huv
    apply Subtype.ext
    exact IncompressibleFlow.vectorL4Embedding_injective J hinj huv
  have hecompact : IsCompactOperator e :=
    (IncompressibleFlow.vectorL4Embedding_isCompactOperator J hcompact).comp_clm inc
  have hnorm (u : Vσ) : ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 :=
    ZeroBoundaryVectorSpace.norm_sq (u : H¹₀(Ω; ℝ^n))
  have hcancel (u : Vσ) (hu : u ∈ S) (v : Vσ) : T u v v = 0 :=
    IncompressibleFlow.l4Convection_energy_eq_zero_of_sobolev J hJ
      (R (e u)) (adv u) (hA u hu) (hadv u hu) (v : H¹₀(Ω; ℝ^n))
  obtain ⟨k, htransport⟩ := exists_norm_correctionTransport_le J R
  -- The weighted ball lies in the ball of radius `r / √η + r`, where the load is Lipschitz.
  obtain ⟨C, hcontinuous⟩ := exists_norm_correctionLoad_sub_le_of_norm_le J R S'
    (ρ := r / √η + r) (by positivity)
  have hball (u : Vσ) (hu : η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2) : ‖u‖ ≤ r / √η + r :=
    PDE.Analysis.Variational.norm_le_of_mem_weightedEnergyBall hη hr (hnorm u) hu
  exact PDE.Analysis.Variational.exists_solution_of_weighted_energy_transport_on_submodule S hS
    mass gradient (fun u _ ↦ hnorm u) B T (ContinuousLinearMap.id ℝ Vσ)
    (fun u hu v _ ↦ hcancel u hu v) e he.injOn hecompact
    (PDE.Analysis.Variational.quadraticLoad e P) ell ha hb hη hηb hr hM hcoercive hell hN
    (fun u _ v _ ↦ htransport u v)
    (fun u _ hu v _ hv ↦ hcontinuous u (hball u hu) v (hball v hv)) hbudget

/-- **The bounded-domain correction with a finite-rank reconstruction, in a weighted energy
ball** (Hou–Wang–Yang, Section 4.3). The load bound of
`exists_solenoidal_weighted_transport_correction_on` is `M₃ = √g A + g I`, the constant (4.33):
`g` bounds the Gram matrix of the `qⱼ` (the constant `Θ_Q` of (4.32)), `A` the derivatives of
the `φⱼ` in `L^∞` and `I` the pairwise interactions `φᵢ · ∇φⱼ` in `L²`. The budget
`ε + (M₃ / η) r² ≤ b √η r` is the invariance of the ball, an equality for the radius (4.35). -/
theorem exists_solenoidal_weighted_transport_correction_of_finiteRank_on {F : Type*} [Fintype F]
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
    (ell : StrongDual ℝ Vσ) {a b η r ε g A I : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hηb : η * b ≤ a) (hr : 0 ≤ r)
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
    (hbudget : ε + (√g * A + g * I) / η * r ^ 2 ≤ b * √η * r) :
    ∃ u ∈ S, η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ r ^ 2 ∧ ∀ v ∈ S,
      B u v + IncompressibleFlow.l4Convection J (R (solenoidalL4Embedding J u))
        (u : H¹₀(Ω; ℝ^n)) (v : H¹₀(Ω; ℝ^n)) +
        ContinuousLinearMap.transportPairing
          (R (solenoidalL4Embedding J u)) (S' (solenoidalL4Embedding J u))
          (solenoidalL4Embedding J v) = ell v := by
  apply exists_solenoidal_weighted_transport_correction_on S hS J hJ hinj hcompact B R S' adv
    hA hadv ell ha hb hη hηb hr (by positivity) hcoercive hell _ hbudget
  intro u hu _ v _
  rw [hS' u hu]
  simpa only [norm_solenoidalMassCoordinates] using
    ContinuousLinearMap.abs_transportPairing_finiteRank_le q φ D₂ Dtop
      (solenoidalMassCoordinates u) (solenoidalMassCoordinates v)
      (R (solenoidalL4Embedding J u)) (solenoidalL4Embedding J v) (hR u hu) hD
      (solenoidalL4Embedding_eq_massCoordinates J hJ v) hg hAn hIn hgram hoperator hinteraction

end NavierStokes
