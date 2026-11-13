/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.SimilarityTransport

/-!
# Nonlinear correction for the similarity equation

Compact `L⁴` inclusion turns the coercive solenoidal transport form into a nonlinear
correction with separate value and gradient radii, for supplied reconstruction maps
and sharp residual and remainder budgets. The correction can be sought in any closed
subspace of the solenoidal space, such as a symmetry sector, with every estimate
required only on that subspace and the equation tested by its fields. The actual
profile and unstable eigenpair require further estimates and certificates.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.24) and the
  Schauder fixed-point argument, pp. 28-31.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order
open SobolevSpace SobolevSpace.GraphSpace
open scoped InnerProductSpace ENNReal Sobolev

set_option linter.missingDocs true

noncomputable section SimilarityCorrection

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "Vσ" => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω))

-- The cached norms of `SimilarityTransport`, before the mixed Lebesgue operator spaces.
attribute [local instance] innerProductSpaceSolenoidal normedSpaceSolenoidal
  completeSpaceSolenoidal normedAddCommGroupSolenoidal seminormedAddCommGroupSolenoidal
  normedAddCommGroupL4Field normedSpaceL4Field seminormedAddCommGroupL4Field
  normedAddCommGroupSolenoidalDual seminormedAddCommGroupSolenoidalDual
  normedAddCommGroupL4FieldToSolenoidalDual seminormedAddCommGroupL4FieldToSolenoidalDual

/-- The transport term of the correction is bounded by the `L⁴` size of its advecting
field, uniformly on the solenoidal space. -/
private theorem exists_norm_correctionTransport_le (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (R : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ]
      PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) :
    ∃ k : NNReal, ∀ u v : Vσ,
      ‖PDE.Analysis.ContinuousTrilinearForm.restrict (IncompressibleFlow.l4Convection J)
        (R.comp (solenoidalL4Embedding J))
        (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω)).ker.subtypeL
        (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω)).ker.subtypeL u v‖ ≤
        k * ‖solenoidalL4Embedding J u‖ * ‖v‖ := by
  refine ⟨‖J‖₊ * ‖R‖₊, fun u v ↦ ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change ‖IncompressibleFlow.l4Convection J (R (solenoidalL4Embedding J u))
    (v : H¹₀(Ω; ℝ^n)) (w : H¹₀(Ω; ℝ^n))‖ ≤ _
  calc
    _ ≤ ‖IncompressibleFlow.l4Convection J (R (solenoidalL4Embedding J u))
        (v : H¹₀(Ω; ℝ^n))‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖J‖ * ‖R (solenoidalL4Embedding J u)‖ * ‖v‖) * ‖w‖ := by
      gcongr
      exact IncompressibleFlow.norm_l4Convection_dual_le J _ _
    _ ≤ (‖J‖ * (‖R‖ * ‖solenoidalL4Embedding J u‖) * ‖v‖) * ‖w‖ := by
      gcongr
      exact R.le_opNorm _
    _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring

/-- The quadratic transport load of the correction is Lipschitz in the weaker `L⁴` norm on
the set where the mass and gradient norms are at most `r₀` and `r₁`. -/
private theorem exists_norm_correctionLoad_sub_le (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (R : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ]
      PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω))
    (S' : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ]
      PiLp 2 (fun _ : Fin n × Fin n ↦ DerivLp n 2 Ω))
    {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) :
    ∃ C : NNReal, ∀ u : Vσ, ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀ →
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁ →
      ∀ v : Vσ, ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖ ≤ r₀ →
      ‖ZeroBoundaryVectorSpace.gradient (v : H¹₀(Ω; ℝ^n))‖ ≤ r₁ →
      ‖PDE.Analysis.Variational.quadraticLoad (solenoidalL4Embedding J)
          (PDE.Analysis.ContinuousTrilinearForm.restrict ContinuousLinearMap.transportPairing
            R S' (solenoidalL4Embedding J)) u -
        PDE.Analysis.Variational.quadraticLoad (solenoidalL4Embedding J)
          (PDE.Analysis.ContinuousTrilinearForm.restrict ContinuousLinearMap.transportPairing
            R S' (solenoidalL4Embedding J)) v‖ ≤ C * ‖solenoidalL4Embedding J (u - v)‖ := by
  let e := solenoidalL4Embedding J
  let P := PDE.Analysis.ContinuousTrilinearForm.restrict
    ContinuousLinearMap.transportPairing R S' e
  let q : NNReal := ‖R‖₊ * ‖S'‖₊ * ‖e‖₊
  have hP : PDE.Analysis.ContinuousTrilinearForm.IsBoundedBy P q := by
    intro u v w
    change ‖ContinuousLinearMap.transportPairing (R u) (S' v) (e w)‖ ≤ _
    calc
      _ ≤ ‖R u‖ * ‖S' v‖ * ‖e w‖ := ContinuousLinearMap.norm_transportPairing_le _ _ _
      _ ≤ (‖R‖ * ‖u‖) * (‖S'‖ * ‖v‖) * (‖e‖ * ‖w‖) := by
        gcongr
        · exact R.le_opNorm u
        · exact S'.le_opNorm v
        · exact e.le_opNorm w
      _ = _ := by simp only [q, NNReal.coe_mul, coe_nnnorm]; ring
  have hbound (u : Vσ) (hu₀ : ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀)
      (hu₁ : ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁) :
      ‖u‖ ≤ r₀ + r₁ := by
    have hnorm : ‖u‖ ^ 2 = ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 :=
      ZeroBoundaryVectorSpace.norm_sq (u : H¹₀(Ω; ℝ^n))
    refine (sq_le_sq₀ (norm_nonneg u) (add_nonneg hr₀ hr₁)).mp ?_
    rw [hnorm]
    linarith only [(sq_le_sq₀ (norm_nonneg _) hr₀).mpr hu₀,
      (sq_le_sq₀ (norm_nonneg _) hr₁).mpr hu₁, mul_nonneg hr₀ hr₁]
  refine ⟨⟨q * (2 * ‖e‖ * (r₀ + r₁)), by positivity⟩, fun u hu₀ hu₁ v hv₀ hv₁ ↦ ?_⟩
  calc
    _ ≤ q * (‖e u‖ + ‖e v‖) * ‖e (u - v)‖ :=
      PDE.Analysis.Variational.quadraticLoad_sub_norm_le e P hP u v
    _ ≤ q * (‖e‖ * (r₀ + r₁) + ‖e‖ * (r₀ + r₁)) * ‖e (u - v)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add
          ((e.le_opNorm u).trans
            (mul_le_mul_of_nonneg_left (hbound u hu₀ hu₁) (norm_nonneg e)))
          ((e.le_opNorm v).trans
            (mul_le_mul_of_nonneg_left (hbound v hv₀ hv₁) (norm_nonneg e)))) q.property)
        (norm_nonneg _)
    _ = _ := by change _ = (q * (2 * ‖e‖ * (r₀ + r₁))) * _; ring

/-- The bounded-domain solenoidal correction in a closed subspace `S` of the solenoidal
space, such as a symmetry sector. The advecting-field identities, coercivity, residual and
nonlinear estimates are required only on `S`, and the solution satisfies the equation
against the test fields of `S`. The fixed-point argument runs in `S` itself, so no
invariance of `S` under the forms or the reconstruction maps is assumed. -/
theorem exists_solenoidal_transport_correction_on (S : Submodule ℝ Vσ)
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
    (ell : StrongDual ℝ Vσ) {a b r₀ r₁ ε M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hM : 0 ≤ M)
    (hcoercive : ∀ u ∈ S,
      a * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        b * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ B u u)
    (hell : ∀ v ∈ S,
      |ell v| ≤ ε * ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hN : ∀ u ∈ S, ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀ →
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁ → ∀ v ∈ S,
      |ContinuousLinearMap.transportPairing
        (R (solenoidalL4Embedding J u)) (S' (solenoidalL4Embedding J u))
        (solenoidalL4Embedding J v)| ≤
          M * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 *
            ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hbudget : ε + M * r₀ ^ 2 ≤ a * r₀)
    (hgradient : a * r₀ ^ 2 ≤ 4 * b * r₁ ^ 2) :
    ∃ u ∈ S, ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀ ∧
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁ ∧ ∀ v ∈ S,
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
  obtain ⟨C, hcontinuous⟩ := exists_norm_correctionLoad_sub_le J R S' hr₀ hr₁
  exact PDE.Analysis.Variational.exists_solution_of_split_energy_transport_on_submodule S hS
    mass gradient (fun u _ ↦ hnorm u) B T (ContinuousLinearMap.id ℝ Vσ)
    (fun u hu v _ ↦ hcancel u hu v) e he.injOn hecompact
    (PDE.Analysis.Variational.quadraticLoad e P) ell ha hb hr₀ hr₁ hM hcoercive hell hN
    (fun u _ v _ ↦ htransport u v)
    (fun u _ hu₀ hu₁ v _ hv₀ hv₁ ↦ hcontinuous u hu₀ hu₁ v hv₀ hv₁) hbudget hgradient

/-- A bounded-domain solenoidal correction with the actual Lebesgue convection pairing.
The application identifies `R` with the unknown plus its finite-rank correction,
and `S` with the correction's derivative matrix. Both maps are continuous in the
weaker `L⁴` topology. Their sharp nonlinear mass bound remains an explicit certificate.

Transport differentiates the unknown inside the linear solve. This gives the
modified iteration (4.24) of Hou, Wang and Yang, without a contraction assumption or
a zero-trace condition on the finite-rank correction. -/
theorem exists_solenoidal_transport_correction
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
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
    (ell : StrongDual ℝ Vσ) {a b r₀ r₁ ε M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hM : 0 ≤ M)
    (hcoercive : ∀ u : Vσ,
      a * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 +
        b * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ^ 2 ≤ B u u)
    (hell : ∀ v : Vσ,
      |ell v| ≤ ε * ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hN : ∀ u : Vσ, ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀ →
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁ → ∀ v : Vσ,
      |ContinuousLinearMap.transportPairing
        (R (solenoidalL4Embedding J u)) (S (solenoidalL4Embedding J u))
        (solenoidalL4Embedding J v)| ≤
          M * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ^ 2 *
            ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Ω; ℝ^n))‖)
    (hbudget : ε + M * r₀ ^ 2 ≤ a * r₀)
    (hgradient : a * r₀ ^ 2 ≤ 4 * b * r₁ ^ 2) :
    ∃ u : Vσ, ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Ω; ℝ^n))‖ ≤ r₀ ∧
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Ω; ℝ^n))‖ ≤ r₁ ∧ ∀ v : Vσ,
      B u v + IncompressibleFlow.l4Convection J (R (solenoidalL4Embedding J u))
        (u : H¹₀(Ω; ℝ^n)) (v : H¹₀(Ω; ℝ^n)) +
        ContinuousLinearMap.transportPairing
          (R (solenoidalL4Embedding J u)) (S (solenoidalL4Embedding J u))
          (solenoidalL4Embedding J v) = ell v := by
  obtain ⟨u, -, hu₀, hu₁, heq⟩ := exists_solenoidal_transport_correction_on ⊤
    (by simp only [Submodule.top_coe, isClosed_univ]) J hJ hinj hcompact B R S adv
    (fun u _ ↦ hA u) (fun u _ ↦ hadv u) ell ha hb hr₀ hr₁ hM (fun u _ ↦ hcoercive u)
    (fun v _ ↦ hell v) (fun u _ hu₀ hu₁ v _ ↦ hN u hu₀ hu₁ v) hbudget hgradient
  exact ⟨u, hu₀, hu₁, fun v ↦ heq v Submodule.mem_top⟩

end SimilarityCorrection

end NavierStokes
