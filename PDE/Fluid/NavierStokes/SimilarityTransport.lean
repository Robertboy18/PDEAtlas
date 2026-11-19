/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.SimilarityPrincipal

/-!
# Transport forms for the similarity equation

On a bounded open domain, an independent solenoidal `L⁴ ∩ H¹` transport coefficient
added to the solenoidal similarity principal form preserves coercivity without a
boundary trace condition, and Lax–Milgram solves the resulting linear equation for
every dual load (`existsUnique_solenoidal_similarity_l4_transport_solution`). The Lax–Milgram step
is `PDE.Analysis.Variational.IsWeakSolution.existsUnique`, which is built on Mathlib's
`IsCoercive.continuousLinearEquivOfBilin`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax–Milgram Theorem), pp. 315-316.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order
open SobolevSpace SobolevSpace.GraphSpace
open scoped InnerProductSpace ENNReal Sobolev

set_option linter.missingDocs true

noncomputable section SimilarityTransport

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "Vσ" => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω))

attribute [local instance] innerProductSpaceSolenoidal normedSpaceSolenoidal
  completeSpaceSolenoidal normedAddCommGroupSolenoidal seminormedAddCommGroupSolenoidal

-- Cache the inherited norms before constructing the mixed Lebesgue operator spaces.
/-- The `ℓ²` product norm on vector fields with components in `L⁴`. -/
local instance normedAddCommGroupL4Field :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) :=
  PiLp.normedAddCommGroup (p := 2) (α := fun _ : Fin n ↦ DerivLp n 4 Ω)

/-- The real scalar action on `L⁴` vector fields, for the product norm. -/
local instance normedSpaceL4Field : NormedSpace ℝ (PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) :=
  PiLp.normedSpace (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n ↦ DerivLp n 4 Ω)

/-- The seminormed group underlying `normedAddCommGroupL4Field`. -/
local instance seminormedAddCommGroupL4Field :
    SeminormedAddCommGroup (PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) :=
  inferInstance

/-- The operator norm on the dual of the weak-divergence kernel. -/
local instance normedAddCommGroupSolenoidalDual : NormedAddCommGroup (StrongDual ℝ Vσ) :=
  inferInstance
/-- The seminormed group underlying `normedAddCommGroupSolenoidalDual`. -/
local instance seminormedAddCommGroupSolenoidalDual : SeminormedAddCommGroup (StrongDual ℝ Vσ) :=
  inferInstance
/-- The operator norm on maps from `L⁴` vector fields to the dual of the kernel. -/
local instance normedAddCommGroupL4FieldToSolenoidalDual : NormedAddCommGroup
    (PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ] StrongDual ℝ Vσ) := inferInstance
/-- The seminormed group underlying `normedAddCommGroupL4FieldToSolenoidalDual`. -/
local instance seminormedAddCommGroupL4FieldToSolenoidalDual : SeminormedAddCommGroup
    (PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) →L[ℝ] StrongDual ℝ Vσ) := inferInstance

/-- The finite Hilbert-product `L⁴` inclusion on the closed solenoidal energy space. -/
noncomputable def solenoidalL4Embedding (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) :
    Vσ →L[ℝ] PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω) :=
  (IncompressibleFlow.vectorL4Embedding J).comp
    (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω)).ker.subtypeL

/-- The compensated principal form with an independent `L⁴` transport coefficient.
Only the unknown and test fields have zero boundary values. -/
def solenoidalSimilarityL4TransportForm
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω)
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) :
    Vσ →L[ℝ] StrongDual ℝ Vσ :=
  PDE.Analysis.Evolution.restrictForm
    (V := H¹₀(Ω; ℝ^n))
    (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω)).ker
    (similarityPrincipalForm hΩ hb b Q + IncompressibleFlow.l4Convection J A)

/-- Solenoidal transport preserves compensation without a boundary condition on the coefficient.
This includes the finite-rank correction in the bounded-domain profile iteration. -/
theorem solenoidalSimilarityL4TransportForm_isCoercive
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (hη : η < ((n : ℝ) - 2) / 4)
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (adv : Fin n → H¹(Ω))
    (hA : ∀ i, (A i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (adv i) : ℝ^n → ℝ))
    (hadv : negativeDivergence adv = 0) :
    IsCoercive (solenoidalSimilarityL4TransportForm hΩ hb b Q J A) := by
  obtain ⟨c, hc, hbound⟩ := IncompressibleFlow.isCoercive_add_l4Convection_of_sobolev
    J hJ A adv hA hadv (similarityPrincipalForm hΩ hb b Q)
    (similarityPrincipalForm_isCoercive hΩ hb b Q η hdiv hcompensation hη)
  refine ⟨c, hc, fun U ↦ ?_⟩
  rw [solenoidalSimilarityL4TransportForm, PDE.Analysis.Evolution.restrictForm_apply]
  exact hbound (U : H¹₀(Ω; ℝ^n))

/-- The linear transport solve allows a solenoidal `H¹` coefficient with nonzero trace.
All bounds on the background and compensation remain explicit. -/
theorem existsUnique_solenoidal_similarity_l4_transport_solution
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (hη : η < ((n : ℝ) - 2) / 4)
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (adv : Fin n → H¹(Ω))
    (hA : ∀ i, (A i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (adv i) : ℝ^n → ℝ))
    (hadv : negativeDivergence adv = 0) (ell : StrongDual ℝ Vσ) :
    ∃! U : Vσ, ∀ V : Vσ,
      solenoidalSimilarityPrincipalForm hΩ hb b Q U V +
        IncompressibleFlow.l4Convection J A
          (U : H¹₀(Ω; ℝ^n)) (V : H¹₀(Ω; ℝ^n)) = ell V := by
  have hcoercive := solenoidalSimilarityL4TransportForm_isCoercive hΩ hb b Q η
    hdiv hcompensation hη J hJ A adv hA hadv
  simpa only [PDE.Analysis.Variational.IsWeakSolution,
    solenoidalSimilarityL4TransportForm, solenoidalSimilarityPrincipalForm,
    PDE.Analysis.Evolution.restrictForm_apply, add_apply] using
    PDE.Analysis.Variational.IsWeakSolution.existsUnique
      (solenoidalSimilarityL4TransportForm hΩ hb b Q J A) hcoercive ell

/-- The compensated principal form with transport by a weak solenoidal field.
The advecting field remains fixed during this linear solve. -/
def solenoidalSimilarityTransportForm
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω)
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (A : Vσ) :
    Vσ →L[ℝ] StrongDual ℝ Vσ :=
  solenoidalSimilarityL4TransportForm hΩ hb b Q J
    (IncompressibleFlow.vectorL4Embedding J (A : H¹₀(Ω; ℝ^n)))

/-- Weak solenoidal transport leaves the compensated energy unchanged.
Its norm need not be small compared with the coercivity margin. -/
theorem solenoidalSimilarityTransportForm_isCoercive
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (hη : η < ((n : ℝ) - 2) / 4)
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : Vσ) : IsCoercive (solenoidalSimilarityTransportForm hΩ hb b Q J A) := by
  apply solenoidalSimilarityL4TransportForm_isCoercive hΩ hb b Q η
    hdiv hcompensation hη J hJ
    (IncompressibleFlow.vectorL4Embedding J (A : H¹₀(Ω; ℝ^n)))
    (fun i ↦ ((A : H¹₀(Ω; ℝ^n)) i : H¹(Ω)))
  · intro i
    exact hJ ((A : H¹₀(Ω; ℝ^n)) i)
  · change -(∑ i, derivCoordCLM i ((A : H¹₀(Ω; ℝ^n)) i)) = 0
    rw [← ZeroBoundaryVectorSpace.divergence_apply]
    simpa only [neg_zero] using congrArg Neg.neg
      (show ZeroBoundaryVectorSpace.divergence (A : H¹₀(Ω; ℝ^n)) = 0 from A.property)

/-- The transport equation has a unique weak solenoidal solution even when the
advecting correction is only `H¹₀`. All profile and matrix bounds remain explicit. -/
theorem existsUnique_solenoidal_similarity_transport_solution
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (hη : η < ((n : ℝ) - 2) / 4)
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : Vσ) (ell : StrongDual ℝ Vσ) :
    ∃! U : Vσ, ∀ V : Vσ,
      solenoidalSimilarityPrincipalForm hΩ hb b Q U V +
        IncompressibleFlow.sobolevConvection J
          (A : H¹₀(Ω; ℝ^n)) (U : H¹₀(Ω; ℝ^n)) (V : H¹₀(Ω; ℝ^n)) = ell V := by
  have hcoercive := solenoidalSimilarityTransportForm_isCoercive hΩ hb b Q η
    hdiv hcompensation hη J hJ A
  simpa only [PDE.Analysis.Variational.IsWeakSolution,
    solenoidalSimilarityTransportForm, solenoidalSimilarityL4TransportForm,
    solenoidalSimilarityPrincipalForm, PDE.Analysis.Evolution.restrictForm_apply, add_apply,
    IncompressibleFlow.sobolevConvection, PDE.Analysis.ContinuousTrilinearForm.restrict_apply,
    ContinuousLinearMap.id_apply] using
    PDE.Analysis.Variational.IsWeakSolution.existsUnique
      (solenoidalSimilarityTransportForm hΩ hb b Q J A) hcoercive ell

end SimilarityTransport

end NavierStokes
