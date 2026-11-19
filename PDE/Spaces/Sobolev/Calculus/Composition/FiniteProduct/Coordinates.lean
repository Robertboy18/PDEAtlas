/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.FirstJet

/-!
# Coordinates for finite-product Sobolev composition

The finite first jet records the value and all spatial derivatives of each
scalar component. Two continuous linear projections assemble its values, or one of its
spatial derivative columns, into Euclidean space. This keeps the scalar Sobolev graph
spaces and their representatives throughout the finite-product chain rule.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open MeasureTheory
open scoped ENNReal Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Assemble the values in a finite first jet as a Euclidean vector. -/
def valuesCLM : (Fin m → ℝ × ℝ^n) →L[ℝ] ℝ^m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦
      (ContinuousLinearMap.fst ℝ ℝ (ℝ^n)).comp (ContinuousLinearMap.proj j))

/-- Assemble one spatial derivative column in a finite first jet. -/
def derivativeCLM (i : Fin n) : (Fin m → ℝ × ℝ^n) →L[ℝ] ℝ^m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦
      (EuclideanSpace.proj i).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ^n)).comp (ContinuousLinearMap.proj j)))

/-- Each assembled value is its original scalar coordinate. -/
@[simp]
theorem valuesCLM_apply (s : Fin m → ℝ × ℝ^n) (j : Fin m) :
    valuesCLM s j = (s j).1 :=
  rfl

/-- Each assembled derivative is its original spatial coordinate. -/
@[simp]
theorem derivativeCLM_apply (i : Fin n) (s : Fin m → ℝ × ℝ^n) (j : Fin m) :
    derivativeCLM i s j = (s j).2 i :=
  rfl

/-- The value vector of a family of scalar Sobolev fields. -/
def values (U : Fin m → W^{1,p}(Ω)) (x : ℝ^n) : ℝ^m :=
  WithLp.toLp 2 (fun j ↦ wkpBaseCoordinateCLM (U j) x)

/-- One derivative column of a family of scalar Sobolev fields. -/
def derivatives (U : Fin m → W^{1,p}(Ω)) (i : Fin n) (x : ℝ^n) : ℝ^m :=
  WithLp.toLp 2 (fun j ↦ wkpCoordinateCLM (singleDerivIndex n i) (U j) x)

/-- The value projection of the finite first jet has its prescribed representative,
including when the spatial dimension is zero. -/
theorem valuesCLM_firstJet_ae (U : Fin m → W^{1,p}(Ω)) :
    ∀ᵐ x ∂domainMeasure n Ω, valuesCLM (vectorWkpFirstJetCLM U x) = values U x := by
  filter_upwards [vectorWkpFirstJetCLM_apply_ae U] with x hx
  ext j
  change (vectorWkpFirstJetCLM U x j).1 = wkpBaseCoordinateCLM (U j) x
  rw [hx]

/-- Each derivative-column projection of the finite first jet has its prescribed
representative on one common set of full measure. -/
theorem derivativeCLM_firstJet_ae (U : Fin m → W^{1,p}(Ω)) (i : Fin n) :
    ∀ᵐ x ∂domainMeasure n Ω,
      derivativeCLM i (vectorWkpFirstJetCLM U x) = derivatives U i x := by
  have hgrad : ∀ᵐ x ∂domainMeasure n Ω, ∀ j : Fin m, ∀ k : Fin n,
      ∇ (U j) x k = wkpCoordinateCLM (singleDerivIndex n k) (U j) x :=
    ae_all_iff.mpr fun j ↦ wkpGradientCLM_apply_ae (U j)
  filter_upwards [vectorWkpFirstJetCLM_apply_ae U, hgrad] with x hx hg
  ext j
  change (vectorWkpFirstJetCLM U x j).2 i =
    wkpCoordinateCLM (singleDerivIndex n i) (U j) x
  rw [hx]
  exact hg j i

end SobolevSpace.GraphSpace.FiniteProductComposition
