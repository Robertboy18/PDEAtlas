/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Coordinates
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Linear variations of a Sobolev family

The value and derivative columns inherit their integrability from the finite
first jet. Their representatives respect affine variations almost everywhere,
which is the form used when varying an integral energy.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open MeasureTheory
open scoped ENNReal Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- On an open domain, almost-everywhere equality of the values determines
the whole Sobolev family, including its weak derivatives. -/
theorem eq_of_values_ae_eq (hΩ : IsOpen Ω)
    {U V : Fin m → W^{1,p}(Ω)}
    (h : values U =ᵐ[domainMeasure n Ω] values V) : U = V := by
  funext j
  apply wkpBaseCoordinateCLM_injective hΩ
  apply Lp.ext
  filter_upwards [h] with x hx
  exact congrArg (fun z : ℝ^m ↦ z j) hx

/-- The assembled value of a finite Sobolev family belongs to the same `Lᵖ`
space as its scalar components. -/
theorem memLp_values (U : Fin m → W^{1,p}(Ω)) :
    MemLp (values U) p (domainMeasure n Ω) :=
  (valuesCLM.comp_memLp (vectorWkpFirstJetCLM U)).ae_eq
    (valuesCLM_firstJet_ae U)

/-- Each assembled derivative column belongs to `Lᵖ`. -/
theorem memLp_derivatives (U : Fin m → W^{1,p}(Ω)) (i : Fin n) :
    MemLp (derivatives U i) p (domainMeasure n Ω) :=
  ((derivativeCLM i).comp_memLp (vectorWkpFirstJetCLM U)).ae_eq
    (derivativeCLM_firstJet_ae U i)

/-- Values of an affine Sobolev variation agree with the affine variation of
the representatives almost everywhere. -/
theorem values_add_smul_ae (U V : Fin m → W^{1,p}(Ω)) (c : ℝ) :
    values (fun j ↦ U j + c • V j) =ᵐ[domainMeasure n Ω]
      fun x ↦ values U x + c • values V x := by
  have h := ae_all_iff.mpr fun j ↦
    (baseRepresentative_add_ae (U j) (c • V j)).and
      (baseRepresentative_smul_ae c (V j))
  filter_upwards [h] with x hx
  ext j
  change baseRepresentative (U j + c • V j) x =
    baseRepresentative (U j) x + c • baseRepresentative (V j) x
  rw [(hx j).1, (hx j).2]

/-- Weak derivatives of an affine Sobolev variation have the expected
representatives almost everywhere. -/
theorem derivatives_add_smul_ae (U V : Fin m → W^{1,p}(Ω))
    (c : ℝ) (i : Fin n) :
    derivatives (fun j ↦ U j + c • V j) i =ᵐ[domainMeasure n Ω]
      fun x ↦ derivatives U i x + c • derivatives V i x := by
  let T := wkpCoordinateCLM (n := n) (p := p) (Ω := Ω) (singleDerivIndex n i)
  have h := ae_all_iff.mpr fun j ↦
    (Lp.coeFn_add (T (U j)) (c • T (V j))).and (Lp.coeFn_smul c (T (V j)))
  filter_upwards [h] with x hx
  ext j
  change T (U j + c • V j) x = T (U j) x + c • T (V j) x
  rw [map_add, map_smul, (hx j).1, Pi.add_apply, (hx j).2, Pi.smul_apply]

end SobolevSpace.GraphSpace.FiniteProductComposition
