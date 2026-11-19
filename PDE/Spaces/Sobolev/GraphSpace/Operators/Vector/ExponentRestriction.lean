/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Jacobian

/-!
# Exponent restriction for finite Sobolev systems

Apply the scalar restriction operator componentwise. Its weak
Jacobian still represents the same derivatives almost everywhere. This permits
several fields of different natural exponents to be placed at a common exponent
without changing the Sobolev model.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace SobolevSpace.GraphSpace

variable {m n k : ℕ} {Ω : Set (ℝ^n)} {p r : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [IsFiniteMeasure (domainMeasure n Ω)]

/-- Continuous componentwise exponent restriction of a finite Sobolev system. -/
def vectorLowerExponentCLM (hrp : r ≤ p) :
    (Fin m → W^{k,p}(Ω)) →L[ℝ] (Fin m → W^{k,r}(Ω)) :=
  ContinuousLinearMap.pi fun i ↦
    (lowerExponentOfFiniteMeasureCLM hrp).comp (ContinuousLinearMap.proj i)

/-- Restriction preserves each original weak derivative coordinate. -/
theorem wkpCoordinate_vectorLowerExponentCLM_apply_ae (hrp : r ≤ p)
    (u : Fin m → W^{k,p}(Ω)) (i : Fin m) (a : DerivIndex n k) :
    wkpCoordinateCLM a (vectorLowerExponentCLM hrp u i) =ᵐ[domainMeasure n Ω]
      wkpCoordinateCLM a (u i) :=
  lowerExponentOfFiniteMeasure_apply_ae hrp (u i) a

/-- The restricted weak Jacobian agrees with the original matrix field. -/
theorem vectorWkpJacobianCLM_vectorLowerExponentCLM_apply_ae (hrp : r ≤ p)
    (u : Fin m → W^{1,p}(Ω)) :
    vectorWkpJacobianCLM (vectorLowerExponentCLM hrp u) =ᵐ[domainMeasure n Ω]
      vectorWkpJacobianCLM u := by
  have hcoords : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j,
      wkpCoordinateCLM (singleDerivIndex n j) (vectorLowerExponentCLM hrp u i) x =
        wkpCoordinateCLM (singleDerivIndex n j) (u i) x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
      wkpCoordinate_vectorLowerExponentCLM_apply_ae hrp u i (singleDerivIndex n j)
  filter_upwards [vectorWkpJacobianCLM_apply_ae (vectorLowerExponentCLM hrp u),
    vectorWkpJacobianCLM_apply_ae u, hcoords] with x hx hy hz
  exact Matrix.ext fun i j ↦ (hx i j).trans ((hz i j).trans (hy i j).symm)

end SobolevSpace.GraphSpace
