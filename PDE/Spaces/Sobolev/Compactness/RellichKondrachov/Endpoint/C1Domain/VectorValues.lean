/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.ValueL1
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import PDE.Analysis.Operator.CompactConvergence

/-!
# Strong L1 convergence of finite Sobolev systems

Weak convergence in the finite product gives weak convergence of every
component. Scalar Rellich compactness gives strong L1 convergence componentwise;
the Euclidean Lp tuple map assembles the coupled value field.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.RellichKondrachov

open Filter MeasureTheory
open scoped ENNReal Topology Sobolev

variable {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [IsFiniteMeasure (domainMeasure n Ω)]

local notation "μ" => domainMeasure n Ω

/-- The Euclidean L1 value of a finite Sobolev system. -/
def vectorValueL1CLM : (Fin m → W^{1,p}(Ω)) →L[ℝ] Lp (ℝ^m) 1 μ :=
  Lp.euclideanTuple.comp
    (ContinuousLinearMap.pi fun i ↦ valueL1CLM.comp (ContinuousLinearMap.proj i))

/-- Exponent lowering and Euclidean assembly preserve the value field. -/
theorem vectorValueL1CLM_apply_ae (u : (Fin m → W^{1,p}(Ω))) :
    (vectorValueL1CLM u : ℝ^n → ℝ^m) =ᵐ[μ] vectorWkpValueCLM u := by
  have hscalar : ∀ᵐ x ∂μ, ∀ i, valueL1CLM (u i) x = wkpBaseCoordinateCLM (u i) x :=
    ae_all_iff.mpr fun i ↦ valueL1CLM_apply_ae (u i)
  filter_upwards [Lp.euclideanTuple_apply_ae (fun i ↦ valueL1CLM (u i)),
    hscalar, vectorWkpValueCLM_apply_ae u] with x hx hy hz
  exact PiLp.ext fun i ↦ (hx i).trans ((hy i).trans (hz i).symm)

/-- On a C1 extension domain in every positive dimension, weak convergence of
finite Sobolev systems implies strong L1 convergence of their Euclidean values.
No norm bound is assumed. -/
theorem tendsto_vectorValueL1CLM_of_tendsto_weak
    [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]
    {u : ℕ → (Fin m → W^{1,p}(Ω))} {uLimit : (Fin m → W^{1,p}(Ω))}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) uLimit))) :
    Tendsto (fun k ↦ vectorValueL1CLM (u k)) atTop (𝓝 (vectorValueL1CLM uLimit)) := by
  have hcoord (i : Fin m) : Tendsto (fun k ↦ valueL1CLM (u k i)) atTop
      (𝓝 (valueL1CLM (uLimit i))) := by
    apply PDE.Analysis.tendsto_compactOperator_of_tendsto_weak
      (valueL1CLM (p := p) (Ω := Ω)) valueL1CLM_isCompactOperator_of_c1Domain
    exact (WeakSpace.map (ContinuousLinearMap.proj i :
      (Fin m → W^{1,p}(Ω)) →L[ℝ] W^{1,p}(Ω))).continuous.continuousAt.tendsto.comp hu
  exact Lp.euclideanTuple.continuous.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr hcoord)

end SobolevSpace.GraphSpace.RellichKondrachov
