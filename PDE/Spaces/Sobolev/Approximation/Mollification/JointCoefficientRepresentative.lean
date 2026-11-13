/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.MultiplierRepresentative
public import PDE.Spaces.Sobolev.Approximation.Mollification.TransportTime

/-!
# Joint representatives of transport coefficients

The base coefficient is continuous in spatial L∞ on the closed time interval. Its
indicated weak derivative is uniformly bounded there, with no time continuity assumed.
The unsmoothed multiplication results therefore put the products with fixed spatial L²
functions in Bochner L². The generic finite-measure exhaustion constructs joint measurable
representatives of both coefficient classes.

The representatives agree with the coefficient and derivative rows for almost every
time and almost every spatial point. No value at either time endpoint is prescribed.
The derivative representative is identified with the weak derivative class;
the coefficient need not be differentiable pointwise in space.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

/-- A base row and one uniformly bounded weak derivative row have joint measurable
representatives on the time-space product. Base continuity is required only on Icc;
the conclusion concerns Ioc almost everywhere. Spatial volume need not be finite. -/
theorem exists_joint_coefficient_representatives
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (j : Fin n) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b,
      ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L) :
    ∃ C D : ℝ × (ℝ^n) → ℝ,
      StronglyMeasurable C ∧ StronglyMeasurable D ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        (fun x ↦ C (t, x)) =ᵐ[domainMeasure n univ]
          ((A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ)) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        (fun x ↦ D (t, x)) =ᵐ[domainMeasure n univ]
          ((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) : ℝ^n → ℝ)) := by
  have hbase (w : DerivLp n 2 univ) : MemLp
      (fun t ↦ (((A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • w :
        DerivLp n 2 univ))
      2 (volume.restrict (Ioc a b)) :=
    memLp_coefficientBase_mul hab A hA (memLp_const w)
  have hderiv (w : DerivLp n 2 univ) : MemLp
      (fun t ↦ (((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • w :
        DerivLp n 2 univ))
      2 (volume.restrict (Ioc a b)) :=
    memLp_coefficientDerivative_mul hab A hA j L hL (memLp_const w)
  obtain ⟨C, hC, hCsection⟩ :=
    exists_jointRepresentative_of_memLp_multiplier
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) hbase
  obtain ⟨D, hD, hDsection⟩ :=
    exists_jointRepresentative_of_memLp_multiplier
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) hderiv
  exact ⟨C, D, hC, hD, hCsection, hDsection⟩

end SobolevSpace.Approximation
