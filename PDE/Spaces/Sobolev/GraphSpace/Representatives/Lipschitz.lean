/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.WeakGradient
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation

/-!
# Lipschitz representatives of whole-space W¹,∞ coefficients

The graph-space coefficient already supplies weak derivatives as L∞ coordinates.
Their norms bound the chosen derivative representatives almost everywhere.
Applying the bounded weak-gradient theorem constructs a Lipschitz representative
of the base coordinate, with constant the sum of the derivative-row norms.

This is a spatial statement. It imposes no continuity in time on either the
coefficient or its derivative rows.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- A whole-space W¹,∞ coefficient has a Lipschitz representative of its base
coordinate. The constant uses only the L∞ norms of its first-derivative rows. -/
theorem WkpSpaceOn.exists_lipschitzWith_baseRepresentative
    (A : W^{1,∞}(ℝ^n)) :
    ∃ v : ℝ^n → ℝ,
      LipschitzWith
        (∑ j : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖₊) v ∧
      v =ᵐ[volume] baseRepresentative A := by
  let g : Fin n → ℝ^n → ℝ := fun j ↦
    ((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) : ℝ^n → ℝ)
  let C : Fin n → ℝ≥0 := fun j ↦
    ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖₊
  have hf : LocallyIntegrable (baseRepresentative A) volume :=
    locallyIntegrableOn_univ.mp
      (A.property (baseIndex n 1)).locallyIntegrable_f
  have hg (j : Fin n) : HasWeakDerivativeOn univ [j] (baseRepresentative A) (g j) := by
    simpa only [singleDerivIndex_toList, baseRepresentative, g] using
      A.property (singleDerivIndex n j)
  have hC (j : Fin n) : ∀ᵐ x ∂volume, ‖g j x‖ ≤ C j := by
    have hae : ae (domainMeasure n univ) = ae (volume : Measure (ℝ^n)) := by
      rw [domainMeasure, Measure.restrict_univ]
    rw [← hae]
    let a : DerivLp n ∞ univ :=
      (A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)
    have hbound : ∀ᵐ x ∂domainMeasure n univ,
        ‖a x‖ₑ ≤ eLpNormEssSup a (domainMeasure n univ) :=
      ae_le_eLpNormEssSup
    have hfinite : eLpNormEssSup a (domainMeasure n univ) ≠ ∞ := by
      simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable a)] using Lp.eLpNorm_ne_top a
    filter_upwards [hbound] with x hx
    have hreal := ENNReal.toReal_mono hfinite hx
    change ‖a x‖ ≤ ‖a‖
    simpa only [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable a),
      toReal_enorm] using hreal
  exact SobolevSpace.exists_lipschitzWith_ae_eq_of_weak_derivative_bound hf g hg C hC

end SobolevSpace.GraphSpace
