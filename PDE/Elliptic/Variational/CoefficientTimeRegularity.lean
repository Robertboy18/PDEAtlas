/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.TimeRegularity
public import PDE.Elliptic.Variational.CoefficientDependence
public import PDE.Analysis.Evolution.Time.AbsoluteContinuity

/-!
# Time regularity of divergence-form coefficients

Uniform bounds for the scalar time derivatives on one common spatial full-measure
set give a Lipschitz curve of `L∞` coefficient matrices. The bounded linear
coefficient-to-form map of `CoefficientDependence` then gives absolute continuity of the
principal form.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal

/-- A common spatial almost-everywhere bound on the time derivatives of every
matrix entry makes the principal form absolutely continuous in operator norm.
The coefficients are represented in `L∞`, but their time regularity is proved
from the scalar sections. This conclusion does not identify an operator derivative. -/
theorem absolutelyContinuousOnInterval_multiplicationCoeffFormOf_of_ae_hasDerivWithinAt
    {n : ℕ} {Ω : Set (ℝ^n)}
    (U V : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Fin n → U →L[ℝ] DerivLp n 2 Ω) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (E : Fin n → V →L[ℝ] DerivLp n 2 Ω) (hE : ∀ i v, ‖E i v‖ ≤ ‖v‖)
    (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (f fdot : ℝ → Fin n → Fin n → ℝ^n → ℝ) {a b : ℝ} (N : ℝ≥0)
    (hrep : ∀ i j t, t ∈ uIcc a b →
      (coeff t i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f t i j)
    (hderiv : ∀ i j, ∀ᵐ x ∂domainMeasure n Ω, ∀ t ∈ uIcc a b,
      HasDerivWithinAt (fun s ↦ f s i j x) (fdot t i j x) (uIcc a b) t)
    (hbound : ∀ i j, ∀ᵐ x ∂domainMeasure n Ω, ∀ t ∈ uIcc a b,
      ‖fdot t i j x‖ ≤ N) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ variableCoeffFormOf U V D hD E hE
        (multiplicationCoefficientOperator (coeff t))) a b := by
  have hentry (i j : Fin n) :
      LipschitzOnWith N (fun t ↦ coeff t i j) (uIcc a b) :=
    lipschitzOnWith_lp_top_of_ae_hasDerivWithinAt
      (fun t ↦ coeff t i j) (fun t ↦ f t i j) (fun t ↦ fdot t i j) N
      (hrep i j) (hderiv i j) (hbound i j)
  have hmatrix : LipschitzOnWith N coeff (uIcc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg N.coe_nonneg dist_nonneg)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg N.coe_nonneg dist_nonneg)).mpr
    intro j
    simpa only [Pi.sub_apply, dist_eq_norm] using
      (hentry i j).dist_le_mul s hs t ht
  exact
    ((lipschitzWith_multiplicationCoeffFormCLMOf U V D hD E hE).comp_lipschitzOnWith
      hmatrix).absolutelyContinuousOnInterval

end SobolevSpace.GraphSpace
