/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Operators

/-!
# Localized quotients of Euclidean fields

A coordinate quotient acts on each component of a Euclidean field. The
assembled `Lp` element has the vector increment as its representative.
The number of components is independent of the spatial dimension.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set
open scoped ENNReal

variable {n d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Assembling component quotients gives the quotient of the assembled
field almost everywhere. This includes zero step and zero components. -/
theorem euclideanTuple_differenceQuotient_ae
    (k : Fin n) (h : ℝ) (P : Fin d → DerivLp n p univ) :
    ∀ᵐ x ∂domainMeasure n univ,
      Lp.euclideanTuple (fun i ↦ differenceQuotientLp p k h (P i)) x =
        h⁻¹ • (Lp.euclideanTuple P (x + coordinateStep k h) - Lp.euclideanTuple P x) := by
  have hbase := Lp.euclideanTuple_apply_ae P
  have htuple := Lp.euclideanTuple_apply_ae
    (fun i ↦ differenceQuotientLp p k h (P i))
  simp only [domainMeasure, Measure.restrict_univ] at hbase htuple ⊢
  have hshift := (measurePreserving_add_right (volume : Measure (ℝ^n))
    (coordinateStep k h)).quasiMeasurePreserving.ae
      (show ∀ᵐ x ∂volume, ∀ i, Lp.euclideanTuple P x i = P i x from hbase)
  have hquot : ∀ᵐ x ∂volume, ∀ i : Fin d,
      differenceQuotientLp p k h (P i) x =
        h⁻¹ * (P i (x + coordinateStep k h) - P i x) :=
    ae_all_iff.mpr fun i ↦ differenceQuotientLp_apply_ae p k h (P i)
  filter_upwards [htuple, hbase, hshift, hquot]
    with x hx hp ht hd
  apply PiLp.ext
  intro i
  change Lp.euclideanTuple (fun i ↦ differenceQuotientLp p k h (P i)) x i =
    h⁻¹ * (Lp.euclideanTuple P (x + coordinateStep k h) i - Lp.euclideanTuple P x i)
  rw [hx i, hp i, ht i]
  exact hd i

/-- The cutoff-weighted vector quotient is the scaled increment. -/
theorem weighted_euclideanTuple_differenceQuotient_ae
    (k : Fin n) (h : ℝ) (η : DerivLp n ∞ univ) (P : Fin d → DerivLp n p univ) :
    ∀ᵐ x ∂domainMeasure n univ,
      (η • Lp.euclideanTuple (fun i ↦ differenceQuotientLp p k h (P i))) x =
        (η x / h) • (Lp.euclideanTuple P (x + coordinateStep k h) - Lp.euclideanTuple P x) := by
  filter_upwards [Lp.coeFn_lpSMul (r := p) η
    (Lp.euclideanTuple (fun i ↦ differenceQuotientLp p k h (P i))),
    euclideanTuple_differenceQuotient_ae k h P] with x hx hp
  change (η • Lp.euclideanTuple (fun i ↦ differenceQuotientLp p k h (P i))) x =
    η x • Lp.euclideanTuple (fun i ↦ differenceQuotientLp p k h (P i)) x at hx
  simpa only [hp, smul_smul, div_eq_mul_inv] using hx

end SobolevSpace.GraphSpace.DifferenceQuotient
