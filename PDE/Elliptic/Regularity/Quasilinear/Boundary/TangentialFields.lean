/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.TangentialDifferenceQuotient

/-!
# Vector fields in a tangential nonlinear energy estimate

The scalar Sobolev coordinates assemble into the Euclidean `L²` fields used in the
monotonicity pairing. Tangential translation preserves the restricted measure, so the
assembled quotient has its difference formula almost everywhere.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The Euclidean tuple of tangential quotients of the scalar coordinates. -/
def tangentialVectorDifference (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (P : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    Lp (ℝ^n) 2 (domainMeasure n (HalfSpace.upper n)) :=
  Lp.euclideanTuple (fun i ↦ tangentialDifferenceQuotientLp 2 k hk h (P i))

/-- The assembled quotient agrees with the difference of the assembled field. -/
theorem tangentialVectorDifference_ae
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (P : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      tangentialVectorDifference k hk h P x =
        h⁻¹ • (Lp.euclideanTuple P (x + DifferenceQuotient.coordinateStep k h) -
          Lp.euclideanTuple P x) := by
  have hbase := Lp.euclideanTuple_apply_ae P
  have hshift := (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving.ae_eq_comp
    (show Lp.euclideanTuple P =ᵐ[domainMeasure n (HalfSpace.upper n)]
      (fun x ↦ WithLp.toLp 2 (fun i ↦ P i x)) from by
        filter_upwards [hbase] with x hx
        exact PiLp.ext hx)
  have hquot : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), ∀ i : Fin n,
      tangentialDifferenceQuotientLp 2 k hk h (P i) x =
        h⁻¹ * (P i (x + DifferenceQuotient.coordinateStep k h) - P i x) :=
    ae_all_iff.mpr fun i ↦ tangentialDifferenceQuotientLp.apply_ae 2 k hk h (P i)
  filter_upwards [Lp.euclideanTuple_apply_ae
    (fun i ↦ tangentialDifferenceQuotientLp 2 k hk h (P i)), hbase, hshift, hquot]
    with x hx hp hps hd
  have hps' : Lp.euclideanTuple P (x + DifferenceQuotient.coordinateStep k h) =
      WithLp.toLp 2 (fun i ↦ P i (x + DifferenceQuotient.coordinateStep k h)) := hps
  apply PiLp.ext
  intro i
  change (tangentialVectorDifference k hk h P x) i =
    h⁻¹ * ((Lp.euclideanTuple P (x + DifferenceQuotient.coordinateStep k h)) i -
      (Lp.euclideanTuple P x) i)
  dsimp only [tangentialVectorDifference]
  rw [hx i, hp i, hps']
  exact hd i

/-- Multiplying the vector quotient by an `L∞` cutoff gives the scaled increment. -/
theorem weighted_tangentialVectorDifference_ae
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (η : DerivLp n ∞ (HalfSpace.upper n))
    (P : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      (η • tangentialVectorDifference k hk h P) x =
        (η x / h) • (Lp.euclideanTuple P (x + DifferenceQuotient.coordinateStep k h) -
          Lp.euclideanTuple P x) := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) η (tangentialVectorDifference k hk h P),
    tangentialVectorDifference_ae k hk h P] with x hx hp
  change (η • tangentialVectorDifference k hk h P) x =
    η x • tangentialVectorDifference k hk h P x at hx
  simpa only [hp, smul_smul, div_eq_mul_inv] using hx

/-- The squared norm of the vector quotient is exactly the sum of scalar quotient energies. -/
theorem norm_tangentialVectorDifference_sq
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (P : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    ‖tangentialVectorDifference k hk h P‖ ^ 2 =
      ∑ i, ‖tangentialDifferenceQuotientLp 2 k hk h (P i)‖ ^ 2 :=
  Lp.norm_euclideanTuple_sq _

end PDE.Elliptic.Regularity.Quasilinear
