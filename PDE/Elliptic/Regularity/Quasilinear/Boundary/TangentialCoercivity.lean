/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.TangentialFields
public import PDE.Analysis.Operator.StrongMonotonicity.PairingEstimate
public import PDE.Analysis.MeasureTheory.Lp.PairingBounds
import PDE.Analysis.MeasureTheory.Lp.NormDomination

/-!
# Coercivity of localized nonlinear tangential quotients

Differencing a uniformly monotone flux leaves a spatial increment error. A cutoff
bounded by `M` controls that error by `K M ‖P‖₂` times the localized quotient norm.
There is no derivative of the unknown coefficient `D²L(Du)` in this estimate.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity PDE.Analysis.Operator
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The nonlinear tangential coercivity inequality, including the spatial parameter
error and an arbitrary bounded cutoff. The flux is identified with its `L²` tuple. -/
theorem weighted_tangential_coercivity
    (A : ℝ^n → ℝ^n → ℝ^n) {m K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z : ℝ^n,
      ‖A y z - A x z‖ ≤ K * ‖y - x‖ * ‖z‖)
    (P Q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (hrep : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (Lp.euclideanTuple P x) = Lp.euclideanTuple Q x)
    (η : DerivLp n ∞ (HalfSpace.upper n))
    (hη : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), |η x| ≤ M)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : 0 < h) :
    m * ‖η • tangentialVectorDifference k hk h P‖ ^ 2 ≤
      ⟪η • tangentialVectorDifference k hk h Q,
        η • tangentialVectorDifference k hk h P⟫ +
      K * M * ‖Lp.euclideanTuple P‖ * ‖η • tangentialVectorDifference k hk h P‖ := by
  let R := (K * M) • Lp.euclideanTuple P
  have hpres := (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving
  have hshift := hpres.tendsto_ae.eventually hrep
  have hpoint : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      m * ‖(η • tangentialVectorDifference k hk h P) x‖ ^ 2 ≤
        ⟪(η • tangentialVectorDifference k hk h Q) x,
          (η • tangentialVectorDifference k hk h P) x⟫ +
        ‖R x‖ * ‖(η • tangentialVectorDifference k hk h P) x‖ := by
    filter_upwards [weighted_tangentialVectorDifference_ae k hk h η P,
      weighted_tangentialVectorDifference_ae k hk h η Q, hrep, hshift, hη,
      Lp.coeFn_smul (K * M) (Lp.euclideanTuple P),
      ae_restrict_mem (HalfSpace.measurableSet_upper n)]
      with x hp hq hx hxy heta hr hxmem
    let y := x + DifferenceQuotient.coordinateStep k h
    have hy : y ∈ HalfSpace.upper n :=
      (add_coordinateStep_mem_upper_iff k hk h x).mpr hxmem
    have hxy' : A y (Lp.euclideanTuple P y) = Lp.euclideanTuple Q y := hxy
    have hd : ‖y - x‖ = h := by
      simp only [y, add_sub_cancel_left, DifferenceQuotient.norm_coordinateStep,
        abs_of_pos hh]
    have hs := scaled_pairing_lower_bound_with_parameter_error A (p := x)
      (hmono y hy) (Lp.euclideanTuple P x) (Lp.euclideanTuple P y) (η x / h)
    have he := norm_scaled_parameter_error_le A hh (Lp.euclideanTuple P x) (η x)
      (by simpa only [hd] using hvariation x hxmem y hy (Lp.euclideanTuple P x))
    have he' : ‖(η x / h) • (A y (Lp.euclideanTuple P x) -
        A x (Lp.euclideanTuple P x))‖ ≤ K * M * ‖Lp.euclideanTuple P x‖ :=
      he.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heta hK) (norm_nonneg _))
    change R x = (K * M) • Lp.euclideanTuple P x at hr
    rw [hr, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK hM),
      hp, hq]
    change m * ‖(η x / h) • (Lp.euclideanTuple P y - Lp.euclideanTuple P x)‖ ^ 2 ≤ _
    rw [hx, hxy'] at hs
    rw [hx] at he'
    exact hs.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right he' (norm_nonneg _)))
  have hint := Lp.mul_norm_sq_le_inner_add_of_ae_le
    (η • tangentialVectorDifference k hk h P)
    (η • tangentialVectorDifference k hk h Q) R m hpoint
  simpa only [R, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK hM)] using hint

/-- Joint spatial and gradient variation bounds the localized flux quotient. This is
the estimate used for the derivative-of-cutoff term in the energy identity. -/
theorem norm_weighted_tangential_flux_le
    (A : ℝ^n → ℝ^n → ℝ^n) {K C M : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (P Q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (hrep : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (Lp.euclideanTuple P x) = Lp.euclideanTuple Q x)
    (η : DerivLp n ∞ (HalfSpace.upper n))
    (hη : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), |η x| ≤ M)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : 0 < h) :
    ‖η • tangentialVectorDifference k hk h Q‖ ≤
      K * M * ‖Lp.euclideanTuple P‖ + C * ‖η • tangentialVectorDifference k hk h P‖ := by
  let R := (K * M) • Lp.euclideanTuple P
  let G := C • (η • tangentialVectorDifference k hk h P)
  have hpres := (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving
  have hshift := hpres.tendsto_ae.eventually hrep
  have hpoint : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      1 * ‖(η • tangentialVectorDifference k hk h Q) x‖ ≤ ‖R x‖ + ‖G x‖ := by
    filter_upwards [weighted_tangentialVectorDifference_ae k hk h η P,
      weighted_tangentialVectorDifference_ae k hk h η Q, hrep, hshift, hη,
      Lp.coeFn_smul (K * M) (Lp.euclideanTuple P),
      Lp.coeFn_smul C (η • tangentialVectorDifference k hk h P),
      ae_restrict_mem (HalfSpace.measurableSet_upper n)]
      with x hp hq hx hxy heta hr hg hxmem
    let y := x + DifferenceQuotient.coordinateStep k h
    have hy : y ∈ HalfSpace.upper n :=
      (add_coordinateStep_mem_upper_iff k hk h x).mpr hxmem
    have hxy' : A y (Lp.euclideanTuple P y) = Lp.euclideanTuple Q y := hxy
    have hd : ‖y - x‖ = h := by
      simp only [y, add_sub_cancel_left, DifferenceQuotient.norm_coordinateStep,
        abs_of_pos hh]
    have hs := norm_scaled_flux_increment_le A hh
      (Lp.euclideanTuple P x) (Lp.euclideanTuple P y) (η x)
      (by simpa only [hd] using
        (hvariation x hxmem y hy (Lp.euclideanTuple P x) (Lp.euclideanTuple P y)))
    rw [hx, hxy'] at hs
    change R x = (K * M) • Lp.euclideanTuple P x at hr
    change G x = C • (η • tangentialVectorDifference k hk h P) x at hg
    rw [one_mul, hr, hg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hK hM), abs_of_nonneg hC, hp, hq]
    exact hs.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heta hK) (norm_nonneg _))
      le_rfl)
  have hb := Lp.mul_norm_le_add_of_ae_le_add zero_le_one
    (η • tangentialVectorDifference k hk h Q) R G hpoint
  simpa only [one_mul, R, G, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hK hM), abs_of_nonneg hC] using hb

end PDE.Elliptic.Regularity.Quasilinear
