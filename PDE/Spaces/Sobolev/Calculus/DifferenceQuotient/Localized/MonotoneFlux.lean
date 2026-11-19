/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.Vector
public import PDE.Analysis.Operator.StrongMonotonicity.PairingEstimate
public import PDE.Analysis.MeasureTheory.Lp.PairingBounds

/-!
# Localized quotients of monotone Lipschitz maps

Uniform monotonicity and Lipschitz continuity pass to cutoff-weighted
quotients in `L²`. The nonlinear relation need hold only on the domain
containing the cutoff and its translate. No derivative of the field or
normalization of the nonlinear map at zero is required.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set PDE.Analysis.Operator
open scoped ENNReal RealInnerProductSpace

variable {n d : ℕ} {Ω : Set (ℝ^n)}

/-- The localized flux quotient has the original monotonicity and
Lipschitz constants. The spatial and target dimensions are independent. -/
theorem weighted_monotone_flux_differenceQuotient_bounds
    (hΩ : MeasurableSet Ω) (A : ℝ^d → ℝ^d) {m C : ℝ} (hC : 0 ≤ C)
    (hmono : ∀ z w, m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    (hLip : ∀ z w, ‖A z - A w‖ ≤ C * ‖z - w‖)
    (P Q : Fin d → DerivLp n 2 univ)
    (hrep : ∀ᵐ x ∂domainMeasure n Ω, A (Lp.euclideanTuple P x) = Lp.euclideanTuple Q x)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) Ω) :
    let a := testFunctionLpTop (Ω := univ) η
    let DP := a • Lp.euclideanTuple (fun i ↦ differenceQuotientLp 2 k h (P i))
    let DQ := a • Lp.euclideanTuple (fun i ↦ differenceQuotientLp 2 k h (Q i))
    m * ‖DP‖ ^ 2 ≤ ⟪DQ, DP⟫ ∧ ‖DQ‖ ≤ C * ‖DP‖ := by
  let a := testFunctionLpTop (Ω := univ) η
  let DP := a • Lp.euclideanTuple (fun i ↦ differenceQuotientLp 2 k h (P i))
  let DQ := a • Lp.euclideanTuple (fun i ↦ differenceQuotientLp 2 k h (Q i))
  have hag : ∀ᵐ x ∂volume, x ∈ Ω →
      A (Lp.euclideanTuple P x) = Lp.euclideanTuple Q x :=
    (ae_restrict_iff' hΩ).mp hrep
  have htrans := (measurePreserving_add_right (volume : Measure (ℝ^n))
    (coordinateStep k h)).quasiMeasurePreserving.ae hag
  have hp := weighted_euclideanTuple_differenceQuotient_ae k h a P
  have hq := weighted_euclideanTuple_differenceQuotient_ae k h a Q
  have ha := testFunctionLpTop_apply_ae (Ω := univ) η
  have hpoint : ∀ᵐ x ∂domainMeasure n univ,
      m * ‖DP x‖ ^ 2 ≤ ⟪DQ x, DP x⟫ ∧ ‖DQ x‖ ≤ C * ‖DP x‖ := by
    simp only [domainMeasure, Measure.restrict_univ] at hp hq ha ⊢
    filter_upwards [hp, hq, ha, hag, htrans] with x hpx hqx hax hx htx
    change DP x = (a x / h) •
      (Lp.euclideanTuple P (x + coordinateStep k h) - Lp.euclideanTuple P x) at hpx
    change DQ x = (a x / h) •
      (Lp.euclideanTuple Q (x + coordinateStep k h) - Lp.euclideanTuple Q x) at hqx
    change a x = η.toFun x at hax
    by_cases hz : η.toFun x = 0
    · simp only [hpx, hqx, hax, hz, zero_div, zero_smul, norm_zero,
        zero_pow (by decide : 2 ≠ 0), mul_zero, inner_zero_left, le_refl, and_self]
    · have hs := subset_tsupport η.toFun hz
      have hx' := hx (hη hs)
      have hy' := htx (hshift hs)
      have hc := scaled_pairing_lower_bound_with_parameter_error
        (fun _ : Unit ↦ A) (p := ()) (q := ()) hmono
        (Lp.euclideanTuple P x) (Lp.euclideanTuple P (x + coordinateStep k h)) (a x / h)
      simp only [sub_self, smul_zero, norm_zero, zero_mul, add_zero] at hc
      rw [hx', hy'] at hc
      refine ⟨by simpa only [hpx, hqx] using hc, ?_⟩
      rw [hpx, hqx, ← hx', ← hy', norm_smul, norm_smul]
      calc
        ‖a x / h‖ * ‖A (Lp.euclideanTuple P (x + coordinateStep k h)) -
            A (Lp.euclideanTuple P x)‖ ≤
          ‖a x / h‖ * (C * ‖Lp.euclideanTuple P (x + coordinateStep k h) -
            Lp.euclideanTuple P x‖) :=
          mul_le_mul_of_nonneg_left (hLip _ _) (norm_nonneg _)
        _ = _ := by ring
  constructor
  · have hz : ∀ᵐ x ∂domainMeasure n univ, (0 : Lp ℝ 2 (domainMeasure n univ)) x = 0 :=
      Lp.coeFn_zero ℝ 2 (domainMeasure n univ)
    have hi := Lp.mul_norm_sq_le_inner_add_of_ae_le DP DQ
      (0 : Lp ℝ 2 (domainMeasure n univ)) m (by
        filter_upwards [hpoint, hz] with x hx hzero
        simpa only [hzero, norm_zero, zero_mul, add_zero] using hx.1)
    simpa only [norm_zero, zero_mul, add_zero] using hi
  · have hdom : ∀ᵐ x ∂domainMeasure n univ, ‖DQ x‖ ≤ ‖(C • DP) x‖ := by
      filter_upwards [hpoint, Lp.coeFn_smul C DP] with x hx hs
      change (C • DP) x = C • DP x at hs
      simpa only [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hx.2
    have hi := Lp.norm_le_norm_of_ae_le hdom
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hi

end SobolevSpace.GraphSpace.DifferenceQuotient
