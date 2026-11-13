/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.StrongMonotonicity.LocalizedEstimate
public import PDE.Spaces.Sobolev.Calculus.Composition.Implicit.HalfSpace

/-!
# Normal inverse recovery with a cutoff

The localized output is a Sobolev function, but the original output and unknown are
only `Lp` fields. Both cutoff commutators are kept in the estimate. Consequently the
argument applies to localization of a nonlinear equation, where a cutoff of its
solution need not satisfy the same equation.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Composition.Implicit

open Filter MeasureTheory Set
open SobolevSpace.Extension.Lp SobolevSpace.GraphSpace.DifferenceQuotient
open SobolevSpace.GraphSpace.Rellich
open scoped ENNReal NNReal Topology RealInnerProductSpace Sobolev

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The localized inverse estimate includes commutators containing the original output
and unknown. The coefficient error is weighted by the translated cutoff. -/
theorem mul_norm_localized_inward_differenceQuotient_le
    (A : ℝ^n → ℝ → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ s t : ℝ,
      m * ‖s - t‖ * ‖s - t‖ ≤ ⟪A x s - A x t, s - t⟫)
    (η : ℝ^n → ℝ) {K : ℝ≥0} (hη : LipschitzWith K η)
    (u q U Q : DerivLp n p (HalfSpace.upper n))
    (heq : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), A x (u x) = q x)
    (hU : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), U x = η x * u x)
    (hQ : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), Q x = η x * q x)
    {h : ℝ} (hh : 0 < h) (r : DerivLp n p (HalfSpace.upper n))
    (hparameter : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      |η (x + coordinateStep (PDE.Common.lastIndex (n := n)) h)| *
        ‖A (x + coordinateStep (PDE.Common.lastIndex (n := n)) h) (u x) - A x (u x)‖
          ≤ h * ‖r x‖) :
    m * ‖restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (zeroExtendLp (HalfSpace.measurableSet_upper n) U))‖ ≤
      ‖restrictDerivLp (subset_univ (HalfSpace.upper n))
        (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
          (zeroExtendLp (HalfSpace.measurableSet_upper n) Q))‖ +
        ‖r‖ + K * (‖q‖ + m * ‖u‖) := by
  let N : DerivLp n p (HalfSpace.upper n) → DerivLp n p (HalfSpace.upper n) :=
    lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : ℝ)‖ = 0)
  let S := N q + m • N u
  let R := N r + (K : ℝ) • S
  have hN (v : DerivLp n p (HalfSpace.upper n)) :
      (N v : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] fun x ↦ ‖v x‖ :=
    lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero : ‖(0 : ℝ)‖ = 0) v
  have hNnorm (v : DerivLp n p (HalfSpace.upper n)) : ‖N v‖ ≤ ‖v‖ := by
    simpa only [N, NNReal.coe_one, one_mul] using
      lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero : ‖(0 : ℝ)‖ = 0) v
  have hR : (R : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)]
      fun x ↦ ‖r x‖ + K * (‖q x‖ + m * ‖u x‖) := by
    filter_upwards [Lp.coeFn_add (N r) ((K : ℝ) • S), Lp.coeFn_smul (K : ℝ) S,
      Lp.coeFn_add (N q) (m • N u), Lp.coeFn_smul m (N u), hN r, hN q, hN u]
      with x ha hK hs hm' hr hq hu
    simp only [R, ha, Pi.add_apply, hK, Pi.smul_apply, smul_eq_mul, hr]
    change _ + K * S x = _
    rw [show S x = N q x + (m • N u) x from hs, hm']
    simp only [Pi.smul_apply, smul_eq_mul, hq, hu]
  have hS : ‖S‖ ≤ ‖q‖ + m * ‖u‖ := (norm_add_le _ _).trans (by
    rw [norm_smul, Real.norm_of_nonneg hm]
    exact add_le_add (hNnorm q) (mul_le_mul_of_nonneg_left (hNnorm u) hm))
  have hRnorm : ‖R‖ ≤ ‖r‖ + K * (‖q‖ + m * ‖u‖) := (norm_add_le _ _).trans (by
    rw [norm_smul, Real.norm_of_nonneg K.coe_nonneg]
    exact add_le_add (hNnorm r) (mul_le_mul_of_nonneg_left hS K.coe_nonneg))
  have hbound := Lp.mul_norm_le_add_of_ae_le_add hm
    (restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (zeroExtendLp (HalfSpace.measurableSet_upper n) U)))
    (restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (zeroExtendLp (HalfSpace.measurableSet_upper n) Q))) R
  refine ((hbound ?_).trans (add_le_add le_rfl hRnorm)).trans_eq (by ring)
  filter_upwards [heq, ae_add_normalStep_upper hh.le heq, hU,
    ae_add_normalStep_upper hh.le hU, hQ, ae_add_normalStep_upper hh.le hQ,
    inward_differenceQuotient_apply_ae U hh.le,
    inward_differenceQuotient_apply_ae Q hh.le, hparameter, hR,
    ae_restrict_mem (HalfSpace.measurableSet_upper n)]
    with x hx hxt hux huy hqx hqy hdu hdq hr hRx hxU
  let y := x + coordinateStep (PDE.Common.lastIndex (n := n)) h
  change A y (u y) = q y at hxt
  change U y = η y * u y at huy
  change Q y = η y * q y at hqy
  have hyU : y ∈ HalfSpace.upper n := mapsTo_add_normalStep_upper hh.le hxU
  have hi := PDE.Analysis.Operator.mul_norm_sub_le_output_add_parameter
    A (q := x) (hmono y hyU (u y) (u x))
  have hi' : m * ‖u y - u x‖ ≤
      ‖q y - q x‖ + ‖A y (u x) - A x (u x)‖ := by
    rw [norm_sub_rev (A x (u x)) (A y (u x))] at hi
    simpa only [hxt, hx] using hi
  have hl := PDE.Analysis.Operator.mul_norm_smul_sub_le_of_inverse_estimate
    hm hi' (η y) (η x)
  simp only [smul_eq_mul, ← hux, ← huy, ← hqx, ← hqy] at hl
  have hdist : ‖y - x‖ = h := by
    simp only [y, add_sub_cancel_left, norm_coordinateStep, abs_of_pos hh]
  have hηdiff : |η y - η x| ≤ K * h := by
    simpa only [dist_eq_norm, hdist, Real.norm_eq_abs] using hη.dist_le_mul y x
  have hb : m * ‖U y - U x‖ ≤
      ‖Q y - Q x‖ + h * (‖r x‖ + K * (‖q x‖ + m * ‖u x‖)) :=
    hl.trans ((add_le_add (add_le_add le_rfl hr)
      (mul_le_mul_of_nonneg_right hηdiff (by positivity))).trans_eq (by ring))
  rw [hdu, hdq, hRx, Real.norm_of_nonneg (show
    0 ≤ ‖r x‖ + K * (‖q x‖ + m * ‖u x‖) by positivity), norm_mul, norm_mul, norm_inv,
    Real.norm_of_nonneg hh.le]
  calc m * (h⁻¹ * ‖U y - U x‖) = h⁻¹ * (m * ‖U y - U x‖) := by ring
    _ ≤ h⁻¹ * (‖Q y - Q x‖ + h * (‖r x‖ + K * (‖q x‖ + m * ‖u x‖))) := by gcongr
    _ = _ := by rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

/-- A localized output in `W¹ᵖ` determines the weak normal derivative of the localized
unknown. The original fields need only be `Lp`; the two cutoff errors remain in the bound. -/
theorem exists_localized_normal_weakDerivative
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (A : ℝ^n → ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ s t : ℝ,
      m * ‖s - t‖ * ‖s - t‖ ≤ ⟪A x s - A x t, s - t⟫)
    (η : ℝ^n → ℝ) {K : ℝ≥0} (hη : LipschitzWith K η)
    (u q U : DerivLp n p (HalfSpace.upper n))
    (Q : W^{1,p}(HalfSpace.upper n))
    (heq : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), A x (u x) = q x)
    (hU : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), U x = η x * u x)
    (hQ : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM Q x = η x * q x)
    (C : ℝ)
    (hparameter : ∀ h : ℝ, 0 < h → ∃ r : DerivLp n p (HalfSpace.upper n),
      ‖r‖ ≤ C ∧ ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
        |η (x + coordinateStep (PDE.Common.lastIndex (n := n)) h)| *
          ‖A (x + coordinateStep (PDE.Common.lastIndex (n := n)) h) (u x) - A x (u x)‖
            ≤ h * ‖r x‖) :
    ∃ g : DerivLp n p (HalfSpace.upper n),
      ‖g‖ ≤
        (‖wkpCoordinateCLM (singleDerivIndex n (PDE.Common.lastIndex (n := n)))
          ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap Q)‖ +
          C + K * (‖q‖ + m * ‖u‖)) / m ∧
      HasWeakDerivativeOn (HalfSpace.upper n) [PDE.Common.lastIndex (n := n)]
        (U : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  apply exists_normal_weakDerivative_of_bounded_inward_differenceQuotients hp hp_top U
  intro h hh
  obtain ⟨r, hr, hpar⟩ := hparameter h hh
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm]
  exact (mul_norm_localized_inward_differenceQuotient_le A hm.le hmono η hη
    u q U (wkpBaseCoordinateCLM Q) heq hU hQ hh r hpar).trans
      (add_le_add (add_le_add
        (norm_inward_differenceQuotient_le hp_top Q hh.le) hr) le_rfl)

end SobolevSpace.GraphSpace.Composition.Implicit
