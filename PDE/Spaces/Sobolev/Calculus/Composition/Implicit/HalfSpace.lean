/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.NormDomination
public import PDE.Analysis.Operator.StrongMonotonicity.InverseEstimate
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.HalfSpace.Converse
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.HalfSpace.Forward

/-!
# Weak normal derivatives recovered from a monotone scalar equation

Suppose `A x (u x) = q x`, where the scalar map `A x` is uniformly strongly monotone.
An inward difference quotient of `u` is bounded by the corresponding quotient of `q`
and the variation of `A` in its parameter, with its scalar argument held fixed. If `q`
is Sobolev and the parameter variation has a uniform `Lp` bound, the difference-quotient
converse constructs the weak normal derivative of `u`.

This argument does not differentiate an inverse or assume that `u` already has a normal
derivative. In boundary regularity the parameter contains the spatial point and the
tangential components of the gradient, whose derivatives have already been recovered.
The half-space translation is inward, so the proof also applies in dimension one.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Composition.Implicit

open Filter MeasureTheory Set
open SobolevSpace.Extension.Lp SobolevSpace.GraphSpace.DifferenceQuotient
open SobolevSpace.GraphSpace.Rellich
open scoped ENNReal Topology RealInnerProductSpace Sobolev

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A strongly monotone scalar equation controls each inward quotient of its unknown.
The error only measures changes in the parameter of `A`, with the scalar argument fixed. -/
theorem mul_norm_inward_differenceQuotient_le
    (A : ℝ^n → ℝ → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ s t : ℝ,
      m * ‖s - t‖ * ‖s - t‖ ≤ ⟪A x s - A x t, s - t⟫)
    (u q : DerivLp n p (HalfSpace.upper n))
    (heq : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), A x (u x) = q x)
    {h : ℝ} (hh : 0 < h) (r : DerivLp n p (HalfSpace.upper n))
    (hparameter : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      ‖A (x + coordinateStep (PDE.Common.lastIndex (n := n)) h) (u x) - A x (u x)‖
        ≤ h * ‖r x‖) :
    m * ‖restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (zeroExtendLp (HalfSpace.measurableSet_upper n) u))‖ ≤
      ‖restrictDerivLp (subset_univ (HalfSpace.upper n))
        (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
          (zeroExtendLp (HalfSpace.measurableSet_upper n) q))‖ + ‖r‖ := by
  apply Lp.mul_norm_le_add_of_ae_le_add hm
  filter_upwards [heq, ae_add_normalStep_upper hh.le heq,
    inward_differenceQuotient_apply_ae u hh.le,
    inward_differenceQuotient_apply_ae q hh.le, hparameter,
    ae_restrict_mem (HalfSpace.measurableSet_upper n)]
    with x hx hxt hu hq hr hxU
  let y := x + coordinateStep (PDE.Common.lastIndex (n := n)) h
  change A y (u y) = q y at hxt
  have hyU : y ∈ HalfSpace.upper n := mapsTo_add_normalStep_upper hh.le hxU
  have hi := PDE.Analysis.Operator.mul_norm_sub_le_output_add_parameter
    A (q := x) (hmono y hyU (u y) (u x))
  have hb : m * ‖u y - u x‖ ≤ ‖q y - q x‖ + h * ‖r x‖ := by
    rw [norm_sub_rev (A x (u x)) (A y (u x))] at hi
    have hb' := hi.trans (add_le_add le_rfl hr)
    simpa only [hxt, hx] using hb'
  rw [hu, hq]
  change m * ‖h⁻¹ * (u y - u x)‖ ≤ ‖h⁻¹ * (q y - q x)‖ + ‖r x‖
  calc
    m * ‖h⁻¹ * (u y - u x)‖ = h⁻¹ * (m * ‖u y - u x‖) := by
      rw [norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hh]
      ring
    _ ≤ h⁻¹ * (‖q y - q x‖ + h * ‖r x‖) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
    _ = ‖h⁻¹ * (q y - q x)‖ + ‖r x‖ := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
      simp only [norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hh]

/-- Recover the missing weak normal derivative from a strongly monotone scalar equation.
The hypotheses require only `Lp` regularity of the unknown, `W¹ᵖ` regularity of the
output, and bounds for changes in the parameter. The derivative and its norm estimate
follow from inward quotients and weak compactness, without any inverse-existence premise. -/
theorem exists_normal_weakDerivative_of_strongMonotone_family
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (A : ℝ^n → ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ s t : ℝ,
      m * ‖s - t‖ * ‖s - t‖ ≤ ⟪A x s - A x t, s - t⟫)
    (u : DerivLp n p (HalfSpace.upper n))
    (Q : W^{1,p}(HalfSpace.upper n))
    (heq : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (u x) = wkpBaseCoordinateCLM Q x)
    (C : ℝ)
    (hparameter : ∀ h : ℝ, 0 < h → ∃ r : DerivLp n p (HalfSpace.upper n),
      ‖r‖ ≤ C ∧ ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
        ‖A (x + coordinateStep (PDE.Common.lastIndex (n := n)) h) (u x) - A x (u x)‖
          ≤ h * ‖r x‖) :
    ∃ g : DerivLp n p (HalfSpace.upper n),
      ‖g‖ ≤
        (‖wkpCoordinateCLM (singleDerivIndex n (PDE.Common.lastIndex (n := n)))
          ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap Q)‖
            + C) / m ∧
      HasWeakDerivativeOn (HalfSpace.upper n) [PDE.Common.lastIndex (n := n)]
        (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  apply exists_normal_weakDerivative_of_bounded_inward_differenceQuotients hp hp_top u
  intro h hh
  obtain ⟨r, hr, hpar⟩ := hparameter h hh
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm]
  exact (mul_norm_inward_differenceQuotient_le A hm.le hmono u
    (wkpBaseCoordinateCLM Q) heq hh r hpar).trans
      (add_le_add (norm_inward_differenceQuotient_le hp_top Q hh.le) hr)

end SobolevSpace.GraphSpace.Composition.Implicit
