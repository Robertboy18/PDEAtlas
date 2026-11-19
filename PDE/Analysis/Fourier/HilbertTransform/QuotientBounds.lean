/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.InteriorBounds
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.InverseSquare
import CAS.ExactTactic

/-!
# Hilbert quotient bounds for the refined derivative estimate

The half-line Hilbert norm estimate uses the parity of the squares. Applying
it to the once-divided pair gives the origin quotient estimate used in
Chen–Hou–Huang (8.17).

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  supplementary material (in the same PDF), Section 8, (8.17).
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal

noncomputable section

namespace PDE.Analysis

/-- The once-divided Hilbert estimate needed by the second term in (8.17).
The origin constant is the principal value. -/
theorem integral_origin_first_quotient_sq_le
    {omega : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (homega : LipschitzWith K omega) (hc : HasCompactSupport omega)
    (hodd : Function.Odd omega) (hsupport : ∀ x, L ≤ x → omega x = 0) :
    (∫ x in Ioo 0 L, ((hilbertPV omega x - hilbertPV omega 0) / x) ^ 2) ≤
      ∫ x in Ioo 0 L, (omega x / x) ^ 2 := by
  have hzero : omega 0 = 0 := by simpa using hodd.map_zero
  have hp := isHilbertPair_div_sub homega hc hzero
  simp only [sub_zero] at hp
  apply hp.integral_sq_Ioo_le_of_even_sq
  · intro x
    dsimp
    rw [hodd x, neg_div_neg_eq]
  · intro x
    dsimp
    rw [hilbertPV_even_of_odd hodd x, div_neg, neg_sq]
  · intro x hx
    rw [hsupport x hx, zero_div]

/-- The principal value satisfies the origin weight comparison.
The second quotient hypothesis records the required vanishing at the origin. -/
theorem integral_hilbertPV_origin_weight_le {f : ℝ → ℝ} {K : ℝ≥0} {L a b : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ x, L ≤ x → f x = 0)
    (hsecond : MemLp (fun x ↦ f x / x ^ 2) 2 volume)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in Ioo 0 L, (hilbertPV f x - hilbertPV f 0) ^ 2 *
      (a / x ^ 4 + b / x ^ 2)) ≤
      ∫ x in Ioo 0 L, f x ^ 2 * (a / x ^ 4 + b / x ^ 2) := by
  have hp2 := isHilbertPair_div_sq hf hc hodd hsecond
  have hp1 := isHilbertPair_div_sub hf hc hodd.map_zero
  simp only [sub_zero] at hp1
  rw [integral_sq_mul_origin_weight (hp2.memLp_right.restrict _)
      (hp1.memLp_right.restrict _),
    integral_sq_mul_origin_weight (hsecond.restrict _) (hp1.memLp_left.restrict _)]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (integral_origin_divided_difference_sq_le hf hc hodd hsupport hsecond) ha)
    (mul_le_mul_of_nonneg_left (integral_origin_first_quotient_sq_le hf hc hodd hsupport) hb)

/-- Both reflected endpoint weights are controlled by the Hilbert
isometry. No classical derivative at the support endpoint is required. -/
theorem integral_hilbertPV_endpoint_weight_le {f : ℝ → ℝ} {K : ℝ≥0} {L a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ x, L ≤ x → f x = 0) (ha : 0 ≤ a) :
    (∫ x in Ioo 0 L, (hilbertPV f x - hilbertPV f L) ^ 2 *
      (a / (x - L) ^ 2 + a / (x + L) ^ 2)) ≤
      ∫ x in Ioo 0 L, f x ^ 2 * (a / (x - L) ^ 2 + a / (x + L) ^ 2) := by
  let v : ℝ → ℝ := fun x ↦ hilbertPV f x - hilbertPV f L
  have hv : Function.Even v := fun x ↦ by
    simp only [v, hilbertPV_even_of_odd hodd x]
  have hp := isHilbertPair_div_sub hf hc (hsupport L le_rfl)
  have hr := memLp_div_add_of_even hv hp.memLp_right
  have hfl : MemLp (fun x ↦ f x / (x - L)) 2 volume := hp.memLp_left
  have hfr : MemLp (fun x ↦ f x / (x + L)) 2 volume := by
    apply (hfl.comp_measurePreserving (Measure.measurePreserving_neg volume)).ae_eq
    exact Eventually.of_forall fun x ↦ by
      simp only [Function.comp_def, hodd x, show -x - L = -(x + L) by cas,
        neg_div_neg_eq]
  rw [integral_sq_mul_endpoint_weight (hp.memLp_right.restrict _) (hr.restrict _),
    integral_sq_mul_endpoint_weight (hfl.restrict _) (hfr.restrict _)]
  apply mul_le_mul_of_nonneg_left _ ha
  rw [← integral_div_sub_sq_eq_Ioo hf hc hodd hsupport, ← hp.integral_sq_eq,
    integral_eq_integral_Ioi_add_reflection hp.memLp_right.integrable_sq]
  have heq (x : ℝ) :
      ((hilbertPV f x - hilbertPV f L) / (x - L)) ^ 2 +
          ((hilbertPV f (-x) - hilbertPV f L) / (-x - L)) ^ 2 =
        (v x / (x - L)) ^ 2 + (v x / (x + L)) ^ 2 := by
    simp only [v, hilbertPV_even_of_odd hodd x, show -x - L = -(x + L) by cas,
      div_neg, neg_sq]
  simp_rw [heq]
  exact setIntegral_mono_set (hp.memLp_right.integrable_sq.add hr.integrable_sq).integrableOn
    (.of_forall fun x ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
    (.of_forall fun _ hx ↦ hx.1)

end PDE.Analysis
