/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.DilationLp
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedJets

/-!
# Weighted reflection on `L^p` derivative coordinates

For each normal multiplicity `r`, we construct a bounded linear extension
whose lower branch is the corresponding weighted sum of reflected normal dilations.
The explicit bound works for every `1 ≤ p ≤ ∞`. Restriction to the upper half-space
is a left inverse, independently of `r`.

These coordinate maps do not by themselves assert the weak-derivative relations
between successive rows. That analytic gluing step is needed to restrict the
ambient bundle map to a higher-order Sobolev space.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory
open SobolevSpace.Extension.Lp
open scoped ENNReal

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The lower half-space branch of the row with `r` normal derivatives. -/
def weightedPullbackLp (r : ℕ) : DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p ℝ^n₋ :=
  ∑ j : Fin (k + 1), (reflectionCoeff k j * reflectionNode k j ^ r) •
    dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j)

/-- A row of weighted reflection, with the original function on the upper half-space. -/
def weightedExtendLp (r : ℕ) : DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p univ :=
  HalfSpace.embedUpper (n := n) (p := p) +
    (HalfSpace.embedLower (n := n) (p := p)).comp (weightedPullbackLp n k p r)

/-- The lower branch is represented by the finite weighted sum of literal dilations. -/
theorem weightedPullbackLp_apply_ae (r : ℕ) (u : DerivLp n p ℝ^n₊) :
    (weightedPullbackLp n k p r u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₋]
      reflectedJet (PDE.Common.lastIndex (n := n)) k r u := by
  have hsum := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin (k + 1)))
    (fun j ↦ (reflectionCoeff k j * reflectionNode k j ^ r) •
      dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u)
  have hterm : ∀ j : Fin (k + 1), ∀ᵐ x ∂domainMeasure n ℝ^n₋,
      (((reflectionCoeff k j * reflectionNode k j ^ r) •
        dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u :
        DerivLp n p ℝ^n₋) : ℝ^n → ℝ) x =
      (reflectionCoeff k j * reflectionNode k j ^ r) *
        u (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j) x) := by
    intro j
    filter_upwards [Lp.coeFn_smul (reflectionCoeff k j * reflectionNode k j ^ r)
      (dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u),
      dilationPullbackLp_apply_ae n p (reflectionNode k j) (reflectionNode_neg k j) u]
      with x hx hy
    simp only [hx, Pi.smul_apply, smul_eq_mul, hy]
  have hall := (ae_all_iff).2 hterm
  simp only [weightedPullbackLp, sum_apply, smul_apply]
  filter_upwards [hsum, hall] with x hx hy
  rw [hx]
  simp only [Finset.sum_apply, reflectedJet]
  exact Finset.sum_congr rfl (fun j _ ↦ hy j)

/-- The lower-branch bound retains the Jacobian contribution of each dilation. -/
theorem norm_weightedPullbackLp_le (r : ℕ) (u : DerivLp n p ℝ^n₊) :
    ‖weightedPullbackLp n k p r u‖ ≤
      (∑ j, ‖reflectionCoeff k j * reflectionNode k j ^ r‖ *
        |(reflectionNode k j)⁻¹| ^ (1 / p).toReal) * ‖u‖ := by
  simp only [weightedPullbackLp, sum_apply, smul_apply]
  calc
    ‖∑ j : Fin (k + 1), (reflectionCoeff k j * reflectionNode k j ^ r) •
        dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u‖ ≤
        ∑ j, ‖reflectionCoeff k j * reflectionNode k j ^ r‖ *
          ‖dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u‖ := by
      simpa only [norm_smul] using norm_sum_le
        (s := Finset.univ) (f := fun j : Fin (k + 1) ↦
          (reflectionCoeff k j * reflectionNode k j ^ r) •
            dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u)
    _ ≤ ∑ j, ‖reflectionCoeff k j * reflectionNode k j ^ r‖ *
        (|(reflectionNode k j)⁻¹| ^ (1 / p).toReal * ‖u‖) :=
      Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
        (norm_dilationPullbackLp_le n p _ (reflectionNode_neg k j) u) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]; simp only [mul_assoc]

/-- An explicit finite bound for the complete extension row, valid at both endpoints. -/
theorem norm_weightedExtendLp_le (r : ℕ) (u : DerivLp n p ℝ^n₊) :
    ‖weightedExtendLp n k p r u‖ ≤
      (1 + ∑ j, ‖reflectionCoeff k j * reflectionNode k j ^ r‖ *
        |(reflectionNode k j)⁻¹| ^ (1 / p).toReal) * ‖u‖ := by
  calc
    ‖weightedExtendLp n k p r u‖ ≤
        ‖HalfSpace.embedUpper (n := n) (p := p) u‖ +
          ‖HalfSpace.embedLower (n := n) (p := p) (weightedPullbackLp n k p r u)‖ :=
      norm_add_le _ _
    _ = ‖u‖ + ‖weightedPullbackLp n k p r u‖ := by
      rw [HalfSpace.embedUpper, HalfSpace.embedLower, norm_zeroExtendLp, norm_zeroExtendLp]
    _ ≤ _ := by
      rw [add_mul, one_mul]
      exact add_le_add le_rfl (norm_weightedPullbackLp_le n k p r u)

/-- The global row is the sum of the two indicator branches almost everywhere. -/
theorem weightedExtendLp_apply_ae (r : ℕ) (u : DerivLp n p ℝ^n₊) :
    (weightedExtendLp n k p r u : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ℝ^n₊.indicator (u : ℝ^n → ℝ) x +
        ℝ^n₋.indicator (reflectedJet (PDE.Common.lastIndex (n := n)) k r u) x := by
  have hu := zeroExtendLp_apply_ae (HalfSpace.measurableSet_upper (n := n)) u
  have hl := zeroExtendLp_apply_ae (HalfSpace.measurableSet_lower (n := n))
    (weightedPullbackLp n k p r u)
  have hp := (ae_restrict_iff' (HalfSpace.measurableSet_lower (n := n))).1
    (weightedPullbackLp_apply_ae n k p r u)
  have ha := Lp.coeFn_add (HalfSpace.embedUpper (n := n) (p := p) u)
    (HalfSpace.embedLower (n := n) (p := p) (weightedPullbackLp n k p r u))
  simp only [domainMeasure, Measure.restrict_univ] at hu hl ha
  filter_upwards [hu, hl, hp, ha] with x hxu hxl hxp hxa
  change ((HalfSpace.embedUpper (n := n) (p := p) u +
    HalfSpace.embedLower (n := n) (p := p) (weightedPullbackLp n k p r u) :
    DerivLp n p univ) : ℝ^n → ℝ) x = _
  rw [hxa, Pi.add_apply]
  change (zeroExtendLp _ u : ℝ^n → ℝ) x +
    (zeroExtendLp _ (weightedPullbackLp n k p r u) : ℝ^n → ℝ) x = _
  rw [hxu, hxl]
  unfold extensionByZero
  by_cases hx : x ∈ ℝ^n₋
  · simp only [Set.indicator_of_mem hx, hxp hx]
  · simp only [Set.indicator_of_notMem hx]

/-- The base row has the literal weighted-reflection representative. -/
theorem weightedExtendLp_zero_apply_ae (u : DerivLp n p ℝ^n₊) :
    (weightedExtendLp n k p 0 u : ℝ^n → ℝ) =ᵐ[volume]
      weightedReflectionFun (PDE.Common.lastIndex (n := n)) k u := by
  have haxis : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∉ HalfSpace.boundary n := by
    rw [MeasureTheory.ae_iff]
    simpa using HalfSpace.volume_boundary n
  filter_upwards [weightedExtendLp_apply_ae n k p 0 u, haxis] with x hx hxb
  rw [hx]
  have hne : x (PDE.Common.lastIndex (n := n)) ≠ 0 := by
    simpa [HalfSpace.boundary] using hxb
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · simp [weightedReflectionFun, HalfSpace.upper, HalfSpace.lower,
      hneg, not_lt.mpr hneg.le]
  · simp [weightedReflectionFun, HalfSpace.upper, HalfSpace.lower,
      hpos, not_lt.mpr hpos.le]

/-- Restricting a weighted extension row to the upper half-space recovers the source. -/
@[simp] theorem restrict_weightedExtendLp (r : ℕ) (u : DerivLp n p ℝ^n₊) :
    restrictDerivLp (subset_univ ℝ^n₊) (weightedExtendLp n k p r u) = u := by
  apply Lp.ext
  apply (restrictDerivLp_apply_ae (subset_univ ℝ^n₊) _).trans
  have he := ae_restrict_of_ae (s := ℝ^n₊) (weightedExtendLp_apply_ae n k p r u)
  filter_upwards [he, ae_restrict_mem (HalfSpace.measurableSet_upper (n := n))]
    with x hx hxupper
  have hxlower : x ∉ ℝ^n₋ := by
    change 0 < x (PDE.Common.lastIndex (n := n)) at hxupper
    change ¬x (PDE.Common.lastIndex (n := n)) < 0
    exact not_lt_of_ge (le_of_lt hxupper)
  simpa only [Set.indicator_of_mem hxupper, Set.indicator_of_notMem hxlower, add_zero]
    using hx

end SobolevSpace.GraphSpace.HigherOrderReflection
