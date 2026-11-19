/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.LocalBranches

/-!
# Second derivatives across spline knots

Matching the first three polynomial jets across neighboring cells identifies
the first and second derivatives at their junction. The second derivative
is continuous there. The jet matching is a hypothesis of each statement.
-/

@[expose] public section

namespace CAS.Splines

open Set

noncomputable section

/-- Second derivative of a fixed Cox–de Boor polynomial branch. -/
def coxDeBoorBranchSecondDerivative (knots : KnotSequence) (cell : ℕ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | degree + 1, index, x =>
      (leftBlendWeight knots degree index x *
          coxDeBoorBranchSecondDerivative knots cell degree index x +
        (2 * leftBlendWeightDerivative knots degree index) *
          coxDeBoorBranchDerivative knots cell degree index x) +
      (rightBlendWeight knots degree index x *
          coxDeBoorBranchSecondDerivative knots cell degree (index + 1) x +
        (2 * rightBlendWeightDerivative knots degree index) *
          coxDeBoorBranchDerivative knots cell degree (index + 1) x)

/-- The polynomial branch derivative has the stated second derivative everywhere. -/
theorem hasDerivAt_coxDeBoorBranchDerivative (knots : KnotSequence)
    (cell degree index : ℕ) (x : ℝ) :
    HasDerivAt (coxDeBoorBranchDerivative knots cell degree index)
      (coxDeBoorBranchSecondDerivative knots cell degree index x) x := by
  induction degree generalizing index with
  | zero => exact hasDerivAt_const x 0
  | succ degree ih =>
      have h :=
        (((hasDerivAt_coxDeBoorBranch knots cell degree index x).const_mul
          (leftBlendWeightDerivative knots degree index)).add
          ((hasDerivAt_leftBlendWeight knots degree index x).mul (ih index))).add
        (((hasDerivAt_coxDeBoorBranch knots cell degree (index + 1) x).const_mul
          (rightBlendWeightDerivative knots degree index)).add
          ((hasDerivAt_rightBlendWeight knots degree index x).mul (ih (index + 1))))
      apply h.congr_deriv
      dsimp only [coxDeBoorBranchSecondDerivative]
      ring

/-- The second derivative of each polynomial branch is continuous. -/
theorem continuousAt_coxDeBoorBranchSecondDerivative (knots : KnotSequence)
    (cell degree index : ℕ) (x : ℝ) :
    ContinuousAt (coxDeBoorBranchSecondDerivative knots cell degree index) x := by
  induction degree generalizing index with
  | zero => exact continuousAt_const
  | succ degree ih =>
      exact (((hasDerivAt_leftBlendWeight knots degree index x).continuousAt.mul (ih index)).add
        (continuousAt_const.mul
          (continuousAt_coxDeBoorBranchDerivative knots cell degree index x))).add
        (((hasDerivAt_rightBlendWeight knots degree index x).continuousAt.mul (ih (index + 1))).add
          (continuousAt_const.mul
            (continuousAt_coxDeBoorBranchDerivative knots cell degree (index + 1) x)))

/-- On the interior of a cell, the derivative has the polynomial second derivative. -/
theorem hasDerivAt_deriv_coxDeBoorBasis_of_mem_Ioo (knots : KnotSequence)
    (cell degree index : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (knots cell) (knots (cell + 1))) :
    HasDerivAt (deriv (coxDeBoorBasis knots degree index))
      (coxDeBoorBranchSecondDerivative knots cell degree index x) x := by
  apply (hasDerivAt_coxDeBoorBranchDerivative knots cell degree index x).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx.1, eventually_lt_nhds hx.2] with y hyLeft hyRight
  rw [(hasDerivAt_coxDeBoorBasis_of_mem_Ioo knots cell degree index ⟨hyLeft, hyRight⟩).deriv]
  exact coxDeBoorBasisDerivative_eq_branchDerivative knots cell degree index ⟨hyLeft.le, hyRight⟩

/-- Matching values, first derivatives, and second derivatives gives the
second derivative at the junction knot. -/
theorem hasDerivAt_deriv_coxDeBoorBasis_of_branch_match (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2))
    (hvalue : coxDeBoorBranch knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranch knots (cell + 1) degree index (knots (cell + 1)))
    (hfirst : coxDeBoorBranchDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1)))
    (hsecond : coxDeBoorBranchSecondDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchSecondDerivative knots (cell + 1) degree index (knots (cell + 1))) :
    HasDerivAt (deriv (coxDeBoorBasis knots degree index))
      (coxDeBoorBranchSecondDerivative knots (cell + 1) degree index (knots (cell + 1)))
      (knots (cell + 1)) := by
  have hglue := hasDerivAt_branch_glue
    ((hasDerivAt_coxDeBoorBranchDerivative knots cell degree index _).congr_deriv hsecond)
    (hasDerivAt_coxDeBoorBranchDerivative knots (cell + 1) degree index _) hfirst
  apply hglue.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with x hxleft hxright
  rw [(hasDerivAt_coxDeBoorBasis_on_adjacent_cells knots cell degree index
    hleft hright hvalue hfirst ⟨hxleft, hxright⟩).deriv]
  split_ifs with hx
  · exact coxDeBoorBasisDerivative_eq_branchDerivative knots cell degree index ⟨hxleft.le, hx⟩
  · exact coxDeBoorBasisDerivative_eq_branchDerivative knots (cell + 1) degree index
      ⟨le_of_not_gt hx, by simpa only [Nat.add_assoc] using hxright⟩

/-- The second derivative is continuous when all three branch jets agree. -/
theorem continuousAt_second_deriv_coxDeBoorBasis_of_branch_match (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2))
    (hvalue : coxDeBoorBranch knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranch knots (cell + 1) degree index (knots (cell + 1)))
    (hfirst : coxDeBoorBranchDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1)))
    (hsecond : coxDeBoorBranchSecondDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchSecondDerivative knots (cell + 1) degree index (knots (cell + 1))) :
    ContinuousAt (deriv (deriv (coxDeBoorBasis knots degree index)))
      (knots (cell + 1)) := by
  have hglue := continuousAt_branch_glue
    (continuousAt_coxDeBoorBranchSecondDerivative knots cell degree index _)
    (continuousAt_coxDeBoorBranchSecondDerivative knots (cell + 1) degree index _) hsecond
  apply hglue.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with x hxleft hxright
  rcases lt_trichotomy x (knots (cell + 1)) with hlt | heq | hgt
  · rw [ite_eq_left hlt]
    exact (hasDerivAt_deriv_coxDeBoorBasis_of_mem_Ioo knots cell degree index ⟨hxleft, hlt⟩).deriv
  · subst x
    rw [ite_eq_right (lt_irrefl _)]
    exact (hasDerivAt_deriv_coxDeBoorBasis_of_branch_match knots cell degree index
      hleft hright hvalue hfirst hsecond).deriv
  · rw [ite_eq_right hgt.asymm]
    exact (hasDerivAt_deriv_coxDeBoorBasis_of_mem_Ioo knots (cell + 1) degree index
      ⟨hgt, by simpa only [Nat.add_assoc] using hxright⟩).deriv

/-- The first derivative is differentiable on a neighborhood of a matched knot. -/
theorem eventually_differentiableAt_deriv_coxDeBoorBasis_of_branch_match (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2))
    (hvalue : coxDeBoorBranch knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranch knots (cell + 1) degree index (knots (cell + 1)))
    (hfirst : coxDeBoorBranchDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1)))
    (hsecond : coxDeBoorBranchSecondDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchSecondDerivative knots (cell + 1) degree index (knots (cell + 1))) :
    ∀ᶠ x in nhds (knots (cell + 1)),
      DifferentiableAt ℝ (deriv (coxDeBoorBasis knots degree index)) x := by
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with x hxleft hxright
  rcases lt_trichotomy x (knots (cell + 1)) with hlt | heq | hgt
  · exact (hasDerivAt_deriv_coxDeBoorBasis_of_mem_Ioo knots cell degree index
      ⟨hxleft, hlt⟩).differentiableAt
  · subst x
    exact (hasDerivAt_deriv_coxDeBoorBasis_of_branch_match knots cell degree index
      hleft hright hvalue hfirst hsecond).differentiableAt
  · exact (hasDerivAt_deriv_coxDeBoorBasis_of_mem_Ioo knots (cell + 1) degree index
      ⟨hgt, by simpa only [Nat.add_assoc] using hxright⟩).differentiableAt

/-- A finite weighted sum has the sum of the second derivatives.
First differentiability is required near the point, since differentiating the
first sum identity requires a neighborhood identity. -/
theorem hasDerivAt_deriv_weighted_sum {ι : Type*} (u : Finset ι)
    (f : ι → ℝ → ℝ) (c second : ι → ℝ) (x : ℝ)
    (hfirst : ∀ᶠ y in nhds x, ∀ i ∈ u, DifferentiableAt ℝ (f i) y)
    (hsecond : ∀ i ∈ u, HasDerivAt (deriv (f i)) (second i) x) :
    HasDerivAt (deriv (fun y ↦ ∑ i ∈ u, c i * f i y)) (∑ i ∈ u, c i * second i) x := by
  apply (HasDerivAt.fun_sum (fun i hi ↦ (hsecond i hi).const_mul (c i))).congr_of_eventuallyEq
  filter_upwards [hfirst] with y hy
  exact (HasDerivAt.fun_sum (fun i hi ↦ (hy i hi).hasDerivAt.const_mul (c i))).deriv

/-- Continuity of second derivatives is preserved by finite weighted sums. -/
theorem continuousAt_second_deriv_weighted_sum {ι : Type*} (u : Finset ι)
    (f : ι → ℝ → ℝ) (c : ι → ℝ) (x : ℝ)
    (hfirst : ∀ᶠ y in nhds x, ∀ i ∈ u, DifferentiableAt ℝ (f i) y)
    (hsecond : ∀ᶠ y in nhds x, ∀ i ∈ u, DifferentiableAt ℝ (deriv (f i)) y)
    (hcont : ∀ i ∈ u, ContinuousAt (deriv (deriv (f i))) x) :
    ContinuousAt (deriv (deriv (fun y ↦ ∑ i ∈ u, c i * f i y))) x := by
  have hc : ContinuousAt (fun y ↦ ∑ i ∈ u, c i * deriv (deriv (f i)) y) x :=
    tendsto_finsetSum u (fun i hi ↦ ((hcont i hi).const_mul (c i)).tendsto)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hfirst.eventually_nhds, hsecond] with y hyfirst hysecond
  exact (hasDerivAt_deriv_weighted_sum u f c (fun i ↦ deriv (deriv (f i)) y) y
    hyfirst (fun i hi ↦ (hysecond i hi).hasDerivAt)).deriv

end

end CAS.Splines
