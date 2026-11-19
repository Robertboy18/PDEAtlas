/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.CoxDeBoor
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Polynomial branches of Cox–de Boor splines

Fixing the active degree-zero cell gives a polynomial extension of every basis
function from that cell. The extensions have derivatives everywhere, including at
knots. Matching the values and first derivatives of adjacent extensions therefore
gives the derivative of the piecewise-defined spline at their junction.
-/

@[expose] public section

namespace CAS.Splines

open Set

noncomputable section

/-- Polynomial extension from a fixed active degree-zero cell. -/
def coxDeBoorBranch (knots : KnotSequence) (cell : ℕ) : ℕ → ℕ → ℝ → ℝ
  | 0, index, _ => if index = cell then 1 else 0
  | degree + 1, index, x =>
      leftBlendWeight knots degree index x * coxDeBoorBranch knots cell degree index x +
        rightBlendWeight knots degree index x *
          coxDeBoorBranch knots cell degree (index + 1) x

/-- Product-rule derivative of the polynomial extension. -/
def coxDeBoorBranchDerivative (knots : KnotSequence) (cell : ℕ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | degree + 1, index, x =>
      (leftBlendWeightDerivative knots degree index * coxDeBoorBranch knots cell degree index x +
        leftBlendWeight knots degree index x *
          coxDeBoorBranchDerivative knots cell degree index x) +
      (rightBlendWeightDerivative knots degree index *
          coxDeBoorBranch knots cell degree (index + 1) x +
        rightBlendWeight knots degree index x *
          coxDeBoorBranchDerivative knots cell degree (index + 1) x)

/-- Polynomial-branch differentiation is valid even at knots. -/
theorem hasDerivAt_coxDeBoorBranch (knots : KnotSequence) (cell degree index : ℕ) (x : ℝ) :
    HasDerivAt (coxDeBoorBranch knots cell degree index)
      (coxDeBoorBranchDerivative knots cell degree index x) x := by
  induction degree generalizing index with
  | zero => exact hasDerivAt_const x _
  | succ degree ih =>
      exact ((hasDerivAt_leftBlendWeight knots degree index x).mul (ih index)).add
        ((hasDerivAt_rightBlendWeight knots degree index x).mul (ih (index + 1)))

/-- On a half-open knot cell, the polynomial extension equals the basis. -/
theorem coxDeBoorBasis_eq_branch (knots : KnotSequence) (cell degree index : ℕ) {x : ℝ}
    (hx : x ∈ Ico (knots cell) (knots (cell + 1))) :
    coxDeBoorBasis knots degree index x = coxDeBoorBranch knots cell degree index x := by
  induction degree generalizing index with
  | zero =>
      by_cases hindex : index = cell
      · subst index
        simp [coxDeBoorBranch, hx]
      · have hnot : x ∉ Ico (knots index) (knots (index + 1)) := by
          intro hmem
          rcases lt_or_gt_of_ne hindex with hlt | hgt
          · exact (not_lt_of_ge (knots.monotone (by omega) |>.trans hx.1)) hmem.2
          · exact (not_lt_of_ge ((knots.monotone (show cell + 1 ≤ index by omega)).trans
              hmem.1)) hx.2
        simp [coxDeBoorBranch, hindex, hnot]
  | succ degree ih =>
      simp only [coxDeBoorBasis_succ, coxDeBoorBranch, ih]

/-- The differentiated algebraic recurrence agrees with the active branch derivative.
Unlike differentiability of the basis, this identity also holds at the left cell endpoint. -/
theorem coxDeBoorBasisDerivative_eq_branchDerivative (knots : KnotSequence)
    (cell degree index : ℕ) {x : ℝ}
    (hx : x ∈ Ico (knots cell) (knots (cell + 1))) :
    coxDeBoorBasisDerivative knots degree index x =
      coxDeBoorBranchDerivative knots cell degree index x := by
  induction degree generalizing index with
  | zero => rfl
  | succ degree ih =>
      simp only [coxDeBoorBasisDerivative_succ, coxDeBoorBranchDerivative, ih,
        coxDeBoorBasis_eq_branch knots cell degree _ hx]

/-- Inside a knot cell, `coxDeBoorBasisDerivative` is the derivative of the basis. -/
theorem hasDerivAt_coxDeBoorBasis_of_mem_Ioo (knots : KnotSequence)
    (cell degree index : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (knots cell) (knots (cell + 1))) :
    HasDerivAt (coxDeBoorBasis knots degree index)
      (coxDeBoorBasisDerivative knots degree index x) x := by
  rw [coxDeBoorBasisDerivative_eq_branchDerivative knots cell degree index ⟨hx.1.le, hx.2⟩]
  apply (hasDerivAt_coxDeBoorBranch knots cell degree index x).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx.1, eventually_lt_nhds hx.2] with y hyLeft hyRight
  exact coxDeBoorBasis_eq_branch knots cell degree index ⟨hyLeft.le, hyRight⟩

/-- The derivative of each polynomial extension is continuous. -/
theorem continuousAt_coxDeBoorBranchDerivative (knots : KnotSequence)
    (cell degree index : ℕ) (x : ℝ) :
    ContinuousAt (coxDeBoorBranchDerivative knots cell degree index) x := by
  induction degree generalizing index with
  | zero => exact continuousAt_const
  | succ degree ih =>
      exact ((continuousAt_const.mul
        (hasDerivAt_coxDeBoorBranch knots cell degree index x).continuousAt).add
        ((hasDerivAt_leftBlendWeight knots degree index x).continuousAt.mul (ih index))).add
        ((continuousAt_const.mul
          (hasDerivAt_coxDeBoorBranch knots cell degree (index + 1) x).continuousAt).add
          ((hasDerivAt_rightBlendWeight knots degree index x).continuousAt.mul (ih (index + 1))))

/-- Continuous branches with a common endpoint value are continuous at their junction. -/
theorem continuousAt_branch_glue {left right : ℝ → ℝ} {cut : ℝ}
    (hleft : ContinuousAt left cut) (hright : ContinuousAt right cut)
    (hvalue : left cut = right cut) :
    ContinuousAt (fun x ↦ if x < cut then left x else right x) cut := by
  have hl : ContinuousWithinAt (fun x ↦ if x < cut then left x else right x)
      (Iio cut) cut := by
    apply hleft.continuousWithinAt.congr
    · intro x hx
      simp only [mem_Iio] at hx
      simp [hx]
    · simp [hvalue]
  have hr : ContinuousWithinAt (fun x ↦ if x < cut then left x else right x)
      (Iio cut)ᶜ cut := by
    apply hright.continuousWithinAt.congr
    · intro x hx
      simp only [mem_compl_iff, mem_Iio] at hx
      simp [hx]
    · simp
  simpa only [union_compl_self, continuousWithinAt_univ] using hl.union hr

/-- Two differentiable branches with matching value and derivative glue at their cut. -/
theorem hasDerivAt_branch_glue {left right : ℝ → ℝ} {cut slope : ℝ}
    (hleft : HasDerivAt left slope cut) (hright : HasDerivAt right slope cut)
    (hvalue : left cut = right cut) :
    HasDerivAt (fun x ↦ if x < cut then left x else right x) slope cut := by
  have hl : HasDerivWithinAt (fun x ↦ if x < cut then left x else right x)
      slope (Iio cut) cut := by
    apply hleft.hasDerivWithinAt.congr
    · intro x hx
      simp only [mem_Iio] at hx
      simp [hx]
    · simp [hvalue]
  have hr : HasDerivWithinAt (fun x ↦ if x < cut then left x else right x)
      slope (Iio cut)ᶜ cut := by
    apply hright.hasDerivWithinAt.congr
    · intro x hx
      simp only [mem_compl_iff, mem_Iio] at hx
      simp [hx]
    · simp
  simpa using hl.union hr

/-- Matching adjacent polynomial jets gives the derivative at a knot.
The two neighboring cells must be nondegenerate. -/
theorem hasDerivAt_coxDeBoorBasis_of_branch_match (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2))
    (hvalue : coxDeBoorBranch knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranch knots (cell + 1) degree index (knots (cell + 1)))
    (hderiv : coxDeBoorBranchDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1))) :
    HasDerivAt (coxDeBoorBasis knots degree index)
      (coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1)))
      (knots (cell + 1)) := by
  have hglue := hasDerivAt_branch_glue
    ((hasDerivAt_coxDeBoorBranch knots cell degree index _).congr_deriv hderiv)
    (hasDerivAt_coxDeBoorBranch knots (cell + 1) degree index _) hvalue
  apply hglue.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with x hxleft hxright
  split_ifs with hx
  · exact coxDeBoorBasis_eq_branch knots cell degree index ⟨hxleft.le, hx⟩
  · exact coxDeBoorBasis_eq_branch knots (cell + 1) degree index
      ⟨le_of_not_gt hx, by simpa only [Nat.add_assoc] using hxright⟩

/-- Matched polynomial jets identify the derivative throughout both neighboring cells. -/
theorem hasDerivAt_coxDeBoorBasis_on_adjacent_cells (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2))
    (hvalue : coxDeBoorBranch knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranch knots (cell + 1) degree index (knots (cell + 1)))
    (hderiv : coxDeBoorBranchDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1)))
    {x : ℝ} (hx : x ∈ Ioo (knots cell) (knots (cell + 2))) :
    HasDerivAt (coxDeBoorBasis knots degree index)
      (coxDeBoorBasisDerivative knots degree index x) x := by
  rcases lt_trichotomy x (knots (cell + 1)) with hlt | heq | hgt
  · exact hasDerivAt_coxDeBoorBasis_of_mem_Ioo knots cell degree index ⟨hx.1, hlt⟩
  · subst x
    rw [coxDeBoorBasisDerivative_eq_branchDerivative knots (cell + 1) degree index
      ⟨le_rfl, by simpa only [Nat.add_assoc] using hright⟩]
    exact hasDerivAt_coxDeBoorBasis_of_branch_match knots cell degree index
      hleft hright hvalue hderiv
  · exact hasDerivAt_coxDeBoorBasis_of_mem_Ioo knots (cell + 1) degree index
      ⟨hgt, by simpa only [Nat.add_assoc] using hx.2⟩

/-- Matching first branch derivatives makes the algebraic derivative continuous at a knot. -/
theorem continuousAt_coxDeBoorBasisDerivative_of_branch_match (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2))
    (hderiv : coxDeBoorBranchDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1))) :
    ContinuousAt (coxDeBoorBasisDerivative knots degree index) (knots (cell + 1)) := by
  have hglue := continuousAt_branch_glue
    (continuousAt_coxDeBoorBranchDerivative knots cell degree index _)
    (continuousAt_coxDeBoorBranchDerivative knots (cell + 1) degree index _) hderiv
  apply hglue.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with x hxleft hxright
  split_ifs with hx
  · exact coxDeBoorBasisDerivative_eq_branchDerivative knots cell degree index ⟨hxleft.le, hx⟩
  · exact coxDeBoorBasisDerivative_eq_branchDerivative knots (cell + 1) degree index
      ⟨le_of_not_gt hx, by simpa only [Nat.add_assoc] using hxright⟩

/-- The derivative is continuous at a knot whose neighboring polynomial jets match. -/
theorem continuousAt_deriv_coxDeBoorBasis_of_branch_match (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2))
    (hvalue : coxDeBoorBranch knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranch knots (cell + 1) degree index (knots (cell + 1)))
    (hderiv : coxDeBoorBranchDerivative knots cell degree index (knots (cell + 1)) =
      coxDeBoorBranchDerivative knots (cell + 1) degree index (knots (cell + 1))) :
    ContinuousAt (deriv (coxDeBoorBasis knots degree index)) (knots (cell + 1)) := by
  apply (continuousAt_coxDeBoorBasisDerivative_of_branch_match knots cell degree index
    hleft hright hderiv).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with x hxleft hxright
  exact (hasDerivAt_coxDeBoorBasis_on_adjacent_cells knots cell degree index
    hleft hright hvalue hderiv ⟨hxleft, hxright⟩).deriv

end

end CAS.Splines
