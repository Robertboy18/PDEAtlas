/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Measure

/-!
# Anisotropic Sobolev derivative families

Anisotropic estimates assign a nonnegative integer cost to each coordinate direction and
measure a derivative word by the sum of its coordinate costs. We apply this grading to the
symmetric derivative indices of `WkpSpaceOn`.

The grading is useful for parabolic and degenerate problems, where derivatives in different
directions have different effective orders. The definitions impose no analytic hypothesis on
either the coordinate costs or the measure density.

## References

* L. Caffarelli, R. Kohn and L. Nirenberg, "First order interpolation inequalities with weights",
  *Compositio Math.* 53 (1984), no. 3, 259-275, for interpolation inequalities between a function
  and its gradient with power weights `|x|^a`.
  <https://www.numdam.org/item/CM_1984__53_3_259_0/>
* E. B. Fabes, C. E. Kenig and R. P. Serapioni, "The local regularity of solutions of degenerate
  elliptic equations", *Comm. Partial Differential Equations* 7 (1982), no. 1, 77-116.
  <https://doi.org/10.1080/03605308208820218>
* A. Kufner, *Weighted Sobolev Spaces*, Teubner-Texte zur Mathematik 31, Teubner, Leipzig, 1981.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace
namespace Weighted

variable {n k : ℕ}

private def derivativeWordDegree (cost : Fin n → ℕ) (α : List (Fin n)) : ℕ :=
  (α.map cost).sum

private theorem derivativeWordDegree_mono_cost {cost cost' : Fin n → ℕ}
    (hcost : ∀ i, cost i ≤ cost' i) (α : List (Fin n)) :
    derivativeWordDegree cost α ≤ derivativeWordDegree cost' α := by
  induction α with
  | nil => rfl
  | cons i α ih =>
      exact Nat.add_le_add (hcost i) ih

/-- Anisotropic degree of a symmetric Sobolev derivative coordinate.

The definition uses the underlying multiset directly, so it is independent of any chosen
ordered representative. -/
def derivativeIndexDegree (cost : Fin n → ℕ)
    (a : GraphSpace.DerivIndex n k) : ℕ :=
  (a.2.1.map cost).sum

private theorem derivativeIndexDegree_eq_word (cost : Fin n → ℕ)
    (a : GraphSpace.DerivIndex n k) :
    derivativeIndexDegree cost a = derivativeWordDegree cost a.toList := by
  simp [derivativeIndexDegree, derivativeWordDegree, GraphSpace.DerivIndex.toList]

/-- Increasing every coordinate cost can only increase the canonical anisotropic degree. -/
theorem derivativeIndexDegree_mono_cost {cost cost' : Fin n → ℕ}
    (hcost : ∀ i, cost i ≤ cost' i)
    (a : GraphSpace.DerivIndex n k) :
    derivativeIndexDegree cost a ≤ derivativeIndexDegree cost' a := by
  rw [derivativeIndexDegree_eq_word, derivativeIndexDegree_eq_word]
  exact derivativeWordDegree_mono_cost hcost a.toList

/-- Unit coordinate costs recover the ordinary total derivative order. -/
@[simp] theorem derivativeIndexDegree_one (a : GraphSpace.DerivIndex n k) :
    derivativeIndexDegree (fun _ ↦ 1) a = a.1.1 := by
  simp [derivativeIndexDegree]

/-- The finite family of Sobolev coordinates whose anisotropic degree is at most `budget`. -/
def anisotropicDerivativeFamily (cost : Fin n → ℕ) (budget : ℕ) :
    Finset (GraphSpace.DerivIndex n k) := by
  classical
  exact Finset.univ.filter (fun a ↦ derivativeIndexDegree cost a ≤ budget)

/-- A derivative index belongs to the anisotropic family exactly when its weighted degree
does not exceed the budget. -/
@[simp] theorem mem_anisotropicDerivativeFamily
    (cost : Fin n → ℕ) (budget : ℕ) (a : GraphSpace.DerivIndex n k) :
    a ∈ anisotropicDerivativeFamily cost budget ↔
      derivativeIndexDegree cost a ≤ budget := by
  classical
  simp [anisotropicDerivativeFamily]

/-- Increasing the admissible budget enlarges the finite derivative family. -/
theorem anisotropicDerivativeFamily_mono_budget (cost : Fin n → ℕ)
    {budget budget' : ℕ} (hbudget : budget ≤ budget') :
    anisotropicDerivativeFamily (k := k) cost budget ⊆
      anisotropicDerivativeFamily cost budget' := by
  intro a ha
  rw [mem_anisotropicDerivativeFamily] at ha ⊢
  exact ha.trans hbudget

/-- Increasing coordinate costs shrinks the derivative family at fixed budget. -/
theorem anisotropicDerivativeFamily_antitone_cost
    {cost cost' : Fin n → ℕ} (hcost : ∀ i, cost i ≤ cost' i)
    (budget : ℕ) :
    anisotropicDerivativeFamily (k := k) cost' budget ⊆
      anisotropicDerivativeFamily cost budget := by
  intro a ha
  rw [mem_anisotropicDerivativeFamily] at ha ⊢
  exact (derivativeIndexDegree_mono_cost hcost a).trans ha

/-- Unit coordinate costs select exactly the ordinary derivative coordinates within the
budget. -/
theorem mem_anisotropicDerivativeFamily_one_iff
    (budget : ℕ) (a : GraphSpace.DerivIndex n k) :
    a ∈ anisotropicDerivativeFamily (fun _ ↦ 1) budget ↔ a.1.1 ≤ budget := by
  simp

variable {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- Density-weighted `L^p` control for a finite family of anisotropic Sobolev coordinates. -/
def AnisotropicCoordinatesMemLpWithDensity
    (density : ℝ^n → ℝ≥0∞) (cost : Fin n → ℕ) (budget : ℕ)
    (U : W^{k,p}(Ω)) : Prop :=
  ∀ a ∈ anisotropicDerivativeFamily cost budget,
    CoordinateMemLpWithDensity density U a

/-- Control through a larger anisotropic budget implies control through every smaller budget. -/
theorem AnisotropicCoordinatesMemLpWithDensity.mono_budget
    {density : ℝ^n → ℝ≥0∞} {cost : Fin n → ℕ} {budget budget' : ℕ}
    {U : W^{k,p}(Ω)}
    (hU : AnisotropicCoordinatesMemLpWithDensity density cost budget' U)
    (hbudget : budget ≤ budget') :
    AnisotropicCoordinatesMemLpWithDensity density cost budget U := by
  intro a ha
  exact hU a (anisotropicDerivativeFamily_mono_budget cost hbudget ha)

/-- Control for cheaper coordinate costs implies control after increasing those costs. -/
theorem AnisotropicCoordinatesMemLpWithDensity.mono_cost
    {density : ℝ^n → ℝ≥0∞} {cost cost' : Fin n → ℕ} {budget : ℕ}
    {U : W^{k,p}(Ω)}
    (hU : AnisotropicCoordinatesMemLpWithDensity density cost budget U)
    (hcost : ∀ i, cost i ≤ cost' i) :
    AnisotropicCoordinatesMemLpWithDensity density cost' budget U := by
  intro a ha
  exact hU a (anisotropicDerivativeFamily_antitone_cost hcost budget ha)

/-- Anisotropic coordinate control is monotone under domination of measure densities. -/
theorem AnisotropicCoordinatesMemLpWithDensity.mono_density
    {w v : ℝ^n → ℝ≥0∞} {cost : Fin n → ℕ} {budget : ℕ}
    {U : W^{k,p}(Ω)}
    (hU : AnisotropicCoordinatesMemLpWithDensity v cost budget U)
    (hwv : w ≤ᵐ[domainMeasure n Ω] v) :
    AnisotropicCoordinatesMemLpWithDensity w cost budget U := by
  intro a ha
  exact CoordinateMemLpWithDensity.mono_density (hU a ha) hwv

end Weighted
end SobolevSpace
