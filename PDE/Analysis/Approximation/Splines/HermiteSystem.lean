/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteC2
public import PDE.Analysis.LinearAlgebra.DiagonalDominance
import CAS.ExactTactic

/-!
# Exact Hermite slopes with a natural left endpoint and prescribed final slope

The unknowns include every nodal slope. The first row is `2 m₀ + m₁`, the
interior rows express equality of second jets, and the final row prescribes
the final slope. Positive panel widths imply strict row diagonal dominance.

On an exact uniform mesh, prescribing the three-point backward difference as the final slope
gives the cubic spline of Chen, Hou and Huang (Section 4.1, step (2)) restricted to `[0, L]`.
The nonuniform construction allows any prescribed final slope. All
constructions use exact real arithmetic.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.1, step (2). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

noncomputable section

namespace CAS.Splines.HermiteSlopeSystem

variable {n : ℕ}

/-- The exact length of a panel in the supplied strict mesh. -/
def width (mesh : StrictKnotMesh (n + 2)) (i : Fin (n + 2)) : ℝ :=
  mesh.panelRight i - mesh.panelLeft i

/-- Every panel of a strict mesh has positive length. -/
theorem width_pos (mesh : StrictKnotMesh (n + 2)) (i : Fin (n + 2)) :
    0 < width mesh i :=
  sub_pos.mpr (mesh.panelLeft_lt_panelRight i)

/-- The slope matrix with the final prescribed slope retained as an unknown. -/
def matrix (mesh : StrictKnotMesh (n + 2)) : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ :=
  Fin.cases (Pi.single 0 2 + Pi.single 1 1)
    (Fin.lastCases (Pi.single (Fin.last (n + 2)) 1) fun i : Fin (n + 1) ↦
      Pi.single i.castSucc.castSucc (width mesh i.succ) +
        Pi.single i.castSucc.succ (2 * (width mesh i.castSucc + width mesh i.succ)) +
        Pi.single i.succ.succ (width mesh i.castSucc))

/-- The first row encodes zero curvature at the left endpoint. -/
@[simp] theorem matrix_zero (mesh : StrictKnotMesh (n + 2)) :
    matrix mesh 0 = Pi.single 0 2 + Pi.single 1 1 := by
  simp [matrix]

/-- An interior row uses the two exact adjacent panel lengths. -/
@[simp] theorem matrix_interior (mesh : StrictKnotMesh (n + 2)) (i : Fin (n + 1)) :
    matrix mesh i.castSucc.succ =
      Pi.single i.castSucc.castSucc (width mesh i.succ) +
        Pi.single i.castSucc.succ (2 * (width mesh i.castSucc + width mesh i.succ)) +
        Pi.single i.succ.succ (width mesh i.castSucc) := by
  simp [matrix]

/-- The final row prescribes the last slope without imposing a curvature condition. -/
@[simp] theorem matrix_last (mesh : StrictKnotMesh (n + 2)) :
    matrix mesh (Fin.last (n + 2)) = Pi.single (Fin.last (n + 2)) 1 := by
  change matrix mesh (Fin.last (n + 1)).succ = _
  simp only [matrix, Fin.cases_succ, Fin.lastCases_last]

/-- A row supported at three columns is dominant when its positive diagonal
exceeds the nonnegative neighboring coefficients. -/
theorem three_entry_row_dominant
    {ι : Type*} [Fintype ι] [DecidableEq ι] (previous center next : ι)
    (hprevious : previous ≠ center) (hnext : next ≠ center)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hdiag : a + c < b) :
    let row : ι → ℝ := Pi.single previous a + Pi.single center b + Pi.single next c
    ∑ j ∈ Finset.univ.erase center, ‖row j‖ < ‖row center‖ := by
  dsimp only
  have hnonneg (j : ι) :
      0 ≤ (Pi.single previous a + Pi.single center b + Pi.single next c : ι → ℝ) j := by
    simp only [Pi.add_apply, Pi.single_apply]
    positivity
  simp_rw [Real.norm_of_nonneg (hnonneg _)]
  simpa [Pi.add_apply, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq',
    hprevious, hnext, Ne.symm hprevious, Ne.symm hnext] using hdiag

/-- Positive widths prove dominance of every row, including both boundary rows. -/
theorem strict_row_dominance (mesh : StrictKnotMesh (n + 2)) :
    ∀ i, ∑ j ∈ Finset.univ.erase i, ‖matrix mesh i j‖ < ‖matrix mesh i i‖ := by
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · rw [matrix_zero]
    have hnonneg (j : Fin (n + 3)) :
        0 ≤ (Pi.single 0 2 + Pi.single 1 1 : Fin (n + 3) → ℝ) j := by
      simp only [Pi.add_apply, Pi.single_apply]
      positivity
    simp_rw [Real.norm_of_nonneg (hnonneg _)]
    simp [Pi.add_apply, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq']
  · refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · rw [Fin.succ_last, matrix_last]
      simp [Pi.single_apply, apply_ite, Finset.sum_ite_eq']
    · rw [matrix_interior]
      apply three_entry_row_dominant
      · intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      · intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      · exact (width_pos mesh j.succ).le
      · exact mul_nonneg (by norm_num)
          (add_nonneg (width_pos mesh j.castSucc).le (width_pos mesh j.succ).le)
      · exact (width_pos mesh j.castSucc).le
      · rw [add_comm (width mesh j.succ)]
        exact lt_two_mul_self (add_pos (width_pos mesh j.castSucc) (width_pos mesh j.succ))

/-- The value data determine the left and interior right-hand sides;
the prescribed final derivative supplies the last entry. -/
def rightHandSide (mesh : StrictKnotMesh (n + 2)) (value : Fin (n + 3) → ℝ)
    (finalSlope : ℝ) : Fin (n + 3) → ℝ :=
  Fin.cases (3 * (value 1 - value 0) / width mesh 0)
    (Fin.lastCases finalSlope fun i : Fin (n + 1) ↦
      3 * (width mesh i.succ *
          (value i.castSucc.succ - value i.castSucc.castSucc) / width mesh i.castSucc +
        width mesh i.castSucc *
          (value i.succ.succ - value i.castSucc.succ) / width mesh i.succ))

/-- The first right-hand side is the first secant slope multiplied by three. -/
@[simp] theorem rightHandSide_zero (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    rightHandSide mesh value finalSlope 0 = 3 * (value 1 - value 0) / width mesh 0 := by
  simp [rightHandSide]

/-- An interior right-hand side combines the adjacent secant slopes. -/
@[simp] theorem rightHandSide_interior (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) (i : Fin (n + 1)) :
    rightHandSide mesh value finalSlope i.castSucc.succ =
      3 * (width mesh i.succ *
          (value i.castSucc.succ - value i.castSucc.castSucc) / width mesh i.castSucc +
        width mesh i.castSucc *
          (value i.succ.succ - value i.castSucc.succ) / width mesh i.succ) := by
  simp [rightHandSide]

/-- The last right-hand side is exactly the prescribed final slope. -/
@[simp] theorem rightHandSide_last (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    rightHandSide mesh value finalSlope (Fin.last (n + 2)) = finalSlope := by
  change rightHandSide mesh value finalSlope (Fin.last (n + 1)).succ = _
  simp only [rightHandSide, Fin.cases_succ, Fin.lastCases_last]

/-- Multiplication by the first row gives the natural left boundary equation. -/
@[simp] theorem mulVec_zero (mesh : StrictKnotMesh (n + 2)) (slope : Fin (n + 3) → ℝ) :
    (matrix mesh).mulVec slope 0 = 2 * slope 0 + slope 1 := by
  simp only [Matrix.mulVec, matrix_zero, add_dotProduct, single_dotProduct, one_mul]

/-- Multiplication by an interior row gives the exact second-jet matching coefficients. -/
@[simp] theorem mulVec_interior (mesh : StrictKnotMesh (n + 2))
    (slope : Fin (n + 3) → ℝ) (i : Fin (n + 1)) :
    (matrix mesh).mulVec slope i.castSucc.succ =
      width mesh i.succ * slope i.castSucc.castSucc +
        2 * (width mesh i.castSucc + width mesh i.succ) * slope i.castSucc.succ +
        width mesh i.castSucc * slope i.succ.succ := by
  simp only [Matrix.mulVec, matrix_interior, add_dotProduct, single_dotProduct]

/-- Multiplication by the last row extracts the final slope. -/
@[simp] theorem mulVec_last (mesh : StrictKnotMesh (n + 2)) (slope : Fin (n + 3) → ℝ) :
    (matrix mesh).mulVec slope (Fin.last (n + 2)) = slope (Fin.last (n + 2)) := by
  simp only [Matrix.mulVec, matrix_last, single_dotProduct, one_mul]

/-- Every right-hand side has a unique exact solution, with dominance proved
from the mesh rather than supplied as an additional hypothesis. -/
theorem existsUnique_solution (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    ∃! slope, (matrix mesh).mulVec slope = rightHandSide mesh value finalSlope :=
  PDE.Analysis.existsUnique_mulVec_of_strict_row_dominance (matrix mesh)
    (strict_row_dominance mesh) (rightHandSide mesh value finalSlope)

/-- The natural left equation, all interior C² equations, and the prescribed
final derivative, expressed independently of the matrix representation. -/
structure Conditions (mesh : StrictKnotMesh (n + 2)) (value : Fin (n + 3) → ℝ)
    (finalSlope : ℝ) (slope : Fin (n + 3) → ℝ) : Prop where
  /-- Zero left curvature. -/
  left_boundary : 2 * slope 0 + slope 1 = 3 * (value 1 - value 0) / width mesh 0
  /-- Equality of second jets at each interior knot. -/
  interior : (HermiteData.mk value slope).C2SlopeEquations mesh
  /-- The final slope is prescribed directly. -/
  right_boundary : slope (Fin.last (n + 2)) = finalSlope

/-- The concrete matrix encodes exactly the endpoint and interior conditions. -/
theorem solution_iff (mesh : StrictKnotMesh (n + 2))
    (value slope : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    (matrix mesh).mulVec slope = rightHandSide mesh value finalSlope ↔
      Conditions mesh value finalSlope slope := by
  constructor
  · intro heq
    refine ⟨?_, ?_, ?_⟩
    · simpa only [mulVec_zero, rightHandSide_zero] using congrFun heq 0
    · intro i hi
      let k : Fin (n + 1) := ⟨i.val, by omega⟩
      have hk : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = StrictKnotMesh.rightNeighbor i hi := Fin.ext rfl
      have hrow := congrFun heq k.castSucc.succ
      rw [mulVec_interior, rightHandSide_interior] at hrow
      simpa only [hk, hj, width] using hrow
    · simpa only [mulVec_last, rightHandSide_last] using congrFun heq (Fin.last (n + 2))
  · intro h
    funext i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simpa only [mulVec_zero, rightHandSide_zero] using h.left_boundary
    · refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · simpa only [Fin.succ_last, mulVec_last, rightHandSide_last] using h.right_boundary
      · have hj : j.castSucc.val + 1 < n + 2 := Nat.succ_lt_succ j.isLt
        have hnext : StrictKnotMesh.rightNeighbor j.castSucc hj = j.succ := Fin.ext rfl
        simpa only [mulVec_interior, rightHandSide_interior, width, hnext] using
          h.interior j.castSucc hj

/-- For arbitrary nodal values and final derivative there are unique exact
slopes satisfying the natural left and C² interior equations. -/
theorem existsUnique_conditions (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    ∃! slope, Conditions mesh value finalSlope slope := by
  obtain ⟨slope, hslope, hunique⟩ := existsUnique_solution mesh value finalSlope
  refine ⟨slope, (solution_iff mesh value slope finalSlope).mp hslope, ?_⟩
  intro other hother
  exact hunique other ((solution_iff mesh value other finalSlope).mpr hother)

/-- The slope equations are equivalent to the second-jet conditions
on the interpolating Hermite panels, together with the prescribed final slope. -/
theorem conditions_iff_jets (mesh : StrictKnotMesh (n + 2))
    (value slope : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    Conditions mesh value finalSlope slope ↔
      polynomialJet 2 (((HermiteData.mk value slope).polynomialData mesh).piece 0)
          (mesh.panelLeft 0) = 0 ∧
        ((HermiteData.mk value slope).polynomialData mesh).MatchesJetsThrough 2 ∧
        slope (Fin.last (n + 2)) = finalSlope := by
  constructor
  · intro h
    exact ⟨(HermiteData.mk value slope).second_origin_eq_zero mesh h.left_boundary,
      ((HermiteData.mk value slope).toC2Spline mesh h.interior).matchesJets, h.right_boundary⟩
  · rintro ⟨hleft, hmatches, hright⟩
    refine ⟨?_, ?_, hright⟩
    · exact (hermitePolynomial_second_left_eq_zero_iff _ _ _ _ _ _
        (width_pos mesh 0).ne').mp hleft
    · intro i hi
      let j := StrictKnotMesh.rightNeighbor i hi
      have hnode : i.succ = j.castSucc := Fin.ext rfl
      have hboundary : mesh.panelLeft i + width mesh i = mesh.panelRight i := by
        unfold width
        cas
      have hj : mesh.panelLeft j = mesh.panelRight i :=
        (mesh.panelRight_eq_panelLeft_rightNeighbor i hi).symm
      apply (hermitePolynomial_second_match_iff (mesh.panelLeft i)
        (width mesh i) (width mesh j) (value i.castSucc) (value i.succ) (value j.succ)
        (slope i.castSucc) (slope i.succ) (slope j.succ)
        (width_pos mesh i).ne' (width_pos mesh j).ne').mp
      rw [hboundary]
      have hmatch := hmatches i hi 2 le_rfl
      change polynomialJet 2
        (((HermiteData.mk value slope).polynomialData mesh).piece i) (mesh.panelRight i) =
        polynomialJet 2 (((HermiteData.mk value slope).polynomialData mesh).piece j)
          (mesh.panelRight i) at hmatch
      simpa only [HermiteData.polynomialData, width, hnode, hj] using hmatch

/-- Unique exact slopes exist for the C² matching and endpoint conditions. -/
theorem existsUnique_c2_slopes (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    ∃! slope : Fin (n + 3) → ℝ,
      polynomialJet 2 (((HermiteData.mk value slope).polynomialData mesh).piece 0)
          (mesh.panelLeft 0) = 0 ∧
        ((HermiteData.mk value slope).polynomialData mesh).MatchesJetsThrough 2 ∧
        slope (Fin.last (n + 2)) = finalSlope := by
  obtain ⟨slope, hslope, hunique⟩ := existsUnique_conditions mesh value finalSlope
  refine ⟨slope, (conditions_iff_jets mesh value slope finalSlope).mp hslope, ?_⟩
  intro other hother
  exact hunique other ((conditions_iff_jets mesh value other finalSlope).mpr hother)

/-- The unique exact slope vector; its equations are theorems, not assumptions
about the output of a numerical solver. -/
def slopes (mesh : StrictKnotMesh (n + 2)) (value : Fin (n + 3) → ℝ)
    (finalSlope : ℝ) : Fin (n + 3) → ℝ :=
  (existsUnique_conditions mesh value finalSlope).exists.choose

/-- The exact construction satisfies every endpoint and interior equation. -/
theorem slopes_conditions (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    Conditions mesh value finalSlope (slopes mesh value finalSlope) :=
  (existsUnique_conditions mesh value finalSlope).exists.choose_spec

/-- Nodal values paired with the uniquely determined exact slopes. -/
def data (mesh : StrictKnotMesh (n + 2)) (value : Fin (n + 3) → ℝ)
    (finalSlope : ℝ) : HermiteData (n + 2) :=
  ⟨value, slopes mesh value finalSlope⟩

/-- The exact matrix solution reconstructs a cubic spline with matching jets
through order two at every interior knot. -/
def spline (mesh : StrictKnotMesh (n + 2)) (value : Fin (n + 3) → ℝ)
    (finalSlope : ℝ) : PolynomialSpline mesh 3 2 :=
  (data mesh value finalSlope).toC2Spline mesh (slopes_conditions mesh value finalSlope).interior

/-- The reconstructed first panel has zero second derivative at the first knot. -/
theorem second_left_eq_zero (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    polynomialJet 2 ((spline mesh value finalSlope).piece 0) (mesh.panelLeft 0) = 0 :=
  (data mesh value finalSlope).second_origin_eq_zero mesh
    (slopes_conditions mesh value finalSlope).left_boundary

/-- The reconstructed last panel has the prescribed first derivative at its right endpoint. -/
theorem first_right_eq_finalSlope (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    polynomialJet 1 ((spline mesh value finalSlope).piece (Fin.last (n + 1)))
      (mesh.panelRight (Fin.last (n + 1))) = finalSlope := by
  change polynomialJet 1
    (((data mesh value finalSlope).polynomialData mesh).piece (Fin.last (n + 1))) _ = _
  rw [HermiteData.slope_right]
  exact (slopes_conditions mesh value finalSlope).right_boundary

/-- The three-point backward difference `(3 vₙ - 4 vₙ₋₁ + vₙ₋₂) / (2h)` of the last three
values, which exist because the mesh has at least two panels. -/
def backwardDifference (value : Fin (n + 3) → ℝ) (h : ℝ) : ℝ :=
  (3 * value (Fin.last (n + 2)) - 4 * value (Fin.last (n + 1)).castSucc +
    value (Fin.last n).castSucc.castSucc) / (2 * h)

/-- On a uniform mesh of step `h`, exactly one slope vector satisfies the natural left row
`2 m₀ + m₁ = 3 (v₁ - v₀) / h`, the `1, 4, 1` interior rows and the backward difference as
final slope. -/
theorem existsUnique_uniform_source_slopes (mesh : StrictKnotMesh (n + 2))
    (value : Fin (n + 3) → ℝ) (h : ℝ) (hmesh : ∀ i, width mesh i = h) :
    ∃! slope : Fin (n + 3) → ℝ,
      2 * slope 0 + slope 1 = 3 * (value 1 - value 0) / h ∧
        (HermiteData.mk value slope).UniformSlopeEquations h ∧
        slope (Fin.last (n + 2)) = backwardDifference value h := by
  have hiff (slope : Fin (n + 3) → ℝ) :
      Conditions mesh value (backwardDifference value h) slope ↔
        2 * slope 0 + slope 1 = 3 * (value 1 - value 0) / h ∧
          (HermiteData.mk value slope).UniformSlopeEquations h ∧
          slope (Fin.last (n + 2)) = backwardDifference value h := by
    constructor
    · intro hc
      refine ⟨?_, ?_, hc.right_boundary⟩
      · simpa only [hmesh 0] using hc.left_boundary
      · exact ((HermiteData.mk value slope).c2SlopeEquations_iff_uniform mesh h hmesh).mp
          hc.interior
    · rintro ⟨hleft, hinterior, hright⟩
      refine ⟨?_, ?_, hright⟩
      · simpa only [hmesh 0] using hleft
      · exact ((HermiteData.mk value slope).c2SlopeEquations_iff_uniform mesh h hmesh).mpr
          hinterior
  obtain ⟨slope, hslope, hunique⟩ :=
    existsUnique_conditions mesh value (backwardDifference value h)
  exact ⟨slope, (hiff slope).mp hslope, fun other hother ↦
    hunique other ((hiff other).mpr hother)⟩

end CAS.Splines.HermiteSlopeSystem
