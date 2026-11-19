/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.LocalizedTest
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.TangentialFields
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Step-independent bounds for the localized tangential test

The norm of the signed test is bounded by the localized gradient quotient and the
original `H¹` norm. Moving one cutoff to the flux gives the corresponding bound for
the cutoff error. All coefficients below depend on the fixed cutoff, before the
solution and difference step are chosen.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The lower-order cutoff constant in the norm of the localized signed test. -/
def localizedTangentialLowerConstant (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ ^ 2 +
    2 * ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ *
      ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖

/-- Each localized scalar quotient is bounded by the Euclidean quotient norm. -/
theorem norm_weighted_tangential_coordinate_le
    (η : DerivLp n ∞ (HalfSpace.upper n))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (P : Fin n → DerivLp n 2 (HalfSpace.upper n)) (i : Fin n) :
    ‖η • tangentialDifferenceQuotientLp 2 k hk h (P i)‖ ≤
      ‖η • tangentialVectorDifference k hk h P‖ := by
  simpa only [Lp.euclideanTuple_lpSMul, tangentialVectorDifference] using
    Lp.norm_coordinate_le_norm_euclideanTuple
      (fun j ↦ η • tangentialDifferenceQuotientLp 2 k hk h (P j)) i

/-- The localized signed test has a bound with no reciprocal step. -/
theorem norm_baseCoord_localizedTangentialTest_le
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(HalfSpace.upper n)) :
    ‖baseCoordCLM (localizedTangentialTest η k hk h u)‖ ≤
      n * ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ *
        ‖testFunctionLpTop (Ω := HalfSpace.upper n) η •
          tangentialVectorDifference k hk h (fun i ↦ derivCoordCLM i u)‖ +
      localizedTangentialLowerConstant η * ‖u‖ := by
  let a := testFunctionLpTop (Ω := HalfSpace.upper n) η
  let d := fun i ↦ partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i
  let b := tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u)
  let X := ‖a • tangentialVectorDifference k hk h (fun i ↦ derivCoordCLM i u)‖
  let w := localizedTangentialForward η k hk h u
  have hb : ‖b‖ ≤ ‖u‖ := by
    simpa only [b, baseCoord_tangentialDifferenceQuotientH10] using
      norm_baseCoord_tangentialDifferenceQuotientH10_le k hk hh u
  have hbase : ‖baseCoordCLM w‖ ≤ ‖a‖ ^ 2 * ‖u‖ := by
    rw [show baseCoordCLM w =
      testFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) • b from
        baseCoord_localizedTangentialForward η k hk h u]
    calc
      _ ≤ ‖a‖ * ‖a • b‖ := norm_squaredCutoff_smul_le η b
      _ ≤ ‖a‖ * (‖a‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left
          ((Lp.norm_smul_le a b).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _)))
          (norm_nonneg _)
      _ = _ := by ring
  have hderiv (i : Fin n) :
      ‖derivCoordCLM i w‖ ≤ ‖a‖ * X + 2 * ‖a‖ * ‖d i‖ * ‖u‖ := by
    rw [show derivCoordCLM i w = _ from derivCoord_localizedTangentialForward η k hk h u i]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_squaredCutoff_smul_le η _).trans
        (mul_le_mul_of_nonneg_left
          (norm_weighted_tangential_coordinate_le a k hk h (fun j ↦ derivCoordCLM j u) i)
          (norm_nonneg _))
    · exact (norm_partialSquaredCutoff_smul_le η i b).trans
        (mul_le_mul_of_nonneg_left hb (by positivity))
  have hw : ‖w‖ ≤ ‖a‖ ^ 2 * ‖u‖ +
      ∑ i, (‖a‖ * X + 2 * ‖a‖ * ‖d i‖ * ‖u‖) :=
    (ambient_norm_le_base_add_sum_deriv
      ((w : H¹(HalfSpace.upper n)) : WkpAmbientOn n 1 2 (HalfSpace.upper n))).trans
      (add_le_add hbase (Finset.sum_le_sum fun i _ ↦ hderiv i))
  have htest : ‖baseCoordCLM (localizedTangentialTest η k hk h u)‖ ≤ ‖w‖ := by
    simpa only [localizedTangentialTest, map_neg, norm_neg, w] using
      norm_baseCoord_tangentialDifferenceQuotientH10_le k hk (neg_ne_zero.mpr hh) w
  apply htest.trans (hw.trans_eq ?_)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  dsimp only [localizedTangentialLowerConstant, a, d, X]
  ring

/-- The complete derivative-of-cutoff pairing is bounded by the localized flux norm.
This retains the cutoff before estimating the nonlinear flux quotient. -/
theorem abs_localizedTangential_cutoff_pairing_le
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(HalfSpace.upper n))
    (Q : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    |∑ i, ⟪tangentialDifferenceQuotientLp 2 k hk h (Q i),
      partialTestFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) i •
        tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u)⟫| ≤
      2 * ‖testFunctionLpTop (Ω := HalfSpace.upper n) η •
        tangentialVectorDifference k hk h Q‖ *
        (∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖) * ‖u‖ := by
  have hb : ‖tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u)‖ ≤ ‖u‖ := by
    simpa only [baseCoord_tangentialDifferenceQuotientH10] using
      norm_baseCoord_tangentialDifferenceQuotientH10_le k hk hh u
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, 2 * ‖testFunctionLpTop (Ω := HalfSpace.upper n) η •
        tangentialVectorDifference k hk h Q‖ *
        ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖ * ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_inner_partialSquaredCutoff_le η i _ _).trans
      gcongr
      exact norm_weighted_tangential_coordinate_le _ k hk h Q i
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

end PDE.Elliptic.Regularity.Quasilinear
