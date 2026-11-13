/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Translation bounds at every finite Sobolev exponent

The sharp coordinate difference-quotient bound controls translation along
each coordinate line. Translation is an isometric additive action, so a
finite telescoping argument controls an arbitrary displacement.

Combining this estimate with the constructed Sobolev zero extension gives
uniform translation control on bounded subsets of `W^{1,p}_0(Ω)`. The domain
need only be measurable, and dimension one is included.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.Rellich

open Function MeasureTheory Set
open DifferenceQuotient ZeroTrace
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translating successively bounds the defect by the sum of the two
individual defects, because the outer translation is an isometry. -/
private theorem norm_translateLp_add_sub_le (a b : ℝ^n)
    (u : DerivLp n p Set.univ) :
    ‖translateLp p (a + b) u - u‖ ≤
      ‖translateLp p a u - u‖ + ‖translateLp p b u - u‖ := by
  calc
    ‖translateLp p (a + b) u - u‖ =
        ‖translateLp p a (translateLp p b u - u) + (translateLp p a u - u)‖ := by
      rw [map_sub, translateLp_add]
      congr 1
      abel
    _ ≤ ‖translateLp p a (translateLp p b u - u)‖ +
        ‖translateLp p a u - u‖ := norm_add_le _ _
    _ = ‖translateLp p a u - u‖ + ‖translateLp p b u - u‖ := by
      rw [norm_translateLp, add_comm]

/-- The coordinate translation estimate includes the zero displacement.
For a nonzero displacement it is the sharp difference-quotient estimate
multiplied by the step length. -/
theorem norm_translateLp_coordinate_base_sub_le (hp : p ≠ ∞)
    (i : Fin n) (t : ℝ) (U : W^{1,p}(ℝ^n)) :
    ‖translateLp p (coordinateStep i t) (wkpBaseCoordinateCLM U) -
        wkpBaseCoordinateCLM U‖ ≤
      |t| * ‖wkpCoordinateCLM (singleDerivIndex n i) U‖ := by
  by_cases ht : t = 0
  · subst t
    simp [coordinateStep]
  · have hbound := norm_differenceQuotientLp_base_le_deriv_of_ne_top
      p hp i ht U
    have hid :
        translateLp p (coordinateStep i t) (wkpBaseCoordinateCLM U) -
            wkpBaseCoordinateCLM U =
          t • differenceQuotientLp p i t (wkpBaseCoordinateCLM U) := by
      rw [differenceQuotientLp_apply, smul_smul, mul_inv_cancel₀ ht, one_smul]
    rw [hid, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hbound (abs_nonneg t)

/-- Every whole-space first-order Sobolev function has a linear translation
modulus in its own finite `Lp` norm. The constant `n` comes from summing
coordinate estimates; no dimension restriction is required. -/
theorem norm_translateLp_base_sub_le (hp : p ≠ ∞)
    (h : ℝ^n) (U : W^{1,p}(ℝ^n)) :
    ‖translateLp p h (wkpBaseCoordinateCLM U) - wkpBaseCoordinateCLM U‖ ≤
      (n : ℝ) * ‖h‖ * ‖U‖ := by
  classical
  have hfinite (s : Finset (Fin n)) :
      ‖translateLp p (∑ i ∈ s, coordinateStep i (h i)) (wkpBaseCoordinateCLM U) -
          wkpBaseCoordinateCLM U‖ ≤
        ∑ i ∈ s, |h i| * ‖wkpCoordinateCLM (singleDerivIndex n i) U‖ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        exact (norm_translateLp_add_sub_le _ _ _).trans
          (add_le_add (norm_translateLp_coordinate_base_sub_le hp i (h i) U) ih)
  have hsum : ∑ i : Fin n, coordinateStep i (h i) = h := by
    ext j
    simp [coordinateStep, Pi.single_apply]
  calc
    ‖translateLp p h (wkpBaseCoordinateCLM U) - wkpBaseCoordinateCLM U‖ ≤
        ∑ i : Fin n, |h i| * ‖wkpCoordinateCLM (singleDerivIndex n i) U‖ := by
      simpa only [hsum] using hfinite Finset.univ
    _ ≤ ∑ _i : Fin n, ‖h‖ * ‖U‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le h i)
        (wkpCoordinateCLM_norm_le (singleDerivIndex n i) U)
        (norm_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * ‖h‖ * ‖U‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_assoc]

/-- Zero extension of a supported-core Sobolev function satisfies the same
translation estimate. Its global weak derivatives and norm bound come
from the zero-extension construction. -/
theorem norm_translateLp_zeroExtendWkp0_base_sub_le
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    (h : ℝ^n) (u : W₀^{1,p}(Ω)) :
    ‖translateLp p h (wkpBaseCoordinateCLM (zeroExtendWkp0 hΩ u)) -
        wkpBaseCoordinateCLM (zeroExtendWkp0 hΩ u)‖ ≤
      (n : ℝ) * ‖h‖ * ‖u‖ := by
  simpa only [norm_zeroExtendWkp0] using
    norm_translateLp_base_sub_le hp h (zeroExtendWkp0 hΩ u)

end SobolevSpace.GraphSpace.Rellich
