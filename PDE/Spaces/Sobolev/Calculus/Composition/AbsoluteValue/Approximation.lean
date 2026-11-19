/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.PositivePart.Continuity
import PDE.Analysis.MeasureTheory.DominatedLp
import PDE.Spaces.Sobolev.GraphSpace.Topology.Convergence

/-!
# Strong approximation of Sobolev absolute values

The smooth zero-preserving absolute values converge in the full finite-exponent Sobolev
norm. The argument uses the weak chain rule and dominated convergence in each row.
It is used in the zero-trace closure argument, and it lets
inequalities on nonnegative smooth tests pass to nonnegative Sobolev tests.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open Filter Function MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Smooth absolute values converge in the Sobolev norm. Each derivative
is dominated by the corresponding original derivative, including at zeros. -/
theorem tendsto_smoothAbsComposition
    (hp : p ≠ ∞) (U : W^{1,p}(ℝ^n))
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j ↦ smoothComposition
      ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
      (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
      (PDE.Analysis.Calculus.smoothAbs_zero (ε j) (hε j).le)
      (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U)
      atTop (𝓝 (absoluteValue U)) := by
  let V : ℕ → W^{1,p}(ℝ^n) := fun j ↦ smoothComposition
    ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
    (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
    (PDE.Analysis.Calculus.smoothAbs_zero (ε j) (hε j).le)
    (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U
  apply tendsto_wkp_of_coordinate_eLpNorm
  intro a
  apply tendsto_Lp_of_tendsto_ae_of_ae_norm_le Fact.out hp
    (fun j ↦ (Lp.memLp (wkpCoordinateCLM a (V j))).aestronglyMeasurable)
    (Lp.memLp (wkpCoordinateCLM a (absoluteValue U)))
    (Lp.memLp (wkpCoordinateCLM a U))
  · intro j
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
    · subst a
      have hv := smoothComposition_base_ae
        ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
        (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
        (PDE.Analysis.Calculus.smoothAbs_zero (ε j) (hε j).le)
        (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U
      filter_upwards [hv] with x hx
      simp only [wkpCoordinateCLM_apply, V]
      rw [hx, Real.norm_eq_abs,
        abs_of_nonneg (PDE.Analysis.Calculus.smoothAbs_nonneg (hε j).le _),
        Real.norm_eq_abs]
      exact PDE.Analysis.Calculus.smoothAbs_le_abs (hε j).le _
    · subst a
      have hv := smoothComposition_derivative_ae
        ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
        (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
        (PDE.Analysis.Calculus.smoothAbs_zero (ε j) (hε j).le)
        (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U i
      filter_upwards [hv] with x hx
      simp only [wkpCoordinateCLM_apply, V]
      rw [hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j) _)
  · rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
    · subst a
      have hv (j : ℕ) := smoothComposition_base_ae
        ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
        (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
        (PDE.Analysis.Calculus.smoothAbs_zero (ε j) (hε j).le)
        (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U
      filter_upwards [ae_all_iff.2 hv, absoluteValue_base_ae U] with x hx hy
      simp only [wkpCoordinateCLM_apply, V]
      simp_rw [hx, hy]
      exact PDE.Analysis.Calculus.tendsto_smoothAbs_of_tendsto_zero
        (Eventually.of_forall fun j ↦ (hε j).le) hε0 _
    · subst a
      have hv (j : ℕ) := smoothComposition_derivative_ae
        ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
        (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
        (PDE.Analysis.Calculus.smoothAbs_zero (ε j) (hε j).le)
        (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U i
      filter_upwards [ae_all_iff.2 hv, absoluteValue_derivative_ae U i] with x hx hy
      simp only [wkpCoordinateCLM_apply, V]
      simp_rw [hx, hy]
      exact (PDE.Analysis.Calculus.tendsto_smoothAbsSlope_of_tendsto_zero hε0 _).mul_const _

/-- Absolute value is strongly continuous for every finite Sobolev exponent. -/
theorem continuous_absoluteValue (hp : p ≠ ∞) :
    Continuous (absoluteValue (n := n) (p := p)) := by
  have heq : absoluteValue (n := n) (p := p) = fun U ↦ (2 : ℝ) • positivePart U - U := by
    funext U
    simp only [positivePart, smul_add, smul_smul]
    norm_num
  rw [heq]
  exact ((continuous_positivePart (n := n) hp).const_smul (2 : ℝ)).sub continuous_id

end SobolevSpace.GraphSpace
