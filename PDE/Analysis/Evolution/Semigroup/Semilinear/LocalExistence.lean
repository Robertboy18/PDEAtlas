/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Positivity.Finset

/-!
# Local mild solutions for globally Lipschitz nonlinearities

On a time interval of length `τ`, an operator bound `M` and a Lipschitz constant `L`
give the Picard map contraction factor `M * L * τ` in the uniform norm.
Banach's fixed-point theorem then constructs the solution, proves uniqueness,
and bounds its dependence on the initial value.

This construction assumes a globally Lipschitz nonlinearity. `Semilinear.LocalLipschitz`
constructs solutions under a local Lipschitz hypothesis, and `Semilinear.Maximal`
constructs their maximal forward trajectories.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Picard map has Lipschitz constant `M * L * τ` in the uniform norm. -/
theorem lipschitzWith_picardMap (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} (hF : LipschitzWith L F)
    (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M) (x₀ : E) :
    LipschitzWith (M * L * τ) (T.picardMap F x₀ τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (ContinuousMap.dist_le (by positivity)).2
  intro t
  change dist
    (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.property u s)) t)
    (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.property v s)) t) ≤ _
  rw [dist_add_left, dist_eq_norm]
  have hfg : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
      ‖F (IccExtend τ.property u s) - F (IccExtend τ.property v s)‖ ≤
        (L : ℝ) * dist u v := by
    intro s _
    rw [← dist_eq_norm]
    exact (hF.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left
        (ContinuousMap.dist_apply_le_dist (projIcc 0 (τ : ℝ) τ.property s)) L.property)
  have h := T.norm_duhamel_sub_le
    (F.continuous.comp u.continuous.Icc_extend')
    (F.continuous.comp v.continuous.Icc_extend') hbound t.property hfg
  calc
    _ ≤ (M : ℝ) * ((L : ℝ) * dist u v) * (t : ℝ) := h
    _ ≤ (M : ℝ) * ((L : ℝ) * dist u v) * (τ : ℝ) :=
      mul_le_mul_of_nonneg_left t.property.2 (by positivity)
    _ = ((M * L * τ : NNReal) : ℝ) * dist u v := by
      simp only [NNReal.coe_mul]
      ring

/-- A sufficiently short interval admits exactly one continuous mild solution. -/
theorem existsUnique_mildSolutionOn_of_mul_lt_one (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} (hF : LipschitzWith L F)
    (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M)
    (hsmall : M * L * τ < 1) (x₀ : E) :
    ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u := by
  have hc : ContractingWith (M * L * τ) (T.picardMap F x₀ τ) :=
    ⟨hsmall, T.lipschitzWith_picardMap hF hbound x₀⟩
  refine ⟨hc.fixedPoint (T.picardMap F x₀ τ), ?_, ?_⟩
  · intro t
    exact (congrArg (fun u : C(Icc (0 : ℝ) (τ : ℝ), E) ↦ u t)
      hc.fixedPoint_isFixedPt).symm
  · intro u hu
    exact hc.fixedPoint_unique (ContinuousMap.ext fun t ↦ (hu t).symm)

/-- Every initial vector admits a unique mild solution on some positive interval.
The semigroup bound and the interval are obtained from strong continuity. -/
theorem exists_pos_existsUnique_mildSolutionOn (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L : NNReal} (hF : LipschitzWith L F) (x₀ : E) :
    ∃ τ : NNReal, 0 < τ ∧
      ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_on_Icc 1
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_mul_lt (zero_lt_one : (0 : ℝ) < 1) (C * (L : ℝ) + 1)
  have hCL : 0 ≤ C * (L : ℝ) := mul_nonneg hC L.property
  have hδle : δ ≤ 1 := by nlinarith
  have hδsmall : C * (L : ℝ) * δ < 1 := by nlinarith
  let τ : NNReal := ⟨δ, hδ.le⟩
  let M : NNReal := ⟨C, hC⟩
  refine ⟨τ, hδ, T.existsUnique_mildSolutionOn_of_mul_lt_one hF
    (M := M) (fun r hr ↦ hbound r ⟨hr.1, hr.2.trans hδle⟩) hδsmall x₀⟩

/-- Mild solutions depend Lipschitz continuously on their initial values on a common
interval with `M * L * τ < 1`. The distance on curves is the uniform distance. -/
theorem IsMildSolutionOn.dist_le_of_mul_lt_one {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {L M τ : NNReal} (hF : LipschitzWith L F)
    (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M)
    (hsmall : M * L * τ < 1) {x₀ y₀ : E}
    {u v : C(Icc (0 : ℝ) (τ : ℝ), E)}
    (hu : T.IsMildSolutionOn F x₀ τ u) (hv : T.IsMildSolutionOn F y₀ τ v) :
    dist u v ≤ (M : ℝ) * dist x₀ y₀ / (1 - ((M * L * τ : NNReal) : ℝ)) := by
  have hc : ContractingWith (M * L * τ) (T.picardMap F x₀ τ) :=
    ⟨hsmall, T.lipschitzWith_picardMap hF hbound x₀⟩
  apply hc.dist_fixedPoint_fixedPoint_of_dist_le' (T.picardMap F y₀ τ)
    (ContinuousMap.ext fun t ↦ (hu t).symm)
    (ContinuousMap.ext fun t ↦ (hv t).symm)
  intro w
  apply (ContinuousMap.dist_le (by positivity)).2
  intro t
  change dist
    (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.property w s)) t)
    (T (t : ℝ).toNNReal y₀ + T.duhamel (fun s ↦ F (IccExtend τ.property w s)) t) ≤ _
  rw [dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub]
  have ht : (t : ℝ).toNNReal ≤ τ := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_mono t.property.2
  exact (T (t : ℝ).toNNReal).le_of_opNorm_le (hbound _ ⟨zero_le, ht⟩) _

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
