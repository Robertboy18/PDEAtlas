/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.LocalExistence
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Positivity.Finset

/-!
# Mild solutions for locally Lipschitz nonlinearities

A Lipschitz bound on a closed ball around the initial vector suffices for local
existence. Strong continuity keeps the homogeneous orbit near that vector, while
the Duhamel estimate keeps the Picard map inside the ball of continuous curves.
The contraction theorem then gives uniqueness among curves in this ball.

The final theorem uses Mathlib's `LocallyLipschitz` hypothesis and retains the
closed-ball restriction on competitors. `Semilinear.Uniqueness` removes that
restriction, and `Semilinear.Maximal` constructs the maximal forward solution.
Continuation from bounded states requires the stronger Lipschitz-on-balls hypothesis
in `Semilinear.Continuation`.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A Lipschitz bound on the state ball gives the usual Picard contraction bound
on the corresponding ball of continuous curves. -/
theorem lipschitzOnWith_picardMap_closedBall (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} {x₀ : E} {r : ℝ} (hr : 0 ≤ r)
    (hF : LipschitzOnWith L F (Metric.closedBall x₀ r))
    (hbound : ∀ t ∈ Icc (0 : NNReal) τ, ‖T t‖ ≤ M) :
    LipschitzOnWith (M * L * τ) (T.picardMap F x₀ τ)
      (Metric.closedBall (ContinuousMap.const (Icc (0 : ℝ) (τ : ℝ)) x₀) r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hu' := (ContinuousMap.dist_le hr).1 hu
  have hv' := (ContinuousMap.dist_le hr).1 hv
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
    exact (hF.dist_le_mul _ (hu' (projIcc 0 (τ : ℝ) τ.property s))
      _ (hv' (projIcc 0 (τ : ℝ) τ.property s))).trans
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

/-- The homogeneous orbit and the forcing each use at most half the available radius,
so the Picard map preserves the closed ball of curves around the initial vector. -/
theorem picardMap_mapsTo_closedBall (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} {x₀ : E} {r : ℝ} (hr : 0 ≤ r)
    (hF : LipschitzOnWith L F (Metric.closedBall x₀ r))
    (hbound : ∀ t ∈ Icc (0 : NNReal) τ, ‖T t‖ ≤ M)
    (horbit : ∀ t ∈ Icc (0 : ℝ) (τ : ℝ), dist (T t.toNNReal x₀) x₀ ≤ r / 2)
    (hforcing : (M : ℝ) * ((L : ℝ) * r + ‖F x₀‖) * (τ : ℝ) ≤ r / 2) :
    MapsTo (T.picardMap F x₀ τ)
      (Metric.closedBall (ContinuousMap.const (Icc (0 : ℝ) (τ : ℝ)) x₀) r)
      (Metric.closedBall (ContinuousMap.const (Icc (0 : ℝ) (τ : ℝ)) x₀) r) := by
  intro u hu
  have hu' := (ContinuousMap.dist_le hr).1 hu
  apply (ContinuousMap.dist_le hr).2
  intro t
  have hforcingBound : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
      ‖F (IccExtend τ.property u s) - 0‖ ≤ (L : ℝ) * r + ‖F x₀‖ := by
    intro s _
    let z := projIcc 0 (τ : ℝ) τ.property s
    have hdist := hF.dist_le_mul (u z) (hu' z) x₀ (Metric.mem_closedBall_self hr)
    calc
      _ = ‖F (u z)‖ := by
        rw [sub_zero]
        rfl
      _ ≤ ‖F (u z) - F x₀‖ + ‖F x₀‖ := by
        simpa only [dist_eq_norm, sub_zero] using dist_triangle (F (u z)) (F x₀) 0
      _ ≤ (L : ℝ) * dist (u z) x₀ + ‖F x₀‖ := by
        rw [← dist_eq_norm]
        exact add_le_add hdist le_rfl
      _ ≤ (L : ℝ) * r + ‖F x₀‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hu' z) L.property) le_rfl
  have hzero : T.duhamel (fun _ ↦ (0 : E)) t = 0 := by simp [duhamel]
  have hnorm := T.norm_duhamel_sub_le
    (F.continuous.comp u.continuous.Icc_extend') continuous_const
    hbound t.property hforcingBound
  rw [hzero, sub_zero] at hnorm
  change dist
    (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.property u s)) t)
    x₀ ≤ r
  calc
    _ ≤ dist
          (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.property u s)) t)
          (T (t : ℝ).toNNReal x₀) + dist (T (t : ℝ).toNNReal x₀) x₀ :=
      dist_triangle _ _ _
    _ = ‖T.duhamel (fun s ↦ F (IccExtend τ.property u s)) t‖ +
        dist (T (t : ℝ).toNNReal x₀) x₀ := by
      rw [dist_eq_norm, add_sub_cancel_left]
    _ ≤ (M : ℝ) * ((L : ℝ) * r + ‖F x₀‖) * (t : ℝ) + r / 2 :=
      add_le_add hnorm (horbit t t.property)
    _ ≤ (M : ℝ) * ((L : ℝ) * r + ‖F x₀‖) * (τ : ℝ) + r / 2 :=
      add_le_add (mul_le_mul_of_nonneg_left t.property.2 (by positivity)) le_rfl
    _ ≤ r := by linarith

/-- On a sufficiently short interval there is a unique mild solution in the prescribed
closed ball of curves. The radius bounds the uniform distance from the initial vector. -/
theorem existsUnique_mildSolutionOn_closedBall_of_bounds (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} {x₀ : E} {r : ℝ} (hr : 0 ≤ r)
    (hF : LipschitzOnWith L F (Metric.closedBall x₀ r))
    (hbound : ∀ t ∈ Icc (0 : NNReal) τ, ‖T t‖ ≤ M)
    (horbit : ∀ t ∈ Icc (0 : ℝ) (τ : ℝ), dist (T t.toNNReal x₀) x₀ ≤ r / 2)
    (hforcing : (M : ℝ) * ((L : ℝ) * r + ‖F x₀‖) * (τ : ℝ) ≤ r / 2)
    (hsmall : M * L * τ < 1) :
    ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E),
      u ∈ Metric.closedBall (ContinuousMap.const _ x₀) r ∧
        T.IsMildSolutionOn F x₀ τ u := by
  have hmaps := T.picardMap_mapsTo_closedBall hr hF hbound horbit hforcing
  have hlip := T.lipschitzOnWith_picardMap_closedBall hr hF hbound
  have hc : ContractingWith (M * L * τ)
      (hmaps.restrict (T.picardMap F x₀ τ) _ _) :=
    ⟨hsmall, hlip.mapsToRestrict hmaps⟩
  obtain ⟨u, hu, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hc
    (Metric.mem_closedBall_self hr) (edist_ne_top _ _)
  refine ⟨u, ⟨hu, ?_⟩, ?_⟩
  · intro t
    exact (congrArg (fun w : C(Icc (0 : ℝ) (τ : ℝ), E) ↦ w t) hfix).symm
  · intro v hv
    have hvfix : T.picardMap F x₀ τ v = v :=
      ContinuousMap.ext fun t ↦ (hv.2 t).symm
    have hdist := hlip.dist_le_mul v hv.1 u hu
    rw [hvfix, hfix.eq] at hdist
    have hq : ((M * L * τ : NNReal) : ℝ) < 1 := hsmall
    apply dist_eq_zero.mp
    nlinarith [dist_nonneg (x := v) (y := u)]

/-- A Lipschitz bound on any positive-radius ball around the initial vector gives a
positive interval with a unique mild solution among curves in that ball. -/
theorem exists_pos_existsUnique_mildSolutionOn_closedBall (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L : NNReal} (x₀ : E) {r : ℝ} (hr : 0 < r)
    (hF : LipschitzOnWith L F (Metric.closedBall x₀ r)) :
    ∃ τ : NNReal, 0 < τ ∧
      ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E),
        u ∈ Metric.closedBall (ContinuousMap.const _ x₀) r ∧
          T.IsMildSolutionOn F x₀ τ u := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_on_Icc 1
  have hcont : Continuous (fun t : ℝ ↦ T t.toNNReal x₀) :=
    (T.continuous_orbit x₀).comp continuous_real_toNNReal
  obtain ⟨δ, hδ, horbit⟩ :=
    Metric.continuousAt_iff.1 (hcont.continuousAt (x := 0)) (r / 2) (half_pos hr)
  obtain ⟨ε₁, hε₁, hforcing⟩ :=
    exists_pos_mul_lt (half_pos hr) (C * ((L : ℝ) * r + ‖F x₀‖) + 1)
  obtain ⟨ε₂, hε₂, hsmall⟩ :=
    exists_pos_mul_lt (zero_lt_one : (0 : ℝ) < 1) (C * (L : ℝ) + 1)
  let t₁ := min 1 (min (δ / 2) (min ε₁ ε₂))
  have ht₁ : 0 < t₁ := lt_min zero_lt_one
    (lt_min (half_pos hδ) (lt_min hε₁ hε₂))
  have ht₁one : t₁ ≤ 1 := min_le_left _ _
  have ht₁δ : t₁ ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have ht₁ε₁ : t₁ ≤ ε₁ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have ht₁ε₂ : t₁ ≤ ε₂ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hforcingCoeff : 0 ≤ C * ((L : ℝ) * r + ‖F x₀‖) := by positivity
  have hforcingSmall : C * ((L : ℝ) * r + ‖F x₀‖) * t₁ ≤ r / 2 :=
    (mul_le_mul_of_nonneg_left ht₁ε₁ hforcingCoeff).trans (by nlinarith)
  have hCL : 0 ≤ C * (L : ℝ) := mul_nonneg hC L.property
  have hcontract : C * (L : ℝ) * t₁ < 1 :=
    (mul_le_mul_of_nonneg_left ht₁ε₂ hCL).trans_lt (by nlinarith)
  let τ : NNReal := ⟨t₁, ht₁.le⟩
  let M : NNReal := ⟨C, hC⟩
  refine ⟨τ, ht₁, T.existsUnique_mildSolutionOn_closedBall_of_bounds
    (M := M) hr.le hF
    (fun t ht ↦ hbound t ⟨ht.1, ht.2.trans ht₁one⟩) ?_ hforcingSmall hcontract⟩
  intro t ht
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact (ht.2.trans ht₁δ).trans_lt (half_lt_self hδ)
  simpa only [Real.toNNReal_zero, map_zero_apply] using (horbit htδ).le

/-- A continuous locally Lipschitz nonlinearity admits a mild solution near every
initial vector, uniquely within a suitable uniform neighborhood of that vector. -/
theorem exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : LocallyLipschitz F) (x₀ : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : NNReal, 0 < τ ∧
      ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E),
        u ∈ Metric.closedBall (ContinuousMap.const _ x₀) r ∧
          T.IsMildSolutionOn F x₀ τ u := by
  obtain ⟨L, s, hs, hLip⟩ := hF x₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hs
  have hlocal : LipschitzOnWith L F (Metric.closedBall x₀ (r / 2)) :=
    hLip.mono ((Metric.closedBall_subset_ball (half_lt_self hr)).trans hball)
  exact ⟨r / 2, half_pos hr,
    T.exists_pos_existsUnique_mildSolutionOn_closedBall x₀ (half_pos hr) hlocal⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
