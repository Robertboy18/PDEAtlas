/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Uniqueness
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Uniform existence times for bounded initial states

Lipschitz bounds on each norm ball give one positive existence time for all
initial states in a prescribed bounded ball. A semigroup operator bound
controls the homogeneous term uniformly, and a Picard contraction on a larger
ball of curves supplies existence. Uniqueness holds among all continuous mild
solutions on that interval.

The hypothesis is stronger than local Lipschitz continuity in infinite
dimensions: a Lipschitz constant is required on each entire norm ball.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A Lipschitz bound on the states visited by a set of curves gives the Picard
contraction bound on that set, independently of the center used to bound the curves. -/
theorem lipschitzOnWith_picardMap_of_mapsTo (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} {s : Set E}
    {A : Set C(Icc (0 : ℝ) (τ : ℝ), E)}
    (hF : LipschitzOnWith L F s)
    (hA : ∀ u ∈ A, ∀ t, u t ∈ s)
    (hbound : ∀ t ∈ Icc (0 : NNReal) τ, ‖T t‖ ≤ M) (x₀ : E) :
    LipschitzOnWith (M * L * τ) (T.picardMap F x₀ τ) A := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  apply (ContinuousMap.dist_le (by positivity)).2
  intro t
  change dist
    (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg u s)) t)
    (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg v s)) t) ≤ _
  rw [dist_add_left, dist_eq_norm]
  have hfg : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
      ‖F (IccExtend τ.coe_nonneg u s) - F (IccExtend τ.coe_nonneg v s)‖ ≤
        (L : ℝ) * dist u v := by
    intro s _
    rw [← dist_eq_norm]
    exact (hF.dist_le_mul _ (hA u hu (projIcc 0 (τ : ℝ) τ.coe_nonneg s))
      _ (hA v hv (projIcc 0 (τ : ℝ) τ.coe_nonneg s))).trans
        (mul_le_mul_of_nonneg_left
          (ContinuousMap.dist_apply_le_dist (projIcc 0 (τ : ℝ) τ.coe_nonneg s)) L.coe_nonneg)
  have hnorm := T.norm_duhamel_sub_le
    (F.continuous.comp u.continuous.Icc_extend')
    (F.continuous.comp v.continuous.Icc_extend') hbound t.property hfg
  calc
    _ ≤ (M : ℝ) * ((L : ℝ) * dist u v) * (t : ℝ) := hnorm
    _ ≤ (M : ℝ) * ((L : ℝ) * dist u v) * (τ : ℝ) :=
      mul_le_mul_of_nonneg_left t.property.2 (by positivity)
    _ = ((M * L * τ : NNReal) : ℝ) * dist u v := by
      simp only [NNReal.coe_mul]
      ring

/-- Uniform bounds on the homogeneous term and the forcing preserve a ball of
curves centered at zero. No estimate of `T(t)x₀ - x₀` is used. -/
theorem picardMap_mapsTo_closedBall_zero (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} {R K : ℝ} (hK : 0 ≤ K)
    (hF : LipschitzOnWith L F (Metric.closedBall (0 : E) K))
    (hbound : ∀ t ∈ Icc (0 : NNReal) τ, ‖T t‖ ≤ M)
    {x₀ : E} (hx₀ : ‖x₀‖ ≤ R)
    (hbudget : (M : ℝ) * R +
      (M : ℝ) * ((L : ℝ) * K + ‖F 0‖) * (τ : ℝ) ≤ K) :
    MapsTo (T.picardMap F x₀ τ)
      (Metric.closedBall (ContinuousMap.const _ (0 : E)) K)
      (Metric.closedBall (ContinuousMap.const _ (0 : E)) K) := by
  intro u hu
  have hu' := (ContinuousMap.dist_le hK).1 hu
  have hforce : ∀ s : ℝ, ‖F (IccExtend τ.coe_nonneg u s)‖ ≤ (L : ℝ) * K + ‖F 0‖ := by
    intro s
    let z := projIcc 0 (τ : ℝ) τ.coe_nonneg s
    have hdist := hF.dist_le_mul (u z) (hu' z) 0 (Metric.mem_closedBall_self hK)
    calc
      ‖F (u z)‖ ≤ ‖F (u z) - F 0‖ + ‖F 0‖ := by
        simpa only [dist_eq_norm, sub_zero] using dist_triangle (F (u z)) (F 0) 0
      _ ≤ (L : ℝ) * dist (u z) 0 + ‖F 0‖ :=
        add_le_add (by simpa only [dist_eq_norm] using hdist) le_rfl
      _ ≤ (L : ℝ) * K + ‖F 0‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hu' z) L.coe_nonneg) le_rfl
  apply (ContinuousMap.dist_le hK).2
  intro t
  have hJ := T.norm_duhamel_sub_le
    (f := fun s ↦ F (IccExtend τ.coe_nonneg u s)) (g := fun _ ↦ (0 : E))
    (D := (L : ℝ) * K + ‖F 0‖)
    (F.continuous.comp u.continuous.Icc_extend') continuous_const hbound t.property
    (fun s _ ↦ by simpa only [sub_zero] using hforce s)
  have hzero : T.duhamel (fun _ ↦ (0 : E)) t = 0 := by simp [duhamel]
  rw [hzero, sub_zero] at hJ
  have ht : (t : ℝ).toNNReal ∈ Icc (0 : NNReal) τ := by
    exact ⟨zero_le, by simpa only [Real.toNNReal_coe] using
      Real.toNNReal_mono t.property.2⟩
  have horbit : ‖T (t : ℝ).toNNReal x₀‖ ≤ (M : ℝ) * R :=
    ((T (t : ℝ).toNNReal).le_of_opNorm_le (hbound _ ht) x₀).trans
      (mul_le_mul_of_nonneg_left hx₀ M.coe_nonneg)
  change dist
    (T (t : ℝ).toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg u s)) t) 0 ≤ K
  rw [dist_zero_right]
  calc
    _ ≤ ‖T (t : ℝ).toNNReal x₀‖ +
        ‖T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg u s)) t‖ := norm_add_le _ _
    _ ≤ (M : ℝ) * R + (M : ℝ) * ((L : ℝ) * K + ‖F 0‖) * (t : ℝ) :=
      add_le_add horbit hJ
    _ ≤ (M : ℝ) * R + (M : ℝ) * ((L : ℝ) * K + ‖F 0‖) * (τ : ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left t.property.2 (by positivity))
    _ ≤ K := hbudget

/-- Explicit bounds on a fixed state ball construct a mild solution for every
initial vector satisfying the same norm bound. -/
theorem exists_mildSolutionOn_closedBall_zero_of_bounds
    (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} {R K : ℝ} (hK : 0 ≤ K)
    (hF : LipschitzOnWith L F (Metric.closedBall (0 : E) K))
    (hbound : ∀ t ∈ Icc (0 : NNReal) τ, ‖T t‖ ≤ M)
    {x₀ : E} (hx₀ : ‖x₀‖ ≤ R)
    (hbudget : (M : ℝ) * R +
      (M : ℝ) * ((L : ℝ) * K + ‖F 0‖) * (τ : ℝ) ≤ K)
    (hsmall : M * L * τ < 1) :
    ∃ u : C(Icc (0 : ℝ) (τ : ℝ), E),
      u ∈ Metric.closedBall (ContinuousMap.const _ (0 : E)) K ∧
        T.IsMildSolutionOn F x₀ τ u := by
  have hmaps := T.picardMap_mapsTo_closedBall_zero hK hF hbound hx₀ hbudget
  have hlip := T.lipschitzOnWith_picardMap_of_mapsTo
    (A := Metric.closedBall (ContinuousMap.const _ (0 : E)) K) hF
    (fun u hu t ↦ (ContinuousMap.dist_le hK).1 hu t) hbound x₀
  have hc : ContractingWith (M * L * τ)
      (hmaps.restrict (T.picardMap F x₀ τ) _ _) :=
    ⟨hsmall, hlip.mapsToRestrict hmaps⟩
  obtain ⟨u, hu, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hc
    (Metric.mem_closedBall_self hK) (edist_ne_top _ _)
  refine ⟨u, hu, fun t ↦ ?_⟩
  exact (congrArg (fun w : C(Icc (0 : ℝ) (τ : ℝ), E) ↦ w t) hfix).symm

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Lipschitz bounds on all positive-radius balls centered at zero imply local
Lipschitz continuity. The converse is not used and fails in infinite dimensions. -/
theorem locallyLipschitz_of_lipschitzOn_closedBall_zero {F : E → E}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R)) :
    LocallyLipschitz F := by
  intro x
  obtain ⟨L, hL⟩ := hF (‖x‖ + 1) (by positivity)
  have hx : x ∈ Metric.ball (0 : E) (‖x‖ + 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖
  exact ⟨L, Metric.closedBall 0 (‖x‖ + 1),
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) Metric.ball_subset_closedBall, hL⟩

/-- A nonlinearity Lipschitz on each norm ball admits a common positive existence
time for all initial states in any prescribed bounded ball. Uniqueness is among all
continuous mild solutions on that interval. -/
theorem exists_pos_forall_existsUnique_mildSolutionOn_of_lipschitzOn_closedBall
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ τ : NNReal, 0 < τ ∧ ∀ x₀ : E, ‖x₀‖ ≤ R →
      ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_on_Icc 1
  let M : NNReal := .mk C hC
  let K : ℝ := C * R + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨L, hL⟩ := hF K hK
  let B : ℝ := C * ((L : ℝ) * K + ‖F 0‖)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨ε₁, hε₁, hforcing⟩ :=
    exists_pos_mul_lt (zero_lt_one : (0 : ℝ) < 1) (B + 1)
  obtain ⟨ε₂, hε₂, hcontract⟩ :=
    exists_pos_mul_lt (zero_lt_one : (0 : ℝ) < 1) (C * (L : ℝ) + 1)
  let δ : ℝ := min 1 (min ε₁ ε₂)
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min hε₁ hε₂)
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδε₁ : δ ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδε₂ : δ ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hbudget : C * R + B * δ ≤ K := by
    have hBδ := mul_le_mul_of_nonneg_left hδε₁ hB
    dsimp only [K]
    nlinarith
  have hsmall : C * (L : ℝ) * δ < 1 := by
    have hCL : 0 ≤ C * (L : ℝ) := mul_nonneg hC L.coe_nonneg
    have hCLδ := mul_le_mul_of_nonneg_left hδε₂ hCL
    nlinarith
  let τ : NNReal := .mk δ hδ.le
  refine ⟨τ, hδ, fun x₀ hx₀ ↦ ?_⟩
  obtain ⟨u, _, hu⟩ := T.exists_mildSolutionOn_closedBall_zero_of_bounds
    (M := M) (τ := τ) hK.le hL
    (fun t ht ↦ hbound t ⟨ht.1, ht.2.trans hδone⟩) hx₀ hbudget hsmall
  exact ⟨u, hu, fun v hv ↦ hv.eq_of_locallyLipschitz
    (locallyLipschitz_of_lipschitzOn_closedBall_zero hF) hu⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
