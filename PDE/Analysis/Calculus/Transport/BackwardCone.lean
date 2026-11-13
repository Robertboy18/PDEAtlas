/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Backward cones for bounded transport speeds

The spatial balls expand towards the initial time. A frozen transport direction
whose norm is bounded by the cone speed points into the past portion of the cone,
even at a lateral contact. This geometric fact does not require a characteristic
curve to exist.
-/

@[expose] public noncomputable section

open Set
open scoped Convex

namespace PDE.Analysis.Transport

variable {E : Type*} [NormedAddCommGroup E]

/-- The closed backward cone with terminal center `x`, terminal radius `r`,
terminal time `T`, and propagation speed `M`. -/
def backwardCone (x : E) (T r M : ℝ) : Set (ℝ × E) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ T ∧ ‖p.2 - x‖ ≤ r + M * (T - p.1)}

/-- A backward cone is closed, including its initial and terminal faces. -/
theorem isClosed_backwardCone (x : E) (T r M : ℝ) :
    IsClosed (backwardCone x T r M) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_const).inter
      (isClosed_le (continuous_snd.sub continuous_const).norm
        (continuous_const.add (continuous_const.mul
          (continuous_const.sub continuous_fst)))))

variable [NormedSpace ℝ E]

/-- A backward cone is convex. -/
theorem convex_backwardCone (x : E) (T r M : ℝ) :
    Convex ℝ (backwardCone x T r M) := by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a * p.1 + b * q.1 ∧ a * p.1 + b * q.1 ≤ T ∧
    ‖a • p.2 + b • q.2 - x‖ ≤ r + M * (T - (a * p.1 + b * q.1))
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hp.2.1 ha,
      mul_le_mul_of_nonneg_left hq.2.1 hb, congrArg (fun z ↦ z * T) hab]
  have hvec : a • p.2 + b • q.2 - x = a • (p.2 - x) + b • (q.2 - x) := by
    have hx : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
    calc
      _ = (a • p.2 + b • q.2) - (a • x + b • x) := by rw [hx]
      _ = _ := by rw [smul_sub, smul_sub]; abel
  rw [hvec]
  calc
    ‖a • (p.2 - x) + b • (q.2 - x)‖ ≤
        ‖a • (p.2 - x)‖ + ‖b • (q.2 - x)‖ := norm_add_le _ _
    _ = a * ‖p.2 - x‖ + b * ‖q.2 - x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * (r + M * (T - p.1)) + b * (r + M * (T - q.1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hp.2.2 ha)
        (mul_le_mul_of_nonneg_left hq.2.2 hb)
    _ = r + M * (T - (a * p.1 + b * q.1)) := by
      nlinarith [congrArg (fun z ↦ z * (r + M * T)) hab]

omit [NormedSpace ℝ E] in
/-- In a proper spatial space, a backward cone is compact. No positivity of
the terminal radius or terminal time is required for this statement. -/
theorem isCompact_backwardCone [ProperSpace E] (x : E) (T r M : ℝ) (hM : 0 ≤ M) :
    IsCompact (backwardCone x T r M) := by
  apply ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).prod
    (isCompact_closedBall x (r + M * T))).of_isClosed_subset
    (isClosed_backwardCone x T r M)
  intro p hp
  refine ⟨⟨hp.1, hp.2.1⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hp.2.2.trans (by nlinarith [mul_nonneg hM hp.1])

/-- A frozen velocity bounded by the cone speed reaches the initial face
along a straight segment contained in the cone. -/
theorem initial_shift_mem_backwardCone
    {x : E} {T r M : ℝ} {p : ℝ × E} (hp : p ∈ backwardCone x T r M)
    {b : E} (hb : ‖b‖ ≤ M) :
    (0, p.2 - p.1 • b) ∈ backwardCone x T r M := by
  refine ⟨le_rfl, hp.1.trans hp.2.1, ?_⟩
  have hvec : p.2 - p.1 • b - x = (p.2 - x) - p.1 • b := by abel
  rw [hvec, sub_zero]
  calc
    ‖p.2 - x - p.1 • b‖ ≤ ‖p.2 - x‖ + ‖p.1 • b‖ := norm_sub_le _ _
    _ = ‖p.2 - x‖ + p.1 * ‖b‖ := by
      rw [norm_smul, Real.norm_of_nonneg hp.1]
    _ ≤ r + M * (T - p.1) + p.1 * M :=
      add_le_add hp.2.2 (mul_le_mul_of_nonneg_left hb hp.1)
    _ = r + M * T := by ring

/-- The full displacement along a frozen backward transport direction is in
the tangent cone of the past region. This includes both lateral faces. -/
theorem initial_shift_sub_mem_posTangentConeAt
    {x : E} {T r M : ℝ} {p : ℝ × E} (hp : p ∈ backwardCone x T r M)
    {b : E} (hb : ‖b‖ ≤ M) :
    (0, p.2 - p.1 • b) - p ∈
      posTangentConeAt (backwardCone x T r M ∩ {q | q.1 ≤ p.1}) p := by
  apply sub_mem_posTangentConeAt_of_segment_subset
  intro q hq
  refine ⟨(convex_backwardCone x T r M).segment_subset hp
    (initial_shift_mem_backwardCone hp hb) hq, ?_⟩
  rcases hq with ⟨a, b, ha, hb, hab, rfl⟩
  change a * p.1 + b * 0 ≤ p.1
  nlinarith [mul_nonneg hb hp.1, congrArg (fun z ↦ z * p.1) hab]

end PDE.Analysis.Transport
