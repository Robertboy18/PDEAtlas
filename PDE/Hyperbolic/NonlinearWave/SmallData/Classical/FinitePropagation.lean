/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Solution
import PDE.FDeriv.Calculus

/-!
# Finite propagation for focusing classical waves

Local Lipschitz uniqueness against the zero solution gives finite propagation. In particular it
applies to the focusing source `|u|^p`; a nonnegative-potential energy theorem would not suffice.
-/

@[expose] public noncomputable section

open PDE.Analysis PDE.Common Set
open scoped Topology

namespace WaveEquation.SmallData.Classical

variable {n : ℕ} [Fact (0 < n)]

/-- Compact Cauchy support propagates at speed one for a classical
solution of a locally Lipschitz reaction fixing zero. -/
theorem IsSolutionBefore.eq_zero_of_norm_gt {f : ℝ → ℝ} (hf : LocallyLipschitz f) (hf0 : f 0 = 0)
    {g h : ℝ^n → ℝ} {R T : ℝ} {u : ℝ^(n + 1) → ℝ} (hu : IsSolutionBefore f g h T u)
    (hg : ∀ x, R < ‖x‖ → g x = 0) (hh : ∀ x, R < ‖x‖ → h x = 0) {t : ℝ} (ht : t ∈ Ico 0 T) (x : ℝ^n)
    (hx : R + t < ‖x‖) :
    u (timeSpaceCons t x) = 0 := by
  let S := (t + T) / 2
  have htS : t ≤ S := by dsimp [S]; linarith [ht.2]
  have hST : S < T := by dsimp [S]; linarith [ht.2]
  obtain ⟨U, hU, heq⟩ := exists_contDiff_eventuallyEq_before hu.regular hST
  have hbase (y : ℝ^n) (hy : y ∈ Metric.closedBall x t) : R < ‖y‖ := by
    have hy' : ‖y - x‖ ≤ t := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    have hn := norm_le_norm_add_norm_sub y x
    linarith
  have hz := eq_on_closed_backwardCone_of_eq_cauchyData_locallyLipschitz
    (v := fun _ ↦ 0) hf hU contDiff_const x (a := 0) (T := t) (fun s hs y _ ↦ ?_) (fun _ _ _ _ ↦ ?_)
    (fun y hy ↦ ?_) (fun y hy ↦ ?_) t ⟨ht.1, le_rfl⟩ x
    (by simp)
  · rw [(heq (timeSpaceCons t x) (by simpa using htS)).eq_of_nhds] at hz
    exact hz
  · have hsS : s ≤ S := hs.2.le.trans htS
    rw [waveOperator_congr_nhds (heq (timeSpaceCons s y) (by simpa using hsS)),
      (heq (timeSpaceCons s y) (by simpa using hsS)).eq_of_nhds]
    exact hu.equation _ (by simpa using And.intro hs.1 (hs.2.trans ht.2))
  · simp [waveOperator, hf0]
  · rw [(heq (timeSpaceCons 0 y) (by simpa using ht.1.trans htS)).eq_of_nhds, hu.position]
    apply hg
    apply hbase
    simpa only [sub_zero] using hy
  · rw [PDE.partialDeriv_congr_nhds 0
      (heq (timeSpaceCons 0 y) (by simpa using ht.1.trans htS)), hu.velocity]
    simp only [PDE.partialDeriv_const]
    apply hh
    apply hbase
    simpa only [sub_zero] using hy

end WaveEquation.SmallData.Classical
