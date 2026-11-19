/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.ZeroExtension
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointRegularity

/-!
# A classical initial jet for zero-displacement Sobolev waves

For zero initial displacement and a reaction fixing zero, initial acceleration
vanishes. The backward field `t h` therefore matches both time derivatives of
the forward solution. Pasting at the Sobolev level preserves joint spatial and
time regularity, including the mixed derivatives at the initial slice.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace WaveEquation.SmallData.Classical

variable {n k : ℕ}

/-- Extend a forward state by its linear zero-displacement initial jet.
The two strong derivative identities hold on an open interval across zero. -/
theorem exists_higherZeroJet_extension (H : W^{k + 2,2}(ℝ^n))
    (U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))) (A : C(ℝ, W^{k,2}(ℝ^n)))
    (hU0 : U 0 = (0, lowerOrderCLM (Nat.le_succ (k + 1)) H)) (hA0 : A 0 = 0) {b : ℝ} (hb : 0 < b)
    (hQ : ∀ t ∈ Icc 0 b,
      HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U s).1) (U t).2 (Icc 0 b) t)
    (hV : ∀ t ∈ Icc 0 b,
      HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (U s).2) (A t) (Icc 0 b) t) :
    ∃ V : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)),
      ∃ B : C(ℝ, W^{k,2}(ℝ^n)),
        (∀ t, 0 ≤ t → V t = U t ∧ B t = A t) ∧
        (∀ t < b,
          HasDerivAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (V s).1)
            (V t).2 t) ∧
        ∀ t < b,
          HasDerivAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (V s).2) (B t) t := by
  let L := lowerOrderCLM (n := n) (p := 2) (Ω := univ) (Nat.le_succ (k + 1))
  let M := lowerOrderCLM (n := n) (p := 2) (Ω := univ) (Nat.le_succ k)
  let V : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) := ⟨pasteZero U (fun t ↦ (t • H, L H)),
      continuous_pasteZero U.continuous
        ((continuous_id.smul continuous_const).prodMk continuous_const)
        (by simpa only [zero_smul] using hU0)⟩
  let B : C(ℝ, W^{k,2}(ℝ^n)) :=
    ⟨pasteZero A (fun _ ↦ 0), continuous_pasteZero A.continuous continuous_const hA0⟩
  have hqeq (t : ℝ) :
      L (V t).1 = pasteZero (fun s ↦ L (U s).1) (fun s ↦ s • L H) t := by
    by_cases ht : 0 ≤ t <;> simp [V, pasteZero, ht]
  have hveq (t : ℝ) :
      (V t).2 = pasteZero (fun s ↦ (U s).2) (fun _ ↦ L H) t := by
    by_cases ht : 0 ≤ t <;> simp [V, pasteZero, ht]
  have hlveq (t : ℝ) :
      M (V t).2 = pasteZero (fun s ↦ M (U s).2) (fun _ ↦ M (L H)) t := by
    by_cases ht : 0 ≤ t <;> simp [V, pasteZero, ht]
  refine ⟨V, B, ?_, ?_, ?_⟩
  · intro t ht
    simp [V, B, pasteZero, ht]
  · intro t ht
    simp only [show (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (V s).1) =
      fun s ↦ pasteZero (fun r ↦ L (U r).1) (fun r ↦ r • L H) s from funext hqeq, hveq]
    exact hasDerivAt_pasteZero hb
      (by simp [hU0]) (by simp [hU0, L]) hQ
      (fun s ↦ by simpa using (hasDerivAt_id s).smul_const (L H)) ht
  · intro t ht
    change HasDerivAt (fun s ↦ M (V s).2) (B t) t
    simp only [hlveq]
    exact hasDerivAt_pasteZero hb (by simp [hU0, L]) hA0 hV
      (fun s ↦ hasDerivAt_const s (M (L H))) ht

end WaveEquation.SmallData.Classical
