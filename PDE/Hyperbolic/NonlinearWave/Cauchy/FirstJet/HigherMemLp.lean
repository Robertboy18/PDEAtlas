/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.HigherReaction

/-!
# Time measurability of the sharp first-jet source

A bounded measurable higher Sobolev trajectory has a bounded measurable
first-jet reaction at the same forcing order. The finite composition bound
is used at precisely the threshold n < 2k.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert ENNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Composition

variable {n k : ℕ} [NeZero n] {f : (ℝ^n × ℝ × ℝ) → ℝ}

/-- A uniformly bounded high Sobolev state has a uniformly bounded reaction
at the same forcing order. No spatial derivative margin is added. -/
theorem exists_norm_higherReaction_bound (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n),
      ‖z‖ ≤ R → ‖higherReaction hk hf hf0 z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_norm_finiteComposition_bound (ι := Fin n ⊕ Bool) hk
    (hf.comp (decodeJetCLM (n := n)).contDiff)
    (by simpa only [Function.comp_apply, map_zero] using hf0) (‖higherJetCLM (n := n) (k := k)‖ * R)
  let J := higherJetCLM (n := n) (k := k)
  refine ⟨C, hC, fun z hz ↦ hb (J z) ?_⟩
  exact (J.le_opNorm z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg J))

/-- The sharp reaction preserves essential boundedness in time, including
strong measurability, for arbitrary measurable higher Sobolev trajectories. -/
theorem memLp_top_higherReaction (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) {μ : Measure ℝ} {u : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hu : MemLp u ∞ μ) :
    MemLp (fun t ↦ higherReaction hk hf hf0 (u t)) ∞ μ := by
  have he : eLpNormEssSup u μ < ∞ := by
    rw [← eLpNorm_exponent_top hu.aestronglyMeasurable]
    exact hu.eLpNorm_lt_top
  obtain ⟨R, hR⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  obtain ⟨C, _, hC⟩ := exists_norm_higherReaction_bound hk hf hf0 R
  apply memLp_top_of_bound
    ((locallyLipschitz_higherReaction hk hf hf0).continuous.comp_aestronglyMeasurable
      hu.aestronglyMeasurable) C
  filter_upwards [hR] with t ht using hC (u t) (by exact_mod_cast ht)

/-- The mass-canceling high first-jet source preserves L-infinity time bounds. -/
theorem memLp_top_higherMap (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) {μ : Measure ℝ} {u : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hu : MemLp u ∞ μ) :
    MemLp (fun t ↦ higherMap hk hf hf0 (u t)) ∞ μ := by
  let Q : (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n) :=
    (lowerOrderCLM (Nat.le_succ k)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hr := (Q.comp_memLp' hu).sub (memLp_top_higherReaction hk hf hf0 hu)
  exact (ContinuousLinearMap.inr ℝ W^{k + 1,2}(ℝ^n) W^{k,2}(ℝ^n)).comp_memLp' hr

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
