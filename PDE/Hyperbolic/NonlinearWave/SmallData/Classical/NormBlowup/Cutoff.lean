/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.SmoothCutoff
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.TimeDerivatives

/-!
# Cutting off a reaction along a compact higher Sobolev trajectory

The scalar range on a compact time interval is bounded by continuity of the
Sobolev representative. A smooth globally Lipschitz cutoff therefore agrees with
the original source throughout that interval.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped NNReal Sobolev

namespace WaveEquation.SmallData.Classical.NormBlowup

variable {n k : ℕ} [NeZero n] {f g : ℝ → ℝ}

/-- Equality on the displacement range identifies the higher source. -/
theorem higherSmoothMap_eq_of_representative_eq (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0 = 0) (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    (he : ∀ x, f (classicalRepresentativeCLM hq z.1 x) = g (classicalRepresentativeCLM hq z.1 x)) :
    higherSmoothMap hk hf hf0 z = higherSmoothMap hk hg hg0 z := by
  have hcomp : higherComposition hk hf hf0 (lowerOrderCLM (Nat.le_succ k) z.1) =
      higherComposition hk hg hg0 (lowerOrderCLM (Nat.le_succ k) z.1) := by
    apply classicalRepresentativeCLM_injective hk
    ext x
    simpa only [classicalRepresentative_higherComposition,
      classicalRepresentativeCLM_lowerOrderCLM hk hq] using he x
  change (0, _ - _) = (0, _ - _)
  rw [hcomp]

omit [NeZero n] in
/-- A single smooth Lipschitz reaction agrees with the original reaction on
every displacement value of a compact higher Sobolev curve. -/
theorem exists_cutoff_on_higher_curve (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {τ : ℝ≥0}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))) :
    ∃ g : ℝ → ℝ, ∃ K : ℝ≥0, ∃ _ : ContDiff ℝ (⊤ : ℕ∞) g, ∃ _ : g 0 = 0, LipschitzWith K g ∧ ∀ t x,
      g (classicalRepresentativeCLM hq (V t).1 x) =
      f (classicalRepresentativeCLM hq (V t).1 x) := by
  let Q : C(Icc (0 : ℝ) (τ : ℝ), BoundedContinuousFunction (ℝ^n) ℝ) :=
    ⟨fun t ↦ classicalRepresentativeCLM hq (V t).1,
      (classicalRepresentativeCLM hq).continuous.comp V.continuous.fst⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn Q.continuous.continuousOn
  let R := max C 0 + 1
  have hR : 0 < R := by positivity
  obtain ⟨g, K, hg, _, hLip, he⟩ :=
    hf.exists_lipschitzWith_compactSupport_eqOn_closedBall (by simp) 0 hR
  refine ⟨g, K, hg, (he (Metric.mem_closedBall_self hR.le)).trans hf0, hLip, ?_⟩
  intro t x
  apply he
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact ((Q t).norm_coe_le_norm x).trans
    ((hC t (mem_univ _)).trans ((le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one)))

/-- Cutting off on the scalar range preserves the mild equation. -/
theorem isMildSolutionOn_of_representative_eq (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0 = 0) {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {τ : ℝ≥0}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n k).IsMildSolutionOn (higherSmoothMap hk hf hf0) x τ V)
    (he : ∀ t y, f (classicalRepresentativeCLM hq (V t).1 y) =
      g (classicalRepresentativeCLM hq (V t).1 y)) :
    (higherLinearSemigroup n k).IsMildSolutionOn (higherSmoothMap hk hg hg0) x τ V := by
  intro t
  rw [hV t]
  congr 1
  apply (higherLinearSemigroup n k).duhamel_congr t.property.1
  intro s hs
  dsimp only
  erw [IccExtend_of_mem τ.property V ⟨hs.1, hs.2.trans t.property.2⟩]
  exact higherSmoothMap_eq_of_representative_eq hk hq hf hf0 hg hg0 _ (he _)

end WaveEquation.SmallData.Classical.NormBlowup
