/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothLifespan
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximalField
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.MaximalInitialData

/-!
# Maximal smooth waves in three dimensions

Smooth compact Cauchy data and an arbitrary smooth scalar reaction fixing zero construct one
canonical field on a positive maximal lifespan. The field is jointly smooth up to the initial face
and satisfies the pointwise wave equation. No classical solution with the same data has a longer
lifespan. At a finite lifespan, the displacement is unbounded on every terminal strip.

This combines both parts of Evans, §12.3.2, Theorem 2, under the standing hypotheses of §12.3.2.
Evans states the blow-up (12) as a limit of `‖u(·, t)‖_{L^∞(ℝ³)}`; at a finite maximal lifespan `T`
we prove that the displacement is unbounded on every strip `[a, T) × ℝ³`, which is what the
continuation argument of step 4 of his proof gives.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, standing hypotheses, Theorem 2 and step 4 of its
  proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Common Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

/-- Smooth compact data construct a maximal smooth wave with the prescribed
Cauchy traces. Its amplitude is unbounded on every terminal strip if the
lifespan is finite. -/
theorem exists_maximal_smooth_wave {f : ℝ → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (g h : ℝ^3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ L : ℝ≥0∞, 0 < L ∧ ∃ u : ℝ^4 → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) u {p | 0 ≤ p 0 ∧ ENNReal.ofReal (p 0) < L} ∧
      (∀ y, u (timeSpaceCons 0 y) = g y) ∧
      (∀ y, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t y)) (h y) (Ici 0) 0) ∧
      (∀ t : ℝ, 0 < t → ENNReal.ofReal t < L → ∀ y : ℝ^3,
        waveOperator u (timeSpaceCons t y) + f (u (timeSpaceCons t y)) = 0) ∧
      (∀ (T : ℝ) (v : ℝ^4 → ℝ),
        ContDiffOn ℝ 2 v {p | p 0 ∈ Ioo 0 T} →
        ContDiffOn ℝ 1 v {p | p 0 ∈ Ico 0 T} →
        (∀ t ∈ Ioo 0 T, ∀ y,
          waveOperator v (timeSpaceCons t y) + f (v (timeSpaceCons t y)) = 0) →
        (∀ y, v (timeSpaceCons 0 y) = g y) →
        (∀ y, derivWithin (fun t ↦ v (timeSpaceCons t y)) (Ici 0) 0 = h y) →
        ENNReal.ofReal T ≤ L) ∧
      (L ≠ ∞ → ∀ a < L.toReal, ∀ B : ℝ,
        ∃ t ∈ Ico (max 0 a) L.toReal, ∃ y, B < ‖u (timeSpaceCons t y)‖) := by
  have hk : (3 : ℝ) < 2 * ((3 : ℝ) - 1) := by norm_num
  have hv : (3 : ℝ) < 2 * (((3 + 1 : ℕ) : ℝ) - 1) := by norm_num
  have hq : (3 : ℝ) < 2 * (((3 + 2 : ℕ) : ℝ) - 1) := by norm_num
  let x : W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3) :=
    (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc)
  let S : StronglyContinuousSemigroup (W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3)) := higherLinearSemigroup 3 4
  let F : C(W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3), W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3)) := higherSmoothMap hv hs hf0
  let hlocal : LocallyLipschitz F := locallyLipschitz_higherSmoothSource hv hs hf0
  refine ⟨S.mildLifespan F x, S.mildLifespan_pos hlocal x, higherSmoothMaximalField hv hq hs hf0 x,
    contDiffOn_infty_higherSmoothMaximalField_of_smoothCompact
      (by norm_num : 3 < 4) hv hq hs hf0 g h hg hh hgc hhc, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [higherSmoothMaximalField_zero]
    exact congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) y
  · intro y
    have hd := hasDerivWithinAt_higherSmoothMaximalField_zero hk hv hq hs hf0 x y
    simpa only [x, classicalRepresentative_mkWkpSpaceOnOfContDiff] using hd
  · intro t ht htL y
    obtain ⟨τ, htτ, V, hV⟩ := (S.lt_mildLifespan_iff_exists_longer F x (τ := t.toNNReal)).mp htL
    have hτL := (S.lt_mildLifespan_iff hlocal x).mpr ⟨V, hV⟩
    exact higherSmoothMaximalField_wave_equation hk hv hq hs hf0 x hτL
      ⟨ht, (Real.toNNReal_lt_iff_lt_coe ht.le).mp htτ⟩ y
  · intro T v hv₂ hv₁ hvwave hvpos hvvel
    exact classical_time_le_higherSmooth_mildLifespan_of_smoothCompact
      (by norm_num : 3 < 4) hk hv hq hs hf0 g h hg hh hgc hhc hv₂ hv₁ hvwave hvpos hvvel
  · intro hfinite a ha B
    obtain ⟨t, ht, y, hy⟩ := higherSmooth_maximal_amplitude_unbounded_near_lifespan
      hv hq hs hf0 x hfinite ha B
    exact ⟨t, ht, y, by simpa only [higherSmoothMaximalField_timeSpaceCons] using hy⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
