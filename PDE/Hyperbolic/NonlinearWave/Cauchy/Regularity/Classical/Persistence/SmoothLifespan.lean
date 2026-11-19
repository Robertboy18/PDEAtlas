/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardSupport
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothComparison
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximal

/-!
# Classical maximality of the smooth higher Sobolev wave

A classical solution with smooth compact data cannot exist beyond the maximal
higher Sobolev lifetime. Finite propagation bounds its amplitude on every
proper closed strip. Classical uniqueness transfers that bound to the canonical
higher trajectory, whose amplitude continuation criterion excludes a finite
lifetime inside the strip.
-/

@[expose] public noncomputable section

open PDE.Common Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- No classical wave with the same smooth compact data exists beyond the
canonical higher Sobolev lifespan. Together with all-orders persistence of
the canonical trajectory, this identifies its lifespan as the smooth lifespan. -/
theorem classical_time_le_higherSmooth_mildLifespan_of_smoothCompact (hn : n < 4)
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {T : ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T}) (hu₀ : ContDiffOn ℝ 1 u {p | p 0 ∈ Ico 0 T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    ENNReal.ofReal T ≤ (higherLinearSemigroup n (k + 1)).mildLifespan (higherSmoothMap hv hs hf0)
      (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc) := by
  let : Fact (0 < n) := ⟨NeZero.pos n⟩
  let x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) :=
    (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc)
  let S : StronglyContinuousSemigroup (W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :=
    higherLinearSemigroup n (k + 1)
  let F : C(W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n),
      W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) := higherSmoothMap hv hs hf0
  let hlocal : LocallyLipschitz F := locallyLipschitz_higherSmoothSource hv hs hf0
  let U : ℝ → W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) := S.maximalMildSolution hlocal x
  change ENNReal.ofReal T ≤ S.mildLifespan F x
  by_contra hle
  have hLT : S.mildLifespan F x < ENNReal.ofReal T := lt_of_not_ge hle
  have hfinite : S.mildLifespan F x ≠ ∞ := ne_top_of_lt hLT
  have hT : 0 < T := ENNReal.ofReal_pos.mp ((S.mildLifespan_pos hlocal x).trans hLT)
  have hbT : (S.mildLifespan F x).toReal < T := by
    have := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hLT
    simpa only [ENNReal.toReal_ofReal hT.le] using this
  obtain ⟨B, -, hbound⟩ := exists_amplitude_bound_on_proper_strip
    ((hs.of_le (by simp)).locallyLipschitz) hf0 hu hu₀ hwave hpos hvel hgc hhc hbT
  apply hfinite
  refine higherSmooth_mildLifespan_eq_top_of_amplitude (B := B) hv hq hs hf0 x fun t ht htl y ↦ ?_
  obtain ⟨τ, htτ, V, hV⟩ := (S.lt_mildLifespan_iff_exists_longer F x (τ := t.toNNReal)).mp htl
  have htτ' : t < (τ : ℝ) := (Real.toNNReal_lt_iff_lt_coe ht).mp htτ
  have hτL := (S.lt_mildLifespan_iff hlocal x).mpr ⟨V, hV⟩
  have hτT : (τ : ℝ) < T := by
    have : (τ : ℝ≥0∞) < ENNReal.ofReal T := hτL.trans hLT
    apply (ENNReal.ofReal_lt_ofReal_iff hT).mp
    simpa only [ENNReal.ofReal_coe_nnreal] using this
  have heq := eq_classical_higherSmooth_trajectory_of_smoothCompact
    hn hk hv hq hs hf0 g h hg hh hgc hhc (ht.trans_lt htτ') hτT.le
    V hV hu hu₀ hwave hpos hvel t ⟨ht, htτ'⟩ y
  have hU := StronglyContinuousSemigroup.maximalMildSolution_eqOn hlocal hV ⟨ht, htτ'.le⟩
  change ‖classicalRepresentativeCLM hq (U t).1 y‖ ≤ B
  rw [show U t = IccExtend τ.property V t from hU, ← heq]
  exact hbound t ⟨ht, ((ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mp htl).le⟩ y

end PDE.Hyperbolic.NonlinearWave.Cauchy
