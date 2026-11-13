/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothTrajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.MaximalAmplitude

/-!
# All-orders regularity before the higher Sobolev lifespan

Every compact prefix of the maximal higher Sobolev trajectory has a smooth
representative when the initial data are smooth and compactly supported.
Locality of smoothness gives one jointly smooth field throughout the maximal
forward domain, including its initial face.
-/

@[expose] public noncomputable section

open Filter Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- The canonical field of the maximal higher trajectory retains every order
from smooth compact Cauchy data at all preterminal times, including time zero. -/
theorem contDiffOn_infty_maximalHigherSmooth_of_smoothCompact (hn : n < 4)
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    let x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) :=
      (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc)
    let S : StronglyContinuousSemigroup (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
      higherLinearSemigroup n k
    let F : C(W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n),
        W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) := higherSmoothMap hk hs hf0
    let U : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) := S.maximalMildSolution (F := F)
      (locallyLipschitz_higherSmoothSource hk hs hf0) x
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hq (U p.1).1 p.2)
      ({t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < S.mildLifespan F x} ×ˢ univ) := by
  intro x S F U
  let hlocal : LocallyLipschitz F := locallyLipschitz_higherSmoothSource hk hs hf0
  intro p hp
  obtain ⟨τ, hpτ, V, hV⟩ :=
    (S.lt_mildLifespan_iff_exists_longer F x (τ := p.1.toNNReal)).mp hp.1.2
  have hpt : p.1 < (τ : ℝ) := (Real.toNNReal_lt_iff_lt_coe hp.1.1).mp hpτ
  have hfield := contDiffOn_infty_higherSmooth_trajectory_of_smoothCompact
    hn hk hq hs hf0 g h hg hh hgc hhc V hV
  have heq : EqOn U (IccExtend τ.property V) (Icc 0 (τ : ℝ)) :=
    StronglyContinuousSemigroup.maximalMildSolution_eqOn (T := S) (F := F) hlocal hV
  have hlocalField : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ^n ↦ classicalRepresentativeCLM hq (U q.1).1 q.2)
      (Icc 0 (τ : ℝ) ×ˢ univ) := by
    apply hfield.congr
    intro q hq'
    exact congrArg (fun z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) ↦
      classicalRepresentativeCLM hq z.1 q.2) (heq hq'.1)
  apply (hlocalField p ⟨⟨hp.1.1, hpt.le⟩, hp.2⟩).mono_of_mem_nhdsWithin
  have hsmall : ∀ᶠ q : ℝ × ℝ^n in 𝓝 p, q.1 < (τ : ℝ) :=
    continuous_fst.continuousAt (Iio_mem_nhds hpt)
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds]
    with q hq' hqt
  exact ⟨⟨hq'.1.1, hqt.le⟩, mem_univ _⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
