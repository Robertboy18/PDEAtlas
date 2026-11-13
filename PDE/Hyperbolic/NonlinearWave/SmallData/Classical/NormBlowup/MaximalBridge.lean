/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Prefix
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Gluing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Continuation
import PDE.FDeriv.Calculus

/-!
# Classical observation before the maximal higher Sobolev lifetime

Every compact prefix of the constructed maximal mild trajectory has the
classical observation proved above. Classical overlap uniqueness glues these
observations, retaining both Sobolev components at every preterminal time.
The lifetime here is the higher Sobolev lifetime, not a supremum over
all C² competitors.
-/

@[expose] public noncomputable section

open PDE PDE.Common PDE.Analysis Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev Topology

namespace WaveEquation.SmallData.Classical.NormBlowup

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- Every compact positive prefix strictly below the constructed higher
lifespan is a classical wave with the same two Sobolev components. -/
theorem exists_classical_prefix_maximal (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (H : W^{k + 2,2}(ℝ^n)) {τ : ℝ≥0} (hτ : 0 < τ)
    (hlt : (τ : ℝ≥0∞) < (higherLinearSemigroup n (k + 1)).mildLifespan (higherSmoothMap hv hf hf0)
      (0, lowerOrderCLM (Nat.le_succ (k + 1)) H)) :
    ∃ u : ℝ^(n + 1) → ℝ,
      IsSolutionBefore f (fun _ ↦ 0) (classicalRepresentativeCLM hq H) (τ : ℝ) u ∧
        ∀ t ∈ Ico 0 (τ : ℝ), ∀ x,
          let U := (higherLinearSemigroup n (k + 1)).maximalMildSolution
            (F := higherSmoothMap hv hf hf0)
            (locallyLipschitz_higherSmoothSource hv hf hf0)
            (0, lowerOrderCLM (Nat.le_succ (k + 1)) H)
          u (timeSpaceCons t x) = classicalRepresentativeCLM hq (U t).1 x ∧
          (∂[0] u) (timeSpaceCons t x) = classicalRepresentativeCLM hv (U t).2 x := by
  let S := higherLinearSemigroup n (k + 1)
  obtain ⟨V, hV, he⟩ := S.exists_mildSolutionOn_eqOn_maximalMildSolution
      (F := higherSmoothMap hv hf hf0) (locallyLipschitz_higherSmoothSource hv hf hf0)
      (0, lowerOrderCLM (Nat.le_succ (k + 1)) H) hlt
  obtain ⟨u, hu, hrep⟩ := exists_classical_of_higher_mild hk hv hq hf hf0 H hτ V hV
  refine ⟨u, hu, fun t ht x ↦ ?_⟩
  have hr := hrep t ht x
  erw [he ⟨ht.1, ht.2.le⟩] at hr
  exact hr

/-- A finite higher Sobolev lifetime carries a classical wave up to
that time, linked to the constructed maximal mild trajectory. Finiteness of the
lifetime is a hypothesis here; the quadratic PDE results prove it separately. -/
theorem exists_classical_maximal_observation (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (H : W^{k + 2,2}(ℝ^n))
    (hfinite : (higherLinearSemigroup n (k + 1)).mildLifespan (higherSmoothMap hv hf hf0)
      (0, lowerOrderCLM (Nat.le_succ (k + 1)) H) ≠ ∞) :
    let S := higherLinearSemigroup n (k + 1)
    let F := higherSmoothMap hv hf hf0
    let X := (0, lowerOrderCLM (Nat.le_succ (k + 1)) H)
    let T := (S.mildLifespan F X).toReal
    let U := S.maximalMildSolution
      (F := F) (locallyLipschitz_higherSmoothSource hv hf hf0) X
    ∃ u : ℝ^(n + 1) → ℝ,
      IsSolutionBefore f (fun _ ↦ 0) (classicalRepresentativeCLM hq H) T u ∧
        ∀ t ∈ Ico 0 T, ∀ x,
          u (timeSpaceCons t x) = classicalRepresentativeCLM hq (U t).1 x ∧
          (∂[0] u) (timeSpaceCons t x) = classicalRepresentativeCLM hv (U t).2 x := by
  let : Fact (0 < n) := ⟨Nat.pos_of_ne_zero (NeZero.ne n)⟩
  intro S F X T U
  have hT : 0 < T := ENNReal.toReal_pos (ne_of_gt (S.mildLifespan_pos (F := F)
      (locallyLipschitz_higherSmoothSource hv hf hf0) X)) hfinite
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hlocal : LocallyLipschitz f := hf1.locallyLipschitz
  have hprefix (a : ℝ) (ha : 0 < a) (haT : a < T) : ∃ u : ℝ^(n + 1) → ℝ,
        IsSolutionBefore f (fun _ ↦ 0) (classicalRepresentativeCLM hq H) a u ∧ ∀ t ∈ Ico 0 a, ∀ x,
            u (timeSpaceCons t x) = classicalRepresentativeCLM hq (U t).1 x ∧
            (∂[0] u) (timeSpaceCons t x) = classicalRepresentativeCLM hv (U t).2 x :=
    exists_classical_prefix_maximal hk hv hq hf hf0 H
      (τ := ⟨a, ha.le⟩) (show (0 : ℝ≥0) < ⟨a, ha.le⟩ from ha)
      ((ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hfinite).mp haT)
  obtain ⟨a, ha, haT⟩ := exists_between hT
  obtain ⟨u₀, h₀, hrep₀⟩ := hprefix a ha haT
  let u := solutionUnion f (fun _ ↦ 0) (classicalRepresentativeCLM hq H) a u₀
  have hcover (b : ℝ) (hb : 0 < b) (hbT : b < T) :
      IsSolutionBefore f (fun _ ↦ 0) (classicalRepresentativeCLM hq H) b u := by
    obtain ⟨v, hv', _⟩ := hprefix b hb hbT
    exact isSolutionBefore_solutionUnion hlocal h₀ hv'
  have hbase := hcover a ha haT
  refine ⟨u, ⟨hT, ?_, ?_, hbase.position, hbase.velocity⟩, ?_⟩
  · intro p hp
    obtain ⟨b, hb, hbT⟩ := exists_between (max_lt hT hp)
    have hb0 := (le_max_left (0 : ℝ) (p 0)).trans_lt hb
    have hpb := (le_max_right (0 : ℝ) (p 0)).trans_lt hb
    exact ((hcover b hb0 hbT).regular.contDiffAt
      ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hpb))
      |>.contDiffWithinAt
  · intro p hp
    obtain ⟨b, hpb, hbT⟩ := exists_between hp.2
    exact (hcover b (hp.1.trans_lt hpb) hbT).equation p ⟨hp.1, hpb⟩
  · intro t ht x
    obtain ⟨b, htb, hbT⟩ := exists_between ht.2
    obtain ⟨v, hv', hrep⟩ := hprefix b (ht.1.trans_lt htb) hbT
    refine ⟨(solutionUnion_eq hlocal h₀ hv' (by simpa using And.intro ht.1 htb)).trans
      (hrep t ⟨ht.1, htb⟩ x).1, ?_⟩
    by_cases ht0 : 0 < t
    · rw [partialDeriv_congr_nhds 0
        (solutionUnion_eventuallyEq hlocal h₀ hv' (by simpa using And.intro ht0 htb))]
      exact (hrep t ⟨ht.1, htb⟩ x).2
    · have htz : t = 0 := le_antisymm (le_of_not_gt ht0) ht.1
      subst t
      rw [partialDeriv_congr_nhds 0
        (solutionUnion_eventuallyEq_initial (by simpa using half_pos ha))]
      exact (hrep₀ 0 ⟨le_rfl, ha⟩ x).2

end WaveEquation.SmallData.Classical.NormBlowup
