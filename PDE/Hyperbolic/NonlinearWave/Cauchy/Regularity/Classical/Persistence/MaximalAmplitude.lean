/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Amplitude

/-!
# Amplitude obstruction at the maximal higher Sobolev lifetime

The tame composition estimate and Grönwall turn bounded displacement amplitude into bounded higher
Sobolev norm. Applying the continuation theorem to the constructed maximal trajectory forces its
amplitude to be unbounded in every terminal time interval when the lifetime is finite.

This is the blow-up alternative of Evans, §12.3.2, Theorem 2(ii), for the higher Sobolev evolution.
Evans states the conclusion (12) as a limit of `‖u(·, t)‖_{L^∞(ℝ³)}`. Step 4 of his proof continues
the solution whenever the amplitude stays bounded, and that argument gives the form we prove: the
amplitude is unbounded on every terminal time interval. Where Evans bounds the derivatives by
difference quotients and Grönwall's inequality in step 3, we bound the higher Sobolev norm by the
tame composition estimate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, Theorem 2(ii), equation (12), and steps 3-4 of its
  proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- A uniform amplitude bound gives a global higher Sobolev trajectory for a
smooth scalar reaction fixing zero. No global Lipschitz bound on the reaction
is required. -/
theorem higherSmooth_mildLifespan_eq_top_of_amplitude (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) {B : ℝ}
    (hamp : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < (higherLinearSemigroup n k).mildLifespan
      (higherSmoothMap hk hs hf0) x → ∀ y, ‖classicalRepresentativeCLM hq
      ((higherLinearSemigroup n k).maximalMildSolution (F := higherSmoothMap hk hs hf0)
      (locallyLipschitz_higherSmoothSource hk hs hf0) x t).1 y‖ ≤ B) :
    (higherLinearSemigroup n k).mildLifespan (higherSmoothMap hk hs hf0) x = ∞ := by
  by_contra hfinite
  let S := higherLinearSemigroup n k
  let F := higherSmoothMap hk hs hf0
  let hlocal : LocallyLipschitz F := locallyLipschitz_higherSmoothSource hk hs hf0
  have hb : 0 < (S.mildLifespan F x).toReal :=
    ENNReal.toReal_pos (ne_of_gt (S.mildLifespan_pos hlocal x)) hfinite
  have hu := S.isMildSolutionBefore_maximalMildSolution hlocal x hfinite
  obtain ⟨ρ, hρ, v, hv, _⟩ :=
    exists_higherSmooth_extension_of_amplitude hk hq hs hf0 hu hb (fun t ht ↦
      hamp t ht.1 ((ENNReal.ofReal_lt_iff_lt_toReal ht.1 hfinite).mpr ht.2))
  exact S.not_exists_mildSolutionOn_at_or_after_lifespan hlocal x hfinite ⟨ρ, hρ.le, v, hv⟩

/-- Before a finite maximal higher Sobolev lifetime, every terminal time strip
contains a displacement value exceeding any prescribed amplitude. This is
terminal-interval unboundedness, not a pointwise-in-time limit assertion. -/
theorem higherSmooth_maximal_amplitude_unbounded_near_lifespan (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    (hfinite : (higherLinearSemigroup n k).mildLifespan (higherSmoothMap hk hs hf0) x ≠ ∞) {a : ℝ}
    (ha : a < ((higherLinearSemigroup n k).mildLifespan (higherSmoothMap hk hs hf0) x).toReal)
    (B : ℝ) :
    ∃ t ∈ Ico (max 0 a) ((higherLinearSemigroup n k).mildLifespan
        (higherSmoothMap hk hs hf0) x).toReal,
      ∃ y, B < ‖classicalRepresentativeCLM hq
        ((higherLinearSemigroup n k).maximalMildSolution
          (F := higherSmoothMap hk hs hf0)
          (locallyLipschitz_higherSmoothSource hk hs hf0) x t).1 y‖ := by
  let S := higherLinearSemigroup n k
  let F := higherSmoothMap hk hs hf0
  let hlocal : LocallyLipschitz F := locallyLipschitz_higherSmoothSource hk hs hf0
  let u := S.maximalMildSolution hlocal x
  let b := (S.mildLifespan F x).toReal
  have hb : 0 < b := ENNReal.toReal_pos (ne_of_gt (S.mildLifespan_pos hlocal x)) hfinite
  have hu := S.isMildSolutionBefore_maximalMildSolution hlocal x hfinite
  have hab : max 0 a < b := max_lt hb ha
  by_contra! hbound
  have hc : ContinuousOn (fun t ↦ classicalRepresentativeCLM hq (u t).1) (Icc 0 (max 0 a)) :=
    (classicalRepresentativeCLM hq).continuous.comp_continuousOn
      ((hu.continuousOn.mono fun t ht ↦ ⟨ht.1, ht.2.trans_lt hab⟩).fst)
  obtain ⟨R, hR⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_norm_le
  apply hfinite
  apply higherSmooth_mildLifespan_eq_top_of_amplitude hk hq hs hf0 x
    (B := max 0 (max R B))
  intro t ht htb y
  have htb' : t < b := (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mp htb
  by_cases hta : t ≤ max 0 a
  · exact ((classicalRepresentativeCLM hq (u t).1).norm_coe_le_norm y).trans
      ((hR _ ⟨t, ⟨ht, hta⟩, rfl⟩).trans ((le_max_left R B).trans (le_max_right 0 _)))
  · exact (hbound t ⟨(not_le.mp hta).le, htb'⟩ y).trans
      ((le_max_right R B).trans (le_max_right 0 _))

end PDE.Hyperbolic.NonlinearWave.Cauchy
