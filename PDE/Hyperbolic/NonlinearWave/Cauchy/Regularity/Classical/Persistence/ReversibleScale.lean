/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.ScaleSmoothness
public import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Smooth gluing of reversible evolution scales

Forward trajectories with opposite velocity can be reflected and glued at
zero. Continuity of the vector field gives the derivative at the joining time
by Mathlib's removable-point theorem. Smoothness then follows simultaneously
at every level of the scale, including the initial time.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Join a forward curve to a reflected curve with the same initial state. -/
def reversibleGluing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E →L[ℝ] E) (u v : C(ℝ, E)) (hzero : u 0 = R (v 0)) : C(ℝ, E) := by
  classical
  refine ⟨(Ici (0 : ℝ)).piecewise u (fun t ↦ R (v (-t))), ?_⟩
  apply continuous_piecewise _ u.continuous.continuousOn
    (R.continuous.comp (v.continuous.comp continuous_neg)).continuousOn
  intro t ht
  have ht0 : t = 0 := by simpa only [frontier_Ici, mem_singleton_iff] using ht
  simpa only [ht0, neg_zero, Function.comp_apply] using hzero

/-- The glued trajectory keeps the original forward values, including at zero. -/
theorem reversibleGluing_of_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E →L[ℝ] E) (u v : C(ℝ, E)) (hzero : u 0 = R (v 0))
    {t : ℝ} (ht : 0 ≤ t) : reversibleGluing R u v hzero t = u t := by
  simp only [reversibleGluing, ContinuousMap.coe_mk, piecewise_eq_of_mem _ _ _ (mem_Ici.mpr ht)]

/-- At negative times the gluing uses the reflected trajectory. -/
theorem reversibleGluing_of_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E →L[ℝ] E) (u v : C(ℝ, E)) (hzero : u 0 = R (v 0))
    {t : ℝ} (ht : t < 0) : reversibleGluing R u v hzero t = R (v (-t)) := by
  classical
  change (Ici (0 : ℝ)).piecewise u (fun s ↦ R (v (-s))) t = R (v (-t))
  exact piecewise_eq_of_notMem _ _ _ (show t ∉ Ici (0 : ℝ) from not_le.mpr ht)

/-- Reversible smooth equations on a scale give a jointly chosen family of
smooth time curves across the initial time, with no loss in the interval. -/
theorem contDiff_reversibleGluing {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, NormedSpace ℝ (E j)] (next : ℕ → ℕ) (R : ∀ j, E j →L[ℝ] E j) (F : ∀ j, E (next j) → E j)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j)) (hR : ∀ j z, F j (R (next j) z) = -R j (F j z))
    (u v : ∀ j, C(ℝ, E j)) (hzero : ∀ j, u j 0 = R j (v j 0))
    (hu : ∀ j t, 0 < t → HasDerivAt (u j) (F j (u (next j) t)) t)
    (hv : ∀ j t, 0 < t → HasDerivAt (v j) (F j (v (next j) t)) t) :
    ∀ j, ContDiff ℝ (⊤ : ℕ∞) (reversibleGluing (R j) (u j) (v j) (hzero j)) := by
  let U (j : ℕ) := reversibleGluing (R j) (u j) (v j) (hzero j)
  have hdiff (j : ℕ) (t : ℝ) (ht : t ≠ 0) :
      HasDerivAt (U j) (F j (U (next j) t)) t := by
    rcases lt_or_gt_of_ne ht with ht | ht
    · have hd := (hv j (-t) (neg_pos.mpr ht)).scomp t (hasDerivAt_id t).neg
      have hdR := (R j).hasFDerivAt.comp_hasDerivAt t hd
      have hval : F j (U (next j) t) = -R j (F j (v (next j) (-t))) := by
        dsimp only [U]
        rw [reversibleGluing_of_neg _ _ _ _ ht, hR]
      rw [hval]
      have hdR' : HasDerivAt (fun s ↦ R j (v j (-s)))
          (-R j (F j (v (next j) (-t)))) t := by
        convert hdR using 1 <;> simp only [Function.comp_def, neg_smul, one_smul, map_neg]
      apply hdR'.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds ht] with s hs using reversibleGluing_of_neg _ _ _ _ hs
    · have hval : F j (U (next j) t) = F j (u (next j) t) := by
        congr 1
        exact reversibleGluing_of_nonneg _ _ _ _ ht.le
      rw [hval]
      apply (hu j t ht).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht] with s hs using reversibleGluing_of_nonneg _ _ _ _ hs.le
  have hd (j : ℕ) (t : ℝ) : HasDerivAt (U j) (F j (U (next j) t)) t :=
    hasDerivAt_of_hasDerivAt_of_ne' (hdiff j) (U j).continuous.continuousAt
      ((hF j).continuous.comp (U (next j)).continuous).continuousAt t
  have hs := contDiffOn_scale_of_hasDerivAt isOpen_univ next (fun j ↦ U j) F
    (fun j ↦ (U j).continuous.continuousOn) hF (fun j t _ ↦ hd j t)
  exact fun j ↦ contDiffOn_univ.mp (hs j)

end PDE.Hyperbolic.NonlinearWave.Cauchy
