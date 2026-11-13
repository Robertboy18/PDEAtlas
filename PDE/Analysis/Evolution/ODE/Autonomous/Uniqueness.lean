/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Uniqueness for autonomous fields Lipschitz on bounded balls

Two continuous curves on a compact time interval have bounded combined image, even
when the state space is infinite dimensional. A Lipschitz bound on a ball containing
that image reduces uniqueness to Mathlib's trajectory comparison theorem.
-/

@[expose] public section

open Metric Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A field Lipschitz on every bounded ball has unique classical trajectories on a
compact interval, with the initial time anywhere in its interior. -/
theorem eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls {F : E → E}
    (hF : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K F (closedBall 0 R))
    {f g : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (F (f t)) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (F (g t)) t)
    (hzero : f t₀ = g t₀) : EqOn f g (Icc a b) := by
  have hc : IsCompact (f '' Icc a b ∪ g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hf).union
      (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨R, hR, hball⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : E)
  obtain ⟨K, hK⟩ := hF R hR
  exact ODE_solution_unique_of_mem_Icc (v := fun _ ↦ F)
    (s := fun _ ↦ closedBall 0 R) (fun _ _ ↦ hK) ht₀ hf hf'
    (fun t ht ↦ hball (Or.inl ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)) hg hg'
    (fun t ht ↦ hball (Or.inr ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)) hzero

/-- Classical trajectories agree on an open interval once they agree at one time.
Only the images of compact subintervals need to be bounded. -/
theorem eqOn_Ioo_of_hasDerivAt_of_lipschitzOn_balls {F : E → E}
    (hF : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K F (closedBall 0 R))
    {f g : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (F (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (F (g t)) t)
    (hzero : f t₀ = g t₀) : EqOn f g (Ioo a b) := by
  intro t ht
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min ht₀.1 ht.1)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt ht₀.2 ht.2)
  have hsub : Icc a' b' ⊆ Ioo a b :=
    fun _ hs ↦ ⟨haa'.trans_le hs.1, hs.2.trans_lt hb'b⟩
  exact eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls hF
    ⟨ha'.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb'⟩
    (fun s hs ↦ (hf s (hsub hs)).continuousAt.continuousWithinAt)
    (fun s hs ↦ hf s (hsub (Ioo_subset_Icc_self hs)))
    (fun s hs ↦ (hg s (hsub hs)).continuousAt.continuousWithinAt)
    (fun s hs ↦ hg s (hsub (Ioo_subset_Icc_self hs)))
    hzero
    ⟨(ha'.trans_le (min_le_right _ _)).le, ((le_max_right _ _).trans_lt hb').le⟩

/-- Whole-line classical trajectories of a field Lipschitz on bounded balls agree
when they agree at one time. No bound on either whole trajectory is assumed. -/
theorem eq_of_hasDerivAt_of_lipschitzOn_balls {F : E → E}
    (hF : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K F (closedBall 0 R))
    {f g : ℝ → E} {t₀ : ℝ}
    (hf : ∀ t, HasDerivAt f (F (f t)) t)
    (hg : ∀ t, HasDerivAt g (F (g t)) t)
    (hzero : f t₀ = g t₀) : f = g := by
  funext t
  apply eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls hF
    (a := min t₀ t - 1) (b := max t₀ t + 1)
    (by constructor <;> linarith [min_le_left t₀ t, le_max_left t₀ t])
    (continuous_iff_continuousAt.mpr (fun s ↦ (hf s).continuousAt)).continuousOn
    (fun s _ ↦ hf s)
    (continuous_iff_continuousAt.mpr (fun s ↦ (hg s).continuousAt)).continuousOn
    (fun s _ ↦ hg s) hzero
  constructor <;> linarith [min_le_right t₀ t, le_max_right t₀ t]

end PDE.Analysis.Evolution
