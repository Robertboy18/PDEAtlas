/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Bounded.Flow

/-!
# Scalar flows between two equilibria

A field that is C¹ on a closed interval has a bounded Lipschitz extension obtained
by interval projection. Its global flow fixes the endpoint equilibria. Injectivity
of each flow map and the intermediate value theorem keep every interior orbit
strictly inside the interval, where it solves the original equation.
-/

@[expose] public noncomputable section

open Metric Set

namespace PDE.Analysis.Evolution.Scalar

/-- Closed-interval C¹ data with two endpoint equilibria generate a continuous
whole-line flow whose interior orbits solve the original scalar equation. -/
theorem exists_flow_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContDiffOn ℝ 1 f (Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    ∃ Φ : Flow ℝ ℝ,
      (∀ t, Φ t a = a) ∧ (∀ t, Φ t b = b) ∧
      (∀ z ∈ Ioo a b, ∀ t, Φ t z ∈ Ioo a b) ∧
      ∀ z ∈ Ioo a b, ∀ t, HasDerivAt (fun s ↦ Φ s z) (f (Φ t z)) t := by
  let g : ℝ → ℝ := IccExtend hab.le (fun z : Icc a b ↦ f z)
  have hgeq {z : ℝ} (hz : z ∈ Icc a b) : g z = f z :=
    IccExtend_of_mem hab.le _ hz
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc a b)
    isCompact_Icc
  have hLip : LipschitzWith K g := by
    intro x y
    simpa only [g, IccExtend, mul_one, Function.comp_apply, domRestrict_apply] using
      (hK.to_restrict.comp (LipschitzWith.projIcc hab.le)) x y
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  have hbound (z : ℝ) : ‖g z‖ ≤ (⟨max M 0, le_max_right M 0⟩ : NNReal) :=
    (hM _ (projIcc a b hab.le z).property).trans (le_max_left M 0)
  have hlocal : ∀ R : ℝ, 0 < R → ∃ C : NNReal,
      LipschitzOnWith C g (closedBall 0 R) :=
    fun _ _ ↦ ⟨K, hLip.lipschitzOnWith⟩
  obtain ⟨Φ, hΦ⟩ := exists_flow_hasDerivAt_of_bounded hbound hlocal
  have hfix (z : ℝ) (hz : g z = 0) (t : ℝ) : Φ t z = z := by
    have heq : (fun s ↦ Φ s z) = fun _ : ℝ ↦ z := by
      apply eq_of_hasDerivAt_of_lipschitzOn_balls hlocal (t₀ := 0) (hΦ z)
      · intro s
        simpa only [hz] using hasDerivAt_const s z
      · exact Φ.map_zero_apply z
    exact congrFun heq t
  have hfa := hfix a ((hgeq (left_mem_Icc.mpr hab.le)).trans ha)
  have hfb := hfix b ((hgeq (right_mem_Icc.mpr hab.le)).trans hb)
  have hmem (z : ℝ) (hz : z ∈ Ioo a b) (t : ℝ) : Φ t z ∈ Ioo a b := by
    have hnea (s : ℝ) : Φ s z ≠ a := by
      intro heq
      exact hz.1.ne' ((Φ.toHomeomorph s).injective (heq.trans (hfa s).symm))
    have hneb (s : ℝ) : Φ s z ≠ b := by
      intro heq
      exact hz.2.ne ((Φ.toHomeomorph s).injective (heq.trans (hfb s).symm))
    have hc : Continuous (fun s : ℝ ↦ Φ s z) :=
      Φ.continuous continuous_id continuous_const
    constructor
    · by_contra h
      have hbetween : a ∈ Icc (Φ t z) (Φ 0 z) :=
        ⟨le_of_not_gt h, by simpa using hz.1.le⟩
      obtain ⟨s, hs⟩ := intermediate_value_univ t 0 hc hbetween
      exact hnea s hs
    · by_contra h
      have hbetween : b ∈ Icc (Φ 0 z) (Φ t z) :=
        ⟨by simpa using hz.2.le, le_of_not_gt h⟩
      obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hc hbetween
      exact hneb s hs
  refine ⟨Φ, hfa, hfb, hmem, ?_⟩
  intro z hz t
  simpa only [hgeq ⟨(hmem z hz t).1.le, (hmem z hz t).2.le⟩] using hΦ z t

end PDE.Analysis.Evolution.Scalar
