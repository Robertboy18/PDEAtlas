/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Caratheodory.Nonlinear
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Characteristics on a whole finite time interval

Joint continuity and a uniform global spatial Lipschitz bound construct a characteristic
on any closed finite time interval. The bound permits linear growth in space. The
nonlinear Volterra construction gives an integral curve, and the fundamental theorem
of calculus gives a classical derivative at every time, including the endpoints.
Reversing time constructs a path from terminal data.

A stationary boundary cannot be crossed: uniqueness prevents a path through a different
terminal point from touching the boundary, and the intermediate value theorem fixes
which side of the boundary the path occupies.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open PDE.Analysis.ODE

namespace PDE.Analysis.Evolution

/-- A continuous velocity with a uniform global spatial Lipschitz bound admits a
classical characteristic on any finite interval, with a prescribed initial point. -/
theorem exists_characteristic_Icc
    {t₀ T : ℝ} (hT : t₀ ≤ T) (b : ℝ → ℝ → ℝ)
    (hb : Continuous (Function.uncurry b)) (K : NNReal)
    (hK : ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ b x t)) (x₀ : ℝ) :
    ∃ path : ℝ → ℝ, Continuous path ∧ path t₀ = x₀ ∧
      ∀ t ∈ Icc t₀ T, HasDerivAt path (b (path t) t) t := by
  have hsection (x : ℝ) : Continuous (fun t ↦ b x t) :=
    hb.comp (continuous_const.prodMk continuous_id)
  obtain ⟨u, hu, _⟩ := existsUnique_nonlinear_integralCurve hT
    (fun t x ↦ b x t)
    (fun x ↦ (hsection x).measurable.indicator measurableSet_Icc) K hK
    ((hsection 0).continuousOn.integrableOn_Icc) x₀
  let q := Set.IccExtend hT u
  have hq : Continuous q := u.continuous.Icc_extend' (h := hT)
  have hg : Continuous (fun t ↦ b (q t) t) :=
    hb.comp (hq.prodMk continuous_id)
  let path : ℝ → ℝ := fun t ↦ x₀ + ∫ s in t₀..t, b (q s) s
  have heq (t : ℝ) (ht : t ∈ Icc t₀ T) : path t = q t := by
    rw [show q t = u ⟨t, ht⟩ from Set.IccExtend_of_mem hT u ht]
    exact (hu ⟨t, ht⟩).symm
  have hd (t : ℝ) : HasDerivAt path (b (q t) t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add x₀
  refine ⟨path, continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt),
    by simp [path], ?_⟩
  intro t ht
  simpa only [heq t ht] using hd t

/-- Terminal data also determine a classical characteristic on the entire interval.
This is a construction by time reversal of the nonlinear integral curve theorem. -/
theorem exists_backward_characteristic_Icc
    {t₀ T : ℝ} (hT : t₀ ≤ T) (b : ℝ → ℝ → ℝ)
    (hb : Continuous (Function.uncurry b)) (K : NNReal)
    (hK : ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ b x t)) (x : ℝ) :
    ∃ path : ℝ → ℝ, Continuous path ∧ path T = x ∧
      ∀ t ∈ Icc t₀ T, HasDerivAt path (b (path t) t) t := by
  have hrev (s : ℝ) (hs : s ∈ Icc (-T) (-t₀)) : -s ∈ Icc t₀ T := by
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨q, hq, hq₀, hq'⟩ := exists_characteristic_Icc (neg_le_neg hT)
    (fun y s ↦ -b y (-s))
    ((hb.comp (continuous_fst.prodMk continuous_snd.neg)).neg) K
    (fun s hs ↦ (hK (-s) (hrev s hs)).neg) x
  refine ⟨fun t ↦ q (-t), hq.comp continuous_neg, hq₀, ?_⟩
  intro t ht
  have ht' : -t ∈ Icc (-T) (-t₀) := ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  convert! (hq' (-t) ht').comp t (hasDerivAt_neg t) using 1
  simp

/-- A path with a terminal point different from a stationary boundary cannot touch
that boundary earlier. This follows from forward uniqueness at a hypothetical contact. -/
theorem characteristic_ne_boundary_of_terminal_ne
    {t₀ T B : ℝ} {b : ℝ → ℝ → ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ b x t))
    (hB : ∀ t ∈ Icc t₀ T, b B t = 0)
    {path : ℝ → ℝ}
    (hpath : ∀ t ∈ Icc t₀ T, HasDerivAt path (b (path t) t) t)
    (hterminal : path T ≠ B) {s : ℝ} (hs : s ∈ Icc t₀ T) :
    path s ≠ B := by
  have hcont : ContinuousOn path (Icc t₀ T) := fun t ht ↦
    (hpath t ht).continuousAt.continuousWithinAt
  intro heq
  have hsub : Icc s T ⊆ Icc t₀ T := Icc_subset_Icc_left hs.1
  have huniq := ODE_solution_unique_of_mem_Icc_right
    (v := fun t x ↦ b x t) (s := fun _ ↦ univ)
    (fun t ht ↦ (hK t (hsub (Ico_subset_Icc_self ht))).lipschitzOnWith)
    (hcont.mono hsub)
    (fun t ht ↦ (hpath t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt)
    (fun _ _ ↦ mem_univ _) continuousOn_const
    (fun t ht ↦ by
      simpa only [hB t (hsub (Ico_subset_Icc_self ht))] using
        (hasDerivAt_const t B).hasDerivWithinAt (s := Ici t))
    (fun _ _ ↦ mem_univ _) heq
  exact hterminal (huniq ⟨hs.2, le_rfl⟩)

/-- A characteristic ending strictly to the right of a stationary boundary stays
strictly to its right throughout the interval. -/
theorem boundary_lt_characteristic_of_lt_terminal
    {t₀ T B : ℝ} {b : ℝ → ℝ → ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ b x t))
    (hB : ∀ t ∈ Icc t₀ T, b B t = 0)
    {path : ℝ → ℝ}
    (hpath : ∀ t ∈ Icc t₀ T, HasDerivAt path (b (path t) t) t)
    (hterminal : B < path T) {s : ℝ} (hs : s ∈ Icc t₀ T) :
    B < path s := by
  have hcont : ContinuousOn path (Icc t₀ T) := fun t ht ↦
    (hpath t ht).continuousAt.continuousWithinAt
  by_contra h
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc hs.2
    (hcont.mono (Icc_subset_Icc_left hs.1)) ⟨le_of_not_gt h, hterminal.le⟩
  exact characteristic_ne_boundary_of_terminal_ne hK hB hpath
    hterminal.ne' ⟨hs.1.trans hr.1, hr.2⟩ heq

/-- A characteristic ending strictly to the left of a stationary boundary stays
strictly to its left throughout the interval. -/
theorem characteristic_lt_boundary_of_terminal_lt
    {t₀ T B : ℝ} {b : ℝ → ℝ → ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ b x t))
    (hB : ∀ t ∈ Icc t₀ T, b B t = 0)
    {path : ℝ → ℝ}
    (hpath : ∀ t ∈ Icc t₀ T, HasDerivAt path (b (path t) t) t)
    (hterminal : path T < B) {s : ℝ} (hs : s ∈ Icc t₀ T) :
    path s < B := by
  have hcont : ContinuousOn path (Icc t₀ T) := fun t ht ↦
    (hpath t ht).continuousAt.continuousWithinAt
  by_contra h
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc' hs.2
    (hcont.mono (Icc_subset_Icc_left hs.1)) ⟨hterminal.le, le_of_not_gt h⟩
  exact characteristic_ne_boundary_of_terminal_ne hK hB hpath
    hterminal.ne ⟨hs.1.trans hr.1, hr.2⟩ heq

end PDE.Analysis.Evolution
