/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike

import Mathlib.Analysis.ODE.ExistUnique

/-!
# Half-line ranges, uniqueness, and isolated orbit segments

A limit and an attained endpoint determine the range of a continuous half-line
profile. These ranges turn isolation of an orbit's middle passage into avoidance
of two closed axis images, including their limiting endpoint. Two solutions of a
`C¹` autonomous equation on a half-line `(-∞, c]` or `[c, ∞)` that agree at `c`
agree on the whole half-line.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- A continuous half-line profile with limiting lower endpoint and attained upper
endpoint fills the half-open interval between them. Monotonicity is unnecessary. -/
theorem image_Iic_eq_Ioc_of_tendsto_atBot {z : ℝ → ℝ} {c a b : ℝ}
    (hz : ContinuousOn z (Iic c)) (hbound : MapsTo z (Iic c) (Ioc a b))
    (hanchor : z c = b) (hlim : Tendsto z atBot (𝓝 a)) :
    z '' Iic c = Ioc a b := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact hbound ht
  · have hl : atBot ≤ 𝓟 (Iic c) :=
      le_principal_iff.mpr (eventually_le_atBot c)
    simpa only [hanchor] using
      isPreconnected_Iic.intermediate_value_Ioc (show c ∈ Iic c from le_rfl) hl hz hlim

/-- The same range statement for a profile tending to its lower endpoint as time
increases. The attained upper endpoint is included in the image. -/
theorem image_Ici_eq_Ioc_of_tendsto_atTop {z : ℝ → ℝ} {c a b : ℝ}
    (hz : ContinuousOn z (Ici c)) (hbound : MapsTo z (Ici c) (Ioc a b))
    (hanchor : z c = b) (hlim : Tendsto z atTop (𝓝 a)) :
    z '' Ici c = Ioc a b := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact hbound ht
  · have hl : atTop ≤ 𝓟 (Ici c) :=
      le_principal_iff.mpr (eventually_ge_atTop c)
    simpa only [hanchor] using
      isPreconnected_Ici.intermediate_value_Ioc (show c ∈ Ici c from le_rfl) hl hz hlim

/-- An open set whose visits have a lower time bound cannot contain the incoming
limit of an orbit. No continuity of the orbit away from that limit is needed. -/
theorem notMem_open_of_tendsto_atBot_of_preimage_subset
    {X : Type*} [TopologicalSpace X] {q : ℝ → X} {U : Set X} {p : X} {a : ℝ}
    (hU : IsOpen U) (hlim : Tendsto q atBot (𝓝 p)) (hpre : q ⁻¹' U ⊆ Ioi a) :
    p ∉ U := by
  intro hp
  have hevent : ∀ᶠ t in atBot, q t ∈ U := hlim.eventually (hU.mem_nhds hp)
  obtain ⟨t, htU, hta⟩ := (hevent.and (eventually_le_atBot a)).exists
  exact (not_lt_of_ge hta) (hpre htU)

/-- Let `q → 0` as `t → -∞`, with `q t = left (zin t)` for `t ≤ 0` and
`q (t + 2e) = right (zout t)` for `t ≥ 0`, where `zin` maps `(-∞, 0]` and `zout` maps
`[0, ∞)` onto `(0, 1]` and `left 0 = right 0 = 0`. If `q` visits the open set `U`
only at times in `J ⊆ (0, e)`, then `U` misses `left '' [0, 1]` and
`right '' [0, 1]`. The point `0` is excluded by the limit at `-∞`. -/
theorem disjoint_closed_axis_images_of_isolated_orbit
    {E : Type*} [TopologicalSpace E] [Zero E]
    {q left right : ℝ → E} {zin zout : ℝ → ℝ} {e : ℝ} {J : Set ℝ} {U : Set E}
    (he : 0 ≤ e) (hU : IsOpen U) (hpre : q ⁻¹' U ⊆ J) (hJ : J ⊆ Ioo 0 e)
    (hlim : Tendsto q atBot (𝓝 0)) (hleftzero : left 0 = 0) (hrightzero : right 0 = 0)
    (hinrange : zin '' Iic 0 = Ioc 0 1) (houtrange : zout '' Ici 0 = Ioc 0 1)
    (hleft : ∀ t ≤ 0, q t = left (zin t))
    (hright : ∀ t ≥ 0, q (t + 2 * e) = right (zout t)) :
    Disjoint (left '' Icc 0 1) U ∧ Disjoint (right '' Icc 0 1) U := by
  have hzero : (0 : E) ∉ U :=
    notMem_open_of_tendsto_atBot_of_preimage_subset hU hlim
      (fun _ ht ↦ (hJ (hpre ht)).1)
  constructor
  · apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ hsU
    by_cases hs0 : s = 0
    · subst s
      exact hzero (by simpa only [hleftzero] using hsU)
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      obtain ⟨t, ht, hts⟩ := hinrange.symm ▸ (show s ∈ Ioc 0 1 from ⟨hspos, hs.2⟩)
      have hqt : q t ∈ U := by
        rw [hleft t ht, hts]
        exact hsU
      exact (not_lt_of_ge ht) (hJ (hpre hqt)).1
  · apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ hsU
    by_cases hs0 : s = 0
    · subst s
      exact hzero (by simpa only [hrightzero] using hsU)
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      obtain ⟨t, ht, hts⟩ := houtrange.symm ▸ (show s ∈ Ioc 0 1 from ⟨hspos, hs.2⟩)
      have hqt : q (t + 2 * e) ∈ U := by
        rw [hright t ht, hts]
        exact hsU
      have he_le : e ≤ t + 2 * e := by
        calc
          e ≤ e + e := le_add_of_nonneg_right he
          _ = 2 * e := (two_mul e).symm
          _ ≤ t + 2 * e := le_add_of_nonneg_left ht
      exact (not_lt_of_ge he_le) (hJ (hpre hqt)).2

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two solutions of `x' = f x` on `(-∞, c]` with `q c = r c` agree on `(-∞, c]`,
for `C¹` `f`. -/
theorem eqOn_Iic_of_hasDerivAt_of_eq {f : E → E} {q r : ℝ → E} {c : ℝ}
    (hf : ContDiff ℝ 1 f)
    (hq : ∀ t ≤ c, HasDerivAt q (f (q t)) t)
    (hr : ∀ t ≤ c, HasDerivAt r (f (r t)) t) (hinit : q c = r c) :
    EqOn q r (Iic c) := by
  intro t ht
  have hqc : ContinuousOn q (Icc t c) :=
    HasDerivAt.continuousOn (fun s hs ↦ hq s hs.2)
  have hrc : ContinuousOn r (Icc t c) :=
    HasDerivAt.continuousOn (fun s hs ↦ hr s hs.2)
  let S : Set E := q '' Icc t c ∪ r '' Icc t c
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hqc).union
      (isCompact_Icc.image_of_continuousOn hrc)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
    hf.locallyLipschitz.locallyLipschitzOn
  have hagree : EqOn q r (Icc t c) :=
    ODE_solution_unique_of_mem_Icc_left (v := fun _ x ↦ f x) (s := fun _ ↦ S)
      (fun _ _ ↦ hC) hqc (fun s hs ↦ (hq s hs.2).hasDerivWithinAt)
      (fun s hs ↦ Or.inl ⟨s, Ioc_subset_Icc_self hs, rfl⟩)
      hrc (fun s hs ↦ (hr s hs.2).hasDerivWithinAt)
      (fun s hs ↦ Or.inr ⟨s, Ioc_subset_Icc_self hs, rfl⟩) hinit
  exact hagree ⟨le_rfl, ht⟩

/-- Two solutions of `x' = f x` on `[c, ∞)` with `q c = r c` agree on `[c, ∞)`,
for `C¹` `f`. -/
theorem eqOn_Ici_of_hasDerivAt_of_eq {f : E → E} {q r : ℝ → E} {c : ℝ}
    (hf : ContDiff ℝ 1 f)
    (hq : ∀ t ≥ c, HasDerivAt q (f (q t)) t)
    (hr : ∀ t ≥ c, HasDerivAt r (f (r t)) t) (hinit : q c = r c) :
    EqOn q r (Ici c) := by
  intro t ht
  have hqc : ContinuousOn q (Icc c t) :=
    HasDerivAt.continuousOn (fun s hs ↦ hq s hs.1)
  have hrc : ContinuousOn r (Icc c t) :=
    HasDerivAt.continuousOn (fun s hs ↦ hr s hs.1)
  let S : Set E := q '' Icc c t ∪ r '' Icc c t
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hqc).union
      (isCompact_Icc.image_of_continuousOn hrc)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
    hf.locallyLipschitz.locallyLipschitzOn
  have hagree : EqOn q r (Icc c t) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ x ↦ f x) (s := fun _ ↦ S)
      (fun _ _ ↦ hC) hqc (fun s hs ↦ (hq s hs.1).hasDerivWithinAt)
      (fun s hs ↦ Or.inl ⟨s, Ico_subset_Icc_self hs, rfl⟩)
      hrc (fun s hs ↦ (hr s hs.1).hasDerivWithinAt)
      (fun s hs ↦ Or.inr ⟨s, Ico_subset_Icc_self hs, rfl⟩) hinit
  exact hagree ⟨ht, le_rfl⟩

end ODE

end PDE.Analysis
