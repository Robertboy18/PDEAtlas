/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Clock
public import PDE.Analysis.Evolution.ODE.Linear.OffCountable

/-!
# Uniqueness of the clock of a dynamic rescaling

Consider two dynamic rescalings `ofRates l₁ cl₁ cω₁` and `ofRates l₂ cl₂ cω₂` whose vorticity rates
are of the form `c_ω(σ) = C_ω(σ) β(t(σ))` for functions `β₁`, `β₂` of the physical time, as the
normalization (2.9) gives them for a rescaled solution of a physical solution. If `β₁ = β₂` on the
physical times `[0, min(t₁(q), t₂(q)))`, the two clocks and vorticity scales agree on `[0, q]`
(`eqOn_physicalTime_vorticityScale_ofRates`). In physical time the vorticity scales
`D_i = C_ω,i ∘ t_i⁻¹` solve the same linear equation `D' = β D` with `D(0) = 1`, so their quotient
is constant; the inverse clocks have the same derivative `1/D`, so they agree, and at the end of the
common interval both clocks reach the same physical time. No regularity of `β` is needed.

## Main results

* `eqOn_physicalTime_vorticityScale_ofRates`: if `c_ω,i(σ) = C_ω,i(σ) β_i(t_i(σ))` on `[0, q]`
  and `β₁ = β₂` on `[0, min(t₁(q), t₂(q)))`, the clocks and the vorticity scales agree on `[0, q]`.
* `mem_range_physicalTime_ofRates`: the clock of `ofRates` maps `[0, q]` onto `[0, t(q)]`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Boussinesq.DynamicRescalingData

variable {l₁ l₂ : ℝ} {cl₁ cω₁ cl₂ cω₂ : ℝ → ℝ}

/-- The clock of `ofRates` maps `[0, q]` onto `[0, t(q)]`. -/
theorem mem_range_physicalTime_ofRates {l₀ : ℝ} {cl cω : ℝ → ℝ} (hcω : Continuous cω) {q : ℝ}
    (hq : 0 ≤ q) {t : ℝ} (ht : t ∈ Icc 0 ((ofRates l₀ cl cω).physicalTime q)) :
    ∃ σ ∈ Icc 0 q, (ofRates l₀ cl cω).physicalTime σ = t := by
  have hc : ContinuousOn (ofRates l₀ cl cω).physicalTime (Icc 0 q) := fun σ _ ↦
    (physicalTime_ofRates_hasStrictDerivAt cl hcω σ).hasDerivAt.continuousAt.continuousWithinAt
  exact (physicalTime_ofRates_zero l₀ cl cω ▸ intermediate_value_Icc hq hc) ht

/-- **Uniqueness of the clock.** If the vorticity rates of two rescalings are
`c_ω,i(σ) = C_ω,i(σ) β_i(t_i(σ))` on `[0, q]` and `β₁ = β₂` on `[0, min(t₁(q), t₂(q)))`, the clocks
and the vorticity scales agree on `[0, q]`. -/
theorem eqOn_physicalTime_vorticityScale_ofRates (hcω₁ : Continuous cω₁) (hcω₂ : Continuous cω₂)
    {q : ℝ} (hq : 0 < q) {β₁ β₂ : ℝ → ℝ}
    (h₁ : ∀ σ ∈ Icc 0 q, cω₁ σ =
      (ofRates l₁ cl₁ cω₁).vorticityScale σ * β₁ ((ofRates l₁ cl₁ cω₁).physicalTime σ))
    (h₂ : ∀ σ ∈ Icc 0 q, cω₂ σ =
      (ofRates l₂ cl₂ cω₂).vorticityScale σ * β₂ ((ofRates l₂ cl₂ cω₂).physicalTime σ))
    (hβ : ∀ t ∈ Ico 0 (min ((ofRates l₁ cl₁ cω₁).physicalTime q)
      ((ofRates l₂ cl₂ cω₂).physicalTime q)), β₁ t = β₂ t) :
    ∀ σ ∈ Icc 0 q, (ofRates l₁ cl₁ cω₁).physicalTime σ = (ofRates l₂ cl₂ cω₂).physicalTime σ ∧
      (ofRates l₁ cl₁ cω₁).vorticityScale σ = (ofRates l₂ cl₂ cω₂).vorticityScale σ := by
  set D₁ := ofRates l₁ cl₁ cω₁
  set D₂ := ofRates l₂ cl₂ cω₂
  set t₁ := min (D₁.physicalTime q) (D₂.physicalTime q)
  have hmono₁ := physicalTime_ofRates_strictMono (l₀ := l₁) cl₁ hcω₁
  have hmono₂ := physicalTime_ofRates_strictMono (l₀ := l₂) cl₂ hcω₂
  have hT₁0 : D₁.physicalTime 0 = 0 := physicalTime_ofRates_zero _ _ _
  have hT₂0 : D₂.physicalTime 0 = 0 := physicalTime_ofRates_zero _ _ _
  have ht₁0 : 0 ≤ t₁ := le_min (hT₁0 ▸ hmono₁.monotone hq.le) (hT₂0 ▸ hmono₂.monotone hq.le)
  -- the inverse clocks on `[0, t₁]`
  have hinv {D : DynamicRescalingData} {cl cω : ℝ → ℝ} {l₀ : ℝ} (hD : D = ofRates l₀ cl cω)
      (hcω : Continuous cω) {t : ℝ} (ht : t ∈ Icc 0 (D.physicalTime q)) :
      D.rescaledTime t ∈ Icc 0 q ∧ D.physicalTime (D.rescaledTime t) = t := by
    subst hD
    obtain ⟨σ, hσ, rfl⟩ := mem_range_physicalTime_ofRates hcω hq.le ht
    rw [rescaledTime_ofRates_physicalTime cl hcω]
    exact ⟨hσ, rfl⟩
  have hinv₁ {t : ℝ} (ht : t ∈ Icc 0 t₁) := hinv rfl hcω₁ ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hinv₂ {t : ℝ} (ht : t ∈ Icc 0 t₁) := hinv rfl hcω₂ ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  -- the vorticity scales in physical time solve `D' = β D`
  have hD {D : DynamicRescalingData} {cl cω : ℝ → ℝ} {l₀ : ℝ} (hDdef : D = ofRates l₀ cl cω)
      (hcω : Continuous cω) {β : ℝ → ℝ}
      (hβD : ∀ σ ∈ Icc 0 q, cω σ = D.vorticityScale σ * β (D.physicalTime σ)) {t : ℝ}
      (ht : t ∈ Icc 0 (D.physicalTime q)) :
      HasDerivAt (fun r ↦ D.vorticityScale (D.rescaledTime r))
        (β t * D.vorticityScale (D.rescaledTime t)) t := by
    subst hDdef
    obtain ⟨σ, hσ, rfl⟩ := mem_range_physicalTime_ofRates hcω hq.le ht
    have hs := (rescaledTime_ofRates_hasStrictDerivAt (l₀ := l₀) cl hcω σ).hasDerivAt
    have hA := hasDerivAt_vorticityScale_ofRates (l₀ := l₀) cl hcω σ
    have hrσ := rescaledTime_ofRates_physicalTime (l₀ := l₀) cl hcω σ
    rw [← hrσ] at hA
    refine (hA.comp ((ofRates l₀ cl cω).physicalTime σ) hs).congr_deriv ?_
    rw [hrσ, hβD σ hσ]
    have := (vorticityScale_ofRates_pos (l₀ := l₀) cl cω σ).ne'
    field_simp
  have hD₁ {t : ℝ} (ht : t ∈ Icc 0 t₁) := hD rfl hcω₁ h₁ ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hD₂ {t : ℝ} (ht : t ∈ Icc 0 t₁) := hD rfl hcω₂ h₂ ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  have hpos₁ (r : ℝ) : 0 < D₁.vorticityScale (D₁.rescaledTime r) := vorticityScale_ofRates_pos _ _ _
  have hpos₂ (r : ℝ) : 0 < D₂.vorticityScale (D₂.rescaledTime r) := vorticityScale_ofRates_pos _ _ _
  -- their quotient is constant
  have hquot : ∀ t ∈ Icc 0 t₁, D₁.vorticityScale (D₁.rescaledTime t) =
      D₂.vorticityScale (D₂.rescaledTime t) := by
    have hc : ContinuousOn (fun r ↦ D₁.vorticityScale (D₁.rescaledTime r) /
        D₂.vorticityScale (D₂.rescaledTime r)) (Icc 0 t₁) := fun t ht ↦
      ((hD₁ ht).continuousAt.div (hD₂ ht).continuousAt (hpos₂ t).ne').continuousWithinAt
    have h0 := PDE.Analysis.Evolution.eqOn_const_of_hasDerivAt_zero hc fun t ht ↦ by
      have hd := (hD₁ (Ioo_subset_Icc_self ht)).div (hD₂ (Ioo_subset_Icc_self ht)) (hpos₂ t).ne'
      convert hd using 1
      rw [hβ t ⟨ht.1.le, ht.2⟩]
      ring
    intro t ht
    have := h0 t ht
    rwa [show D₁.rescaledTime 0 = 0 from rescaledTime_ofRates_zero _ hcω₁,
      show D₂.rescaledTime 0 = 0 from rescaledTime_ofRates_zero _ hcω₂,
      show D₁.vorticityScale 0 = 1 from vorticityScale_ofRates_zero _ _ _,
      show D₂.vorticityScale 0 = 1 from vorticityScale_ofRates_zero _ _ _, div_one,
      div_eq_one_iff_eq (hpos₂ t).ne'] at this
  -- the inverse clocks agree
  have hs : ∀ t ∈ Icc 0 t₁, D₁.rescaledTime t = D₂.rescaledTime t := by
    have hderiv {D : DynamicRescalingData} {cl cω : ℝ → ℝ} {l₀ : ℝ} (hDdef : D = ofRates l₀ cl cω)
        (hcω : Continuous cω) {t : ℝ} (ht : t ∈ Icc 0 (D.physicalTime q)) :
        HasDerivAt D.rescaledTime (D.vorticityScale (D.rescaledTime t))⁻¹ t := by
      subst hDdef
      obtain ⟨σ, -, rfl⟩ := mem_range_physicalTime_ofRates hcω hq.le ht
      rw [rescaledTime_ofRates_physicalTime cl hcω σ]
      exact (rescaledTime_ofRates_hasStrictDerivAt cl hcω σ).hasDerivAt
    have hd₁ {t : ℝ} (ht : t ∈ Icc 0 t₁) :=
      hderiv rfl hcω₁ (D := D₁) ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
    have hd₂ {t : ℝ} (ht : t ∈ Icc 0 t₁) :=
      hderiv rfl hcω₂ (D := D₂) ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
    have hc : ContinuousOn (fun r ↦ D₁.rescaledTime r - D₂.rescaledTime r) (Icc 0 t₁) :=
      fun t ht ↦ ((hd₁ ht).continuousAt.sub (hd₂ ht).continuousAt).continuousWithinAt
    have h0 := PDE.Analysis.Evolution.eqOn_const_of_hasDerivAt_zero hc fun t ht ↦ by
      have hd := (hd₁ (Ioo_subset_Icc_self ht)).sub (hd₂ (Ioo_subset_Icc_self ht))
      rwa [hquot t (Ioo_subset_Icc_self ht), sub_self] at hd
    intro t ht
    have := h0 t ht
    rw [show D₁.rescaledTime 0 = 0 from rescaledTime_ofRates_zero _ hcω₁,
      show D₂.rescaledTime 0 = 0 from rescaledTime_ofRates_zero _ hcω₂, sub_self] at this
    linarith
  -- both clocks reach `t₁` at `q`
  have hend : D₁.physicalTime q = t₁ ∧ D₂.physicalTime q = t₁ := by
    have ht₁ : t₁ ∈ Icc 0 t₁ := ⟨ht₁0, le_rfl⟩
    rcases min_choice (D₁.physicalTime q) (D₂.physicalTime q) with h | h
    · refine ⟨h.symm, ?_⟩
      have hq₁ : D₁.rescaledTime t₁ = q := by
        rw [show t₁ = D₁.physicalTime q from h, rescaledTime_ofRates_physicalTime _ hcω₁]
      rw [← hq₁, hs t₁ ht₁, (hinv₂ ht₁).2]
    · refine ⟨?_, h.symm⟩
      have hq₂ : D₂.rescaledTime t₁ = q := by
        rw [show t₁ = D₂.physicalTime q from h, rescaledTime_ofRates_physicalTime _ hcω₂]
      rw [← hq₂, ← hs t₁ ht₁, (hinv₁ ht₁).2]
  intro σ hσ
  have hT : D₁.physicalTime σ ∈ Icc 0 t₁ :=
    ⟨hT₁0 ▸ hmono₁.monotone hσ.1, hend.1 ▸ hmono₁.monotone hσ.2⟩
  have hs₁ : D₁.rescaledTime (D₁.physicalTime σ) = σ := rescaledTime_ofRates_physicalTime _ hcω₁ σ
  have hs₂ : D₂.rescaledTime (D₁.physicalTime σ) = σ := by rw [← hs _ hT, hs₁]
  have hT₂ : D₂.physicalTime σ = D₁.physicalTime σ := by
    have := (hinv₂ hT).2
    rwa [hs₂] at this
  exact ⟨hT₂.symm, by simpa only [hs₁, hs₂] using hquot _ hT⟩

end Boussinesq.DynamicRescalingData
