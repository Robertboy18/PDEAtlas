/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation

/-!
# Local Sobolev membership

A function belongs to `W^{k,p}_loc(Ω)` when it is represented by a Sobolev
graph element on every relatively compact open subdomain. This reuses the
completed spaces and their almost-everywhere identification, without imposing
a global norm or choosing a separate family of local weak derivatives.

The standard interpretation is on open domains. The definition accepts every
finite order and exponent; the Banach-space calculus uses `1 ≤ p ≤ ∞`.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} {Ω V : Set (ℝ^n)} {u v : ℝ^n → ℝ}

/-- Local `W^{k,p}` membership, expressed by a Sobolev representative on
every relatively compact open subdomain. No global integrability is required. -/
def IsLocallyWkpOn (k : ℕ) (p : ℝ≥0∞)
    (Ω : Set (ℝ^n)) (u : ℝ^n → ℝ) : Prop :=
  ∀ V : Set (ℝ^n), IsOpen V → IsCompact (closure V) → closure V ⊆ Ω →
    ∃ U : W^{k,p}(V), baseRepresentative U =ᵐ[domainMeasure n V] u

/-- Local Sobolev membership restricts to a smaller domain. -/
theorem IsLocallyWkpOn.mono (hu : IsLocallyWkpOn k p Ω u) (hVΩ : V ⊆ Ω) :
    IsLocallyWkpOn k p V u :=
  fun S hS hcompact hSV ↦ hu S hS hcompact (hSV.trans hVΩ)

/-- Local Sobolev membership depends only on the almost-everywhere class
of the function on its domain. -/
theorem IsLocallyWkpOn.congr_ae (hu : IsLocallyWkpOn k p Ω u)
    (huv : u =ᵐ[domainMeasure n Ω] v) : IsLocallyWkpOn k p Ω v := by
  intro V hV hcompact hVΩ
  obtain ⟨U, hU⟩ := hu V hV hcompact hVΩ
  exact ⟨U, hU.trans
    (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVΩ) huv)⟩

/-- Local Sobolev membership is preserved by sums. -/
theorem IsLocallyWkpOn.add [Fact (1 ≤ p)] (hu : IsLocallyWkpOn k p Ω u)
    (hv : IsLocallyWkpOn k p Ω v) : IsLocallyWkpOn k p Ω (u + v) := by
  intro V hV hcompact hVΩ
  obtain ⟨U₁, hU₁⟩ := hu V hV hcompact hVΩ
  obtain ⟨U₂, hU₂⟩ := hv V hV hcompact hVΩ
  refine ⟨U₁ + U₂, ?_⟩
  have hadd := Lp.coeFn_add ((U₁ : WkpAmbientOn n k p V) (baseIndex n k))
    ((U₂ : WkpAmbientOn n k p V) (baseIndex n k))
  filter_upwards [hadd, hU₁, hU₂] with x hx h₁ h₂
  simp only [baseRepresentative, Submodule.coe_add, PiLp.add_apply, Pi.add_apply] at hx h₁ h₂ ⊢
  rw [hx, h₁, h₂]

/-- A local Sobolev function is locally integrable on an open domain.
The graph's order-zero weak-derivative identity already includes local integrability,
so no restriction on the exponent is needed. -/
theorem IsLocallyWkpOn.locallyIntegrableOn (hu : IsLocallyWkpOn k p Ω u)
    (hΩ : IsOpen Ω) : LocallyIntegrableOn u Ω volume := by
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, hcompact⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := x)) hΩ (singleton_subset_iff.mpr hx)
  have hxV' : x ∈ V := hxV (mem_singleton x)
  obtain ⟨U, hU⟩ := hu V hV hcompact hVΩ
  have h := ((U.property (baseIndex n k)).locallyIntegrable_f.congr hU) x hxV'
  rw [hV.nhdsWithin_eq hxV'] at h
  exact h.filter_mono nhdsWithin_le_nhds

end SobolevSpace.GraphSpace
