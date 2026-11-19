/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.SupportedClosure.Generators

import PDE.Analysis.Distribution.Schwartz.Density

/-!
# Compactly supported smooth approximation

A smooth complex function with compact support determines a Schwartz function
through `HasCompactSupport.toSchwartzMap`, and hence an element of `H^s`.
We consider those functions whose closed support is contained in a prescribed set.

Multiplying by expanding smooth cutoffs preserves the support condition and
approximates every Schwartz function in the Schwartz topology. Continuity of the
Schwartz embedding into `H^s` identifies the supported closure with the closure of
these smooth compactly supported functions, in every dimension and at every real
order. No openness or boundedness assumption on the support set is needed.

On a bounded set, the generating sets themselves agree: closed support contained
in a bounded set is compact.
-/

@[expose] public section

open scoped BesselPotentialSpace SchwartzMap Topology ContDiff

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

/-- The `H^s` images of smooth compactly supported complex functions with closed support in `Ω`. -/
def compactSmoothSupportedInSet (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    Set (H^{s}(ℝ^n)) :=
  {u | ∃ (f : ℝ^n → ℂ) (hf : HasCompactSupport f) (hfd : ContDiff ℝ ∞ f),
    tsupport f ⊆ Ω ∧ ofSchwartzLinear n s (hf.toSchwartzMap hfd) = u}

/-- Compactly supported smooth generators are supported Schwartz generators. -/
theorem compactSmoothSupportedInSet_subset_schwartzSupportedInSet :
    compactSmoothSupportedInSet n s Ω ⊆ schwartzSupportedInSet n s Ω := by
  rintro u ⟨f, hf, hfd, hΩ, rfl⟩
  exact ⟨hf.toSchwartzMap hfd, hΩ, rfl⟩

/-- A compactly supported Schwartz function gives a smooth compact generator. -/
theorem ofSchwartzLinear_mem_compactSmoothSupportedInSet
    (φ : 𝓢(ℝ^n, ℂ)) (hc : HasCompactSupport φ.toFun) (hφ : tsupport φ.toFun ⊆ Ω) :
    ofSchwartzLinear n s φ ∈ compactSmoothSupportedInSet n s Ω := by
  refine ⟨φ.toFun, hc, φ.smooth ⊤, hφ, congrArg (ofSchwartzLinear n s) ?_⟩
  ext x
  rfl

/-- A Schwartz function whose closed support lies in a bounded set has compact support. -/
theorem hasCompactSupport_of_tsupport_subset_isBounded
    {φ : 𝓢(ℝ^n, ℂ)} (hΩ : Bornology.IsBounded Ω) (hφ : tsupport φ.toFun ⊆ Ω) :
    HasCompactSupport φ.toFun :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport φ.toFun) (hΩ.subset hφ)

/-- On a bounded set, supported Schwartz generators are exactly the smooth compact generators. -/
theorem compactSmoothSupportedInSet_eq_schwartzSupportedInSet_of_isBounded
    (hΩ : Bornology.IsBounded Ω) :
    compactSmoothSupportedInSet n s Ω = schwartzSupportedInSet n s Ω := by
  apply Set.Subset.antisymm compactSmoothSupportedInSet_subset_schwartzSupportedInSet
  rintro u ⟨φ, hφ, rfl⟩
  exact ofSchwartzLinear_mem_compactSmoothSupportedInSet φ
    (hasCompactSupport_of_tsupport_subset_isBounded hΩ hφ) hφ

/-- The compact smooth closure is always contained in the supported closure. -/
theorem closure_compactSmoothSupportedInSet_subset :
    closure (compactSmoothSupportedInSet n s Ω) ⊆
      (hsSupportedClosureSubmodule n s Ω : Set (H^{s}(ℝ^n))) := by
  rw [coe_hsSupportedClosureSubmodule_eq_closure]
  exact closure_mono compactSmoothSupportedInSet_subset_schwartzSupportedInSet

/-- Support-preserving smooth cutoffs approximate every supported Schwartz generator in `H^s`. -/
theorem schwartzSupportedInSet_subset_closure_compactSmoothSupportedInSet :
    schwartzSupportedInSet n s Ω ⊆ closure (compactSmoothSupportedInSet n s Ω) := by
  rintro u ⟨φ, hφ, rfl⟩
  obtain ⟨ψ, hc, hs, hψ⟩ := φ.exists_tendsto_hasCompactSupport
  have hlim := (continuous_ofSchwartzLinear n s).tendsto φ |>.comp hψ
  apply mem_closure_of_tendsto hlim
  exact Filter.Eventually.of_forall fun m ↦
    ofSchwartzLinear_mem_compactSmoothSupportedInSet (ψ m) (hc m) ((hs m).trans hφ)

/-- The supported closure is exactly the closure of smooth compactly supported functions. -/
theorem coe_hsSupportedClosureSubmodule_eq_closure_compactSmooth :
    (hsSupportedClosureSubmodule n s Ω : Set (H^{s}(ℝ^n))) =
      closure (compactSmoothSupportedInSet n s Ω) := by
  apply Set.Subset.antisymm
  · rw [coe_hsSupportedClosureSubmodule_eq_closure]
    exact closure_minimal schwartzSupportedInSet_subset_closure_compactSmoothSupportedInSet
      isClosed_closure
  · exact closure_compactSmoothSupportedInSet_subset

/-- Norm approximation by smooth compactly supported functions characterizes their closure. -/
theorem mem_closure_compactSmoothSupportedInSet_iff (u : H^{s}(ℝ^n)) :
    u ∈ closure (compactSmoothSupportedInSet n s Ω) ↔
      ∀ ε > 0, ∃ (f : ℝ^n → ℂ) (hf : HasCompactSupport f) (hfd : ContDiff ℝ ∞ f),
        tsupport f ⊆ Ω ∧ ‖u - ofSchwartzLinear n s (hf.toSchwartzMap hfd)‖ < ε := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨v, ⟨f, hf, hfd, hΩ, rfl⟩, hv⟩ := h ε hε
    exact ⟨f, hf, hfd, hΩ, by simpa only [dist_eq_norm] using hv⟩
  · intro h ε hε
    obtain ⟨f, hf, hfd, hΩ, hfε⟩ := h ε hε
    exact ⟨_, ⟨f, hf, hfd, hΩ, rfl⟩, by simpa only [dist_eq_norm] using hfε⟩

/-- Supported-closure membership is equivalent to approximation by `C_c∞` functions. -/
theorem mem_hsSupportedClosureSubmodule_iff_compactSmooth (u : H^{s}(ℝ^n)) :
    u ∈ hsSupportedClosureSubmodule n s Ω ↔
      ∀ ε > 0, ∃ (f : ℝ^n → ℂ) (hf : HasCompactSupport f) (hfd : ContDiff ℝ ∞ f),
        tsupport f ⊆ Ω ∧ ‖u - ofSchwartzLinear n s (hf.toSchwartzMap hfd)‖ < ε := by
  rw [← SetLike.mem_coe, coe_hsSupportedClosureSubmodule_eq_closure_compactSmooth,
    mem_closure_compactSmoothSupportedInSet_iff]

namespace HsSupportedClosureSpace

/-- Every supported-closure element can be approximated by smooth compactly supported functions. -/
theorem exists_compactSmooth_approx (u : HsSupportedClosureSpace n s Ω) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (f : ℝ^n → ℂ) (hf : HasCompactSupport f) (hfd : ContDiff ℝ ∞ f),
      tsupport f ⊆ Ω ∧
        ‖toHs n s Ω u - ofSchwartzLinear n s (hf.toSchwartzMap hfd)‖ < ε :=
  (mem_hsSupportedClosureSubmodule_iff_compactSmooth (toHs n s Ω u)).mp u.prop ε hε

end HsSupportedClosureSpace

end SobolevSpace.Fractional
