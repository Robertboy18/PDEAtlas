/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.SupportedClosure.Space
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Operators
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The supported closure is nontrivial

If `Ω` has nonempty interior, the supported closure `hsSupportedClosureSubmodule n s Ω`
contains a nonzero element, so it is not `⊥` and `HsSupportedClosureSpace n s Ω` is
nontrivial. For `Ω = ∅` the supported closure is `⊥`.

The nonzero element is a smooth bump centred at an interior point of `Ω`, viewed as a
Schwartz function. It is nonzero in `H^s(ℝ^n)` for every real `s` because the maps from
Schwartz functions to `L²` and from `L²` to tempered distributions are injective.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace Metric
open scoped BesselPotentialSpace ENNReal SchwartzMap ContDiff

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

/-- The embedding of Schwartz functions into tempered distributions is injective. -/
theorem schwartz_coe_dist_injective :
    Function.Injective (fun φ : 𝓢(ℝ^n, ℂ) ↦ (φ : 𝓢'(ℝ^n, ℂ))) := by
  intro φ ψ h
  apply SchwartzMap.injective_toLp 2 (volume : Measure (ℝ^n))
  apply LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  simpa only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
    Lp.toTemperedDistribution_toLp_eq] using h

/-- Distinct Schwartz functions give distinct elements of `H^s(ℝ^n)`, for every real `s`. -/
theorem ofSchwartzLinear_injective : Function.Injective (ofSchwartzLinear n s) :=
  fun φ ψ h ↦ schwartz_coe_dist_injective
    ((SchwartzMap.memSobolev (s := s) (p := 2) φ).toBesselPotentialSpace_injective
      (SchwartzMap.memSobolev (s := s) (p := 2) ψ) h)

/-- A Schwartz function is zero in `H^s(ℝ^n)` exactly when it is zero. -/
@[simp] theorem ofSchwartzLinear_eq_zero_iff {φ : 𝓢(ℝ^n, ℂ)} :
    ofSchwartzLinear n s φ = 0 ↔ φ = 0 :=
  map_eq_zero_iff (ofSchwartzLinear n s) ofSchwartzLinear_injective

/-- If `Ω` has nonempty interior, some nonzero Schwartz function has topological support
in `Ω`. -/
theorem exists_schwartz_ne_zero_tsupport_subset (hΩ : (interior Ω).Nonempty) :
    ∃ φ : 𝓢(ℝ^n, ℂ), tsupport φ.toFun ⊆ Ω ∧ φ ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := hΩ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  obtain ⟨f, hrOut⟩ : ∃ f : ContDiffBump x₀, f.rOut = ε / 2 :=
    ⟨⟨ε / 3, ε / 2, by positivity, by linarith⟩, rfl⟩
  have hcs : HasCompactSupport (Complex.ofRealCLM ∘ (f : ℝ^n → ℝ)) :=
    f.hasCompactSupport.comp_left rfl
  have hsm : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (f : ℝ^n → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp f.contDiff
  refine ⟨hcs.toSchwartzMap hsm, ?_, ?_⟩
  · have hsub : tsupport (Complex.ofRealCLM ∘ (f : ℝ^n → ℝ)) ⊆ tsupport (f : ℝ^n → ℝ) :=
      tsupport_comp_subset rfl _
    refine hsub.trans ?_
    rw [f.tsupport_eq, hrOut]
    exact (closedBall_subset_ball (by linarith)).trans (hball.trans interior_subset)
  · intro hzero
    have h1 : f x₀ = 1 := f.one_of_mem_closedBall (mem_closedBall_self f.rIn_pos.le)
    have h2 : ((f x₀ : ℝ) : ℂ) = 0 := DFunLike.congr_fun hzero x₀
    rw [h1] at h2
    exact one_ne_zero (Complex.ofReal_eq_zero.1 h2)

/-- If `Ω` has nonempty interior, the supported closure of `Ω` in `H^s(ℝ^n)` contains a
nonzero element. -/
theorem exists_ne_zero_mem_hsSupportedClosure (hΩ : (interior Ω).Nonempty) :
    ∃ u : H^{s}(ℝ^n), u ∈ hsSupportedClosureSubmodule n s Ω ∧ u ≠ 0 := by
  obtain ⟨φ, hsupp, hne⟩ := exists_schwartz_ne_zero_tsupport_subset (n := n) hΩ
  exact ⟨ofSchwartzLinear n s φ, ofSchwartz_mem_hsSupportedClosure hsupp,
    fun h ↦ hne (ofSchwartzLinear_eq_zero_iff.1 h)⟩

/-- If `Ω` has nonempty interior, the supported closure of `Ω` in `H^s(ℝ^n)` is not the
zero submodule. -/
theorem hsSupportedClosureSubmodule_ne_bot (hΩ : (interior Ω).Nonempty) :
    hsSupportedClosureSubmodule n s Ω ≠ ⊥ := by
  obtain ⟨u, hmem, hne⟩ := exists_ne_zero_mem_hsSupportedClosure (s := s) hΩ
  exact (Submodule.ne_bot_iff _).2 ⟨u, hmem, hne⟩

/-- If `Ω` has nonempty interior, the supported closure space of `Ω` is nontrivial. -/
theorem nontrivial_hsSupportedClosureSpace (hΩ : (interior Ω).Nonempty) :
    Nontrivial (HsSupportedClosureSpace n s Ω) :=
  Submodule.nontrivial_iff_ne_bot.2 (hsSupportedClosureSubmodule_ne_bot hΩ)

/-- The supported closure of `ℝ^n` in `H^s(ℝ^n)` is not the zero submodule. -/
theorem hsSupportedClosureSubmodule_univ_ne_bot :
    hsSupportedClosureSubmodule n s Set.univ ≠ ⊥ :=
  hsSupportedClosureSubmodule_ne_bot (by simp)

/-- The supported closure of the empty set is the zero submodule, so the nonempty interior
hypothesis of `hsSupportedClosureSubmodule_ne_bot` cannot be dropped. -/
theorem hsSupportedClosureSubmodule_empty :
    hsSupportedClosureSubmodule n s (∅ : Set (ℝ^n)) = ⊥ := by
  have hbot : IsClosed ((⊥ : Submodule ℂ (H^{s}(ℝ^n))) : Set (H^{s}(ℝ^n))) := by
    rw [Submodule.bot_coe]
    exact isClosed_singleton
  refine le_antisymm ?_ bot_le
  have h1 : Submodule.span ℂ (schwartzSupportedInSet n s (∅ : Set (ℝ^n))) ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro u ⟨φ, hφ, rfl⟩
    have hφ0 : φ = 0 := by
      refine DFunLike.ext _ _ fun x ↦ ?_
      by_contra hx
      have hmem : x ∈ Function.support φ.toFun := hx
      exact Set.notMem_empty x (hφ (subset_tsupport _ hmem))
    subst hφ0
    exact (Submodule.mem_bot ℂ).2 (map_zero (ofSchwartzLinear n s))
  calc hsSupportedClosureSubmodule n s (∅ : Set (ℝ^n))
      ≤ (⊥ : Submodule ℂ (H^{s}(ℝ^n))).topologicalClosure :=
        Submodule.topologicalClosure_mono h1
    _ = ⊥ := hbot.submodule_topologicalClosure_eq

end SobolevSpace.Fractional
