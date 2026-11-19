/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Definitions

/-!
# The supported closure inside whole-space `H^s`

We take the closure in `H^s(ℝ^n)` of the span of Schwartz functions
whose topological support lies in `Ω`.  The result is a closed subspace of the
whole-space Bessel-potential space, rather than a space of functions whose
domain is only `Ω`.

Taking a `Submodule.span` before the topological closure means no support lemmas
are needed for closure under addition and scalar multiplication: the span
supplies them.

Being a closed subspace of a Hilbert space, the resulting space is complete.
`SupportedClosure` adds the functoriality of the inclusions and the orthogonal projection.

## Main definitions

* `SobolevSpace.Fractional.schwartzSupportedInSet`: the generating set of
  Schwartz functions supported in `Ω`, viewed inside `H^s`.
* `SobolevSpace.Fractional.hsSupportedClosureSubmodule`: the closed span of the
  generating set.
* `SobolevSpace.Fractional.HsSupportedClosureSpace`: the associated space.
* `SobolevSpace.Fractional.HsSupportedClosureSpace.inclusionCLM`: the
  isometric inclusion induced by `Ω₁ ⊆ Ω₂`.

## Main statements

* `SobolevSpace.Fractional.isClosed_hsSupportedClosureSubmodule`: the submodule
  is closed.
* `SobolevSpace.Fractional.ofSchwartz_mem_hsSupportedClosure`: every generator
  lies in the supported closure.
* `SobolevSpace.Fractional.mem_hsSupportedClosureSubmodule_iff`: membership is
  equivalent to norm approximation by the supported Schwartz span.
-/

@[expose] public section

open TemperedDistribution MeasureTheory
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

open BesselPotentialSpace

/-- The elements of `H^s` coming from Schwartz functions with closed support in `Ω`. -/
def schwartzSupportedInSet (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) : Set (H^{s}(ℝ^n)) :=
  {u | ∃ φ : 𝓢(ℝ^n, ℂ), tsupport φ.toFun ⊆ Ω ∧
    (SchwartzMap.memSobolev φ).toBesselPotentialSpace = u}

/-- The closure in `H^s(ℝ^n)` of the span of Schwartz functions whose
topological support lies in `Ω`. -/
noncomputable def hsSupportedClosureSubmodule (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    Submodule ℂ (H^{s}(ℝ^n)) :=
  (Submodule.span ℂ (schwartzSupportedInSet n s Ω)).topologicalClosure

/-- The supported closure is closed in `H^s(ℝ^n)`, being a topological closure by definition. -/
theorem isClosed_hsSupportedClosureSubmodule :
    IsClosed (hsSupportedClosureSubmodule n s Ω : Set (H^{s}(ℝ^n))) :=
  Submodule.isClosed_topologicalClosure _

/-- A Schwartz function supported in `Ω` lies in the supported closure. -/
theorem ofSchwartz_mem_hsSupportedClosure {φ : 𝓢(ℝ^n, ℂ)}
    (hφ : tsupport φ.toFun ⊆ Ω) :
    (SchwartzMap.memSobolev (s := s) φ).toBesselPotentialSpace ∈
      hsSupportedClosureSubmodule n s Ω := by
  refine Submodule.le_topologicalClosure _ ?_
  exact Submodule.subset_span ⟨φ, hφ, rfl⟩

/-- The span of the generators is contained in the supported closure. -/
theorem span_le_hsSupportedClosureSubmodule :
    Submodule.span ℂ (schwartzSupportedInSet n s Ω) ≤
      hsSupportedClosureSubmodule n s Ω :=
  Submodule.le_topologicalClosure _

/-- The supported closure as a type. -/
noncomputable abbrev HsSupportedClosureSpace
    (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) : Type :=
  ↥(hsSupportedClosureSubmodule n s Ω)

/-- The supported closure is complete, being a closed subspace of a Hilbert space. -/
instance instCompleteSpaceHsSupportedClosure :
    CompleteSpace (HsSupportedClosureSpace n s Ω) :=
  isClosed_hsSupportedClosureSubmodule.completeSpace_coe

/-- Monotonicity in the domain. -/
theorem hsSupportedClosureSubmodule_mono {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂) :
    hsSupportedClosureSubmodule n s Ω₁ ≤ hsSupportedClosureSubmodule n s Ω₂ := by
  refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
  rintro u ⟨φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨φ, hφ.trans h, rfl⟩

/-- Membership in the supported closure is equivalent to approximation in the
`H^s` norm by the complex span of supported Schwartz functions. -/
theorem mem_hsSupportedClosureSubmodule_iff (u : H^{s}(ℝ^n)) :
    u ∈ hsSupportedClosureSubmodule n s Ω ↔
      ∀ ε > 0, ∃ v ∈ Submodule.span ℂ (schwartzSupportedInSet n s Ω),
        ‖u - v‖ < ε := by
  change u ∈ (Submodule.span ℂ (schwartzSupportedInSet n s Ω)).topologicalClosure ↔ _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  simp only [dist_eq_norm, SetLike.mem_coe]

namespace HsSupportedClosureSpace

/-- The canonical isometric embedding of the supported closure into whole-space `H^s`. -/
noncomputable def toHs (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    HsSupportedClosureSpace n s Ω →L[ℂ] H^{s}(ℝ^n) :=
  (hsSupportedClosureSubmodule n s Ω).subtypeL

/-- `toHs` is the subtype coercion into `H^s(ℝ^n)`. -/
@[simp]
theorem toHs_apply (u : HsSupportedClosureSpace n s Ω) :
    toHs n s Ω u = u :=
  rfl

/-- The canonical embedding into whole-space `H^s` is injective. -/
theorem toHs_injective :
    Function.Injective (toHs n s Ω) :=
  Subtype.val_injective

/-- The embedding into `H^s(ℝ^n)` preserves the norm; the supported closure carries the
restricted `H^s` norm. -/
@[simp]
theorem norm_toHs (u : HsSupportedClosureSpace n s Ω) :
    ‖toHs n s Ω u‖ = ‖u‖ :=
  rfl

/-- The embedding into `H^s(ℝ^n)` preserves the inner product. -/
@[simp]
theorem inner_toHs (u v : HsSupportedClosureSpace n s Ω) :
    inner ℂ (toHs n s Ω u) (toHs n s Ω v) = inner ℂ u v :=
  rfl

/-- A supported Schwartz function, as an element of the supported closure. -/
noncomputable def ofSchwartz (φ : 𝓢(ℝ^n, ℂ)) (hφ : tsupport φ.toFun ⊆ Ω) :
    HsSupportedClosureSpace n s Ω :=
  ⟨(SchwartzMap.memSobolev φ).toBesselPotentialSpace, ofSchwartz_mem_hsSupportedClosure hφ⟩

/-- The `H^s` element underlying this supported Schwartz element is `ofSchwartz φ`. -/
@[simp]
theorem coe_ofSchwartz (φ : 𝓢(ℝ^n, ℂ)) (hφ : tsupport φ.toFun ⊆ Ω) :
    (ofSchwartz (n := n) (s := s) φ hφ : H^{s}(ℝ^n)) =
      (SchwartzMap.memSobolev φ).toBesselPotentialSpace :=
  rfl

/-- Inclusion of supported closures induced by an inclusion of support sets. -/
noncomputable def inclusionCLM {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂) :
    HsSupportedClosureSpace n s Ω₁ →L[ℂ] HsSupportedClosureSpace n s Ω₂ :=
  ContinuousLinearMap.codRestrict
    (toHs n s Ω₁)
    (hsSupportedClosureSubmodule n s Ω₂)
    fun u ↦ hsSupportedClosureSubmodule_mono h u.prop

/-- The inclusion along `Ω₁ ⊆ Ω₂` does not change the underlying `H^s` element. -/
@[simp]
theorem coe_inclusionCLM {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂)
    (u : HsSupportedClosureSpace n s Ω₁) :
    (inclusionCLM h u : H^{s}(ℝ^n)) = (u : H^{s}(ℝ^n)) :=
  rfl

/-- The inclusion along `Ω₁ ⊆ Ω₂` is isometric. -/
@[simp]
theorem norm_coe_inclusionCLM_apply {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂)
    (u : HsSupportedClosureSpace n s Ω₁) :
    ‖(inclusionCLM h u : H^{s}(ℝ^n))‖ = ‖(u : H^{s}(ℝ^n))‖ :=
  rfl

/-- Inclusion along `Ω₁ ⊆ Ω₂` has operator norm at most one. -/
theorem norm_inclusionCLM_le {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂) :
    ‖inclusionCLM (n := n) (s := s) h‖ ≤ 1 := by
  refine (inclusionCLM (n := n) (s := s) h).opNorm_le_bound zero_le_one ?_
  intro u
  simpa only [one_mul, Submodule.norm_coe] using
    le_of_eq (norm_coe_inclusionCLM_apply h u)

end HsSupportedClosureSpace

end SobolevSpace.Fractional
