/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.SupportedClosure
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Operators

import PDE.Analysis.FunctionalSpaces.BesselPotentialSpace.Schwartz

/-!
# Supported Schwartz generators

Schwartz functions whose closed support lies in a fixed set form a complex vector
space. Their images in whole-space Bessel potential space therefore form a
submodule as well. Consequently, the supported closure can be described by
limits of individual supported Schwartz functions.

These statements hold for every real order, every dimension, and arbitrary
support sets. The supported closure is defined as a closed span; the results here
identify that span with its generating set.
-/

@[expose] public section

open scoped BesselPotentialSpace SchwartzMap Topology

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

/-- Schwartz convergence implies convergence in `H^s` for every real order. -/
theorem continuous_ofSchwartzLinear (n : ℕ) (s : ℝ) :
    Continuous (ofSchwartzLinear n s) := by
  simpa only [ofSchwartzLinear, LinearMap.coe_mk, AddHom.coe_mk] using
    SchwartzMap.continuous_toBesselPotentialSpace (ℝ^n) ℂ s 2

/-- Supported Schwartz functions, viewed in `H^s`, form a complex submodule. -/
noncomputable def schwartzSupportedSubmodule (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    Submodule ℂ (H^{s}(ℝ^n)) where
  carrier := schwartzSupportedInSet n s Ω
  zero_mem' := by
    refine ⟨0, ?_, map_zero (ofSchwartzLinear n s)⟩
    change tsupport (0 : ℝ^n → ℂ) ⊆ Ω
    simp
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    refine ⟨φ + ψ, ?_, map_add (ofSchwartzLinear n s) φ ψ⟩
    exact (tsupport_add φ.toFun ψ.toFun).trans (Set.union_subset hφ hψ)
  smul_mem' := by
    rintro c _ ⟨φ, hφ, rfl⟩
    refine ⟨c • φ, ?_, map_smul (ofSchwartzLinear n s) c φ⟩
    exact (tsupport_smul_subset_right (fun _ : ℝ^n ↦ c) φ.toFun).trans hφ

/-- The submodule has exactly the original supported Schwartz generators as its carrier. -/
@[simp]
theorem coe_schwartzSupportedSubmodule :
    (schwartzSupportedSubmodule n s Ω : Set (H^{s}(ℝ^n))) =
      schwartzSupportedInSet n s Ω :=
  rfl

/-- Taking the complex span does not enlarge the supported Schwartz generating set. -/
theorem span_schwartzSupportedInSet :
    Submodule.span ℂ (schwartzSupportedInSet n s Ω) =
      schwartzSupportedSubmodule n s Ω := by
  rw [← coe_schwartzSupportedSubmodule]
  exact Submodule.span_eq (schwartzSupportedSubmodule n s Ω)

/-- The supported closure is the ordinary topological closure of its Schwartz generators. -/
theorem coe_hsSupportedClosureSubmodule_eq_closure :
    (hsSupportedClosureSubmodule n s Ω : Set (H^{s}(ℝ^n))) =
      closure (schwartzSupportedInSet n s Ω) := by
  rw [hsSupportedClosureSubmodule, span_schwartzSupportedInSet,
    Submodule.topologicalClosure_coe, coe_schwartzSupportedSubmodule]

/-- Membership is equivalent to approximation by individual supported Schwartz functions. -/
theorem mem_hsSupportedClosureSubmodule_iff_schwartz (u : H^{s}(ℝ^n)) :
    u ∈ hsSupportedClosureSubmodule n s Ω ↔
      ∀ ε > 0, ∃ φ : 𝓢(ℝ^n, ℂ), tsupport φ.toFun ⊆ Ω ∧
        ‖u - ofSchwartzLinear n s φ‖ < ε := by
  rw [← SetLike.mem_coe, coe_hsSupportedClosureSubmodule_eq_closure,
    Metric.mem_closure_iff]
  simp only [schwartzSupportedInSet, Set.mem_ofPred_eq, exists_exists_and_eq_and,
    dist_eq_norm]
  rfl

namespace HsSupportedClosureSpace

/-- Every supported-closure element admits supported Schwartz approximation in its ambient norm. -/
theorem exists_schwartz_approx (u : HsSupportedClosureSpace n s Ω) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : 𝓢(ℝ^n, ℂ), tsupport φ.toFun ⊆ Ω ∧
      ‖toHs n s Ω u - ofSchwartzLinear n s φ‖ < ε :=
  (mem_hsSupportedClosureSubmodule_iff_schwartz (toHs n s Ω u)).mp u.prop ε hε

end HsSupportedClosureSpace

end SobolevSpace.Fractional
