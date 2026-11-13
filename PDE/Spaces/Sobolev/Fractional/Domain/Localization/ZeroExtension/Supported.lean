/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph

/-!
# Gagliardo functions with a fixed a.e. support

This is a submodule of the graph space with its inherited norm. The support
condition is imposed on the underlying Lᵖ class. Masking a representative by the fixed
set gives a pointwise supported representative without requiring measurability of that
set: the masked function is a.e. equal to the original measurable representative.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.GagliardoSpace.ZeroExtension

variable {n : ℕ} {s : ℝ} {A S : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The submodule of Gagliardo functions vanishing a.e. outside a specified set. -/
def supportedSubmodule (n : ℕ) (s : ℝ) (A S : Set (ℝ^n))
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)] :
    Submodule ℝ (GagliardoSpace n s A (p := p) (F := F)) where
  carrier := {u | ∀ᵐ x ∂volume.restrict A, x ∉ S → toLp n s A u x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero F p (volume.restrict A)] with x hx
    intro _
    simpa only [map_zero, Pi.zero_apply] using hx
  add_mem' {u v} hu hv := by
    filter_upwards [hu, hv, Lp.coeFn_add (toLp n s A u) (toLp n s A v)]
      with x hu hv hadd
    intro hx
    simp only [map_add, hadd, Pi.add_apply, hu hx, hv hx, add_zero]
  smul_mem' c u hu := by
    filter_upwards [hu, Lp.coeFn_smul c (toLp n s A u)] with x hu hsmul
    intro hx
    simp only [map_smul, hsmul, Pi.smul_apply, hu hx, smul_zero]

/-- Membership is independent of which a.e. representative of the Lᵖ class is used. -/
theorem mem_supportedSubmodule_iff_of_ae
    (u : GagliardoSpace n s A (p := p) (F := F)) {f : ℝ^n → F}
    (hf : (toLp n s A u : ℝ^n → F) =ᵐ[volume.restrict A] f) :
    u ∈ supportedSubmodule n s A S (p := p) (F := F) ↔
      ∀ᵐ x ∂volume.restrict A, x ∉ S → f x = 0 := by
  change (∀ᵐ x ∂volume.restrict A, x ∉ S → toLp n s A u x = 0) ↔ _
  apply Filter.eventually_congr
  filter_upwards [hf] with x hx
  rw [hx]

/-- Choose a representative that vanishes pointwise outside the prescribed support. -/
def representative (u : supportedSubmodule n s A S (p := p) (F := F)) : ℝ^n → F :=
  S.indicator (toLp n s A u.val)

/-- Masking on the prescribed support does not change the represented function. -/
theorem representative_ae (u : supportedSubmodule n s A S (p := p) (F := F)) :
    (toLp n s A u.val : ℝ^n → F) =ᵐ[volume.restrict A] representative u := by
  classical
  filter_upwards [u.prop] with x hx
  by_cases hS : x ∈ S
  · exact (indicator_of_mem hS _).symm
  · simpa only [representative, indicator_of_notMem hS] using hx hS

/-- The supported representative satisfies the original intrinsic membership condition. -/
theorem memGagliardo_representative
    (u : supportedSubmodule n s A S (p := p) (F := F)) :
    MemGagliardo n s A (representative u) (p := p) :=
  (show MemGagliardo n s A (toLp n s A u.val) (p := p) from
    ⟨Lp.memLp _, toLp_mem_domain u.val⟩).congr_ae (representative_ae u)

/-- A nonzero value of the chosen representative lies in the prescribed support. -/
theorem mem_of_representative_ne_zero
    (u : supportedSubmodule n s A S (p := p) (F := F)) {x : ℝ^n}
    (hx : representative u x ≠ 0) : x ∈ S := by
  classical
  by_contra hS
  exact hx (indicator_of_notMem hS _)

/-- A physical Gagliardo function with the a.e. support property defines a supported element. -/
def supportedOfFunction (f : ℝ^n → F) (hf : MemGagliardo n s A f (p := p))
    (hS : ∀ᵐ x ∂volume.restrict A, x ∉ S → f x = 0) :
    supportedSubmodule n s A S (p := p) (F := F) :=
  ⟨ofFunction f hf,
    (mem_supportedSubmodule_iff_of_ae _ (toLp_ofFunction_apply_ae f hf)).2 hS⟩

/-- Forgetting the support proof returns the ordinary graph-space constructor. -/
@[simp]
theorem supportedOfFunction_val (f : ℝ^n → F) (hf : MemGagliardo n s A f (p := p))
    (hS : ∀ᵐ x ∂volume.restrict A, x ∉ S → f x = 0) :
    (supportedOfFunction f hf hS).val = ofFunction f hf := rfl

end SobolevSpace.Fractional.GagliardoSpace.ZeroExtension
