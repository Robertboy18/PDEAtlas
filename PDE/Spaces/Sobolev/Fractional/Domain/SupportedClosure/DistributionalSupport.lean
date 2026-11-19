/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.FunctionalSpaces.BesselPotentialSpace.Distribution
public import PDE.Spaces.Sobolev.Fractional.Domain.SupportedClosure
public import Mathlib.Analysis.Distribution.Support

/-!
# Distributional support of supported Sobolev limits

A Sobolev limit of Schwartz functions supported in `Ω` still pairs to zero with
every test function supported outside `Ω`. Evaluation on a fixed test function is
continuous in every Bessel potential norm, so its kernel contains the entire
supported closure.

Consequently the distributional support lies in `closure Ω`, for every real
Sobolev order. This argument also applies at negative orders, where the limit
need not be represented by a function. It does not identify all distributions
supported in `closure Ω` with this closure.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Fractional.HsSupportedClosureSpace

open MeasureTheory BesselPotentialSpace
open scoped BesselPotentialSpace SchwartzMap

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

/-- A supported Sobolev limit pairs to zero with every Schwartz test supported outside `Ω`. -/
theorem toDistr_apply_eq_zero (u : HsSupportedClosureSpace n s Ω)
    (φ : 𝓢(ℝ^n, ℂ)) (hφ : tsupport φ.toFun ⊆ Ωᶜ) :
    u.val.toDistr φ = 0 := by
  let T : H^{s}(ℝ^n) →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
      (toDistrCLM (ℝ^n) ℂ s 2)
  have hspan : Submodule.span ℂ (schwartzSupportedInSet n s Ω) ≤ T.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ψ, hψ, rfl⟩
    change T (TemperedDistribution.MemSobolev.toBesselPotentialSpace
      (SchwartzMap.memSobolev ψ)) = 0
    simp only [T, ContinuousLinearMap.comp_apply, toDistrCLM_apply,
      TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr]
    change (ψ : 𝓢'(ℝ^n, ℂ)) φ = 0
    rw [SchwartzMap.toTemperedDistributionCLM_apply_apply volume]
    apply integral_eq_zero_of_ae
    filter_upwards with x
    change φ x • ψ x = 0
    by_cases hx : x ∈ Ω
    · have hnot : x ∉ tsupport φ.toFun := fun h ↦ hφ h hx
      have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
      rw [hzero, zero_smul]
    · have hnot : x ∉ tsupport ψ.toFun := fun h ↦ hx (hψ h)
      have hzero : ψ x = 0 := image_eq_zero_of_notMem_tsupport hnot
      rw [hzero, smul_zero]
  have hT : T u.val = 0 :=
    (Submodule.topologicalClosure_minimal _ hspan T.isClosed_ker) u.property
  change toDistrCLM (ℝ^n) ℂ s 2 u.val φ = 0 at hT
  rwa [toDistrCLM_apply] at hT

/-- The underlying distribution vanishes on the complement of the supporting set. -/
theorem isVanishingOn_compl (u : HsSupportedClosureSpace n s Ω) :
    Distribution.IsVanishingOn u.val.toDistr Ωᶜ :=
  toDistr_apply_eq_zero u

/-- Taking a Sobolev limit can move support to the boundary, but never outside `closure Ω`. -/
theorem dsupport_subset_closure (u : HsSupportedClosureSpace n s Ω) :
    Distribution.dsupport u.val.toDistr ⊆ closure Ω := by
  intro x hx
  exact (Distribution.mem_dsupport_iff x).mp hx (closure Ω)
    ((isVanishingOn_compl u).mono (Set.compl_subset_compl.mpr subset_closure))
    isClosed_closure

/-- On a closed supporting set the distributional support stays inside that set. -/
theorem dsupport_subset (hΩ : IsClosed Ω) (u : HsSupportedClosureSpace n s Ω) :
    Distribution.dsupport u.val.toDistr ⊆ Ω := by
  simpa only [hΩ.closure_eq] using dsupport_subset_closure u

end SobolevSpace.Fractional.HsSupportedClosureSpace
