/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.Cutoff
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction

/-!
# Fixed points and relative cutoff norms

A cutoff that fixes the physical base fixes the full weak jet. Restricting a relative
cutoff to its original intersection recovers the localized jet, and extension of these
localized coordinates preserves their graph norm.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Distributions

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω V : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A compact multiplier fixing the base representative fixes the whole Sobolev graph. -/
theorem compactSmoothMultiplierCLM_eq_self_of_base_ae
    (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (U : W^{k,p}(Ω; F))
    (h : (fun x ↦ ζ x • U.val (baseIndex n k) x)
      =ᵐ[domainMeasure n Ω] U.val (baseIndex n k)) :
    compactSmoothMultiplierCLM ζ hζ hc U = U := by
  apply WkpSpaceOn.ext_of_base_ae
  exact (compactSmoothMultiplierCLM_base_ae ζ hζ hc U).trans h

/-- A cutoff equal to one on the base support fixes every derivative coordinate. -/
theorem compactSmoothMultiplierCLM_eq_self_of_base_support
    (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (U : W^{k,p}(Ω; F)) (C : Set ℝ^n) (hζC : ∀ x ∈ C, ζ x = 1)
    (hU : ∀ᵐ x ∂domainMeasure n Ω, x ∉ C → U.val (baseIndex n k) x = 0) :
    compactSmoothMultiplierCLM ζ hζ hc U = U := by
  apply compactSmoothMultiplierCLM_eq_self_of_base_ae ζ hζ hc U
  filter_upwards [hU] with x hx
  by_cases hxC : x ∈ C
  · simp only [hζC x hxC, one_smul]
  · simp only [hx hxC, smul_zero]

/-- Restricting a relative cutoff recovers the compact multiplier on the intersection. -/
theorem restrictCLM_interMultiplier
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) :
    restrictCLM (show V ⊓ Ω ≤ Ω from inf_le_right) (interMultiplier ψ hψ U)
      = compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport U := by
  apply WkpSpaceOn.ext_of_base_ae
  refine (restrictCLM_apply_ae inf_le_right (interMultiplier ψ hψ U)
    (baseIndex n k)).trans ?_
  have hbase : ((interMultiplier ψ hψ U).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n (V ⊓ Ω)] fun x ↦ ψ.toFun x • U.val (baseIndex n k) x :=
    ae_mono (Measure.restrict_mono (show V ⊓ Ω ≤ Ω from inf_le_right) le_rfl)
      (interMultiplier_base_ae ψ hψ U Filter.EventuallyEq.rfl)
  exact hbase.trans
    (compactSmoothMultiplierCLM_base_ae ψ.toFun ψ.contDiff ψ.hasCompactSupport U).symm

/-- Extending the localized jet preserves its full graph norm, including at infinity. -/
theorem norm_interMultiplier_eq
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) :
    ‖interMultiplier ψ hψ U‖ =
      ‖compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport U‖ := by
  apply le_antisymm (norm_interMultiplier_apply_le ψ hψ U)
  have h := norm_restrictCLM_apply_le (show V ⊓ Ω ≤ Ω from inf_le_right)
    (interMultiplier ψ hψ U)
  rwa [restrictCLM_interMultiplier] at h

/-- Every coordinate of a relative cutoff vanishes off the cutoff support. -/
theorem interMultiplier_eq_zero_ae
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) :
    ∀ᵐ x ∂domainMeasure n Ω, x ∉ tsupport ψ.toFun →
      ∀ a, (interMultiplier ψ hψ U).val a x = 0 := by
  filter_upwards [ae_all_iff.mpr (fun a ↦ interMultiplier_coordinate_ae ψ hψ U a)]
    with x hx
  intro hxψ a
  exact (hx a).trans (smoothLeibnizRepresentative_eq_zero ψ.toFun U a.toList hxψ)

end SobolevSpace.VectorValued
