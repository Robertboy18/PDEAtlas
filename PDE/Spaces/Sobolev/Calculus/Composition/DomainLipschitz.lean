/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition
public import PDE.Spaces.Sobolev.Calculus.Composition.OpenDomainLipschitz

/-!
# Lipschitz composition on domains of finite measure

A Lipschitz scalar map acts on `W¹ᵖ(Ω)` whenever `Ω` is open and has finite
measure, for every `1 ≤ p ≤ ∞`. The map need not fix zero: its constant
offset is integrable on `Ω`, while Lipschitz growth controls the remaining
part by the original function.

The weak chain rule itself is local and imposes no boundary regularity.
This construction uses that rule directly. On domains of infinite measure,
`lipschitzCompositionOfMemLp` provides the same construction whenever the
composition belongs to `Lᵖ`.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function
open scoped ENNReal NNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
  [IsFiniteMeasure (domainMeasure n Ω)]

/-- Compose a first-order Sobolev function with a Lipschitz scalar map on
an open domain of finite measure. No regularity of the boundary is needed. -/
def lipschitzCompositionOn
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (U : W^{1,p}(Ω)) : W^{1,p}(Ω) :=
  lipschitzCompositionOfMemLp hΩ hF U
    (hF.comp_memLp_of_memLp_const (memLp_const _) (Lp.memLp _))

/-- The base representative is the pointwise composition almost everywhere. -/
theorem lipschitzCompositionOn_base_ae
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (U : W^{1,p}(Ω)) :
    baseRepresentative (lipschitzCompositionOn hΩ hF U)
      =ᵐ[domainMeasure n Ω] F ∘ baseRepresentative U :=
  lipschitzCompositionOfMemLp_base_ae hΩ hF U _

/-- Weak derivatives of composition satisfy the scalar chain rule. -/
theorem lipschitzCompositionOn_derivative_ae
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    ((lipschitzCompositionOn hΩ hF U).val (singleDerivIndex n i) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x :=
  lipschitzCompositionOfMemLp_derivative_ae hΩ hF U _ i

omit [IsFiniteMeasure (domainMeasure n Ω)] in
/-- A scalar map Lipschitz on the essential value range of an H¹ function has an
H¹ representative. The extension outside that range is only used in the proof. -/
theorem exists_h1_composition_of_lipschitzOn
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℝ → ℝ} {s : Set ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (U : W^{1,2}(Ω)) (hU : ∀ᵐ x ∂domainMeasure n Ω, wkpBaseCoordinateCLM U x ∈ s) :
    ∃ F : W^{1,2}(Ω), (wkpBaseCoordinateCLM F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ f (wkpBaseCoordinateCLM U x) := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  refine ⟨lipschitzCompositionOn hΩ hg U, ?_⟩
  filter_upwards [lipschitzCompositionOn_base_ae hΩ hg U, hU] with x hx hs
  exact hx.trans (hfg hs).symm

end SobolevSpace.GraphSpace
