/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FullEmbedding

/-!
# Morrey representatives up to a C¹ boundary

A bounded open set with C¹ graph boundary has a bounded Sobolev extension operator.
Applying whole-space Morrey embedding to that extension gives a Hölder representative
on the closure, with the full norm controlled by the original Sobolev norm. The result
includes the Lipschitz endpoint `p = ∞` and takes no atlas or extension operator as input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace

/-- Sobolev elements on a bounded C¹ domain have globally defined Hölder representatives
of controlled norm. The constant depends only on the domain, dimension and exponent. -/
theorem exists_morreyExtensionBound_of_hasC1GraphBoundary
    {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)} [Fact (1 ≤ p)]
    (hn : 0 < n) (hp : (n : ℝ≥0∞) < p)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : Boundary.HasC1GraphBoundary Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : W^{1,p}(Ω),
      ∃ F : HolderSpace.C0GammaOn (ℝ^n) (morreyHolderExponent n p hn hp),
        (fun x ↦ F x) =ᵐ[domainMeasure n Ω] GraphSpace.baseRepresentative U ∧
        ‖F‖ ≤ C * ‖U‖ := by
  cases n with
  | zero => cases hn
  | succ n =>
    have : Fact (0 < n + 1) := ⟨hn⟩
    let := hboundary.c1ExtensionAtlas hopen hbounded
    let E := Extension.C1.extensionCLM (n := n + 1) (p := p) (Ω := Ω)
    obtain ⟨C, hC, hbound⟩ := exists_morreyEmbeddingBound hn hp
    refine ⟨C * ‖E‖, mul_nonneg hC (norm_nonneg E), fun U ↦ ?_⟩
    obtain ⟨F, heq, hnorm⟩ := hbound (E U)
    refine ⟨F, ?_, ?_⟩
    · filter_upwards [ae_restrict_of_ae (s := Ω) heq,
        Extension.C1.extensionCLM_agree_ae U] with x hx hE
      exact hx.trans hE
    · calc
        ‖F‖ ≤ C * ‖E U‖ := hnorm
        _ ≤ C * (‖E‖ * ‖U‖) := mul_le_mul_of_nonneg_left (E.le_opNorm U) hC
        _ = (C * ‖E‖) * ‖U‖ := (mul_assoc _ _ _).symm

/-- The full Morrey estimate on the closure of a bounded C¹ domain, for every
supercritical exponent including infinity. Agreement is almost everywhere on the
original domain, as appropriate for a Sobolev representative. -/
theorem exists_morreyClosureBound_of_hasC1GraphBoundary
    {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)} [Fact (1 ≤ p)]
    (hn : 0 < n) (hp : (n : ℝ≥0∞) < p)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : Boundary.HasC1GraphBoundary Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : W^{1,p}(Ω),
      ∃ F : HolderSpace.C0GammaOn (closure Ω) (morreyHolderExponent n p hn hp),
        (∀ᵐ x ∂domainMeasure n Ω, ∀ hx : x ∈ closure Ω,
          F ⟨x, hx⟩ = GraphSpace.baseRepresentative U x) ∧
        ‖F‖ ≤ C * ‖U‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_morreyExtensionBound_of_hasC1GraphBoundary hn hp hopen hbounded hboundary
  refine ⟨C, hC, fun U ↦ ?_⟩
  obtain ⟨F, heq, hnorm⟩ := hbound U
  refine ⟨HolderSpace.C0GammaOn.restrict (closure Ω) F, ?_, ?_⟩
  · filter_upwards [heq] with x hx
    exact fun _ ↦ hx
  · exact (HolderSpace.C0GammaOn.norm_restrict_le (closure Ω) F).trans hnorm

end SobolevSpace
