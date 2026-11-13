/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge
public import PDE.Spaces.Sobolev.Inequalities.Morrey.GraphBoundary

/-!
# Lipschitz representatives and W¹,∞

On a bounded measurable set, a Lipschitz function is bounded. A Lipschitz extension
to the whole space then supplies bounded weak derivatives through the
line-derivative integration-by-parts theorem.

On a bounded open set with C¹ graph boundary the converse follows from Sobolev extension and the
infinite-exponent Morrey theorem. Thus W¹,∞ membership is equivalent to the existence of an
almost-everywhere equal Lipschitz representative, as in Evans, §5.8.2, Theorem 4. Neither direction
assumes a bound or an extension as additional data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2, Theorem 4, pp. 294-295: on a bounded open set with C¹
  boundary, `u` is Lipschitz continuous if and only if `u ∈ W^{1,∞}(U)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace

namespace GraphSpace

/-- A function Lipschitz on a bounded measurable domain has a W¹,∞ graph
element representing it. Boundedness of the function and all weak derivatives are
derived, rather than supplied as hypotheses. -/
theorem exists_w1Top_of_lipschitzOnWith
    {n : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ} {K : ℝ≥0}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hf : LipschitzOnWith K f Ω) :
    ∃ U : W^{1,∞}(Ω),
      baseRepresentative U =ᵐ[domainMeasure n Ω] f := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  obtain ⟨B, hB⟩ := (hg.isBounded_image hbounded).exists_norm_le
  have hmem : MemLp g ∞ (domainMeasure n Ω) := by
    apply memLp_top_of_bound hg.continuous.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hB (g x) (mem_image_of_mem g hx)
  let F := hmem.toLp g
  have hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g := hmem.coeFn_toLp
  refine ⟨w1TopOfLipschitzRepresentative hΩ F g K hg hF, ?_⟩
  filter_upwards [w1TopOfLipschitzRepresentative_base_ae hΩ F g K hg hF,
    hF, ae_restrict_mem hΩ] with x hx hxg hxΩ
  exact hx.trans (hxg.trans (heq hxΩ).symm)

end GraphSpace

/-- On a bounded open C¹ domain, W¹,∞ membership is equivalent to having a
Lipschitz representative. The Sobolev element on the left has the given function as its base,
so this statement includes both its essential boundedness and its weak derivatives. -/
theorem exists_sobolevSpaceOn_iff_lipschitzRepresentative
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : Boundary.HasC1GraphBoundary Ω) (f : ℝ^n → ℝ) :
    (∃ u : SobolevSpaceOn n 1 ∞ Ω, u.toFun = f) ↔
      ∃ (K : ℝ≥0) (v : ℝ^n → ℝ),
        LipschitzOnWith K v Ω ∧ v =ᵐ[domainMeasure n Ω] f := by
  constructor
  · rintro ⟨u, rfl⟩
    let U := GraphSpace.ofRepresentative u
    obtain ⟨C, _, hbound⟩ :=
      exists_morreyExtensionBound_of_hasC1GraphBoundary hn
        (p := ∞) (by simp) hopen hbounded hboundary
    obtain ⟨F, heq, _⟩ := hbound U
    have hLip : LipschitzWith F.holderSeminorm (fun x ↦ F x) := by
      apply holderWith_one.mp
      simpa only [morreyHolderExponent_top, HolderSpace.Exponent.coe_one] using F.holderWith
    refine ⟨F.holderSeminorm, fun x ↦ F x, hLip.lipschitzOnWith, ?_⟩
    exact heq.trans (GraphSpace.ofRepresentative_base_ae u)
  · rintro ⟨K, v, hv, heq⟩
    obtain ⟨U, hU⟩ :=
      GraphSpace.exists_w1Top_of_lipschitzOnWith hopen.measurableSet hbounded hv
    refine ⟨(GraphSpace.toRepresentative U).ofAEEq f ?_, rfl⟩
    exact (hU.trans heq).symm

end SobolevSpace
