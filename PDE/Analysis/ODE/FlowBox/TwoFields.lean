/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.FlowBox.Transverse

/-!
# Invariant coordinates for two transverse planar fields

The second coordinate of a flow box is constant along its field. Apply this construction
to each of two transverse C¹ fields. At the base point the two resulting differentials
are the two dual coordinates, in reverse order, so their pair is locally invertible.
Continuity preserves the nonzero transverse derivatives on a common neighborhood.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.ODE

/-- Two C¹ planar fields transverse at a point construct a C¹ coordinate pair.
The first coordinate annihilates `v₀`, the second annihilates `v₁`, and both
transverse derivatives are nonzero throughout the chart source. -/
theorem exists_invariant_coordinates_of_transverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v₀ v₁ : E → E} {q₀ : E}
    (hv₀ : ContDiffAt ℝ 1 v₀ q₀) (hv₁ : ContDiffAt ℝ 1 v₁ q₀)
    (e : (ℝ × ℝ) ≃L[ℝ] E) (he₀ : v₀ q₀ = e (1, 0)) (he₁ : v₁ q₀ = e (0, 1)) :
    ∃ c : OpenPartialHomeomorph E (ℝ × ℝ),
      q₀ ∈ c.source ∧ c q₀ = 0 ∧
      ContDiffOn ℝ 1 c c.source ∧ ContDiffOn ℝ 1 c.symm c.target ∧
      ∀ q ∈ c.source,
        fderiv ℝ (fun x ↦ (c x).1) q (v₀ q) = 0 ∧
        fderiv ℝ (fun x ↦ (c x).2) q (v₁ q) = 0 ∧
        fderiv ℝ (fun x ↦ (c x).1) q (v₁ q) ≠ 0 ∧
        fderiv ℝ (fun x ↦ (c x).2) q (v₀ q) ≠ 0 := by
  let swap := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  obtain ⟨c₀, hq₀, hc₀zero, hc₀, _, hDc₀, hann₀⟩ :=
    exists_flow_box_of_transverse hv₀ e he₀
  obtain ⟨c₁, hq₁, hc₁zero, hc₁, _, hDc₁, hann₁⟩ :=
    exists_flow_box_of_transverse hv₁ (swap.trans e) he₁
  let w₀ : E → ℝ := fun q ↦ (c₀ q).2
  let w₁ : E → ℝ := fun q ↦ (c₁ q).2
  let W : E → ℝ × ℝ := fun q ↦ (w₀ q, w₁ q)
  have hw₀ : ContDiffAt ℝ 1 w₀ q₀ := (hc₀.contDiffAt (c₀.open_source.mem_nhds hq₀)).snd
  have hw₁ : ContDiffAt ℝ 1 w₁ q₀ := (hc₁.contDiffAt (c₁.open_source.mem_nhds hq₁)).snd
  have hW : ContDiffAt ℝ 1 W q₀ := hw₀.prodMk hw₁
  have hWzero : W q₀ = 0 := by simp [W, w₀, w₁, hc₀zero, hc₁zero]
  have hDW : HasFDerivAt W (e.symm.trans swap : E →L[ℝ] ℝ × ℝ) q₀ := by
    convert! hDc₀.snd.prodMk hDc₁.snd using 1
  have htrans₀ : fderiv ℝ w₀ q₀ (v₁ q₀) = 1 := by
    rw [hDc₀.snd.fderiv, he₁]
    change (e.symm (e (0, 1))).2 = 1
    simp
  have htrans₁ : fderiv ℝ w₁ q₀ (v₀ q₀) = 1 := by
    rw [hDc₁.snd.fderiv, he₀]
    change (swap.symm (e.symm (e (1, 0)))).2 = 1
    simp [swap]
  have hnonzero₀ : ∀ᶠ q in 𝓝 q₀, fderiv ℝ w₀ q (v₁ q) ≠ 0 := by
    have hc := (hw₀.continuousAt_fderiv one_ne_zero).clm_apply hv₁.continuousAt
    exact hc.eventually_ne (by rw [htrans₀]; exact one_ne_zero)
  have hnonzero₁ : ∀ᶠ q in 𝓝 q₀, fderiv ℝ w₁ q (v₀ q) ≠ 0 := by
    have hc := (hw₁.continuousAt_fderiv one_ne_zero).clm_apply hv₀.continuousAt
    exact hc.eventually_ne (by rw [htrans₁]; exact one_ne_zero)
  let a := hW.toOpenPartialHomeomorph W hDW one_ne_zero
  have hqa : q₀ ∈ a.source := hW.mem_toOpenPartialHomeomorph_source hDW one_ne_zero
  have hai : ContDiffAt ℝ 1 a.symm (W q₀) := hW.to_localInverse hDW one_ne_zero
  have hgood : ∀ᶠ q in 𝓝 q₀,
      q ∈ c₀.source ∧ q ∈ c₁.source ∧
      ContDiffAt ℝ 1 a.symm (W q) ∧
      fderiv ℝ w₀ q (v₁ q) ≠ 0 ∧ fderiv ℝ w₁ q (v₀ q) ≠ 0 := by
    filter_upwards [c₀.open_source.mem_nhds hq₀, c₁.open_source.mem_nhds hq₁,
      hW.continuousAt.eventually (hai.eventually (by simp)), hnonzero₀, hnonzero₁]
      with q hq₀ hq₁ hreg ht₀ ht₁
    exact ⟨hq₀, hq₁, hreg, ht₀, ht₁⟩
  obtain ⟨V, hVsub, hV, hqV⟩ := mem_nhds_iff.mp hgood
  let c := a.restrOpen V hV
  have hsource (q : E) (hq : q ∈ c.source) : q ∈ V := hq.2
  refine ⟨c, ⟨hqa, hqV⟩, hWzero, ?_, ?_, ?_⟩
  · intro q hq
    have h := hVsub (hsource q hq)
    exact ((hc₀.contDiffAt (c₀.open_source.mem_nhds h.1)).snd.prodMk
      (hc₁.contDiffAt (c₁.open_source.mem_nhds h.2.1)).snd).contDiffWithinAt
  · intro p hp
    have h := hVsub (hsource (c.symm p) (c.map_target hp))
    have heq : W (c.symm p) = p := c.right_inv hp
    exact (heq ▸ h.2.2.1).contDiffWithinAt
  · intro q hq
    obtain ⟨hq₀, hq₁, _, ht₀, ht₁⟩ := hVsub (hsource q hq)
    have hd₀ := (hc₀.contDiffAt (c₀.open_source.mem_nhds hq₀)).differentiableAt_one
    have hd₁ := (hc₁.contDiffAt (c₁.open_source.mem_nhds hq₁)).differentiableAt_one
    refine ⟨?_, ?_, ht₀, ht₁⟩
    · change fderiv ℝ w₀ q (v₀ q) = 0
      rw [hd₀.hasFDerivAt.snd.fderiv]
      exact congrArg Prod.snd (hann₀ q hq₀)
    · change fderiv ℝ w₁ q (v₁ q) = 0
      rw [hd₁.hasFDerivAt.snd.fderiv]
      exact congrArg Prod.snd (hann₁ q hq₁)

end PDE.Analysis.ODE
