/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Gluing local classical representatives

For a measure positive on nonempty open sets, continuous representatives of the same
almost-everywhere class agree on open overlaps. Second countability gives a countable
subcover, which preserves almost-everywhere agreement after gluing.

The same pointwise agreement identifies representatives obtained at different derivative
orders. One representative then inherits all finite orders, on the domain or its closure.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace MeasureTheory

/-- Local `C^k` representatives of one almost-everywhere class glue to a representative that
is `C^k` at every point of the domain. The measure need only be positive on nonempty
open sets, and the normed spaces need not be complete or finite-dimensional. -/
theorem exists_contDiffAt_ae_eq_of_locally
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : Measure E} [μ.IsOpenPosMeasure]
    {Ω : Set E} {f : E → F} {k : ℕ∞ω}
    (hlocal : ∀ x ∈ Ω, ∃ N : Set E, IsOpen N ∧ x ∈ N ∧ N ⊆ Ω ∧
      ∃ g : E → F, ContDiffOn 𝕜 k g N ∧ g =ᵐ[μ.restrict N] f) :
    ∃ g : E → F, (∀ x ∈ Ω, ContDiffAt 𝕜 k g x) ∧ g =ᵐ[μ.restrict Ω] f := by
  classical
  choose N hN hxN hNΩ g hg hgf using fun x : Ω ↦ hlocal x x.2
  have hsame (x y : Ω) : EqOn (g x) (g y) (N x ∩ N y) := by
    have hx : g x =ᵐ[μ.restrict (N x ∩ N y)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hgf x)
    have hy : g y =ᵐ[μ.restrict (N x ∩ N y)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hgf y)
    exact Measure.eqOn_open_of_ae_eq (hx.trans hy.symm)
      ((hN x).inter (hN y))
      ((hg x).continuousOn.mono inter_subset_left)
      ((hg y).continuousOn.mono inter_subset_right)
  let G : E → F := fun x ↦ if hx : x ∈ Ω then g ⟨x, hx⟩ x else 0
  have hG (x : Ω) : EqOn G (g x) (N x) := by
    intro y hy
    have hyΩ : y ∈ Ω := hNΩ x hy
    dsimp only [G]
    rw [dite_eq_left hyΩ]
    exact hsame ⟨y, hyΩ⟩ x ⟨hxN ⟨y, hyΩ⟩, hy⟩
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    have hreg : ContDiffAt 𝕜 k (g ⟨x, hx⟩) x :=
      (hg ⟨x, hx⟩).contDiffAt ((hN ⟨x, hx⟩).mem_nhds (hxN ⟨x, hx⟩))
    apply hreg.congr_of_eventuallyEq
    filter_upwards [(hN ⟨x, hx⟩).mem_nhds (hxN ⟨x, hx⟩)] with y hy
    exact hG ⟨x, hx⟩ hy
  · have hcover : Ω ⊆ ⋃ x : Ω, N x := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
    obtain ⟨s, hs, hscov⟩ :=
      (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover N hN hcover
    apply ae_restrict_of_ae_restrict_of_subset hscov
    apply (ae_eq_restrict_biUnion_iff N hs G f).mpr
    intro x _
    have hGae : G =ᵐ[μ.restrict (N x)] g x :=
      ae_restrict_of_forall_mem (hN x).measurableSet (hG x)
    exact hGae.trans (hgf x)

/-- Classical representatives at every finite order determine one smooth representative.
All orders represent the same almost-everywhere class on the open set `Ω`. Continuity
identifies them on `Ω`, and then on any set `S` between `Ω` and its closure. This includes
both interior smoothness (`S = Ω`) and smoothness up to the boundary (`S = closure Ω`).
Neither finite dimension nor second countability is needed for this coherence step. -/
theorem exists_contDiffOn_ae_eq_of_forall_nat
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace E] {μ : Measure E} [μ.IsOpenPosMeasure]
    {Ω S : Set E} {f : E → F}
    (hΩ : IsOpen Ω) (hΩS : Ω ⊆ S) (hSΩ : S ⊆ closure Ω)
    (hfinite : ∀ k : ℕ, ∃ g : E → F,
      ContDiffOn 𝕜 k g S ∧ g =ᵐ[μ.restrict Ω] f) :
    ∃ g : E → F, ContDiffOn 𝕜 (⊤ : ℕ∞) g S ∧ g =ᵐ[μ.restrict Ω] f := by
  classical
  choose g hg hgf using hfinite
  refine ⟨g 0, contDiffOn_infty.mpr ?_, hgf 0⟩
  intro k
  have hEqOpen : EqOn (g k) (g 0) Ω :=
    Measure.eqOn_open_of_ae_eq ((hgf k).trans (hgf 0).symm) hΩ
      ((hg k).continuousOn.mono hΩS) ((hg 0).continuousOn.mono hΩS)
  have hEq : EqOn (g k) (g 0) S :=
    hEqOpen.of_subset_closure (hg k).continuousOn (hg 0).continuousOn hΩS hSΩ
  exact (hg k).congr fun x hx ↦ (hEq hx).symm


end MeasureTheory
