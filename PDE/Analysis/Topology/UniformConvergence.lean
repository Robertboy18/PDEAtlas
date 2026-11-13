/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.Pi

/-!
# Continuous transformations of locally uniform limits

Continuous composition preserves a continuous locally uniform limit. Product
limits are checked coordinate by coordinate, including infinite products.
-/

public section

open Filter Set
open scoped Topology

/-- A continuous function preserves locally uniform convergence to a continuous
limit. No uniform continuity on the entire target space is required. -/
theorem Continuous.comp_tendstoLocallyUniformlyOn
    {α β γ ι : Type*} [TopologicalSpace α] [UniformSpace β] [UniformSpace γ]
    {F : ι → α → β} {f : α → β} {g : β → γ} {l : Filter ι} {s : Set α}
    (hg : Continuous g) (hF : TendstoLocallyUniformlyOn F f l s)
    (hf : ContinuousOn f s) :
    TendstoLocallyUniformlyOn (fun i x ↦ g (F i x)) (fun x ↦ g (f x)) l s := by
  refine tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr fun x hx ↦ ?_
  have hleft : Tendsto (fun y : ι × α ↦ f y.2) (l ×ˢ 𝓝[s] x) (𝓝 (f x)) :=
    (hf x hx).tendsto.comp tendsto_snd
  have hright := hleft.congr_uniformity
    (tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hF x hx)
  exact ((hg.continuousAt.tendsto.comp hleft).prodMk_nhds
    (hg.continuousAt.tendsto.comp hright)).mono_right (nhds_le_uniformity (g (f x)))

namespace PDE

/-- Locally uniform convergence into a product is equivalent to locally uniform
convergence in every coordinate. The index set need not be finite. -/
theorem tendstoLocallyUniformlyOn_pi
    {α ι J : Type*} [TopologicalSpace α] {β : J → Type*} [∀ j, UniformSpace (β j)]
    {F : ι → α → ∀ j, β j} {f : α → ∀ j, β j} {l : Filter ι} {S : Set α} :
    TendstoLocallyUniformlyOn F f l S ↔
      ∀ j, TendstoLocallyUniformlyOn (fun i x ↦ F i x j) (fun x ↦ f x j) l S := by
  simp only [tendstoLocallyUniformlyOn_iff_forall_tendsto, Pi.uniformity,
    tendsto_iInf, tendsto_comap_iff, Function.comp_def]
  exact ⟨fun h j x hx ↦ h x hx j, fun h x hx j ↦ h j x hx⟩

end PDE
