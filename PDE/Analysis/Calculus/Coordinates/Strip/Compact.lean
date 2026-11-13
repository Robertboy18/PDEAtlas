/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import PDE.Common.Euclidean

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import PDE.Analysis.Calculus.Jet.Localization

/-!
# State coordinates along a compact strip segment

The time interval is prescribed before the chart is constructed. Injectivity of
the base curve and invertibility of the strip derivative along its compact
zero section give one injective open neighborhood of that entire section.
Mathlib's compact injectivity theorem supplies the global step between the
pointwise inverse function theorems.

The existing compact localization owner extends the inverse near the whole base
image. A uniform closed box then remains inside the inverse agreement region.
Its time set contains the prescribed compact set; only the two transverse widths
are chosen afterwards. All witnesses precede any later cutoff width.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PDE.Analysis

/-- A smooth map that is injective on a compact set and has an invertible
derivative there is a smooth chart on one neighborhood of the whole set.

The target stays inside the prescribed open state domain `Ω`. The derivative
assumption is pointwise on `S`; neither a chart nor a neighborhood on which the
map is injective is assumed. -/
theorem exists_smooth_chart_of_injOn_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} {Ω : Set F}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hinj : InjOn f S)
    (hD : ∀ x ∈ S, ∃ D : E ≃L[ℝ] F, HasFDerivAt f (D : E →L[ℝ] F) x)
    (hΩ : IsOpen Ω) (himage : MapsTo f S Ω) :
    ∃ chart : OpenPartialHomeomorph E F,
      (chart : E → F) = f ∧ S ⊆ chart.source ∧ chart.target ⊆ Ω ∧
      ContDiffOn ℝ ∞ chart chart.source ∧ ContDiffOn ℝ ∞ chart.symm chart.target := by
  let O : Set E := (fderiv ℝ f) ⁻¹' range (fun D : E ≃L[ℝ] F ↦ (D : E →L[ℝ] F))
  have hO : IsOpen O :=
    (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := F)).preimage
      (hf.continuous_fderiv (by simp))
  have hSO : S ⊆ O := fun x hx ↦ (hD x hx).elim fun D hDx ↦ ⟨D, hDx.fderiv.symm⟩
  have hderiv (x : E) (hx : x ∈ O) :
      ∃ D : E ≃L[ℝ] F, HasFDerivAt f (D : E →L[ℝ] F) x := by
    obtain ⟨D, hDx⟩ := hx
    refine ⟨D, ?_⟩
    rw [show (D : E →L[ℝ] F) = fderiv ℝ f x from hDx]
    exact (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hlocal (x : E) (hx : x ∈ O) :
      ∃ c : OpenPartialHomeomorph E F, x ∈ c.source ∧ (c : E → F) = f := by
    obtain ⟨D, hDx⟩ := hderiv x hx
    exact ⟨hf.contDiffAt.toOpenPartialHomeomorph f hDx (by simp),
      hf.contDiffAt.mem_toOpenPartialHomeomorph_source hDx (by simp), rfl⟩
  obtain ⟨V, hV, hSV, hVinj⟩ := hinj.exists_isOpen_superset hS
    (fun _ _ ↦ hf.continuous.continuousAt) fun x hx ↦ by
      obtain ⟨c, hxc, rfl⟩ := hlocal x (hSO hx)
      exact ⟨c.source, c.open_source.mem_nhds hxc, c.injOn⟩
  let U : Set E := (V ∩ O) ∩ f ⁻¹' Ω
  have hU : IsOpen U := (hV.inter hO).inter (hΩ.preimage hf.continuous)
  -- Every point of U still has an invertible derivative, so images of open sets are open.
  have hopen : IsOpenMap (U.domRestrict f) := by
    refine fun s hs ↦ isOpen_iff_mem_nhds.mpr ?_
    rintro y ⟨x, hxs, rfl⟩
    obtain ⟨c, hxc, hc⟩ := hlocal x x.property.1.2
    have hcOpen : IsOpen (f '' (c.source ∩ Subtype.val '' s)) :=
      hc ▸ c.isOpen_image_source_inter (hU.isOpenMap_subtype_val s hs)
    refine mem_of_superset (hcOpen.mem_nhds ⟨x, ⟨hxc, x, hxs, rfl⟩, rfl⟩) ?_
    rintro z ⟨a, ⟨-, a', ha', rfl⟩, rfl⟩
    exact ⟨a', ha', rfl⟩
  let chart : OpenPartialHomeomorph E F :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict
      ((hVinj.mono fun _ hx ↦ hx.1.1).toPartialEquiv f U) hf.continuous.continuousOn hopen hU
  refine ⟨chart, rfl, fun x hx ↦ ⟨⟨hSV hx, hSO hx⟩, himage hx⟩, fun y hy ↦ ?_, hf.contDiffOn,
    chart.open_target.contDiffOn_iff.mpr fun y hy ↦ ?_⟩
  · rw [← show f (chart.symm y) = y from chart.right_inv hy]
    exact (chart.map_target hy).2
  · obtain ⟨D, hDy⟩ := hderiv (chart.symm y) (chart.map_target hy).1.2
    exact chart.contDiffAt_symm hy hDy hf.contDiffAt

/-- An open neighborhood of a compact strip zero section contains a uniform
closed transverse box. The open time set contains all of `K`, including its
endpoints when `K` is a closed interval. -/
theorem exists_uniform_strip_box
    {K : Set ℝ} {O : Set ((ℝ × ℝ) × ℝ)}
    (hK : IsCompact K) (hO : IsOpen O)
    (hzero : ((K ×ˢ {(0 : ℝ)}) ×ˢ {(0 : ℝ)}) ⊆ O) :
    ∃ (T : Set ℝ) (r : ℝ), IsOpen T ∧ K ⊆ T ∧ 0 < r ∧
      ((T ×ˢ Icc (-r) r) ×ˢ Icc (-r) r) ⊆ O := by
  obtain ⟨TM, N, hTM, hN, hKTM, hzeroN, hTMN⟩ :=
    generalized_tube_lemma (hK.prod isCompact_singleton) isCompact_singleton hO hzero
  obtain ⟨T, M, hT, hM, hKT, hzeroM, hTMsub⟩ :=
    generalized_tube_lemma hK isCompact_singleton hTM hKTM
  obtain ⟨r, hr, hball⟩ :
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ℝ) r ⊆ M ∩ N :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      ((hM.inter hN).mem_nhds ⟨hzeroM rfl, hzeroN rfl⟩)
  have hinterval : Icc (-r) r ⊆ M ∩ N := by
    intro x hx
    apply hball
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr hx
  refine ⟨T, r, hT, hKT, hr, ?_⟩
  intro p hp
  exact hTMN ⟨hTMsub ⟨hp.1.1, (hinterval hp.1.2).1⟩, (hinterval hp.2).2⟩

/-- Construct coordinates for the strip on a neighborhood of a prescribed
compact time set, with a global smooth, compactly supported inverse representative.

The derivative of `Ξ((t, μ), n) = w(t, μ) + n • ν` must be an equivalence
at every `((t, 0), 0)` with `t ∈ K`. In dimension three its columns are the time
tangent, the speed variation and `ν`; independence at just one time is insufficient
for an arbitrarily prescribed `K`.

The representative `coord` agrees with the inverse on one open neighborhood `U`
of the entire base image. The closed box has a single positive transverse width
and an open time set containing `K`. The chart, box, representative and derivative
bound are selected without a later cutoff width. -/
theorem exists_smooth_compact_strip_state_chart
    {d : ℕ} {w : ℝ × ℝ → ℝ^d} {K : Set ℝ} {Ω : Set (ℝ^d)}
    (hw : ContDiff ℝ ∞ w) (hK : IsCompact K)
    (hbaseInj : InjOn (fun t ↦ w (t, 0)) K) (ν : ℝ^d)
    (hD : ∀ t ∈ K, ∃ D : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ℝ^d,
      HasFDerivAt (fun p : (ℝ × ℝ) × ℝ ↦ w p.1 + p.2 • ν)
        (D : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ^d) ((t, 0), 0))
    (hΩ : IsOpen Ω) (hbaseΩ : MapsTo (fun t ↦ w (t, 0)) K Ω) :
    ∃ (chart : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) (ℝ^d))
      (coord : ℝ^d → (ℝ × ℝ) × ℝ) (T : Set ℝ) (U : Set (ℝ^d)) (r B : ℝ),
      (chart : ((ℝ × ℝ) × ℝ) → ℝ^d) = (fun p ↦ w p.1 + p.2 • ν) ∧
      ContDiffOn ℝ ∞ chart chart.source ∧
      ContDiffOn ℝ ∞ chart.symm chart.target ∧ chart.target ⊆ Ω ∧
      ContDiff ℝ ∞ coord ∧ HasCompactSupport coord ∧ tsupport coord ⊆ chart.target ∧
      IsOpen U ∧ MapsTo (fun t ↦ w (t, 0)) K U ∧
      U ⊆ chart.target ∧ EqOn coord chart.symm U ∧
      IsOpen T ∧ K ⊆ T ∧ 0 < r ∧
      ((T ×ˢ Icc (-r) r) ×ˢ Icc (-r) r) ⊆ chart.source ∩
        (fun p : (ℝ × ℝ) × ℝ ↦ w p.1 + p.2 • ν) ⁻¹' U ∧
      (∀ t ∈ T, ∀ μ ∈ Icc (-r) r, ∀ n ∈ Icc (-r) r,
        coord (w (t, μ) + n • ν) = ((t, μ), n)) ∧
      (∀ x ∈ U, w (coord x).1 + (coord x).2 • ν = x) ∧
      1 ≤ B ∧ ∀ i : ℕ, i ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ i coord x‖ ≤ B := by
  let Ξ : ((ℝ × ℝ) × ℝ) → ℝ^d := fun p ↦ w p.1 + p.2 • ν
  let S : Set ((ℝ × ℝ) × ℝ) := (K ×ˢ {(0 : ℝ)}) ×ˢ {(0 : ℝ)}
  have hΞ : ContDiff ℝ ∞ Ξ := (hw.comp contDiff_fst).add (contDiff_snd.smul contDiff_const)
  have hS : IsCompact S := (hK.prod isCompact_singleton).prod isCompact_singleton
  have hSinj : InjOn Ξ S := by
    rintro ⟨⟨t, _⟩, _⟩ ⟨⟨ht : t ∈ K, rfl⟩, rfl⟩ ⟨⟨s, _⟩, _⟩ ⟨⟨hs : s ∈ K, rfl⟩, rfl⟩ heq
    rw [hbaseInj ht hs (by simpa only [Ξ, zero_smul, add_zero] using heq)]
  obtain ⟨chart, hchart, hsource, htargetΩ, hchartSmooth, hinverse⟩ :=
    exists_smooth_chart_of_injOn_compact hΞ hS hSinj
      (by rintro ⟨⟨t, _⟩, _⟩ ⟨⟨ht, rfl⟩, rfl⟩; exact hD t ht) hΩ
      (by rintro ⟨⟨t, _⟩, _⟩ ⟨⟨ht, rfl⟩, rfl⟩; simpa only [Ξ, zero_smul, add_zero] using hbaseΩ ht)
  have himageTarget : Ξ '' S ⊆ chart.target := by
    rintro x ⟨p, hp, rfl⟩
    exact hchart ▸ chart.map_source (hsource hp)
  -- Localize around the compact image, rather than a germ at one selected time.
  obtain ⟨χ, U, _, _, _, _, hU, himageU, hUtarget, _, hcoord, hcompact, hsupport, hagree⟩ :=
    exists_smooth_cutoff_localization hinverse chart.open_target
      (hS.image hΞ.continuous) himageTarget
  set coord : ℝ^d → (ℝ × ℝ) × ℝ := chart.target.indicator (fun x ↦ χ x • chart.symm x)
  obtain ⟨T, r, hT, hKT, hr, hbox⟩ := exists_uniform_strip_box hK
    (chart.open_source.inter (hU.preimage hΞ.continuous))
    fun p hp ↦ ⟨hsource hp, himageU ⟨p, hp, rfl⟩⟩
  have hrecover (t : ℝ) (ht : t ∈ T) (μ : ℝ) (hμ : μ ∈ Icc (-r) r)
      (n : ℝ) (hn : n ∈ Icc (-r) r) :
      coord (w (t, μ) + n • ν) = ((t, μ), n) := by
    have hp := hbox (show ((t, μ), n) ∈ (T ×ˢ Icc (-r) r) ×ˢ Icc (-r) r from ⟨⟨ht, hμ⟩, hn⟩)
    change coord (Ξ ((t, μ), n)) = ((t, μ), n)
    rw [hagree hp.2, ← hchart]
    exact chart.left_inv hp.1
  have hright (x : ℝ^d) (hx : x ∈ U) : w (coord x).1 + (coord x).2 • ν = x := by
    change Ξ (coord x) = x
    rw [hagree hx, ← hchart]
    exact chart.right_inv (hUtarget hx)
  obtain ⟨C, _, hC⟩ := hcompact.exists_bound_iteratedFDeriv hcoord 2
  exact ⟨chart, coord, T, U, r, max 1 C, hchart, hchartSmooth, hinverse, htargetΩ,
    hcoord, hcompact, hsupport, hU,
    fun ⦃t⦄ ht ↦ by simpa only [Ξ, zero_smul, add_zero] using
      (himageU ⟨((t, 0), 0), ⟨⟨ht, rfl⟩, rfl⟩, rfl⟩ : Ξ ((t, 0), 0) ∈ U),
    hUtarget, hagree, hT, hKT, hr, hbox, hrecover, hright, le_max_left _ _,
    fun i hi x ↦ (hC i hi x).trans (le_max_right _ _)⟩

end PDE.Analysis
