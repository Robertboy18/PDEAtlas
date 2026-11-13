/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Cylinder
public import PDE.Analysis.Calculus.CompactCurry.Boundary
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# First jets at the initial face of a cylinder

Continuous extensions of the interior first partials determine spatial
derivatives on the initial slice and the right derivative in time.
Uniform derivative closure handles the spatial directions; the one-sided
derivative extension theorem handles time. Neither argument differentiates an
arbitrary continuation outside the cylinder.
-/

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open PDE.Common Filter Set
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^(n + 1) → ℝ}

/-- The continuous interior spatial jet differentiates the slice even at
a boundary time. No regularity of the spatial boundary is required. -/
theorem hasFDerivAt_spaceSlice_closure
    (hu : ContDiffUpToBoundary 1 u (spaceTimeCylinder Ω I))
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hI : IsOpen I)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω I)))
    (D : Fin (n + 1) → ℝ^(n + 1) → ℝ) (hD : ∀ i, Continuous (D i))
    (heq : ∀ i, EqOn (D i) (∂[i] u) (spaceTimeCylinder Ω I))
    {t : ℝ} (ht : t ∈ closure I) {x : ℝ^n} (hx : x ∈ Ω) :
    HasFDerivAt (fun y ↦ u (timeSpaceCons t y))
      (∑ i : Fin n, D i.succ (timeSpaceCons t x) • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  obtain ⟨F, hF, hFu⟩ := hu.exists_continuous_eqOn
  have hFuc : EqOn F u (closure (spaceTimeCylinder Ω I)) :=
    hFu.of_subset_closure hF.continuousOn hc subset_closure Subset.rfl
  have hcons := (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous
  have hd := BoundedContinuousFunction.hasFDerivAt_slice_closure_parameter
    ⟨closure Ω, hbounded.isCompact_closure⟩ hΩ subset_closure
    (fun s y ↦ F (timeSpaceCons s y))
    (fun s y ↦ ∑ i : Fin n, D i.succ (timeSpaceCons s y) • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ))
    (hF.comp hcons)
    (continuous_finsetSum _ fun i _ ↦
      ((hD i.succ).comp hcons).smul continuous_const) (S := I) ?_ ht hx
  · apply hd.congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (hFuc (by
      rw [closure_spaceTimeCylinder]
      exact timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, subset_closure hy⟩)).symm
  · intro s hs y hy
    have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hy⟩
    have hud := (hu.contDiffOn.contDiffAt
      ((isOpen_spaceTimeCylinder hΩ hI).mem_nhds hp)).differentiableAt (by simp)
    have hsliced := hud.comp y (hasFDerivAt_timeSpaceCons_spatial n s y).differentiableAt
    have hmap :
        fderiv ℝ (fun z ↦ u (timeSpaceCons s z)) y =
          ∑ i : Fin n, D i.succ (timeSpaceCons s y) • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) := by
      rw [PDE.fderiv_eq_sum_partialDeriv_smul_proj]
      apply Finset.sum_congr rfl
      intro i _
      rw [PDE.partialDeriv_timeSpaceCons_spatial i u s y hud, heq i.succ hp]
    rw [← hmap]
    apply hsliced.hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hy] with z hz
    exact hFu (timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hz⟩)

/-- The continuous time-partial trace is the right derivative at the
initial time. In particular, the total `derivWithin` expression is justified. -/
theorem hasDerivWithinAt_initial_time
    {a b : ℝ} (hab : a < b)
    (hu : ContDiffUpToBoundary 1 u (spaceTimeCylinder Ω (Ioo a b)))
    (hΩ : IsOpen Ω)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    {D : ℝ^(n + 1) → ℝ} (hD : Continuous D)
    (heq : EqOn D (∂[0] u) (spaceTimeCylinder Ω (Ioo a b)))
    {x : ℝ^n} (hx : x ∈ Ω) :
    HasDerivWithinAt (fun s ↦ u (timeSpaceCons s x))
      (D (timeSpaceCons a x)) (Ici a) a := by
  have hd (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r ↦ u (timeSpaceCons r x)) (D (timeSpaceCons s x)) s := by
    have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hx⟩
    rw [heq hp]
    exact PDE.hasDerivAt_timeSpaceCons u s x ((hu.contDiffOn.contDiffAt
      ((isOpen_spaceTimeCylinder hΩ isOpen_Ioo).mem_nhds hp)).differentiableAt (by simp))
  have hcurve : Continuous (fun s ↦ timeSpaceCons (n := n) s x) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have huc : ContinuousOn (fun s ↦ u (timeSpaceCons s x)) (Icc a b) := by
    apply hc.comp hcurve.continuousOn
    intro s hs
    rw [closure_spaceTimeCylinder, closure_Ioo hab.ne]
    exact timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, subset_closure hx⟩
  refine hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
    ((huc a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab) ?_
  apply (((hD.comp hcurve).tendsto a).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [Ioo_mem_nhdsGT hab] with s hs
  exact (hd s hs).deriv.symm

/-- Zero initial displacement and right velocity force all continuous
first-partial traces to vanish on the initial spatial domain. The traces are
constructed from raw closure regularity. -/
theorem continuousRepresentative_partialDeriv_initial_eq_zero
    {k : ℕ}
    {a b : ℝ} (hab : a < b)
    (hu : ContDiffUpToBoundary (k + 1) u (spaceTimeCylinder Ω (Ioo a b)))
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hpos : ∀ x ∈ Ω, u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Ω, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici a) a = 0)
    (i : Fin (n + 1)) {x : ℝ^n} (hx : x ∈ Ω) :
    (hu.partialDeriv_of_succ (isOpen_spaceTimeCylinder hΩ isOpen_Ioo) i).continuousRepresentative
      (timeSpaceCons a x) = 0 := by
  have hj (j : Fin (n + 1)) :=
    hu.partialDeriv_of_succ (isOpen_spaceTimeCylinder hΩ isOpen_Ioo) j
  let D (j : Fin (n + 1)) := (hj j).continuousRepresentative
  have hD (j : Fin (n + 1)) : Continuous (D j) :=
    (hj j).continuous_continuousRepresentative
  have heq (j : Fin (n + 1)) :
      EqOn (D j) (∂[j] u) (spaceTimeCylinder Ω (Ioo a b)) :=
    (hj j).continuousRepresentative_eqOn
  have hu1 := hu.of_le (show 1 ≤ k + 1 by omega)
  change D i (timeSpaceCons a x) = 0
  cases i using Fin.cases with
  | zero =>
    exact ((hu1.hasDerivWithinAt_initial_time hab hΩ hc (hD 0) (heq 0) hx).derivWithin
      (uniqueDiffOn_Ici a a (by simp))).symm.trans (hvel x hx)
  | succ i =>
    have hd := hu1.hasFDerivAt_spaceSlice_closure hΩ hbounded isOpen_Ioo hc D hD heq
      (show a ∈ closure (Ioo a b) by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩) hx
    have hz : (fun _ : ℝ^n ↦ (0 : ℝ)) =ᶠ[𝓝 x] fun y ↦ u (timeSpaceCons a y) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy using (hpos y hy).symm
    have hzero := (hd.congr_of_eventuallyEq hz).unique (hasFDerivAt_const 0 x)
    have hi := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hzero
    simpa using hi

/-- Raw C¹ closure data have a right time derivative at every interior
spatial point on the initial face. No derivative trace is supplied. -/
theorem differentiableWithinAt_initial_time
    {a b : ℝ} (hab : a < b)
    (hu : ContDiffUpToBoundary 1 u (spaceTimeCylinder Ω (Ioo a b)))
    (hΩ : IsOpen Ω)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    {x : ℝ^n} (hx : x ∈ Ω) :
    DifferentiableWithinAt ℝ (fun s ↦ u (timeSpaceCons s x)) (Ici a) a := by
  have hd := hu.partialDeriv_of_succ (isOpen_spaceTimeCylinder hΩ isOpen_Ioo) 0
  have h := hu.hasDerivWithinAt_initial_time hab hΩ hc
    hd.continuous_continuousRepresentative hd.continuousRepresentative_eqOn hx
  exact h.differentiableWithinAt

end SobolevSpace.ContDiffUpToBoundary
