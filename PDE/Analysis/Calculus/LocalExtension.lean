/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Compactly supported representatives of differentiable germs

A map that is `C^m` near one point has a globally `C^m`, compactly supported representative
with the same germ there. Multiplication by a bump function proves this without requiring
regularity outside the original neighborhood. For a finite-order germ, the domain
may be any finite-dimensional real normed space: transport to Euclidean coordinates
and back gives the same conclusion without changing the given norm.

This permits local differential identities to reuse globally stated calculus results.
For `C^∞`, regularity on an open neighborhood is required: `C^∞` at a point alone need
not give a common neighborhood on which all derivative orders are continuous.

The annular version cuts off a kernel near zero and far away while preserving
its values between two positive radii, so singular potentials can use the
compact-support convolution lemmas without differentiating the kernel repeatedly.

`PDE.Analysis.standardBump` is a fixed smooth bump on `ℝ^n`, equal to one on the unit ball and
supported in the ball of radius two. The Sobolev cutoffs, the half-line zero-trace argument, and
the affine-interface trace all use rescalings of it.
-/

@[expose] public section

open Filter Function Metric Set
open scoped Topology

/-- A function `C^m` on an open neighborhood has a compactly supported global representative
of the same germ and regularity. The order may be infinite. -/
theorem ContDiffOn.exists_contDiff_compactSupport_eventuallyEq
    {d : ℕ} {m : ℕ∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ^d → F} {s : Set (ℝ^d)} {x : ℝ^d}
    (hf : ContDiffOn ℝ m f s) (hs : IsOpen s) (hx : x ∈ s) :
    ∃ g : ℝ^d → F, ContDiff ℝ m g ∧ HasCompactSupport g ∧ f =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hnear⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let b : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨fun y ↦ b y • f y, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport b
    · have hyBall : y ∈ Metric.ball x r := by
        rw [b.tsupport_eq] at hy
        exact Metric.closedBall_subset_ball (half_lt_self hr) hy
      exact b.contDiff.contDiffAt.smul (hf.contDiffAt (hs.mem_nhds (hnear hyBall)))
    · have hz : (fun z ↦ b z • f z) =ᶠ[𝓝 y] fun _ ↦ (0 : F) := by
        filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hy] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact b.hasCompactSupport.smul_right
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp [hy]

/-- A finite-order differentiable germ on a finite-dimensional real normed space
has a compactly supported global representative of the same regularity.

Transport to Euclidean coordinates, apply the Euclidean cutoff construction, and
transport back. No change to the original norm or inner product is required. -/
theorem ContDiffAt.exists_contDiff_compactSupport_eventuallyEq
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} {f : E → G} {x : E} (hf : ContDiffAt ℝ m f x) :
    ∃ g : E → G, ContDiff ℝ m g ∧ HasCompactSupport g ∧ f =ᶠ[𝓝 x] g := by
  classical
  let e : E ≃L[ℝ] ℝ^(Module.finrank ℝ E) :=
    (Module.finBasis ℝ E).equivFunL.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  have hf' : ContDiffAt ℝ m f (e.symm (e x)) := by
    simpa only [e.symm_apply_apply] using hf
  have hlocal : ContDiffAt ℝ m (fun y ↦ f (e.symm y)) (e x) :=
    hf'.comp (e x) e.symm.contDiff.contDiffAt
  obtain ⟨s, hs, hfs⟩ := hlocal.contDiffOn le_rfl (by simp)
  obtain ⟨u, hus, hu, hxu⟩ := _root_.mem_nhds_iff.mp hs
  obtain ⟨g, hg, hcompact, heq⟩ :=
    (hfs.mono hus).exists_contDiff_compactSupport_eventuallyEq hu hxu
  refine ⟨g ∘ e, hg.comp e.contDiff,
    hcompact.comp_homeomorph e.toHomeomorph, ?_⟩
  have h := heq.comp_tendsto e.continuous.continuousAt
  simpa only [Function.comp_def, e.symm_apply_apply] using h

/-- A kernel smooth away from zero has a smooth compactly supported representative
agreeing with it on a prescribed annulus. The regularity order may be infinite. -/
theorem ContDiffOn.exists_contDiff_compactSupport_eqOn_annulus
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ∞} {K : E → F} (hK : ContDiffOn ℝ m K ({0}ᶜ : Set E))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ G : E → F, ContDiff ℝ m G ∧ HasCompactSupport G ∧
      ∀ z, a ≤ ‖z‖ → ‖z‖ ≤ b → G z = K z := by
  let _ : FiniteDimensional ℝ E := .of_locallyCompactSpace ℝ
  let innerCutoff : ContDiffBump (0 : E) :=
    { rIn := a / 2
      rOut := a
      rIn_pos := half_pos ha
      rIn_lt_rOut := half_lt_self ha }
  let outerCutoff : ContDiffBump (0 : E) :=
    { rIn := b
      rOut := b + 1
      rIn_pos := hb
      rIn_lt_rOut := lt_add_one b }
  let G : E → F := fun z ↦ outerCutoff z • ((1 - innerCutoff z) • K z)
  refine ⟨G, ?_, outerCutoff.hasCompactSupport.smul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst z
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [innerCutoff.eventuallyEq_one] with z hz
      simp [G, hz]
    · have hreg : ContDiffAt ℝ m K z :=
        hK.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hz)
      exact outerCutoff.contDiffAt.smul
        ((contDiffAt_const.sub innerCutoff.contDiffAt).smul hreg)
  · intro z haz hzb
    have hi : innerCutoff z = 0 := innerCutoff.zero_of_le_dist (by
      simpa [innerCutoff, dist_zero_right] using haz)
    have ho : outerCutoff z = 1 := outerCutoff.one_of_mem_closedBall (by
      simpa [outerCutoff, mem_closedBall, dist_zero_right] using hzb)
    simp [G, hi, ho]

namespace PDE.Analysis

/-- The standard smooth bump on `ℝ^n`: equal to one on the closed unit ball and supported in
the closed ball of radius two. Cutoff and test-function constructions rescale this bump. -/
def standardBump (n : ℕ) : ContDiffBump (0 : ℝ^n) :=
  { rIn := 1
    rOut := 2
    rIn_pos := zero_lt_one
    rIn_lt_rOut := one_lt_two }

end PDE.Analysis
