/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Extend
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal

/-!
# Extending classical derivatives to a smooth domain closure

An operational `C¹` boundary atlas makes the domain locally equivalent to
an upper half-space. Consequently, a globally continuous derivative field
that is the Fréchet derivative in the open domain remains the derivative
within the closure.

The proof flattens a boundary point, applies mathlib's derivative-extension
theorem on a convex half-ball, and transports the result back through the
chart.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Regularity

open Filter Metric Set
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Continuous first-order data that agree with the Fréchet derivative in an
operational `C¹` domain also give the derivative within its closure.
-/
theorem hasFDerivWithinAt_closure_of_continuous_derivative
    {f : ℝ^n → F} {f' : ℝ^n → (ℝ^n →L[ℝ] F)}
    (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x ∈ Ω, HasFDerivAt f (f' x) x)
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    HasFDerivWithinAt f (f' x) (closure Ω) x := by
  by_cases hxΩ : x ∈ Ω
  · exact (hderiv x hxΩ).hasFDerivWithinAt
  obtain ⟨i, hxSource⟩ := Trace.C1.exists_chart_source_of_mem_frontier (n := n) (Ω := Ω)
    (show x ∈ frontier Ω from hΩ.isOpen.frontier_eq ▸ ⟨hx, hxΩ⟩)
  let e := hΩ.chart i
  have hsymm := hΩ.chart_symm_contDiff i
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hxSource))
  let s : Set (ℝ^n) := Metric.ball (e x) r ∩ HalfSpace.upper n
  let g' : ℝ^n → (ℝ^n →L[ℝ] F) := fun z ↦
    (f' (e.symm z)).comp (fderiv ℝ (fun w ↦ e.symm w) z)
  have hg (z : ℝ^n) (hz : z ∈ s) : HasFDerivAt (f ∘ e.symm) (g' z) z :=
    (hderiv (e.symm z) ((Trace.C1.chart_isImage_domain (n := n) (Ω := Ω) i).symm_apply_mem_iff
      (hball hz.1) |>.2 hz.2)).comp z (hsymm.differentiable (by norm_num) z).hasFDerivAt
  have hFDerivTendsto : Tendsto (fun z ↦ fderiv ℝ (f ∘ e.symm) z) (𝓝[s] (e x)) (𝓝 (g' (e x))) :=
    (((hf'.comp hsymm.continuous).clm_comp (hsymm.continuous_fderiv (by norm_num))).continuousAt
      |>.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun z hz ↦ (hg z hz).fderiv.symm)
  have hGClosure : HasFDerivWithinAt (f ∘ e.symm) (g' (e x)) (closure s) (e x) :=
    hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun z hz ↦ (hg z hz).differentiableAt.differentiableWithinAt)
      ((convex_ball _ r).inter (HalfSpace.convex_upper n))
      (isOpen_ball.inter (HalfSpace.isOpen_upper n))
      (fun _ _ ↦ (hf.comp hsymm.continuous).continuousWithinAt) hFDerivTendsto
  have hGUpper : HasFDerivWithinAt (f ∘ e.symm) (g' (e x)) (closure (HalfSpace.upper n)) (e x) :=
    hGClosure.mono_of_mem_nhdsWithin <| mem_of_superset (inter_mem
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hr)) self_mem_nhdsWithin)
      isOpen_ball.inter_closure
  have hChartTendsto : Tendsto (fun z ↦ e z) (𝓝[closure Ω] x)
      (𝓝[closure (HalfSpace.upper n)] (e x)) := by
    rw [← (Trace.C1.chart_isImage_domain (n := n) (Ω := Ω) i).closure.map_nhdsWithin_eq hxSource]
    exact tendsto_map
  have hComp := hGUpper.comp_of_tendsto x ((hΩ.chart_contDiff i).differentiable (by norm_num) x
    |>.hasFDerivAt.hasFDerivWithinAt (s := closure Ω)) hChartTendsto
  have hDerivative : (g' (e x)).comp (fderiv ℝ (fun z ↦ e z) x) = f' x := by
    dsimp only [g']
    rw [e.left_inv hxSource, ContinuousLinearMap.comp_assoc,
      Trace.C1.fderiv_chart_symm_comp_fderiv_chart (n := n) (Ω := Ω) i hxSource,
      ContinuousLinearMap.comp_id]
  rw [hDerivative] at hComp
  have hEventual : (f ∘ e.symm) ∘ (fun z ↦ e z) =ᶠ[𝓝[closure Ω] x] f :=
    (eventually_nhdsWithin_of_eventually_nhds (e.eventually_left_inverse hxSource)).mono
      fun z hz ↦ congrArg f hz
  exact hComp.congr_of_eventuallyEq hEventual.symm (by simp [e.left_inv hxSource])

end SobolevSpace.Boundary.Regularity
