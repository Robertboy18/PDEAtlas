/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import PDE.Analysis.Calculus.LocalExtension

/-!
# The Laplacian under dilation

The Laplacian of a composition with scalar multiplication acquires the square of
the scalar. Local `C²` regularity suffices: a representative of the germ permits
reuse of Mathlib's formula for the iterated Fréchet derivative of a dilation.
-/

@[expose] public section

open Filter Topology

/-- Composition with a dilation multiplies the Laplacian by the square of its
factor. Regularity is required only near the image point. -/
theorem ContDiffAt.laplacian_comp_const_smul
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (c : ℝ) (hf : ContDiffAt ℝ 2 f (c • x)) :
    Laplacian.laplacian (fun y ↦ f (c • y)) x =
      c ^ 2 • Laplacian.laplacian f (c • x) := by
  classical
  obtain ⟨g, hg, _, heq⟩ := hf.exists_contDiff_compactSupport_eventuallyEq
  have hcomp : (fun y ↦ f (c • y)) =ᶠ[𝓝 x] (fun y ↦ g (c • y)) :=
    heq.comp_tendsto (continuous_const_smul c).continuousAt
  rw [(InnerProductSpace.laplacian_congr_nhds hcomp).eq_of_nhds,
    (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_const_smul c hg, smul_apply,
    Finset.smul_sum]
