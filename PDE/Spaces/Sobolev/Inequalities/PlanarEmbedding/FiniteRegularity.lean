/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.PlanarEmbedding.Representative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Planar order-two embedding for finite classical regularity

A `C²` function whose classical derivative rows through order two are in
`L²` defines a whole-plane `W^{2,2}` class. Its bundled norm is the exact
six-row sum, and its continuous representative identity gives the pointwise
bound `3 / (2√π)` times that norm. Compact support is not required.

The representative construction is in
`PDE.Spaces.Sobolev.Inequalities.PlanarEmbedding.Representative`.

## Main results

* `SobolevSpace.finiteSmooth_orderTwo_norm_sq`: the squared bundled norm is the six-row sum.
* `SobolevSpace.finiteSmooth_orderTwo_pointwise`: `|f x| ≤ (3 / (2√π)) ‖f‖_{W^{2,2}}`.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.4, Propositions 8 and 9,
  where whole-plane bounds of this kind are applied to parity reflections of half-plane functions.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open PDE.FDeriv
open LineDeriv
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap Topology Sobolev

namespace SobolevSpace

/-- For a `C²` function `f` on `ℝ²` whose classical derivatives through order two lie in `L²`,
the squared bundled `W^{2,2}` norm of `mkWkpSpaceOnOfContDiffMemLpFinite` is the sum of the
squared `L²` norms of `f`, `∂₀f`, `∂₁f`, `∂₀∂₀f`, `∂₀∂₁f` and `∂₁∂₁f`. The six symmetric
derivative coordinates of the graph space are the six Cartesian derivative rows through order two.
-/
theorem finiteSmooth_orderTwo_norm_sq
    (f : (ℝ^2) → ℝ) (hf : ContDiff ℝ 2 f)
    (hmem : ∀ a : GraphSpace.DerivIndex 2 2,
      MemLp (iteratedPartialDeriv (n := 2) a.toList f) 2 volume) :
    ‖GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
        (n := 2) (k := 2) (p := 2) (Ω := Set.univ)
        f hf (by simpa [domainMeasure] using hmem)‖ ^ 2 =
      (∫ x, f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [0] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [1] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [0, 0] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [0, 1] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [1, 1] f x ^ 2) := by
  have hmem' : ∀ a : GraphSpace.DerivIndex 2 2,
      MemLp (iteratedPartialDeriv (n := 2) a.toList f) 2
        (domainMeasure 2 Set.univ) := by
    simpa [domainMeasure] using hmem
  let U : W^{2,2}((Set.univ : Set (ℝ^2))) :=
    GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
      (n := 2) (k := 2) (p := 2) (Ω := Set.univ)
      f hf hmem'
  have hcoord (a : GraphSpace.DerivIndex 2 2) :
      ‖((U : GraphSpace.WkpAmbientOn 2 2 2 Set.univ) a)‖ ^ 2 =
        ∫ x, iteratedPartialDeriv (n := 2) a.toList f x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    simp only [domainMeasure, Measure.restrict_univ]
    apply integral_congr_ae
    have hae := GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
      (n := 2) (k := 2) (p := 2) (Ω := Set.univ)
      f hf hmem' a
    have hae' :
        (((U : GraphSpace.WkpAmbientOn 2 2 2 Set.univ) a : (ℝ^2) → ℝ))
          =ᵐ[volume] fun x ↦ iteratedPartialDeriv (n := 2) a.toList f x := by
      simpa [U, domainMeasure] using hae
    filter_upwards [hae'] with x hx
    rw [hx]
    simp [pow_two]
  have hidxInt (α : List (Fin 2)) (hα : α.length ≤ 2) :
      (∫ x, iteratedPartialDeriv (n := 2)
          (GraphSpace.derivIndexOfList α hα).toList f x ^ 2) =
        ∫ x, iteratedPartialDeriv (n := 2) α f x ^ 2 := by
    have hfα : ContDiff ℝ (α.length : ℕ∞) f := by
      apply hf.of_le
      exact WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hα)
    have hperm := GraphSpace.derivIndexOfList_toList_perm α hα
    have heq :=
      (iteratedPartialDeriv_congr_perm_of_contDiff hfα hperm.symm).symm
    apply integral_congr_ae
    filter_upwards [] with x
    rw [congrFun heq x]
  change ‖(U : GraphSpace.WkpAmbientOn 2 2 2 Set.univ)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, GraphSpace.sum_derivIndex_two_two]
  rw [hcoord, hcoord, hcoord, hcoord, hcoord, hcoord]
  rw [hidxInt [0] (by simp), hidxInt [1] (by simp),
    hidxInt [0, 0] (by simp), hidxInt [0, 1] (by simp),
    hidxInt [1, 1] (by simp)]
  simp [GraphSpace.baseIndex_toList, iteratedPartialDeriv]

/-- For a `C²` function `f` on `ℝ²` whose classical derivatives through order two belong to
`L²`, `|f x| ≤ (3 / (2√π)) ‖f‖` at every point, where the norm is the bundled `W^{2,2}` norm of
`mkWkpSpaceOnOfContDiffMemLpFinite`. No compact-support hypothesis is imposed, which is the form
needed after a parity-compatible reflection.
-/
theorem finiteSmooth_orderTwo_pointwise
    (f : (ℝ^2) → ℝ) (hf : ContDiff ℝ 2 f)
    (hmem : ∀ a : GraphSpace.DerivIndex 2 2,
      MemLp (iteratedPartialDeriv (n := 2) a.toList f) 2 volume) :
    ∀ x : (ℝ^2),
      |f x| ≤ (3 / (2 * Real.sqrt Real.pi)) *
        ‖GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
          (n := 2) (k := 2) (p := 2) (Ω := Set.univ)
          f hf (by simpa [domainMeasure] using hmem)‖ := by
  have hmem' : ∀ a : GraphSpace.DerivIndex 2 2,
      MemLp (iteratedPartialDeriv (n := 2) a.toList f) 2
        (domainMeasure 2 Set.univ) := by
    simpa [domainMeasure] using hmem
  let U : W^{2,2}((Set.univ : Set (ℝ^2))) :=
    GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
      (n := 2) (k := 2) (p := 2) (Ω := Set.univ)
      f hf hmem'
  obtain ⟨g, hg, hgrep, hbound⟩ := orderTwoSobolev_continuousRepresentative U
  have hUbase :
      ((((U : GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) =ᵐ[volume] f := by
    simpa [U, domainMeasure, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
        (n := 2) (k := 2) (p := 2) (Ω := Set.univ)
        f hf hmem' (GraphSpace.baseIndex 2 2))
  have hgf : g = f := MeasureTheory.Measure.eq_of_ae_eq
    (hgrep.trans hUbase) hg hf.continuous
  intro x
  calc
    |f x| = |g x| := by rw [hgf]
    _ ≤ (3 / (2 * Real.sqrt Real.pi)) * ‖U‖ := hbound x
    _ = (3 / (2 * Real.sqrt Real.pi)) *
        ‖GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
          (n := 2) (k := 2) (p := 2) (Ω := Set.univ)
          f hf (by simpa [domainMeasure] using hmem)‖ := by
      rfl

end SobolevSpace
