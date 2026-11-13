/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.SpatialJets.ForwardTime
import PDE.FDeriv.SpaceTime.SpatialJets

/-!
# Duhamel regularity for a smooth spacetime source

A globally `C²`, compactly supported source supplies the forward-time spatial derivatives
needed by the Duhamel theorem. Restriction to nonnegative time preserves compact support.

For a source with only continuous time dependence, use
`nonhomogeneousSolution_regularity_of_forward_spatial_jets` instead.
-/

@[expose] public section

open PDE (laplacian)

open Set PDE.Common

namespace HeatEquation

variable {n : ℕ}

/-- A globally `C²`, compactly supported source gives a classical Duhamel solution, with joint
continuity through time zero, continuous mixed second spatial derivatives, the forced heat equation,
and a spatially uniform zero initial trace. -/
theorem nonhomogeneousSolution_regularity_classical
    (f : ℝ^(n + 1) → ℝ) (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (fun p : ℝ^n × ℝ ↦ nonhomogeneousSolution f p.1 p.2) ∧
    ContDiffOn ℝ 1 (fun p : ℝ^n × ℝ ↦ nonhomogeneousSolution f p.1 p.2)
      (univ ×ˢ Ioi 0) ∧
    (∀ t : ℝ, ContDiff ℝ 2 (fun x ↦ nonhomogeneousSolution f x t)) ∧
    (∀ i j : Fin n, Continuous (fun p : ℝ^n × ℝ ↦
      (∂[i] (∂[j] (fun x ↦ nonhomogeneousSolution f x p.2))) p.1)) ∧
    (∀ (x : ℝ^n) (t : ℝ), 0 < t →
      deriv (fun τ ↦ nonhomogeneousSolution f x τ) t -
        laplacian (fun y ↦ nonhomogeneousSolution f y t) x = f (timeSpaceCons t x)) ∧
    (∀ x : ℝ^n, nonhomogeneousSolution f x 0 = 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (x : ℝ^n) (t : ℝ), 0 < t → t < δ →
        |nonhomogeneousSolution f x t| < ε := by
  have hglobal : HasCompactSupport
      (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons p.1 p.2)) :=
    hfc.comp_homeomorph (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph
  have hmap : Topology.IsClosedEmbedding
      (fun p : Ici (0 : ℝ) × ℝ^n ↦ ((p.1 : ℝ), p.2)) :=
    isClosed_Ici.isClosedEmbedding_subtypeVal.prodMap
      (Topology.IsClosedEmbedding.id (X := ℝ^n))
  have hrestrict : Continuous (fun p : Ici (0 : ℝ) × ℝ^n ↦ ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact nonhomogeneousSolution_regularity_of_forward_spatial_jets f
    ((hf2.comp (contDiff_timeSpaceCons_uncurry n)).continuous.comp hrestrict)
    (fun s _ ↦ hf2.comp (contDiff_timeSpaceCons_spatial n s))
    (hglobal.comp_isClosedEmbedding
      (g := fun p : Ici (0 : ℝ) × ℝ^n ↦ ((p.1 : ℝ), p.2)) hmap)
    (fun i ↦ (PDE.continuous_partialDeriv_timeSpaceCons_spatial
      f (hf2.of_le (by norm_num)) i).comp hrestrict)
    (fun i j ↦ (PDE.continuous_secondPartialDeriv_timeSpaceCons_spatial f hf2 i j).comp hrestrict)

end HeatEquation
