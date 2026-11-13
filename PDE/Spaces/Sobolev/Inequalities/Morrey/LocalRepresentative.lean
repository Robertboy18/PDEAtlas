/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FullEmbedding
import PDE.Analysis.MeasureTheory.LocalRepresentative
import PDE.Elliptic.Regularity.Boundary.ConcreteUnitBallAtlas
import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.BallPullback

/-!
# Continuous representatives of locally supercritical Sobolev functions

The affine Sobolev pullback sends each interior ball to the unit ball, whose
extension operator and Morrey embedding supply a continuous representative. These local
representatives agree on open overlaps and glue to one continuous representative.
No boundedness or boundary regularity of the ambient open domain is required.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace

open GraphSpace

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every supercritical Sobolev element on a ball has a continuous representative,
including the exponent infinity and dimension one. -/
theorem exists_continuous_representative_ball
    (hp : (n : ℝ≥0∞) < p) (x : ℝ^n) {r : ℝ} (hr : 0 < r)
    (U : W^{1,p}(ball x r)) :
    ∃ F : ℝ^n → ℝ, Continuous F ∧
      F =ᵐ[domainMeasure n (ball x r)] baseRepresentative U := by
  let : Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1) :=
    (Boundary.Atlas.UnitBall.ConcreteAtlas.c2BoundaryAtlas n).toC1ExtensionAtlas
  obtain ⟨V, hV, _⟩ := MeanScaling.exists_ballPullback x hr U
  obtain ⟨_, _, hMorrey⟩ := exists_morreyEmbeddingBound (Fact.out : 0 < n) hp
  obtain ⟨F, hF, _⟩ := hMorrey (Extension.C1.extensionCLM V)
  let e := MeanScaling.ballHomeomorph x hr
  refine ⟨F ∘ e.symm, F.continuous.comp e.symm.continuous, ?_⟩
  have hunit : (fun y ↦ F y) =ᵐ[domainMeasure n (ball (0 : ℝ^n) 1)]
      fun y ↦ baseRepresentative U (e y) := by
    filter_upwards [ae_restrict_of_ae (s := ball (0 : ℝ^n) 1) hF,
      Extension.C1.extensionCLM_agree_ae V, hV] with y hy hE hVy
    exact hy.trans (hE.trans hVy)
  have hmap : ∀ᵐ y ∂(volume.restrict (ball (0 : ℝ^n) 1)).map e,
      F (e.symm y) = baseRepresentative U y := by
    apply e.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
    change ∀ᵐ y ∂volume.restrict (ball (0 : ℝ^n) 1),
      F (e.symm (e y)) = baseRepresentative U (e y)
    filter_upwards [hunit] with y hy
    simpa only [e.symm_apply_apply] using hy
  rw [MeanScaling.map_ball_volume] at hmap
  exact (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr n))).ne').mp hmap

/-- Local `Lᵖ` membership of a function and its weak gradient, with `p > n`, gives
a continuous representative on any open domain. Compact sets express precisely
the local Sobolev hypothesis, with no global integrability requirement. -/
theorem exists_continuousOn_representative_of_locally_memLp_weakGradient
    {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ} {g : ℝ^n → ℝ^n}
    (hp : (n : ℝ≥0∞) < p) (hΩ : IsOpen Ω)
    (hf : ∀ K ⊆ Ω, IsCompact K → MemLp f p (volume.restrict K))
    (hg : ∀ K ⊆ Ω, IsCompact K → MemLp g p (volume.restrict K))
    (hweak : ∀ i : Fin n, HasWeakDerivativeOn Ω [i] f (fun x ↦ g x i)) :
    ∃ F : ℝ^n → ℝ, ContinuousOn F Ω ∧ F =ᵐ[volume.restrict Ω] f := by
  have hlocal (x : ℝ^n) (hx : x ∈ Ω) :
      ∃ N : Set (ℝ^n), IsOpen N ∧ x ∈ N ∧ N ⊆ Ω ∧
        ∃ F : ℝ^n → ℝ, ContDiffOn ℝ 0 F N ∧ F =ᵐ[volume.restrict N] f := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hΩ x hx
    have hr : 0 < δ / 2 := half_pos hδ
    have hclosed : closedBall x (δ / 2) ⊆ Ω :=
      (closedBall_subset_ball (half_lt_self hδ)).trans hsub
    have hball : ball x (δ / 2) ⊆ Ω := ball_subset_closedBall.trans hclosed
    have hfr : MemLp f p (domainMeasure n (ball x (δ / 2))) :=
      (hf _ hclosed (isCompact_closedBall x _)).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)
    have hgr : MemLp g p (domainMeasure n (ball x (δ / 2))) :=
      (hg _ hclosed (isCompact_closedBall x _)).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)
    obtain ⟨U, hU, _⟩ := exists_of_weakGradient hfr hgr
      (fun i ↦ HasWeakDerivativeOn.mono measurableSet_ball hball (hweak i))
    obtain ⟨F, hF, hFU⟩ := exists_continuous_representative_ball hp x hr U
    exact ⟨ball x (δ / 2), isOpen_ball, mem_ball_self hr, hball,
      F, contDiffOn_zero.mpr hF.continuousOn, hFU.trans hU⟩
  obtain ⟨F, hF, hrep⟩ := exists_contDiffAt_ae_eq_of_locally hlocal
  exact ⟨F, fun x hx ↦ (hF x hx).continuousAt.continuousWithinAt, hrep⟩

end SobolevSpace
