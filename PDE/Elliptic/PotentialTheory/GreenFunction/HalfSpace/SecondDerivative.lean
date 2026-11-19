/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.FirstDerivative
import PDE.Analysis.Convolution.WeakDerivative
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TangentialDerivative
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Tangential derivatives of planar Green potentials

Tangential differentiation commutes with the canonical odd source extension,
including when its normal jump is nonzero. Moving this weak derivative through
convolution identifies the tangential derivative of the Green potential with
the Green inverse of the tangential source derivative. Its first derivatives
therefore are continuous across the boundary, without asserting global `C²`
regularity of the original method-of-images potential.

## Main results

* `hasWeakDerivativeOn_oddHalfSpaceExtension_tangential`: a horizontal weak derivative passes
  through the odd source extension, also when the source is nonzero on the boundary.
* `partialDeriv_halfSpaceGreenPotential_eq`: the horizontal derivative of the Green potential is
  the Green potential of the horizontal source derivative.
* `contDiff_one_partialDeriv_halfSpaceGreenPotential`: for a compact `C¹` source the horizontal
  derivative of the Green potential is globally `C¹`.
* `continuous_secondPartialDeriv_halfSpaceGreenPotential_tangential`: the tangential and mixed
  second derivatives are continuous on the whole plane.
* `secondPartialDeriv_halfSpaceGreenPotential_boundary_tangential`: the pure tangential second
  derivative vanishes on the boundary.
* `tendsto_secondPartialDeriv_halfSpaceGreenPotential_mixed`: both orders of mixed
  differentiation have the same limit from the upper half-plane.
* `tendsto_secondPartialDeriv_halfSpaceGreenPotential_boundary_normal`: the normal-normal second
  derivative tends to minus the boundary value of the source.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Topology Set SobolevSpace
open scoped Convolution ENNReal

/-- A horizontal weak derivative passes through the odd source extension.
The source need not vanish on the horizontal boundary. -/
theorem hasWeakDerivativeOn_oddHalfSpaceExtension_tangential
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    HasWeakDerivativeOn univ [(0 : Fin 2)] (oddHalfSpaceExtension f)
      (oddHalfSpaceExtension (∂[(0 : Fin 2)] f)) := by
  have hd : Continuous (∂[(0 : Fin 2)] f) := by
    change Continuous (fun x ↦ fderiv ℝ f x (EuclideanSpace.single 0 (1 : ℝ)))
    exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (∂[(0 : Fin 2)] f) :=
    hc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ))
  have hLf : MemLp f 1 (domainMeasure 2 (HalfSpace.upper 2)) :=
    (hf.continuous.memLp_of_hasCompactSupport hc).restrict (HalfSpace.upper 2)
  have hLd : MemLp (∂[(0 : Fin 2)] f) 1 (domainMeasure 2 (HalfSpace.upper 2)) :=
    (hd.memLp_of_hasCompactSupport hdc).restrict (HalfSpace.upper 2)
  have hw := hasWeakDerivativeOn_of_contDiffAt_one (HalfSpace.isOpen_upper 2)
    (fun x _ ↦ hf.contDiffAt (x := x)) (0 : Fin 2)
  have hwLp := hw.congr_ae hLf.coeFn_toLp.symm hLd.coeFn_toLp.symm
  have hext := Extension.GraphSpace.HalfSpace.hasWeakDerivativeOn_univ_oddExtend_of_upper_ne_last
    (n := 2) (p := 1) (0 : Fin 2) (by decide) (hLf.toLp f)
    (hLd.toLp (∂[(0 : Fin 2)] f)) hwLp
  have heqf := HalfSpace.oddExtendLp_apply_ae_of_ae_eq
    (n := 2) (p := 1) (hLf.toLp f) f hLf.coeFn_toLp
  have heqd := HalfSpace.oddExtendLp_apply_ae_of_ae_eq
    (n := 2) (p := 1) (hLd.toLp (∂[(0 : Fin 2)] f)) (∂[(0 : Fin 2)] f) hLd.coeFn_toLp
  apply hext.congr_ae
  · simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [heqf] with y hy
    exact hy
  · simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [heqd] with y hy
    exact hy

/-- Differentiation in the horizontal coordinate commutes with planar Green inversion,
even when the source has nonzero boundary values. -/
theorem partialDeriv_halfSpaceGreenPotential_eq
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) =
      halfSpaceGreenPotential (∂[(0 : Fin 2)] f) := by
  have hd : Continuous (∂[(0 : Fin 2)] f) := by
    change Continuous (fun x ↦ fderiv ℝ f x (EuclideanSpace.single 0 (1 : ℝ)))
    exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (∂[(0 : Fin 2)] f) :=
    hc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ))
  have hFc := hasCompactSupport_oddHalfSpaceExtension hc
  have hGc := hasCompactSupport_oddHalfSpaceExtension hdc
  have hFi : Integrable (oddHalfSpaceExtension f) volume :=
    (integrableOn_iff_integrable_of_support_subset
      (subset_tsupport (oddHalfSpaceExtension f))).mp
        ((locallyIntegrable_oddHalfSpaceExtension hf.continuous).integrableOn_isCompact hFc)
  have hGi : Integrable (oddHalfSpaceExtension (∂[(0 : Fin 2)] f)) volume :=
    (integrableOn_iff_integrable_of_support_subset
      (subset_tsupport (oddHalfSpaceExtension (∂[(0 : Fin 2)] f)))).mp
        ((locallyIntegrable_oddHalfSpaceExtension hd).integrableOn_isCompact hGc)
  have hweak : HasWeakDerivativeOn univ [(0 : Fin 2)] (halfSpaceGreenPotential f)
      (halfSpaceGreenPotential (∂[(0 : Fin 2)] f)) := by
    rw [halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension hf.continuous hc,
      halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension hd hdc]
    exact PDE.Analysis.hasWeakDerivativeOn_convolution_right (0 : Fin 2)
      (PotentialTheory.locallyIntegrable_fundamentalSolution 2)
      (hasWeakDerivativeOn_oddHalfSpaceExtension_tangential hf hc) hFi hFc hGi hGc
      (continuous_convolution_oddHalfSpaceExtension
        (PotentialTheory.locallyIntegrable_fundamentalSolution 2) hf.continuous hc)
      (continuous_convolution_oddHalfSpaceExtension
        (PotentialTheory.locallyIntegrable_fundamentalSolution 2) hd hdc)
  have hu := contDiff_one_halfSpaceGreenPotential hf.continuous hc
  have hclassical := hasWeakDerivativeOn_of_contDiffAt_one isOpen_univ
    (fun x _ ↦ hu.contDiffAt (x := x)) (0 : Fin 2)
  have hdu : Continuous (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) := by
    change Continuous (fun x ↦ fderiv ℝ (halfSpaceGreenPotential f) x
      (EuclideanSpace.single 0 (1 : ℝ)))
    exact (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hae := hweak.unique_ae isOpen_univ hclassical
  have haeVol : halfSpaceGreenPotential (∂[(0 : Fin 2)] f) =ᵐ[volume]
      (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) := by
    simpa only [domainMeasure, Measure.restrict_univ] using hae
  exact (Measure.eq_of_ae_eq haeVol (continuous_halfSpaceGreenPotential hd hdc) hdu).symm


/-- The horizontal derivative of a compact `C¹` source's Green potential is globally `C¹`.
Its Cartesian first derivatives give continuous tangential and mixed second derivatives. -/
theorem contDiff_one_partialDeriv_halfSpaceGreenPotential
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ContDiff ℝ 1 (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) := by
  rw [partialDeriv_halfSpaceGreenPotential_eq hf hc]
  apply contDiff_one_halfSpaceGreenPotential
  · change Continuous (fun x ↦ fderiv ℝ f x (EuclideanSpace.single 0 (1 : ℝ)))
    exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  · exact hc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ))

/-- Tangential and mixed second derivatives, obtained by first differentiating
horizontally, are continuous on the entire plane. -/
theorem continuous_secondPartialDeriv_halfSpaceGreenPotential_tangential
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (j : Fin 2) :
    Continuous (∂[j] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) := by
  change Continuous (fun x ↦ fderiv ℝ (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) x
    (EuclideanSpace.single j (1 : ℝ)))
  exact ((contDiff_one_partialDeriv_halfSpaceGreenPotential hf hc).continuous_fderiv
    one_ne_zero).clm_apply continuous_const

/-- The pure tangential second derivative vanishes at the horizontal boundary. -/
theorem secondPartialDeriv_halfSpaceGreenPotential_boundary_tangential
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {x : ℝ^2} (hx : x ∈ HalfSpace.boundary 2) :
    (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x = 0 := by
  rw [partialDeriv_halfSpaceGreenPotential_eq hf hc]
  apply partialDeriv_halfSpaceGreenPotential_boundary _ _ hx
  · change Continuous (fun x ↦ fderiv ℝ f x (EuclideanSpace.single 0 (1 : ℝ)))
    exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  · exact hc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ))

/-- Tangential and mixed second derivatives have their continuous boundary values
as limits from the upper half-plane. -/
theorem tendsto_secondPartialDeriv_halfSpaceGreenPotential_tangential
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (j : Fin 2) (x : ℝ^2) :
    Tendsto (∂[j] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) (𝓝[HalfSpace.upper 2] x)
      (𝓝 ((∂[j] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x)) := by
  exact ((continuous_secondPartialDeriv_halfSpaceGreenPotential_tangential hf hc j).tendsto x)
    |>.mono_left nhdsWithin_le_nhds

/-- The other order of mixed differentiation has the same one-sided limit.
Schwarz's theorem is applied only inside the upper half-plane. -/
theorem tendsto_secondPartialDeriv_halfSpaceGreenPotential_mixed
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (x : ℝ^2) :
    Tendsto (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f)))
      (𝓝[HalfSpace.upper 2] x)
      (𝓝 ((∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x)) := by
  have heq : (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))) =ᶠ[
      𝓝[HalfSpace.upper 2] x] (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hreg := (halfSpaceGreenPotential_local_poisson hf.continuous hc hy hf.contDiffAt).1
    exact PDE.partialDeriv_partialDeriv_comm_at (0 : Fin 2) (1 : Fin 2) hreg
  exact (tendsto_congr' heq).mpr
    (tendsto_secondPartialDeriv_halfSpaceGreenPotential_tangential
      (hf.of_le (by norm_num)) hc (1 : Fin 2) x)

/-- The normal-normal second derivative tends to the negative source boundary value.
This is a one-sided trace; a nonzero value is compatible with the source's normal jump. -/
theorem tendsto_secondPartialDeriv_halfSpaceGreenPotential_boundary_normal
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {x : ℝ^2} (hx : x ∈ HalfSpace.boundary 2) :
    Tendsto (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f)))
      (𝓝[HalfSpace.upper 2] x) (𝓝 (-f x)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have htan := tendsto_secondPartialDeriv_halfSpaceGreenPotential_tangential hf1 hc 0 x
  rw [secondPartialDeriv_halfSpaceGreenPotential_boundary_tangential hf1 hc hx] at htan
  have hforcing : Tendsto f (𝓝[HalfSpace.upper 2] x) (𝓝 (f x)) :=
    (hf.continuous.tendsto x).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun y ↦ -f y -
      (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) y)
      (𝓝[HalfSpace.upper 2] x) (𝓝 (-f x)) := by
    simpa only [sub_zero] using hforcing.neg.sub htan
  have heq : (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))) =ᶠ[
      𝓝[HalfSpace.upper 2] x] (fun y ↦ -f y -
        (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hp := (halfSpaceGreenPotential_local_poisson hf.continuous hc hy hf.contDiffAt).2
    simp only [PDE.laplacian, Fin.sum_univ_two] at hp
    linarith
  exact (tendsto_congr' heq).mpr hlim

end GreenFunction
