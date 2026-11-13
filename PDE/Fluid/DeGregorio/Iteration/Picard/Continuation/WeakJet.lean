/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakDifferentiation
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder.Convergence
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.WeakDerivative

/-!
# Weak derivative jets of an H² vorticity and its Hilbert velocity

An H² graph gives a continuous first derivative and an L² second weak derivative
of vorticity. Commutation of the spectral Hilbert transform with weak derivatives
then gives a continuous second derivative of velocity and its third weak derivative.
These are the spatial regularity inputs to the second differentiated transport
identity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The first two weak derivative rows of a continuous H² representative.
The second derivative remains an L² class; the first is the classical derivative. -/
theorem exists_weak_secondDerivative_of_h2
    (W : W^{2,2}(ℝ^1)) {w : ℝ → ℝ} (hw : Continuous w)
    (hrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
      =ᵐ[volume] w) :
    ∃ r : Lp ℝ 2 (volume : Measure ℝ),
      ContDiff ℝ 1 w ∧ MemLp (deriv w) 2 volume ∧
      HasWeakTimeDerivativeOn univ w (deriv w) ∧
      HasWeakTimeDerivativeOn univ (deriv w) r := by
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W
  let Q := ∂[0] W
  have heq : realLineRepresentative U = w :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) hw).mp
      ((realLineRepresentative_lowerOrder_ae W).symm.trans hrep)
  have hq : realLineRepresentative Q = deriv w := by
    rw [← heq]
    exact (deriv_realLineRepresentative_lowerOrder W).symm
  have hweak := hasWeakTimeDerivativeOn_realLineRepresentative U
  rw [heq] at hweak
  have hae : (realLineCoordinateCLM (singleDerivIndex 1 0) U : ℝ → ℝ)
      =ᵐ[volume] deriv w := by
    filter_upwards [hweak.ae_hasDerivAt_of_continuous hw] with x hx
    exact hx.deriv.symm
  refine ⟨realLineCoordinateCLM (singleDerivIndex 1 0) Q,
    (contDiff_and_bounds_of_h2_representative W hw hrep).1,
    hq ▸ memLp_realLineRepresentative Q,
    hweak.congr_ae EventuallyEq.rfl hae, ?_⟩
  exact hq ▸ hasWeakTimeDerivativeOn_realLineRepresentative Q

/-- Weak differentiation of the Hilbert pair gives the velocity jet
needed by H² transport. The continuous second velocity derivative is recovered
from compatible H¹ graphs, and its third derivative is only weak and L². -/
theorem IsHilbertPair.exists_weak_velocity_jet
    {w u r : ℝ → ℝ} (hpair : IsHilbertPair w (deriv u))
    (hu : ContDiff ℝ 1 u)
    (hq : MemLp (deriv w) 2 volume) (hr : MemLp r 2 volume)
    (hwq : HasWeakTimeDerivativeOn univ w (deriv w))
    (hqr : HasWeakTimeDerivativeOn univ (deriv w) r) :
    ContDiff ℝ 2 u ∧ IsHilbertPair (deriv w) (deriv (deriv u)) ∧
      ∃ s : ℝ → ℝ, IsHilbertPair r s ∧
        HasWeakTimeDerivativeOn univ (deriv (deriv u)) s := by
  obtain ⟨d, hqd, hcd⟩ := hpair.exists_hasWeakTimeDerivativeOn hq hwq
  obtain ⟨s, hrs, hds⟩ := hqd.exists_hasWeakTimeDerivativeOn hr hqr
  let C := mkW12OfWeakDerivative hpair.memLp_right hqd.memLp_right hcd
  let D := mkW12OfWeakDerivative hqd.memLp_right hrs.memLp_right hds
  have hcompat : realLineCoordinateCLM (baseIndex 1 1) D =
      realLineCoordinateCLM (singleDerivIndex 1 0) C := by
    simp only [C, D, realLineCoordinateCLM_mkW12_base, realLineCoordinateCLM_mkW12_single]
  have hC : realLineRepresentative C = deriv u :=
    realLineRepresentative_mkW12 _ _ _ (hu.continuous_deriv le_rfl)
  have hd (x : ℝ) : HasDerivAt (deriv u) (realLineRepresentative D x) x := by
    rw [← hC]
    exact hasDerivAt_realLineRepresentative_of_h1_derivative C D hcompat x
  have hD : realLineRepresentative D = deriv (deriv u) :=
    funext fun x ↦ (hd x).deriv.symm
  have hd_ae : d =ᵐ[volume] deriv (deriv u) := by
    have h := realLineCoordinate_ae_representative D
    rw [show realLineCoordinateCLM (baseIndex 1 1) D = hqd.memLp_right.toLp d by
      simp only [D, realLineCoordinateCLM_mkW12_base], hD] at h
    exact hqd.memLp_right.coeFn_toLp.symm.trans h
  refine ⟨(contDiff_succ_iff_deriv (n := 1)).mpr
    ⟨hu.differentiable one_ne_zero, by simp, ?_⟩,
    hqd.congr_right_ae hd_ae, s, hrs, hds.congr_ae hd_ae EventuallyEq.rfl⟩
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun x ↦ (hd x).differentiableAt, hD ▸ continuous_realLineRepresentative D⟩

end DeGregorio.Iteration
