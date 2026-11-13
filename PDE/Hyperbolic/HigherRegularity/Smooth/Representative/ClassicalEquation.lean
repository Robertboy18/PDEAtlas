/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Representative.SobolevEquation

/-!
# Pointwise full wave equations through the time endpoints

The Sobolev equation determines the continuous scalar residual on the open
spatial domain. This gives the classical equation at every time of the closed
interval and for every time derivative. The original representative has the
same spatial germ as its canonical zeroth slice, so the operator in the
undifferentiated equation acts on that original representative itself.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  (P : SmoothFullCoefficients n Ω)
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {f U : SpaceTime n → ℝ}
  (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hU : ∀ k, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hcont : ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
  {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
  {v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
  {w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
  {q₀ : H¹₀(Ω)} {p₀ : DerivLp n 2 Ω}
  (hweak : Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
    (fun _ ↦ P.form hopen hbounded)
    (dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf 0 0).head)
    u v w q₀ p₀)
  (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
    (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
      baseRepresentative (h10SubtypeL (u t)))

include hcont hweak hae

/-- The canonical time derivatives satisfy the full classical equation
at every spatial interior point and every time in the closed interval. -/
theorem classical_equation_timeDerivative (j : ℕ) {t : ℝ} (ht : t ∈ Icc a b)
    {x : ℝ^n} (hx : x ∈ Ω) :
    derivativeSlice hopen hU (List.replicate (j + 2) 0) t x +
      P.classicalLoad (derivativeSlice hopen hU (List.replicate j 0) t) x =
        derivativeSlice hopen hf (List.replicate j 0) t x := by
  have hL := P.classicalLoad_regular hopen hbounded
    (derivativeSlice_regular hopen hbounded hab hU (List.replicate j 0) 2 ht)
  have hload : (wkpBaseCoordinateCLM
      (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 j t)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        P.classicalLoad (derivativeSlice hopen hU (List.replicate j 0) t) := by
    rw [sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hU 2 j ht, P.load_toWkpSpaceOn]
    exact hL.toWkpSpaceOn_base_ae hopen hbounded 2
  have heq := congrArg wkpBaseCoordinateCLM
    (sobolev_equation_timeDerivative P hopen hbounded hab hf hU hcont hweak hae j 0 ht)
  rw [map_add] at heq
  have hscalar : (fun y ↦ derivativeSlice hopen hU (List.replicate (j + 2) 0) t y +
        P.classicalLoad (derivativeSlice hopen hU (List.replicate j 0) t) y)
        =ᵐ[domainMeasure n Ω] derivativeSlice hopen hf (List.replicate j 0) t := by
    filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU 0 (j + 2) ht,
      hload, wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hf 0 j ht,
      Lp.coeFn_add (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 (j + 2) t))
        (wkpBaseCoordinateCLM
          (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 j t)))] with
      y hacc hload hforce hadd
    have hpoint := congrArg (fun z : DerivLp n 2 Ω ↦ z y) heq
    rwa [hadd, Pi.add_apply, hacc, hload, hforce] at hpoint
  have hc (hF : ∀ k, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
      (l : ℕ) : Continuous (derivativeSlice hopen hF (List.replicate l 0) t) :=
    (continuous_derivativeSlice hopen hF (List.replicate l 0)).comp
      (continuous_const.prodMk continuous_id)
  exact Measure.eqOn_open_of_ae_eq hscalar hopen
    ((hc hU (j + 2)).continuousOn.add hL.contDiffOn.continuousOn)
    ((continuous_derivativeSlice hopen hf (List.replicate j 0)).comp
      (continuous_const.prodMk continuous_id)).continuousOn hx

/-- The full signed divergence operator acts on the original joint
representative, including at the final time and the canonical initial limit. -/
theorem classical_equation {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ Ω) :
    derivativeSlice hopen hU [0, 0] t x + P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x =
      derivativeSlice hopen hf [] t x := by
  have hzero : EqOn (derivativeSlice hopen hU [] t) (fun y ↦ U (timeSpaceCons t y)) Ω :=
    fun y hy ↦ derivativeSlice_nil hopen hab hU hcont ht (subset_closure hy)
  have hload := P.classicalLoad_congr hopen hzero hx
  simpa only [List.replicate_succ, List.replicate_zero, hload] using
    classical_equation_timeDerivative P hopen hbounded hab hf hU hcont hweak hae 0 ht hx

end Hyperbolic.HigherRegularity.SmoothWave
