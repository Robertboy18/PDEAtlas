/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Equation.Sobolev

/-!
# The pointwise full equation of the smooth parabolic solution

The derivative slices satisfy the spatial Sobolev equation. On the open
cylinder they are the pointwise time derivative and spatial function, so the
equation holds pointwise with the full signed divergence expression.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open Filter MeasureTheory Set PDE.Common PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open SobolevSpace.Evolution.Classical HigherOrder

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)
local notation "K" => splitSpaceTime ⁻¹' Set.prod (closure Ω) (Icc a b)

/-- The continuous extensions of the time derivatives satisfy the full
signed equation at every time, including the initial and terminal faces. -/
theorem derivativeSlice_equation (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    {g : DerivLp n 2 Ω}
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase) u g) :
    ∀ t ∈ Icc a b, ∀ x ∈ Ω,
      derivativeSlice hopen hU [0] t x +
          P.classicalLoad (derivativeSlice hopen hU [] t) x =
        derivativeSlice hopen hf [] t x := by
  intro t htc x hx
  have heq := sobolev_equation P hopen hbounded hab hf hU hc u hae hu t htc
  have hz := derivativeSlice_regular hopen hbounded hab hU [] 2 htc
  have hload := P.classicalLoad_regular hopen hbounded hz
  have hae' : (fun y ↦ derivativeSlice hopen hU [0] t y +
      P.classicalLoad (derivativeSlice hopen hU [] t) y) =ᵐ[domainMeasure n Ω]
        derivativeSlice hopen hf [] t := by
    have hloadClass :
        P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t) =
          hload.toWkpSpaceOn hopen hbounded 2 := by
      rw [sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hU 2 0 htc]
      exact P.load_toWkpSpaceOn hopen hbounded hz
    filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU 0 1 htc,
      hload.toWkpSpaceOn_base_ae hopen hbounded 2,
      wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hf 0 0 htc,
      Lp.coeFn_add (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 1 t))
        (wkpBaseCoordinateCLM
          (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t)))]
      with y hdt hL hf₀ hsum
    have hp := congrArg (fun v : DerivLp n 2 Ω ↦ (v : ℝ^n → ℝ) y) heq
    rw [hsum, hloadClass] at hp
    exact (congrArg₂ (· + ·) hdt hL).symm.trans (hp.trans hf₀)
  exact Measure.eqOn_open_of_ae_eq hae' hopen
    (((derivativeSlice_regular hopen hbounded hab hU [0] 0 htc).contDiffOn.continuousOn).add
      hload.contDiffOn.continuousOn)
    (derivativeSlice_regular hopen hbounded hab hf [] 0 htc).contDiffOn.continuousOn hx

/-- Any smooth representative of the original weak solution satisfies the
full signed PDE pointwise in the open cylinder. -/
theorem pointwise_equation (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    {g : DerivLp n 2 Ω}
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase) u g) :
    ∀ t ∈ Ioo a b, ∀ x ∈ Ω,
      (∂[0] U) (timeSpaceCons t x) +
          P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x =
        f (timeSpaceCons t x) := by
  intro t ht x hx
  have htc := Ioo_subset_Icc_self ht
  have hpoint := derivativeSlice_equation P hopen hbounded hab hf hU hc u hae hu t htc x hx
  have hslice : EqOn (derivativeSlice hopen hU [] t)
      (fun y ↦ U (timeSpaceCons t y)) Ω :=
    fun y hy ↦ derivativeSlice_nil hopen hab hU hc htc (subset_closure hy)
  have hmem : timeSpaceCons t x ∈ Q := by
    change splitSpaceTime (joinSpaceTime (x, t)) ∈ Ω ×ˢ Ioo a b
    rw [split_joinSpaceTime]
    exact ⟨hx, ht⟩
  have hdt : derivativeSlice hopen hU [0] t x =
      (∂[0] U) (timeSpaceCons t x) :=
    derivativeField_eqOn hopen hU [0] hmem
  have hforcing : derivativeSlice hopen hf [] t x = f (timeSpaceCons t x) :=
    derivativeField_eqOn hopen hf [] hmem
  rwa [hdt, P.classicalLoad_congr hopen hslice hx, hforcing] at hpoint

/-- For forcing continuous on the closed cylinder, the equation at the initial
and terminal faces uses its pointwise value and the continuous time derivative
of the solution from the interior. -/
theorem pointwise_equation_closed_time (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hfc : ContinuousOn f K)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    {g : DerivLp n 2 Ω}
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase) u g) :
    ∀ t ∈ Icc a b, ∀ x ∈ Ω,
      derivativeSlice hopen hU [0] t x +
          P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x =
        f (timeSpaceCons t x) := by
  intro t ht x hx
  have hpoint := derivativeSlice_equation P hopen hbounded hab hf hU hc u hae hu t ht x hx
  have hslice : EqOn (derivativeSlice hopen hU [] t)
      (fun y ↦ U (timeSpaceCons t y)) Ω :=
    fun y hy ↦ derivativeSlice_nil hopen hab hU hc ht (subset_closure hy)
  rwa [P.classicalLoad_congr hopen hslice hx,
    derivativeSlice_nil hopen hab hf hfc ht (subset_closure hx)] at hpoint

/-- Conversely, the pointwise classical equation gives the equation for the
Sobolev derivative classes. This is how classical solutions are compared with
the solution constructed by the weak theory. -/
theorem sobolev_equation_of_pointwise (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (heq : ∀ t ∈ Ioo a b, ∀ x ∈ Ω,
      (∂[0] U) (timeSpaceCons t x) +
          P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x =
        f (timeSpaceCons t x)) :
    ∀ t ∈ Ioo a b,
      wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 1 t) +
          wkpBaseCoordinateCLM
            (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t)) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 0 t) := by
  intro t ht
  have htc := Ioo_subset_Icc_self ht
  have hz := derivativeSlice_regular hopen hbounded hab hU [] 2 htc
  have hload := P.classicalLoad_regular hopen hbounded hz
  have hloadClass :
      P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t) =
        hload.toWkpSpaceOn hopen hbounded 2 := by
    rw [sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hU 2 0 htc]
    exact P.load_toWkpSpaceOn hopen hbounded hz
  apply Lp.ext
  filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU 1 1 htc,
    hload.toWkpSpaceOn_base_ae hopen hbounded 2,
    wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hf 0 0 htc,
    Lp.coeFn_add (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 1 t))
      (wkpBaseCoordinateCLM
        (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t))),
    ae_restrict_mem hopen.measurableSet] with x hdt hL hf₀ hsum hx
  rw [hsum, hloadClass]
  simp only [Pi.add_apply]
  rw [hdt, hL, hf₀]
  have hslice : EqOn (derivativeSlice hopen hU [] t)
      (fun y ↦ U (timeSpaceCons t y)) Ω :=
    fun y hy ↦ derivativeSlice_nil hopen hab hU hc htc (subset_closure hy)
  have hmem : timeSpaceCons t x ∈ Q := by
    change splitSpaceTime (joinSpaceTime (x, t)) ∈ Ω ×ˢ Ioo a b
    rw [split_joinSpaceTime]
    exact ⟨hx, ht⟩
  have htime : derivativeSlice hopen hU [0] t x =
      (∂[0] U) (timeSpaceCons t x) :=
    derivativeField_eqOn hopen hU [0] hmem
  have hforcing : derivativeSlice hopen hf [] t x = f (timeSpaceCons t x) :=
    derivativeField_eqOn hopen hf [] hmem
  simp only [List.replicate_succ, List.replicate_zero]
  rw [htime, P.classicalLoad_congr hopen hslice hx, hforcing]
  exact heq t ht x hx

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
