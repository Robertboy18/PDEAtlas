/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Definition
public import PDE.Spaces.Sobolev.Evolution.Classical.Data.ZeroBoundary

/-!
# The Sobolev equation of a classical wave

The pointwise full equation identifies the canonical Sobolev classes. The
zero-boundary curve then satisfies the variational acceleration equation.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave.IsClassicalSolution

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical
open PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  {P : SmoothFullCoefficients n Ω}
  {hopen : IsOpen Ω} (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {f U : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
  {hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))}
  {hg : ∀ k, ContDiffUpToBoundary k g Ω} {hh : ∀ k, ContDiffUpToBoundary k h Ω}
  (hU : IsClassicalSolution P hopen hf hg hh U)

/-- The pointwise equation gives the same full equation in every spatial
Sobolev order at every closed-interval time. -/
theorem sobolev_equation (r : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    sobolevCurve hopen hbounded hab hU.smooth r 2 t +
      P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU.smooth (r + 2) 0 t) =
        sobolevCurve hopen hbounded hab hf r 0 t := by
  have hL := P.classicalLoad_regular hopen hbounded
    (derivativeSlice_regular hopen hbounded hab hU.smooth [] (r + 2) ht)
  have hload : (wkpBaseCoordinateCLM
      (P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU.smooth (r + 2) 0 t)) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      P.classicalLoad (derivativeSlice hopen hU.smooth [] t) := by
    rw [sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hU.smooth (r + 2) 0 ht, P.load_toWkpSpaceOn]
    exact hL.toWkpSpaceOn_base_ae hopen hbounded 2
  apply wkpBaseCoordinateCLM_injective hopen
  rw [map_add]
  apply Lp.ext
  filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU.smooth r 2 ht,
    hload, wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hf r 0 ht,
    Lp.coeFn_add (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU.smooth r 2 t))
      (wkpBaseCoordinateCLM
        (P.load hopen hbounded r (sobolevCurve hopen hbounded hab hU.smooth (r + 2) 0 t))),
    ae_restrict_mem hopen.measurableSet] with x hacc hload hforce hadd hx
  rw [hadd, Pi.add_apply, hacc, hload, hforce]
  have heq := P.classicalLoad_congr hopen
    (fun y hy ↦ derivativeSlice_nil hopen hab hU.smooth hU.continuous ht (subset_closure hy)) hx
  simpa only [List.replicate_succ, List.replicate_zero, heq] using hU.equation t ht x hx

/-- The canonical velocity has the full variational acceleration.
The zero-boundary curve is constructed from the literal lateral values. -/
theorem velocity_hasWeakTimeDerivativeOn [Fact (0 < n)] (hgraph : Boundary.HasC1GraphBoundary Ω) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ (h10L2GelfandTriple hopen).pivotToDual
        (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU.smooth 1 1 t)))
      (fun t ↦ (h10L2GelfandTriple hopen).pivotToDual
        (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 0 t)) -
          P.form hopen hbounded
            (zeroBoundaryCurve hopen hbounded hgraph hab hU.smooth hU.continuous
              hU.boundary 0 t)) := by
  have hd := ((hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hU.smooth 1 1).map
    wkpBaseCoordinateCLM).map (h10L2GelfandTriple hopen).pivotToDual
  apply hd.congr_ae_restrict measurableSet_Ioo (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hti := Ioo_subset_Icc_self ht
  have hbase : wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU.smooth 2 0 t) =
      baseCoordCLM (zeroBoundaryCurve hopen hbounded hgraph hab hU.smooth hU.continuous
        hU.boundary 0 t) := by
    change _ = wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU.smooth 1 0 t)
    rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU.smooth 2 0 hti,
      wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU.smooth 1 0 hti]
  have hform : P.form hopen hbounded
      (zeroBoundaryCurve hopen hbounded hgraph hab hU.smooth hU.continuous hU.boundary 0 t) =
      (h10L2GelfandTriple hopen).pivotToDual (wkpBaseCoordinateCLM (P.load hopen hbounded 0
          (sobolevCurve hopen hbounded hab hU.smooth 2 0 t))) := by
    ext z
    exact P.form_eq_load hopen hbounded 0 _ _ z hbase
  have heq := congrArg (fun z ↦ (h10L2GelfandTriple hopen).pivotToDual
    (wkpBaseCoordinateCLM z)) (hU.sobolev_equation hbounded hab 0 hti)
  rw [map_add, map_add] at heq
  dsimp only [Function.comp_apply]
  rw [hform]
  rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU.smooth 1 2 hti,
    ← wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU.smooth 0 2 hti]
  exact eq_sub_iff_add_eq.mpr heq

end Hyperbolic.HigherRegularity.SmoothWave.IsClassicalSolution
