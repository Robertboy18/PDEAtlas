/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Representative.SobolevEquation

/-!
# Initial traces of all wave derivatives

The first two traces come from the original weak identities. The differentiated
equation then identifies every higher initial trace with the compatibility
recurrence, in every spatial Sobolev order. This proves that the computed
compatibility values are derivatives of the same solution.
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
  {f U : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
  (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hg : ∀ k, ContDiffUpToBoundary k g Ω)
  (hh : ∀ k, ContDiffUpToBoundary k h Ω)
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
  (hq₀ : baseCoordCLM q₀ =
    wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 1 0))
  (hp₀ : p₀ =
    wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 0 1))
  (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
    (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
      baseRepresentative (h10SubtypeL (u t)))

include hcont hweak hq₀ hp₀ hae

/-- Every canonical initial derivative equals the recursively computed
initial value, as an equality of full spatial Sobolev classes. -/
theorem initial_sobolev_eq (j r : ℕ) :
    sobolevCurve hopen hbounded hab hU r j a =
      initialSobolevValue P hopen hbounded hab hf hg hh r j := by
  have hbase (r s j : ℕ) :
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh r j) =
        wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh s j) := by
    apply Lp.ext
    exact ((initialValue_regular P hopen hbounded hab hf hg hh j r).toWkpSpaceOn_base_ae
      hopen hbounded 2).trans
      ((initialValue_regular P hopen hbounded hab hf hg hh j s).toWkpSpaceOn_base_ae
        hopen hbounded 2).symm
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  induction j using Nat.twoStepInduction generalizing r with
  | zero =>
    apply wkpBaseCoordinateCLM_injective hopen
    calc
      _ = wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 0 a) := by
        rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU r 0 ha,
          wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU 1 0 ha]
      _ = baseCoordCLM q₀ := initial_displacement_eq hopen hbounded hab hU hcont hweak hae
      _ = _ := hq₀.trans (hbase 1 r 0)
  | one =>
    apply wkpBaseCoordinateCLM_injective hopen
    calc
      _ = wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 1 a) := by
        rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU r 1 ha,
          wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU 1 1 ha]
      _ = p₀ := initial_velocity_eq hopen hbounded hab hU hcont hweak hae
      _ = _ := hp₀.trans (hbase 0 r 1)
  | more j ih _ =>
    calc
      _ = sobolevCurve hopen hbounded hab hf r j a - P.load hopen hbounded r
            (sobolevCurve hopen hbounded hab hU (r + 2) j a) :=
        eq_sub_of_add_eq (sobolev_equation_timeDerivative P hopen hbounded hab hf hU
          hcont hweak hae j r ha)
      _ = (forcingTrace_regular hopen hbounded hab hf j r).toWkpSpaceOn hopen hbounded 2 -
          P.load hopen hbounded r
            (initialSobolevValue P hopen hbounded hab hf hg hh (r + 2) j) := by
        rw [ih, sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hf r j ha]
        rfl
      _ = _ := (classicalWaveInitialSobolevValue_add_two P hopen hbounded
        (forcingTrace_regular hopen hbounded hab hf) hg hh r j).symm

/-- Every initial time derivative has the canonical continuous
compatibility value on the whole spatial closure. -/
theorem initial_derivativeSlice_eq (j : ℕ) {x : ℝ^n} (hx : x ∈ closure Ω) :
    derivativeSlice hopen hU (List.replicate j 0) a x =
      initialBoundaryValue P hopen hbounded hab hf hg hh j x := by
  have hclass := initialValue_regular P hopen hbounded hab hf hg hh j 0
  have hbase : baseRepresentative (sobolevCurve hopen hbounded hab hU 0 j a)
      =ᵐ[domainMeasure n Ω] initialBoundaryValue P hopen hbounded hab hf hg hh j := by
    rw [initial_sobolev_eq P hopen hbounded hab hf hg hh hU hcont hweak hq₀ hp₀ hae]
    filter_upwards [hclass.toWkpSpaceOn_base_ae hopen hbounded 2,
      ae_restrict_mem hopen.measurableSet] with y hy hymem
    exact hy.trans (hclass.continuousRepresentative_eqOn hymem).symm
  have heq := (wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU 0 j
    ⟨le_rfl, hab.le⟩).symm.trans hbase
  have hc : Continuous (derivativeSlice hopen hU (List.replicate j 0) a) :=
    (continuous_derivativeSlice hopen hU (List.replicate j 0)).comp
    (continuous_const.prodMk continuous_id)
  have hq := hclass.continuous_continuousRepresentative
  exact (Measure.eqOn_open_of_ae_eq heq hopen hc.continuousOn hq.continuousOn)
    |>.of_subset_closure hc.continuousOn hq.continuousOn subset_closure Subset.rfl <| hx

end Hyperbolic.HigherRegularity.SmoothWave
