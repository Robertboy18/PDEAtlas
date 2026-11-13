/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Compatibility.Forcing
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# The Sobolev equation of a smooth parabolic representative

The integrated weak equation identifies the time derivative of any smooth
representative with the residual of the full spatial operator. Uniqueness of
weak derivatives and injectivity of the pivot inclusion give the equation in
`L²(Ω)`. Continuity extends it to every time in the closed interval.
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

/-- A smooth representative of an integrated weak solution satisfies the full
parabolic equation in the pivot space at every time, including both endpoints. -/
theorem sobolev_equation (P : SmoothFullCoefficients n Ω)
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
    ∀ t ∈ Icc a b,
      wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 1 t) +
          wkpBaseCoordinateCLM
            (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t)) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 0 t) := by
  let T := h10L2GelfandTriple hopen
  let B := P.form hopen hbounded
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
    (forcingJet hopen hbounded hab hf 0 0).headBase
  have hBmeas (v : H¹₀(Ω)) :
      AEStronglyMeasurable (fun _ : ℝ ↦ B v) (volume.restrict (Ioc a b)) :=
    aestronglyMeasurable_const
  have hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B‖ ≤ ‖B‖ :=
    Eventually.of_forall fun _ ↦ le_rfl
  let du := gelfandResidualLp (fun _ ↦ B) ell u hBmeas ‖B‖ hBbound
  have hdu : HasGelfandWeakTimeDerivativeOn T u du :=
    hu.hasWeakTimeDerivative_residual hBmeas ‖B‖ hBbound
  have hbase (r : ℕ) : ∀ᵐ t ∂volume.restrict (Ioo a b),
      wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU r 0 t) =
        baseCoordCLM (u t) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htm
    exact wkpBaseCoordinate_sobolevCurve_zero_eq hopen hbounded hab hU hc r
      (Ioo_subset_Icc_self htm) ht
  have hactual := ((hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hU 0 0).map
    (wkpBaseCoordinateCLM (n := n) (m := 0) (p := 2) (Ω := Ω))).map T.pivotToDual
  have hactual' : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ T.energyToDual (u t))
      (fun t ↦ T.pivotToDual
        (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 1 t))) := by
    apply hactual.congr_ae_restrict measurableSet_Ioo _ Filter.EventuallyEq.rfl
    filter_upwards [hbase 0] with t ht
    exact congrArg T.pivotToDual ht
  have hderiv := hactual'.ae_eq isOpen_Ioo hdu.hasWeakTimeDerivativeOn
  have hIoo : ae (volume.restrict (Ioo a b)) ≤ ae (volume.restrict (Ioc a b)) :=
    ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)
  have hres := (gelfandResidualLp_apply_ae (fun _ ↦ B) ell u hBmeas ‖B‖ hBbound).filter_mono hIoo
  have hell := (T.pivotToDual.coeFn_compLpL
    (forcingJet hopen hbounded hab hf 0 0).headBase).filter_mono hIoo
  have hfbase := (forcingJet hopen hbounded hab hf 0 0).headBase_ae.filter_mono hIoo
  have hfcurve := (sobolevTimeDerivative_ae hopen hbounded hab hf 0 0).filter_mono hIoo
  have heq : ∀ᵐ t ∂volume.restrict (Icc a b),
      wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 1 t) +
          wkpBaseCoordinateCLM
            (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t)) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 0 t) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    filter_upwards [hderiv, hres, hell, hfbase, hfcurve, hbase 2]
      with t hd hr he hf₀ hf₁ hu₂
    have hform : B (u t) = T.pivotToDual (wkpBaseCoordinateCLM
        (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t))) := by
      ext v
      exact P.form_eq_load hopen hbounded 0 _ (u t) v hu₂
    apply T.pivotToDual_injective
    rw [map_add, ← hform, hd]
    change du t + B (u t) = _
    rw [hr, sub_add_cancel, he, hf₀, head_forcingJet, hf₁]
  have := continuousOn_sobolevCurve hopen hbounded hab hU 0 1
  have := continuousOn_sobolevCurve hopen hbounded hab hU 2 0
  have := continuousOn_sobolevCurve hopen hbounded hab hf 0 0
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne heq (by fun_prop) (by fun_prop)

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
