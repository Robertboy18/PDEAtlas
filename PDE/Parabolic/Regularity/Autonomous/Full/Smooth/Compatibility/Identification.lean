/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Compatibility.InitialValues
public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Equation.HigherTimeDerivatives
public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.InitialValue

/-!
# The initial time derivatives are the compatibility values

The differentiated full equation gives the initial recurrence in every Sobolev
order. Spatial continuity identifies these classes with the pointwise
compatibility values on the entire spatial closure.
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

/-- At every spatial order, every initial time derivative has the
recursively derived Sobolev compatibility value. -/
theorem initial_sobolev_value_all_orders (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      u ((hg 0).toLp hopen hbounded 2)) (j r : ℕ) :
    sobolevCurve hopen hbounded hab hU r j a =
      initialSobolevValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg r j := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  let hF := initialForcingValue_regular hopen hbounded hab hf
  induction j generalizing r with
  | zero =>
    apply wkpBaseCoordinateCLM_injective hopen
    exact (initial_sobolev_value P hopen hbounded hab hf hU hc u hae hu r).trans
      (base_initialSobolevValue_zero P hopen hbounded hF hg r).symm
  | succ j ih =>
    apply wkpBaseCoordinateCLM_injective hopen
    have heq := sobolev_equation_derivatives P hopen hbounded hab hf hU
      (sobolev_equation P hopen hbounded hab hf hU hc u hae hu) j a ha
    rw [ih 2] at heq
    have hrec : wkpBaseCoordinateCLM
        (initialSobolevValue P hopen hbounded hF hg 0 (j + 1)) =
          wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 j a) -
            wkpBaseCoordinateCLM
              (P.load hopen hbounded 0 (initialSobolevValue P hopen hbounded hF hg 2 j)) := by
      rw [initialSobolevValue_succ, map_sub,
        sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hf 0 j ha]
      rfl
    have hUbase : wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU r (j + 1) a) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 (j + 1) a) := by
      rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU r (j + 1) ha,
        wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU 0 (j + 1) ha]
    have hbase : wkpBaseCoordinateCLM
        (initialSobolevValue P hopen hbounded hF hg 0 (j + 1)) =
          wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hF hg r (j + 1)) := by
      apply Lp.ext
      exact ((initialValue_regular P hopen hbounded hF hg (j + 1) 0).toWkpSpaceOn_base_ae
        hopen hbounded 2).trans
          ((initialValue_regular P hopen hbounded hF hg (j + 1) r).toWkpSpaceOn_base_ae
            hopen hbounded 2).symm
    exact hUbase.trans ((eq_sub_of_add_eq heq).trans (hrec.symm.trans hbase))

/-- The continuous extension of every initial time derivative equals
the recursively derived compatibility value at every point of the spatial
closure. In particular, the zero compatibility values are attained. -/
theorem initial_derivative_value_all_orders (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      u ((hg 0).toLp hopen hbounded 2)) (j : ℕ) :
    EqOn (derivativeSlice hopen hU (List.replicate j 0) a)
      (initialBoundaryValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg j) (closure Ω) := by
  let hF := initialForcingValue_regular hopen hbounded hab hf
  let hval := initialValue_regular P hopen hbounded hF hg j 0
  have hclass := wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU 0 j
    (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
  rw [initial_sobolev_value_all_orders P hopen hbounded hab hf hg hU hc u hae hu j 0]
    at hclass
  have heq : derivativeSlice hopen hU (List.replicate j 0) a
      =ᵐ[domainMeasure n Ω] hval.continuousRepresentative := by
    filter_upwards [hclass, hval.toWkpSpaceOn_base_ae hopen hbounded 2,
      ae_restrict_mem hopen.measurableSet] with x hx hv hxΩ
    exact hx.symm.trans (hv.trans (hval.continuousRepresentative_eqOn hxΩ).symm)
  have hc₁ : Continuous (derivativeSlice hopen hU (List.replicate j 0) a) :=
    (continuous_derivativeSlice hopen hU _).comp (continuous_const.prodMk continuous_id)
  have hc₂ := hval.continuous_continuousRepresentative
  have hon := Measure.eqOn_open_of_ae_eq heq hopen hc₁.continuousOn hc₂.continuousOn
  exact hon.of_subset_closure hc₁.continuousOn hc₂.continuousOn subset_closure Subset.rfl

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
