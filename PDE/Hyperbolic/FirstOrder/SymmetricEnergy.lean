/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.Gronwall
public import PDE.Hyperbolic.FirstOrder.SymmetricSystem
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.SpaceTime

/-!
# Global energy for symmetric first-order systems

We integrate the local energy-flux identity for symmetric first-order
systems. Differentiation under the spatial integral uses a local
dominating function, and spatial fluxes are removed only under `C¹` regularity
and compact-support hypotheses.

The resulting energy balance and Grönwall estimate hold for any sufficiently
regular solution. They are steps 1 and 2 of the proof of Theorem 2 in Evans, §7.3.2, without the
viscous term, and give the analogue of the `L²` estimate (21).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, proof of Theorem 2, steps 1 and 2,
  equations (18)-(21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory Set
open scoped InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

section CompactlySupportedDerivatives

variable {n : ℕ}

end CompactlySupportedDerivatives

namespace LinearFirstOrderSystem

variable {n m : ℕ}

/-- The energy density on the fixed-time spatial slice. -/
def spatialEnergyDensity
    (u : SpaceTime n → ℝ^m) (t : ℝ) (x : ℝ^n) : ℝ :=
  energyDensity (u (PDE.Common.timeSpaceCons t x))

/-- Total energy on a fixed-time spatial slice. -/
def spatialEnergy (u : SpaceTime n → ℝ^m) (t : ℝ) : ℝ :=
  ∫ x, spatialEnergyDensity u t x

/-- The time-coordinate derivative of the energy density on a spatial slice. -/
def spatialEnergyTimeDerivative
    (u : SpaceTime n → ℝ^m) (t : ℝ) (x : ℝ^n) : ℝ :=
  (∂[0] (energyField u)) (PDE.Common.timeSpaceCons t x)

/-- The `j`th energy flux restricted to a fixed-time spatial slice. -/
def spatialEnergyFlux
    (S : LinearFirstOrderSystem n m) (j : Fin n)
    (u : SpaceTime n → ℝ^m) (t : ℝ) (x : ℝ^n) : ℝ :=
  S.energyFluxField j u (PDE.Common.timeSpaceCons t x)

/-- Energy production in the local balance, including the
variable-coefficient correction. -/
def energyProductionField (S : LinearFirstOrderSystem n m) (u : SpaceTime n → ℝ^m)
    (p : SpaceTime n) : ℝ :=
  ⟪S.forcing p, u p⟫_ℝ + (1 / 2 : ℝ) * ∑ j : Fin n, ⟪((∂[j.succ] (S.coefficient j)) p) (u p), u p⟫_ℝ

/-- Energy production restricted to a fixed-time spatial slice. -/
def spatialEnergyProduction
    (S : LinearFirstOrderSystem n m)
    (u : SpaceTime n → ℝ^m) (t : ℝ) (x : ℝ^n) : ℝ :=
  S.energyProductionField u (PDE.Common.timeSpaceCons t x)

/-- Differentiation under the spatial integral for the quadratic energy.

The hypotheses are the local dominated-differentiation assumptions from
Mathlib: measurable nearby slices, integrability at the base time,
measurability of the time derivative, an integrable local dominator, and
pointwise differentiability almost everywhere throughout one common
neighborhood of the base time. -/
theorem hasDerivAt_spatialEnergy
    {u : SpaceTime n → ℝ^m} {t : ℝ} {s : Set ℝ} {bound : ℝ^n → ℝ} (hs : s ∈ 𝓝 t)
    (henergyMeasurable : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (spatialEnergyDensity u r))
    (henergyIntegrable : Integrable (spatialEnergyDensity u t))
    (hderivMeasurable : AEStronglyMeasurable (spatialEnergyTimeDerivative u t))
    (hdominated : ∀ᵐ x, ∀ r ∈ s, ‖spatialEnergyTimeDerivative u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound)
    (hu : ∀ᵐ x, ∀ r ∈ s, DifferentiableAt ℝ u (PDE.Common.timeSpaceCons r x)) :
    Integrable (spatialEnergyTimeDerivative u t) ∧
      HasDerivAt (spatialEnergy u) (∫ x, spatialEnergyTimeDerivative u t x) t := by
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le hs henergyMeasurable henergyIntegrable
    hderivMeasurable hdominated hboundIntegrable ?_
  filter_upwards [hu] with x hx r hr
  have henergyAt : DifferentiableAt ℝ (energyField u) (PDE.Common.timeSpaceCons r x) :=
    ((hx r hr).norm_sq ℝ).const_mul (1 / 2 : ℝ)
  simpa [spatialEnergyDensity, spatialEnergyTimeDerivative, spatialEnergy, energyField] using
    hasDerivAt_timeSpaceCons (energyField u) r x henergyAt

/-- The spatial derivative of a fixed-time flux slice is its corresponding
spacetime derivative. -/
theorem partialDeriv_spatialEnergyFlux
    {S : LinearFirstOrderSystem n m} {u : SpaceTime n → ℝ^m} {t : ℝ} {x : ℝ^n} (j : Fin n)
    (hB : DifferentiableAt ℝ (S.coefficient j) (PDE.Common.timeSpaceCons t x))
    (hu : DifferentiableAt ℝ u (PDE.Common.timeSpaceCons t x)) :
    (∂[j] (S.spatialEnergyFlux j u t)) x =
      (∂[j.succ] (S.energyFluxField j u)) (PDE.Common.timeSpaceCons t x) :=
  partialDeriv_timeSpaceCons_spatial j (S.energyFluxField j u) t x
    (((hB.clm_apply hu).inner ℝ hu).const_mul (1 / 2 : ℝ))

/-- Integrating the local symmetric-system identity over a spatial slice
removes every compactly supported flux divergence.

Besides the pointwise PDE and symmetry hypotheses, this theorem assumes each
fixed-time flux slice is `C¹` and compactly supported. Integrability of the
time derivative then implies integrability of the full production term. -/
theorem integral_spatialEnergyTimeDerivative_eq_production
    {S : LinearFirstOrderSystem n m} {u : SpaceTime n → ℝ^m} {t : ℝ} (hS : S.IsSymmetric)
    (hdomain : ∀ x, PDE.Common.timeSpaceCons t x ∈ S.domain)
    (hu : ∀ x, DifferentiableAt ℝ u (PDE.Common.timeSpaceCons t x))
    (hB : ∀ j x, DifferentiableAt ℝ (S.coefficient j) (PDE.Common.timeSpaceCons t x))
    (hop : ∀ x,
      S.operator u (PDE.Common.timeSpaceCons t x) = S.forcing (PDE.Common.timeSpaceCons t x))
    (hfluxRegular : ∀ j, ContDiff ℝ 1 (S.spatialEnergyFlux j u t))
    (hfluxCompact : ∀ j, HasCompactSupport (S.spatialEnergyFlux j u t))
    (htimeIntegrable : Integrable (spatialEnergyTimeDerivative u t)) :
    Integrable (S.spatialEnergyProduction u t) ∧
      (∫ x, spatialEnergyTimeDerivative u t x) = ∫ x, S.spatialEnergyProduction u t x := by
  have hdiv (j : Fin n) := PDE.DistributionTheory.integrable_partialDeriv_of_hasCompactSupport j
    (hfluxRegular j) (hfluxCompact j)
  have hsum := integrable_finsetSum Finset.univ fun j _ ↦ hdiv j
  have hbalance (x : ℝ^n) : spatialEnergyTimeDerivative u t x +
      ∑ j : Fin n, (∂[j] (S.spatialEnergyFlux j u t)) x = S.spatialEnergyProduction u t x := by
    simp_rw [fun j ↦ partialDeriv_spatialEnergyFlux j (hB j x) (hu x)]
    simpa [spatialEnergyTimeDerivative, spatialEnergyProduction, energyProductionField] using
      local_energy_flux_identity hS (hdomain x) (hu x) (fun j ↦ hB j x) (hop x)
  refine ⟨(htimeIntegrable.add hsum).congr (.of_forall hbalance), ?_⟩
  rw [← integral_congr_ae (.of_forall hbalance), integral_add htimeIntegrable hsum,
    integral_finsetSum _ fun j _ ↦ hdiv j]
  simp [PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport _
    (hfluxRegular _) (hfluxCompact _)]

/-- Exact derivative of the global spatial energy for a sufficiently regular
solution of a symmetric system.

The dominated-differentiation assumptions control the time derivative of the
integral. The domain, PDE, coefficient regularity, and compactly supported
`C¹` flux assumptions then identify that derivative with the integral of the
local production field. -/
theorem hasDerivAt_spatialEnergy_of_solution
    {S : LinearFirstOrderSystem n m} {u : SpaceTime n → ℝ^m} {t : ℝ} {s : Set ℝ}
    {bound : ℝ^n → ℝ} (hS : S.IsSymmetric) (hs : s ∈ 𝓝 t)
    (henergyMeasurable : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (spatialEnergyDensity u r))
    (henergyIntegrable : Integrable (spatialEnergyDensity u t))
    (hderivMeasurable : AEStronglyMeasurable (spatialEnergyTimeDerivative u t))
    (hdominated : ∀ᵐ x, ∀ r ∈ s, ‖spatialEnergyTimeDerivative u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound)
    (huNeighborhood : ∀ᵐ x, ∀ r ∈ s, DifferentiableAt ℝ u (PDE.Common.timeSpaceCons r x))
    (hdomain : ∀ x, PDE.Common.timeSpaceCons t x ∈ S.domain)
    (hu : ∀ x, DifferentiableAt ℝ u (PDE.Common.timeSpaceCons t x))
    (hB : ∀ j x, DifferentiableAt ℝ (S.coefficient j) (PDE.Common.timeSpaceCons t x))
    (hop : ∀ x,
      S.operator u (PDE.Common.timeSpaceCons t x) = S.forcing (PDE.Common.timeSpaceCons t x))
    (hfluxRegular : ∀ j, ContDiff ℝ 1 (S.spatialEnergyFlux j u t))
    (hfluxCompact : ∀ j, HasCompactSupport (S.spatialEnergyFlux j u t)) :
    Integrable (S.spatialEnergyProduction u t) ∧
      HasDerivAt (spatialEnergy u) (∫ x, S.spatialEnergyProduction u t x) t := by
  obtain ⟨htime, hderiv⟩ := hasDerivAt_spatialEnergy hs henergyMeasurable henergyIntegrable
    hderivMeasurable hdominated hboundIntegrable huNeighborhood
  obtain ⟨hprod, hint⟩ := integral_spatialEnergyTimeDerivative_eq_production hS hdomain hu hB hop
    hfluxRegular hfluxCompact htime
  exact ⟨hprod, hderiv.congr_deriv hint⟩

/-- Sum of the operator norms of the spatial derivatives `∂ⱼ Bⱼ` that
enter the variable-coefficient energy production. -/
def coefficientSpatialVariation (S : LinearFirstOrderSystem n m) (p : SpaceTime n) : ℝ :=
  ∑ j : Fin n, ‖(∂[j.succ] (S.coefficient j)) p‖

/-- The quadratic energy density is nonnegative. -/
theorem energyDensity_nonneg (v : ℝ^m) : 0 ≤ energyDensity v := by
  unfold energyDensity
  positivity

/-- Pointwise production is controlled by forcing energy and the spatial
variation of the symmetric-system coefficients.

This algebraic estimate holds for arbitrary fields: the total `fderiv` values occurring in the
production field are bounded by their continuous-linear-map operator norms. -/
theorem energyProductionField_le
    (S : LinearFirstOrderSystem n m) (u : SpaceTime n → ℝ^m) (p : SpaceTime n) :
    S.energyProductionField u p ≤ energyDensity (S.forcing p) +
      (1 + S.coefficientSpatialVariation p) * energyDensity (u p) := by
  have hforcing : ⟪S.forcing p, u p⟫_ℝ ≤ energyDensity (S.forcing p) + energyDensity (u p) := by
    unfold energyDensity
    nlinarith [real_inner_le_norm (S.forcing p) (u p), two_mul_le_add_sq ‖S.forcing p‖ ‖u p‖]
  have hcoefficient : (1 / 2 : ℝ) * ∑ j : Fin n, ⟪((∂[j.succ] (S.coefficient j)) p) (u p), u p⟫_ℝ ≤
      S.coefficientSpatialVariation p * energyDensity (u p) := by
    simp only [coefficientSpatialVariation, energyDensity, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ by
      linarith [real_inner_le_norm (((∂[j.succ] (S.coefficient j)) p) (u p)) (u p),
        mul_le_mul_of_nonneg_right (((∂[j.succ] (S.coefficient j)) p).le_opNorm (u p))
          (norm_nonneg (u p))]
  unfold energyProductionField
  linarith

/-- Spatial integral of the quadratic forcing energy at a fixed time. -/
def spatialForcingEnergy (S : LinearFirstOrderSystem n m) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, energyDensity (S.forcing (PDE.Common.timeSpaceCons t x))

/-- The integrated production is controlled by forcing energy and a uniform
spatial coefficient-variation bound.

The coefficient bound is only required almost everywhere. Integrability of
the production is stated explicitly; for regular solutions it follows from
`hasDerivAt_spatialEnergy_of_solution`. -/
theorem integral_spatialEnergyProduction_le {S : LinearFirstOrderSystem n m} {u : SpaceTime n → ℝ^m}
    {t C : ℝ} (hproductionIntegrable : Integrable (S.spatialEnergyProduction u t))
    (hforcingIntegrable :
      Integrable (fun x : ℝ^n ↦ energyDensity (S.forcing (PDE.Common.timeSpaceCons t x))))
    (henergyIntegrable : Integrable (spatialEnergyDensity u t))
    (hcoefficientBound : ∀ᵐ x ∂(volume : Measure (ℝ^n)),
      S.coefficientSpatialVariation (PDE.Common.timeSpaceCons t x) ≤ C) :
    (∫ x, S.spatialEnergyProduction u t x) ≤
      S.spatialForcingEnergy t + (1 + C) * spatialEnergy u t := by
  have hscaled := henergyIntegrable.const_mul (1 + C)
  have hupper : Integrable (fun x ↦ energyDensity (S.forcing (PDE.Common.timeSpaceCons t x)) +
      (1 + C) * spatialEnergyDensity u t x) := hforcingIntegrable.add hscaled
  refine (integral_mono_ae hproductionIntegrable hupper ?_).trans_eq ?_
  · filter_upwards [hcoefficientBound] with x hx
    refine (S.energyProductionField_le u _).trans ?_
    unfold spatialEnergyDensity
    gcongr
    exact energyDensity_nonneg _
  · rw [integral_add hforcingIntegrable hscaled, integral_const_mul]
    rfl

/-- Conditional global energy estimate for a regular solution of a symmetric
first-order system.

This theorem combines the exact global balance, the integrated production
bound, and Mathlib's Grönwall inequality. Every analytic assumption used by
those steps is a hypothesis: continuity of total energy, local dominated
differentiation, pointwise PDE and coefficient regularity, integrable forcing,
and compactly supported `C¹` flux slices. It does not construct a solution or
establish the hypotheses. -/
theorem spatialEnergy_le_gronwallBound {S : LinearFirstOrderSystem n m} {u : SpaceTime n → ℝ^m}
    {a b δ C ε : ℝ} {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ} (hS : S.IsSymmetric)
    (henergyContinuous : ContinuousOn (spatialEnergy u) (Icc a b)) (hs : ∀ t ∈ Ico a b, s t ∈ 𝓝 t)
    (henergyMeasurable : ∀ t ∈ Ico a b, ∀ᶠ r in 𝓝 t,
      AEStronglyMeasurable (spatialEnergyDensity u r))
    (henergyIntegrable : ∀ t ∈ Icc a b, Integrable (spatialEnergyDensity u t))
    (hderivMeasurable : ∀ t ∈ Ico a b, AEStronglyMeasurable (spatialEnergyTimeDerivative u t))
    (hdominated : ∀ t ∈ Ico a b, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖spatialEnergyTimeDerivative u r x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t ∈ Ico a b, Integrable (bound t))
    (huNeighborhood : ∀ t ∈ Ico a b, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      DifferentiableAt ℝ u (PDE.Common.timeSpaceCons r x))
    (hdomain : ∀ t ∈ Ico a b, ∀ x, PDE.Common.timeSpaceCons t x ∈ S.domain)
    (hu : ∀ t ∈ Ico a b, ∀ x, DifferentiableAt ℝ u (PDE.Common.timeSpaceCons t x))
    (hB : ∀ t ∈ Ico a b, ∀ j x, DifferentiableAt ℝ (S.coefficient j) (PDE.Common.timeSpaceCons t x))
    (hop : ∀ t ∈ Ico a b, ∀ x, S.operator u (PDE.Common.timeSpaceCons t x) =
      S.forcing (PDE.Common.timeSpaceCons t x))
    (hfluxRegular : ∀ t ∈ Ico a b, ∀ j, ContDiff ℝ 1 (S.spatialEnergyFlux j u t))
    (hfluxCompact : ∀ t ∈ Ico a b, ∀ j, HasCompactSupport (S.spatialEnergyFlux j u t))
    (hforcingIntegrable : ∀ t ∈ Ico a b,
      Integrable (fun x : ℝ^n ↦ energyDensity (S.forcing (PDE.Common.timeSpaceCons t x))))
    (hcoefficientBound : ∀ t ∈ Ico a b, ∀ᵐ x ∂(volume : Measure (ℝ^n)),
      S.coefficientSpatialVariation (PDE.Common.timeSpaceCons t x) ≤ C)
    (hforcingBound : ∀ t ∈ Ico a b, S.spatialForcingEnergy t ≤ ε)
    (hinitial : spatialEnergy u a ≤ δ) :
    ∀ t ∈ Icc a b, spatialEnergy u t ≤ gronwallBound δ (1 + C) ε (t - a) := by
  have hbalance (t) (ht : t ∈ Ico a b) := hasDerivAt_spatialEnergy_of_solution hS (hs t ht)
    (henergyMeasurable t ht) (henergyIntegrable t (Ico_subset_Icc_self ht)) (hderivMeasurable t ht)
    (hdominated t ht) (hboundIntegrable t ht) (huNeighborhood t ht) (hdomain t ht) (hu t ht)
    (hB t ht) (hop t ht) (hfluxRegular t ht) (hfluxCompact t ht)
  refine le_gronwallBound_of_liminf_deriv_right_le
    (f' := fun t ↦ ∫ x, S.spatialEnergyProduction u t x) henergyContinuous
    (fun t ht r hr ↦ (hbalance t ht).2.hasDerivWithinAt.liminf_right_slope_le hr) hinitial
    fun t ht ↦ ?_
  linarith [integral_spatialEnergyProduction_le (hbalance t ht).1 (hforcingIntegrable t ht)
    (henergyIntegrable t (Ico_subset_Icc_self ht)) (hcoefficientBound t ht), hforcingBound t ht]

end LinearFirstOrderSystem

end PDE.Hyperbolic.FirstOrder
