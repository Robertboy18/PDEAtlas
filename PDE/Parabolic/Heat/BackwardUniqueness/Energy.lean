/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.EnergyMethods.Dirichlet.Classical.Cylinder
public import PDE.Parabolic.Heat.Equation
import PDE.Analysis.MeasureTheory.Lp.WeightedL2

/-!
# Energy derivatives for the heat equation on a bounded domain

Both identities integrate by parts against functions that vanish on a C¹ spatial boundary. Joint C²
regularity up to the boundary suffices: the second energy derivative uses commuting mixed second
derivatives, without differentiating the Laplacian in time.

These are the identities (44)-(46) in Evans's proof of §2.3.4(b), Theorem 11. His (45) ends with
`4∫(Δw)²`; here the derivative of `∫|Du|²` is written as `-2∫(∂ₜu)²`, the same quantity by the heat
equation.

## Main results

* `hasDerivAt_squareEnergy_of_zero_boundary`: the derivative of `∫ u²` is `-2∫|Du|²`, Evans's (44).
* `hasDerivAt_dirichletEnergy_of_zero_boundary`: the derivative of `∫|Du|²` is `-2∫(∂ₜu)²`, which
  gives (45).
* `squareEnergy_derivative_sq_le`: the Cauchy-Schwarz bound (46).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.4(b), Theorem 11 (Backwards uniqueness) and step 1 of
  its proof, (44)-(46), pp. 64-65.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public noncomputable section

open PDE (laplacian iteratedPartialDeriv)

namespace HeatEquation

open MeasureTheory PDE.Common PDE.Analysis PDE.EnergyMethods Set SobolevSpace
open Filter
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}
  {u : ℝ^(n + 1) → ℝ}

/-- The first square-energy identity, from the interior heat equation and zero lateral
values. -/
theorem hasDerivAt_squareEnergy_of_zero_boundary
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    (hPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, heatOperator u (timeSpaceCons t x) = 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ ∫ x in Ω, u (timeSpaceCons s x) ^ 2)
      (-2 * ∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons t y)) x‖ ^ 2) t := by
  have hder := hasDerivAt_integral_sq_of_cylinder_closure hΩ hbounded
    (hu.of_le (by omega)) hc ht
  have hslice := hu.spaceSlice hΩ isOpen_Ioo ht
  have hsliceC : ContinuousOn (fun x ↦ u (timeSpaceCons t x)) (closure Ω) := by
    apply hc.comp (contDiff_timeSpaceCons_spatial n t (m := 0)).continuous.continuousOn
    intro x hx
    rw [closure_spaceTimeCylinder]
    exact timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨subset_closure ht, hx⟩
  have hibp := integral_mul_laplacian_eq_neg_energy_of_zero_boundary
    hΩ hbounded hgraph hslice hsliceC
    (fun x hx ↦ hzero x hx t (Ioo_subset_Icc_self ht))
  have heq : (∫ x in Ω, u (timeSpaceCons t x) * (∂[0] u) (timeSpaceCons t x)) =
      ∫ x in Ω, u (timeSpaceCons t x) * laplacian (fun y ↦ u (timeSpaceCons t y)) x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    congr 1
    have h := hPDE x hx t ht
    simpa only [heatOperator, timeSpaceCons_zero, spatialPartCLM_timeSpaceCons,
      sub_eq_zero] using h
  rw [heq, hibp.2.2] at hder
  convert hder using 1
  ring

/-- The derivative of the Dirichlet energy is `-2 ∫ (∂ₜu)²`. The proof uses the mixed second
derivatives of `u` and the vanishing of `∂ₜu` on the lateral boundary; no third derivative is
required. -/
theorem hasDerivAt_dirichletEnergy_of_zero_boundary
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    (hPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, heatOperator u (timeSpaceCons t x) = 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ ∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons s y)) x‖ ^ 2)
      (-2 * ∫ x in Ω, (∂[0] u) (timeSpaceCons t x) ^ 2) t := by
  have hder := PDE.EnergyMethods.hasDerivAt_dirichletEnergy_of_zero_boundary
    hΩ hbounded hgraph hu hc hzero ht
  have heq : (∫ x in Ω, laplacian (fun y ↦ u (timeSpaceCons t y)) x *
      (∂[0] u) (timeSpaceCons t x)) =
        ∫ x in Ω, (∂[0] u) (timeSpaceCons t x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    have h := hPDE x hx t ht
    simp only [heatOperator, timeSpaceCons_zero, spatialPartCLM_timeSpaceCons, sub_eq_zero] at h
    rw [← h, pow_two]
  rwa [heq] at hder

/-- Cauchy-Schwarz for the first and second square-energy derivatives. -/
theorem squareEnergy_derivative_sq_le
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    (hPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, heatOperator u (timeSpaceCons t x) = 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    (-2 * ∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons t y)) x‖ ^ 2) ^ 2 ≤
      (∫ x in Ω, u (timeSpaceCons t x) ^ 2) *
        (4 * ∫ x in Ω, (∂[0] u) (timeSpaceCons t x) ^ 2) := by
  have hQ := isOpen_spaceTimeCylinder (I := Ioo a b) hΩ isOpen_Ioo
  have hslice := hu.spaceSlice hΩ isOpen_Ioo ht
  have hdslice := (hu.partialDeriv_of_succ hQ 0).spaceSlice hΩ isOpen_Ioo ht
  have hf := hslice.memLp_iteratedPartialDeriv hΩ hbounded 2 [] (by simp)
  have hg := hdslice.memLp_iteratedPartialDeriv hΩ hbounded 2 [] (by simp)
  have hCS := (abs_integral_le_integral_abs).trans
    (integral_abs_mul_le_sqrt_integral_sq hf hg)
  have hsquare := mul_self_le_mul_self (abs_nonneg _) hCS
  simp only [← pow_two, sq_abs, mul_pow,
    Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)),
    iteratedPartialDeriv, domainMeasure] at hsquare
  have heq := (hasDerivAt_squareEnergy_of_zero_boundary
    hΩ hbounded hgraph hu hc hzero hPDE ht).unique
      (hasDerivAt_integral_sq_of_cylinder_closure hΩ hbounded
        (hu.of_le (by omega)) hc ht)
  rw [heq]
  nlinarith

end HeatEquation
