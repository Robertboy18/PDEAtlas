/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.BackwardUniqueness.Energy
public import PDE.Analysis.Calculus.LogConvexity.Energy

/-!
# Backwards uniqueness from classical closure data

Equal lateral and terminal values determine a heat solution throughout the closed cylinder; this is
Evans's §2.3.4(b), Theorem 11 (Backwards uniqueness). The spatial domain is bounded and open with a
C¹ graph boundary; it need not be connected or nonempty. The solution is jointly C² up to the
boundary of the cylinder (`ContDiffUpToBoundary 2`) and continuous on its closure, as in Evans's
`u ∈ C²(Ū_T)`.

The energy identities, and the vanishing of `∂ₜu` on the lateral boundary that they use, follow from
these hypotheses. No initial equality or extension across the spacetime boundary is assumed.

## Main results

* `eq_on_closedCylinder_of_terminal_eq`: two solutions with equal lateral and terminal values agree
  on the closed cylinder.
* `eq_zero_on_closedCylinder_of_terminal_eq_zero`: the case of zero data.

## How it works

Evans sets `e(t) = ∫_U w²` for the difference `w`, computes `ė = -2∫|Dw|²` (44) and `ë = 4∫(Δw)²`
(45), deduces `ė² ≤ e ë` (46) from the Cauchy-Schwarz inequality, and uses the convexity of `log e`
on an interval where `e > 0`, (47)-(48). We use the same identities:
`hasDerivAt_squareEnergy_of_zero_boundary` and `hasDerivAt_dirichletEnergy_of_zero_boundary` give
the two derivatives, and `squareEnergy_derivative_sq_le` gives (46).
`PDE.Analysis.energy_eq_zero_of_terminal_eq_zero` avoids the choice of that interval: by (46) and
`E'' ≥ 0`, `log (E + ε)` is convex for every `ε > 0`, and letting `ε → 0` in the convexity bound
shows that `E(b) = 0` forces `E = 0` on the whole interval.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.4(b), (42)-(43), p. 63, and Theorem 11 (Backwards
  uniqueness) and its proof, (44)-(48), pp. 64-65.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)
open scoped Gradient

@[expose] public noncomputable section

namespace HeatEquation

open MeasureTheory PDE.Common PDE.Analysis Set SobolevSpace
open Filter
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}
  {u v : ℝ^(n + 1) → ℝ}

/-- Zero lateral and terminal values force vanishing on the closed cylinder. -/
theorem eq_zero_on_closedCylinder_of_terminal_eq_zero
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    (hPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, heatOperator u (timeSpaceCons t x) = 0)
    (hterminal : ∀ x ∈ Ω, u (timeSpaceCons b x) = 0) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0 := by
  let E (s : ℝ) := ∫ x in Ω, u (timeSpaceCons s x) ^ 2
  let E₁ (s : ℝ) := -2 * ∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons s y)) x‖ ^ 2
  let E₂ (s : ℝ) := 4 * ∫ x in Ω, (∂[0] u) (timeSpaceCons s x) ^ 2
  have h₁ (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt E (E₁ t) t :=
    hasDerivAt_squareEnergy_of_zero_boundary hΩ hbounded hgraph hu hc hzero hPDE ht
  have h₂ (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt E₁ (E₂ t) t := by
    convert (hasDerivAt_dirichletEnergy_of_zero_boundary
      hΩ hbounded hgraph hu hc hzero hPDE ht).const_mul (-2) using 1
    dsimp [E₂]
    ring
  have hterminalE : E b = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    simp only [hterminal x hx, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply]
  have hEzero : EqOn E (fun _ ↦ 0) (Icc a b) :=
    energy_eq_zero_of_terminal_eq_zero
      (continuousOn_integral_sq_of_cylinder_closure hΩ hbounded hab hc)
      (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) h₁ h₂
      (fun _ _ ↦ mul_nonneg (by norm_num) (integral_nonneg (fun _ ↦ sq_nonneg _)))
      (fun _ ht ↦ squareEnergy_derivative_sq_le hΩ hbounded hgraph hu hc hzero hPDE ht)
      hab hterminalE
  have hslicezero {t : ℝ} (ht : t ∈ Ioo a b) :
      EqOn (fun x ↦ u (timeSpaceCons t x)) (fun _ ↦ 0) Ω := by
    have hr := hu.spaceSlice hΩ isOpen_Ioo ht
    have hint : IntegrableOn (fun x ↦ u (timeSpaceCons t x) ^ 2) Ω := by
      simpa only [pow_two] using (hr.mul hr hΩ hbounded).integrableOn hΩ hbounded
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _) hint).mp
      (hEzero (Ioo_subset_Icc_self ht))
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hΩ
      hr.contDiffOn.continuousOn continuousOn_const
    filter_upwards [hae] with x hx
    exact (sq_eq_zero_iff).mp hx
  have hQzero : EqOn u (fun _ ↦ 0) (spaceTimeCylinder Ω (Ioo a b)) := by
    intro p hp
    change p 0 ∈ Ioo a b ∧ spatialPartCLM n p ∈ Ω at hp
    simpa only [timeSpaceCons_spatialPartCLM] using hslicezero hp.1 hp.2
  have hclosed := hQzero.of_subset_closure hc continuousOn_const subset_closure Subset.rfl
  intro x hx t ht
  apply hclosed
  rw [closure_spaceTimeCylinder, closure_Ioo hab.ne]
  exact timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩

/-- Backwards uniqueness for two classical heat solutions with arbitrary equal
lateral values and equal terminal values in the spatial interior. -/
theorem eq_on_closedCylinder_of_terminal_eq
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hv : ContDiffUpToBoundary 2 v (spaceTimeCylinder Ω (Ioo a b)))
    (huc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hvc : ContinuousOn v (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hub : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = v (timeSpaceCons t x))
    (huPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, heatOperator u (timeSpaceCons t x) = 0)
    (hvPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, heatOperator v (timeSpaceCons t x) = 0)
    (hterminal : ∀ x ∈ Ω, u (timeSpaceCons b x) = v (timeSpaceCons b x)) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc a b,
      u (timeSpaceCons t x) = v (timeSpaceCons t x) := by
  have hQ := isOpen_spaceTimeCylinder (I := Ioo a b) hΩ isOpen_Ioo
  have hres {w : ℝ^(n + 1) → ℝ}
      (hw : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, heatOperator w (timeSpaceCons t x) = 0) :
      SatisfiesPDEProblem (heatEquation (spaceTimeCylinder Ω (Ioo a b))) w := by
    apply heatEquation.of_residual
    intro p hp
    change p 0 ∈ Ioo a b ∧ spatialPartCLM n p ∈ Ω at hp
    simpa only [timeSpaceCons_spatialPartCLM] using hw _ hp.2 _ hp.1
  have hspace {w : ℝ^(n + 1) → ℝ}
      (hw : ContDiffUpToBoundary 2 w (spaceTimeCylinder Ω (Ioo a b))) :
      ∀ p ∈ spaceTimeCylinder Ω (Ioo a b),
        ContDiffAt ℝ 2 (fun y ↦ w (timeSpaceCons (p 0) y)) (spatialPartCLM n p) := by
    intro p hp
    change p 0 ∈ Ioo a b ∧ spatialPartCLM n p ∈ Ω at hp
    exact (hw.spaceSlice hΩ isOpen_Ioo hp.1).contDiffOn.contDiffAt (hΩ.mem_nhds hp.2)
  have hsub := heatEquation_sub (hres huPDE) (hres hvPDE)
    (fun p hp ↦ (hu.contDiffOn.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp))
    (fun p hp ↦ (hv.contDiffOn.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp))
    (hspace hu) (hspace hv)
  have hz := eq_zero_on_closedCylinder_of_terminal_eq_zero hΩ hbounded hgraph hab
    (hu.sub hv hQ) (huc.sub hvc)
    (fun x hx t ht ↦ sub_eq_zero.mpr (hub x hx t ht))
    (fun x hx t ht ↦ heatEquation.residual_eq hsub
      (timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩))
    (fun x hx ↦ sub_eq_zero.mpr (hterminal x hx))
  exact fun x hx t ht ↦ sub_eq_zero.mp (hz x hx t ht)

end HeatEquation
