/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.Galerkin
public import PDE.Elliptic.Monotone.GradientFlux
import PDE.Analysis.Operator.Coercivity

/-!
# Galerkin solutions and uniform bounds for monotone gradient fluxes

The weak gradient-flux operator restricts to the span of any finite trial family.
The resulting coefficients solve the integral equations on that span.
The quadratic flux lower bound and bounded-domain Poincaré give one energy constant
for all loads, trial families, and solutions of their finite Galerkin systems.

Only the finite Galerkin equations are used for the energy estimate. They extend
by linearity in the test variable to the trial solution itself. No equation against
arbitrary `H¹₀` tests is assumed. All flux integrals are integrable by
`integrable_inner_gradientFlux`; the load is the usual `L²` pairing.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "V" => H¹₀(Ω)
local notation "μ" => domainMeasure n Ω
local notation "B₀" => baseCoordCLM (n := n) (Ω := Ω)

/-- A measurable monotone gradient flux with linear growth, right hemicontinuity,
and a positive quadratic lower bound admits Galerkin coefficients for any finite
family in `H¹₀`. The equations hold for every test in the trial span. -/
theorem exists_galerkin_coefficients_gradientFlux
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h 2 μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hmono : ∀ᵐ x ∂μ, ∀ p q, 0 ≤ inner ℝ (a x p - a x q) (p - q))
    (hhemi : ∀ᵐ x ∂μ, ∀ p q : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (p + t • q)) q) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ p, c * ‖p‖ ^ 2 - b x ≤ inner ℝ (a x p) p)
    (f : Lp ℝ 2 μ) {ι : Type*} [Fintype ι] (w : ι → V) :
    ∃ d : ι → ℝ, ∀ v ∈ Submodule.span ℝ (range w),
      (∫ x, inner ℝ (a x (∇ ((∑ i, d i • w i : H¹₀(Ω)) : H¹(Ω)) x))
        (∇ (v : H¹(Ω)) x) ∂μ) =
        ∫ x, f x * B₀ v x ∂μ := by
  let A := gradientFluxOperator a hmeas hh hgrowth
  obtain ⟨K, hK, hlowerA⟩ :=
    exists_pos_quadratic_lower_bound_gradientFluxOperator
      a hmeas hh hgrowth hn hΩ hc hb hlower
  have hcoercive : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : V, R ≤ ‖u‖ → M * ‖u‖ ≤ A u u := by
    intro M _
    exact PDE.Analysis.exists_radius_mul_norm_le_of_rpow_lower_bound
      (r := 2) (F := fun u : V ↦ A u u) (by norm_num) hK
      (fun u ↦ by simpa only [Real.rpow_two] using hlowerA u) M
  obtain ⟨d, hd⟩ := @PDE.Analysis.Operator.exists_galerkin_coefficients
    V inferInstance inferInstance A
    (gradientFluxOperator_monotone a hmeas hh hgrowth hmono)
    (gradientFluxOperator_hemicontinuous a hmeas hh hgrowth hhemi)
    hcoercive (loadFunctional f) ι inferInstance w
  refine ⟨d, fun v hv ↦ ?_⟩
  simpa only [A, gradientFluxOperator_apply, loadFunctional_eq_integral,
    ← wkpGradientCLM_h10SubtypeL, h10SubtypeL_apply] using hd v hv

/-- One positive constant bounds every finite Galerkin solution by `1 + ‖f‖₂`.
It is chosen before the load, index type, family, and coefficients. Monotonicity is
unnecessary for this estimate: the lower bound and the finite equations suffice. -/
theorem exists_pos_galerkin_bound_gradientFlux
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h 2 μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ p, c * ‖p‖ ^ 2 - b x ≤ inner ℝ (a x p) p) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f : Lp ℝ 2 μ) {ι : Type*} [Fintype ι]
      (w : ι → V) (d : ι → ℝ),
      (∀ i, (∫ x, inner ℝ (a x (∇ ((∑ j, d j • w j : H¹₀(Ω)) : H¹(Ω)) x))
        (∇ (w i : H¹(Ω)) x) ∂μ) =
        ∫ x, f x * B₀ (w i) x ∂μ) →
      ‖∑ i, d i • w i‖ ≤ M * (1 + ‖f‖) := by
  let A := gradientFluxOperator a hmeas hh hgrowth
  obtain ⟨K, hK, hlowerA⟩ :=
    exists_pos_quadratic_lower_bound_gradientFluxOperator
      a hmeas hh hgrowth hn hΩ hc hb hlower
  obtain ⟨M, hM, hbound⟩ :=
    PDE.Analysis.Operator.exists_pos_galerkin_norm_bound A hK hlowerA
  refine ⟨M, hM, ?_⟩
  intro f ι _ w d heq
  have heqA : ∀ i, A (∑ j, d j • w j) (w i) = loadFunctional f (w i) := by
    simpa only [A, gradientFluxOperator_apply, loadFunctional_eq_integral,
      ← wkpGradientCLM_h10SubtypeL, h10SubtypeL_apply] using heq
  exact (hbound (loadFunctional f) w d heqA).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right (norm_loadFunctional_le f) 1) hM.le)

end SobolevSpace.GraphSpace
