/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.PowerGrowth
public import PDE.Analysis.Operator.Coercivity
public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent

/-!
# Power-growth fluxes on the zero-trace Sobolev closure

The vector-valued weak gradient gives a dual-valued flux operator on `Wkp0SpaceOn`.
This is the supported-core closure; on an open domain it represents `W₀¹ᵖ`.
The integral formula itself requires no boundedness or openness assumption.

On a bounded set in positive dimension, Poincaré turns a positive power lower bound
for the flux into a lower bound in the full Sobolev norm, for finite `p ≥ 1`.
When `p > 1`, this lower bound eventually dominates any prescribed multiple of the
norm. This is the coercivity radius estimate.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

local notation "μ" => domainMeasure n Ω
local notation "V" => W₀^{1,p}(Ω)

/-- A measurable flux of `(p-1)` growth defines a weak functional on the
supported-core Sobolev closure, the standard `W^{1,p}_0(Ω)` when `Ω` is open.
The gradient map is `wkpGradientCLM` restricted to this closure. -/
def wkpGradientFluxOperator
    (hp_top : p ≠ ∞) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1)) :
    V → StrongDual ℝ V :=
  PDE.Analysis.Operator.pGrowthFluxOperator (X := V)
    ((wkpGradientCLM (n := n) (p := p) (Ω := Ω)).comp
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule.subtypeL)
    hp_top a hmeas hh hgrowth

/-- The weak flux functional has the expected integral formula
against every test function in the supported-core Sobolev closure. -/
theorem wkpGradientFluxOperator_apply
    (hp_top : p ≠ ∞) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (u v : V) :
    wkpGradientFluxOperator hp_top a hmeas hh hgrowth u v =
      ∫ x, inner ℝ
        (a x (∇ (u : W^{1,p}(Ω)) x))
        (∇ (v : W^{1,p}(Ω)) x) ∂μ := by
  -- Fix the inherited additive structure before applying generic normed-space lemmas.
  let : NormedAddCommGroup V := inferInstance
  simpa only [wkpGradientFluxOperator, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] using
    PDE.Analysis.Operator.pGrowthFluxOperator_apply (X := V)
    ((wkpGradientCLM (n := n) (p := p) (Ω := Ω)).comp
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule.subtypeL)
    hp_top a hmeas hh hgrowth u v

omit [Fact (1 ≤ q)] in
/-- The weak pairing in the general-exponent Dirichlet equation is
integrable under conjugate power growth. -/
theorem integrable_inner_wkpGradientFlux
    (hp_top : p ≠ ∞) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (u v : W^{1,p}(Ω)) :
    Integrable (fun x ↦ inner ℝ (a x (∇ u x)) (∇ v x)) μ :=
  PDE.Analysis.Operator.integrable_inner_flux_of_rpow_growth hp_top a hmeas hh hgrowth
    (Lp.memLp (∇ u)) (Lp.memLp (∇ v))

end SobolevSpace.GraphSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal} {q : ℝ≥0∞}
  [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate (p : ℝ≥0∞) q]

local notation "μ" => domainMeasure n Ω
local notation "V" => W₀^{1,p}(Ω)

/-- Bounded-domain Poincaré turns a positive power lower bound for the
flux into a lower bound in the full supported-core Sobolev norm. This
holds for every finite `p ≥ 1`, without boundary regularity. -/
theorem exists_pos_rpow_lower_bound_wkpGradientFluxOperator
    (hp : 1 ≤ p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : V, K * ‖u‖ ^ (p : ℝ) - (∫ x, b x ∂μ) ≤
      wkpGradientFluxOperator ENNReal.coe_ne_top a hmeas hh hgrowth u u := by
  -- Fix the inherited additive structure before applying generic normed-space lemmas.
  let : NormedAddCommGroup V := inferInstance
  obtain ⟨K, hK, hP⟩ :=
    exists_pos_mul_norm_rpow_le_norm_wkpGradientCLM_rpow hn hΩ hp
  let D : V →L[ℝ] Lp (ℝ^n) p μ :=
    (wkpGradientCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)).comp
      (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
        (Ω := Ω)).toSubmodule.subtypeL
  refine ⟨c * K, mul_pos hc hK, ?_⟩
  intro u
  have hscaled : (c * K) * ‖u‖ ^ (p : ℝ) ≤
      c * ‖D u‖ ^ (p : ℝ) := by
    simpa [D, mul_assoc] using mul_le_mul_of_nonneg_left (hP u) hc.le
  have hflux := PDE.Analysis.Operator.pGrowthFluxOperator_lower_bound
    (X := V)
    D ENNReal.coe_ne_top a hmeas hh hgrowth hb hlower u
  exact (sub_le_sub_right hscaled _).trans hflux

/-- A strictly superlinear pairing lower bound gives the radius
condition used by Browder–Minty on the supported-core Sobolev closure,
the standard `W^{1,p}_0(Ω)` on open sets. Bounded-domain Poincaré controls
the full Sobolev norm by the weak gradient. -/
theorem wkpGradientFluxOperator_coercive
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : V, R ≤ ‖u‖ →
      M * ‖u‖ ≤ wkpGradientFluxOperator ENNReal.coe_ne_top a hmeas hh hgrowth u u := by
  obtain ⟨K, hK, hbound⟩ := exists_pos_rpow_lower_bound_wkpGradientFluxOperator
    hp.le a hmeas hh hgrowth hn hΩ hc hb hlower
  exact PDE.Analysis.exists_radius_mul_norm_le_of_rpow_lower_bound
    (by exact_mod_cast hp) hK hbound M

end SobolevSpace.GraphSpace
