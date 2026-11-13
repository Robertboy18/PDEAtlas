/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.PowerGrowth

/-!
# Quantitative monotonicity of integral flux operators

A pointwise power lower bound for the difference of a flux passes to its
weak operator. Conjugate growth makes both tested fluxes integrable before
their integrals are subtracted. The measure is arbitrary, and the field map
may be any continuous linear map into a finite-exponent `Lᵖ` space.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Operator

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology

variable {α E X : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- A power modulus of monotonicity for the pointwise flux gives the same
modulus in the `Lᵖ` norm of the field difference. No lower bound on the field
map, completeness, finite measure, or continuity of the flux is needed.
The input exponent is finite; `p = 1` and conjugate exponent `q = ∞` are allowed. -/
theorem pGrowthFluxOperator_sub_lower_bound (D : X →L[ℝ] Lp E p μ)
    (hp_top : p ≠ ∞) (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    {c : ℝ}
    (hmono : ∀ᵐ x ∂μ, ∀ z w,
      c * ‖z - w‖ ^ p.toReal ≤ inner ℝ (a x z - a x w) (z - w))
    (u v : X) :
    c * ‖D (u - v)‖ ^ p.toReal ≤
      (pGrowthFluxOperator D hp_top a hmeas hh hgrowth u -
        pGrowthFluxOperator D hp_top a hmeas hh hgrowth v) (u - v) := by
  have hp_zero := ENNReal.HolderConjugate.ne_zero p q
  have hint := (Lp.memLp (D (u - v))).integrable_norm_rpow hp_zero hp_top
  have hIu := integrable_inner_flux_of_rpow_growth hp_top a hmeas hh hgrowth
    (Lp.memLp (D u)) (Lp.memLp (D (u - v)))
  have hIv := integrable_inner_flux_of_rpow_growth hp_top a hmeas hh hgrowth
    (Lp.memLp (D v)) (Lp.memLp (D (u - v)))
  have hsub : D (u - v) =ᵐ[μ] fun x ↦ D u x - D v x := by
    rw [map_sub]
    exact Lp.coeFn_sub (D u) (D v)
  rw [sub_apply, pGrowthFluxOperator_apply, pGrowthFluxOperator_apply,
    ← integral_sub hIu hIv]
  calc
    c * ‖D (u - v)‖ ^ p.toReal =
        ∫ x, c * ‖D (u - v) x‖ ^ p.toReal ∂μ := by
      rw [integral_const_mul, ← Lp.norm_rpow_eq_integral hp_zero hp_top]
    _ ≤ _ := by
      apply integral_mono_ae (hint.const_mul c) (hIu.sub hIv)
      filter_upwards [hmono, hsub] with x hx hdx
      rw [Pi.sub_apply, hdx, ← inner_sub_left]
      exact hx _ _

end PDE.Analysis.Operator
