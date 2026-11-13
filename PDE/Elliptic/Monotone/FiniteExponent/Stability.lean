/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.PowerGrowthStability
public import PDE.Elliptic.Variational.PowerGrowth

/-!
# Dependence of monotone Dirichlet solutions on their loads

Suppose a flux satisfies
`c ‖z - w‖ᵖ ≤ ⟨a(x,z) - a(x,w), z - w⟩` with `c > 0`.
Subtracting two weak equations and testing with the difference gives an
`Lᵖ` gradient estimate. Bounded-domain Poincaré turns it into
`‖u - v‖^(p-1) ≤ K ‖ℓ₁ - ℓ₂‖` in the full Sobolev norm.
This is a Hölder estimate with exponent `1/(p-1)`. The theorem assumes `2 ≤ p`, because for
`1 < p < 2` the monotonicity and growth hypotheses contradict each other on any domain of
positive measure.

The theorem concerns solutions, so neither hemicontinuity nor an existence
hypothesis is needed. Power growth supplies the integrability of the weak
pairings. The domain is any bounded set of positive dimension, with boundary
data understood as membership in the supported smooth-core closure. On open
sets this is the usual zero Sobolev boundary condition.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal Sobolev Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal}
  [Fact (1 ≤ (p : ℝ≥0∞))]

local notation "μ" => domainMeasure n Ω
local notation "q" => ENNReal.conjExponent (p : ℝ≥0∞)
local notation "V" => W₀^{1,p}(Ω)

/-- Uniform power monotonicity gives quantitative dependence on the continuous
dual load for finite-exponent weak Dirichlet solutions.

The positive constant comes from the domain's Poincaré constant, the exponent,
and the pointwise monotonicity coefficient. Growth and measurability derive
integrability of the tested fluxes; no estimate on the assembled weak operator
is assumed. The conclusion also bounds the error of any approximation whose
weak residual is represented by a continuous dual load.

The exponent is restricted to `2 ≤ p`. For `1 < p < 2` the hypotheses cannot hold on a domain
of positive measure: summing `hmono` over unit steps along a unit vector `e` gives
`c k ≤ ⟨a(x,k e) - a(x,0), e⟩`, while `hgrowth` bounds the right side by `2 h(x) + C k^(p-1)`. -/
theorem exists_norm_sub_rpow_le_load_norm_of_wkpGradientFlux
    (hp : 2 ≤ p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) {c : ℝ} (hc : 0 < c)
    (hmono : ∀ᵐ x ∂μ, ∀ z w,
      c * ‖z - w‖ ^ (p : ℝ) ≤ inner ℝ (a x z - a x w) (z - w)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ℓ₁ ℓ₂ : StrongDual ℝ V) (u v : V),
      (∀ z : V, (∫ x, inner ℝ (a x (∇ (u : W^{1,p}(Ω)) x)) (∇ (z : W^{1,p}(Ω)) x) ∂μ) = ℓ₁ z) →
      (∀ z : V, (∫ x, inner ℝ (a x (∇ (v : W^{1,p}(Ω)) x)) (∇ (z : W^{1,p}(Ω)) x) ∂μ) = ℓ₂ z) →
      ‖u - v‖ ^ ((p : ℝ) - 1) ≤ K * ‖ℓ₁ - ℓ₂‖ := by
  -- Cache the inherited normed structure and its projection for dual-norm estimates.
  let : NormedAddCommGroup V := inferInstance
  let : SeminormedAddCommGroup V :=
    (inferInstance : NormedAddCommGroup V).toSeminormedAddCommGroup
  let : NormedSpace ℝ V := inferInstance
  let D : V →L[ℝ] Lp (ℝ^n) p μ :=
    (wkpGradientCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)).comp
      (wkp0SubmoduleOn (n := n) (k := 1)
        (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule.subtypeL
  have hp1 : 1 < p := one_lt_two.trans_le hp
  obtain ⟨C₀, hP⟩ := exists_norm_le_wkpGradientCLM hn hΩ hp1.le
  let s : ℝ := C₀ + 1
  have hs : 0 < s := by dsimp [s]; positivity
  have hden : 0 < s ^ (p : ℝ) := Real.rpow_pos_of_pos hs _
  let k : ℝ := c / s ^ (p : ℝ)
  have hk : 0 < k := div_pos hc hden
  have hpR : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp1)
  refine ⟨k⁻¹, inv_pos.mpr hk, fun ℓ₁ ℓ₂ u v hu hv ↦ ?_⟩
  have hnorm : ‖u - v‖ ≤ s * ‖D (u - v)‖ :=
    (hP (u - v)).trans (mul_le_mul_of_nonneg_right (by dsimp [s]; linarith) (norm_nonneg _))
  have hpow : ‖u - v‖ ^ (p : ℝ) ≤
      s ^ (p : ℝ) * ‖D (u - v)‖ ^ (p : ℝ) := by
    simpa only [Real.mul_rpow hs.le (norm_nonneg (D (u - v)))] using
      Real.rpow_le_rpow (norm_nonneg (u - v)) hnorm p.coe_nonneg
  have hscaled : k * ‖u - v‖ ^ (p : ℝ) ≤ c * ‖D (u - v)‖ ^ (p : ℝ) :=
    (mul_le_mul_of_nonneg_left hpow hk.le).trans_eq
      (by dsimp [k]; rw [← mul_assoc, div_mul_cancel₀ _ hden.ne'])
  have hlower := PDE.Analysis.Operator.pGrowthFluxOperator_sub_lower_bound (X := V)
    D ENNReal.coe_ne_top a hmeas hh hgrowth hmono u v
  have happ := PDE.Analysis.Operator.pGrowthFluxOperator_apply (X := V)
    D ENNReal.coe_ne_top a hmeas hh hgrowth
  rw [sub_apply, happ u (u - v), happ v (u - v)] at hlower
  change c * ‖D (u - v)‖ ^ (p : ℝ) ≤
    (∫ x, inner ℝ (a x (∇ (u : W^{1,p}(Ω)) x)) (∇ ((u - v : V) : W^{1,p}(Ω)) x) ∂μ) -
      (∫ x, inner ℝ (a x (∇ (v : W^{1,p}(Ω)) x)) (∇ ((u - v : V) : W^{1,p}(Ω)) x) ∂μ) at hlower
  rw [hu (u - v), hv (u - v)] at hlower
  have hdual : ℓ₁ (u - v) - ℓ₂ (u - v) ≤ ‖ℓ₁ - ℓ₂‖ * ‖u - v‖ := by
    calc
      _ ≤ |ℓ₁ (u - v) - ℓ₂ (u - v)| := le_abs_self _
      _ = ‖(ℓ₁ - ℓ₂) (u - v)‖ := by rw [sub_apply, Real.norm_eq_abs]
      _ ≤ _ := ContinuousLinearMap.le_opNorm (ℓ₁ - ℓ₂) (u - v)
  have hbound := hscaled.trans (hlower.trans hdual)
  by_cases heq : u = v
  · rw [norm_sub_eq_zero_iff.mpr heq, Real.zero_rpow hpR.ne']
    exact mul_nonneg (inv_nonneg.mpr hk.le) (norm_nonneg (ℓ₁ - ℓ₂))
  · have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
    have hcancel : k * ‖u - v‖ ^ ((p : ℝ) - 1) ≤ ‖ℓ₁ - ℓ₂‖ := by
      apply (mul_le_mul_iff_left₀ hd).mp
      rw [mul_assoc, Real.rpow_sub_one hd.ne', div_mul_cancel₀ _ hd.ne']
      exact hbound
    calc
      _ ≤ ‖ℓ₁ - ℓ₂‖ / k := (le_div_iff₀ hk).mpr (by simpa [mul_comm] using hcancel)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]; rfl

end SobolevSpace.GraphSpace
