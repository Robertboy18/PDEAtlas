/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FiniteExponent

/-!
# Prescribed Sobolev boundary values for convex gradient energies

Writing `u = g + w`, with `w ∈ W¹ᵖ₀`, turns the prescribed-boundary problem
into a zero-boundary problem with density `F(x, Dg(x) + z)`. Its power-growth
bounds follow from Mathlib's inequality for the power of a sum. The new
offsets contain `|Dg|ᵖ`, which is integrable because `g ∈ W¹ᵖ`.

The boundary condition is `u - g ∈ W¹ᵖ₀`, expressed using the supported-core
closure. No boundary trace theorem or boundary regularity is assumed.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev ENNReal NNReal

namespace PDE.CalculusOfVariations

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0}
  [Fact (1 ≤ (p : ℝ≥0∞))]

local notation "μ" => domainMeasure n Ω
local notation "V" => W₀^{1,p}(Ω)

/-- The power mean inequality controls translation of a gradient, with the
factor `2^(r-1)` for exponents at least one. -/
private theorem norm_add_rpow_le_of_one_le {r : ℝ} (hr : 1 ≤ r) (q z : ℝ^n) :
    ‖q + z‖ ^ r ≤ (2 : ℝ) ^ (r - 1) * (‖q‖ ^ r + ‖z‖ ^ r) := by
  have hsum : (‖q‖ + ‖z‖) ^ r ≤ (2 : ℝ) ^ (r - 1) * (‖q‖ ^ r + ‖z‖ ^ r) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖q‖₊ ‖z‖₊ hr
  exact (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le q z)
    (zero_le_one.trans hr)).trans hsum

/-- The weak gradient is linear. Its chosen `Lp` representatives agree
almost everywhere, which is enough to identify the two energy integrals. -/
private theorem integral_gradient_add_wkp0
    (F : ℝ^n → ℝ^n → ℝ) (g : W^{1,p}(Ω)) (w : V) :
    (∫ x, F x (∇ (g + (w : W^{1,p}(Ω))) x) ∂μ) =
      ∫ x, F x (∇ g x + ∇ (w : W^{1,p}(Ω)) x) ∂μ := by
  rw [map_add]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (∇ g) (∇ (w : W^{1,p}(Ω)))] with x hx
  exact congrArg (F x) hx

/-- A convex gradient density with two-sided `p` growth has a minimizer for
every prescribed Sobolev boundary value, when `1 < p < ∞`. Admissibility is
the condition `u - g ∈ W¹ᵖ₀`; the given field `g` itself makes this class
nonempty. The bounded domain needs no boundary regularity. -/
theorem exists_minimizer_wkpGradientIntegral_prescribed_boundary
    (hp : 1 < p) (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    {F : ℝ^n → ℝ^n → ℝ} {a b : ℝ^n → ℝ} {c C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ F x z)
    (hupper : ∀ᵐ x ∂μ, ∀ z, F x z ≤ a x + C * ‖z‖ ^ (p : ℝ))
    (g : W^{1,p}(Ω)) :
    ∃ u : W^{1,p}(Ω),
      u - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) ∧
      ∀ v : W^{1,p}(Ω),
        v - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) →
          (∫ x, F x (∇ u x) ∂μ) ≤
            ∫ x, F x (∇ v x) ∂μ := by
  let q := ∇ g
  let Fg (x z : ℝ^n) := F x (q x + z)
  let K : ℝ := 2 ^ ((p : ℝ) - 1)
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp.le
  have hp0 : (p : ℝ≥0∞) ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : 1 ≤ (p : ℝ≥0∞))).ne'
  have hqint : Integrable (fun x ↦ ‖q x‖ ^ (p : ℝ)) μ := by
    simpa only [ENNReal.coe_toReal] using
      (Lp.memLp q).integrable_norm_rpow hp0 ENNReal.coe_ne_top
  have hq : Measurable (fun x ↦ q x) := (Lp.stronglyMeasurable q).measurable
  have hFg : Measurable (Function.uncurry Fg) :=
    hF.comp (measurable_fst.prodMk ((hq.comp measurable_fst).add measurable_snd))
  have hFgconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (Fg x) := by
    filter_upwards [hconvex] with x hx
    simpa only [preimage_univ, Function.comp_def, Fg] using hx.translate_right (q x)
  have hGlower : ∀ᵐ x ∂μ, ∀ z,
      (c / K) * ‖z‖ ^ (p : ℝ) - (b x + c * ‖q x‖ ^ (p : ℝ)) ≤ Fg x z := by
    filter_upwards [hlower] with x hx
    intro z
    have hsum := norm_add_rpow_le_of_one_le hpR (q x + z) (-q x)
    have heq : q x + z + -q x = z := by
      simp [add_comm (q x) z, add_assoc]
    rw [heq, norm_neg] at hsum
    have hscaled : (c / K) * ‖z‖ ^ (p : ℝ) ≤
        c * (‖q x + z‖ ^ (p : ℝ) + ‖q x‖ ^ (p : ℝ)) := by
      calc
        _ ≤ (c / K) * (K * (‖q x + z‖ ^ (p : ℝ) + ‖q x‖ ^ (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum (div_nonneg hc.le hK.le)
        _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hK.ne']
    dsimp only [Fg]
    linarith [hx (q x + z)]
  have hGupper : ∀ᵐ x ∂μ, ∀ z,
      Fg x z ≤ (a x + (C * K) * ‖q x‖ ^ (p : ℝ)) +
        (C * K) * ‖z‖ ^ (p : ℝ) := by
    filter_upwards [hupper] with x hx
    intro z
    have hscaled := mul_le_mul_of_nonneg_left
      (norm_add_rpow_le_of_one_le hpR (q x) z) hC
    dsimp only [Fg]
    nlinarith [hx (q x + z)]
  obtain ⟨w, hw⟩ := exists_minimizer_wkpGradientIntegral hp hn hΩ hFg hFgconvex
    (ha.add (hqint.const_mul (C * K))) (hb.add (hqint.const_mul c))
    (div_pos hc hK) (mul_nonneg hC hK.le) hGlower hGupper
  refine ⟨g + (w : W^{1,p}(Ω)), ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact w.property
  · intro v hv
    let z : V := ⟨v - g, hv⟩
    have hv' : g + (z : W^{1,p}(Ω)) = v := by
      change g + (v - g) = v
      rw [add_comm, sub_add_cancel]
    rw [integral_gradient_add_wkp0, ← hv', integral_gradient_add_wkp0]
    exact hw z

end PDE.CalculusOfVariations
