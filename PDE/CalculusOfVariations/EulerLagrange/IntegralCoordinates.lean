/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ScalarPartials
public import PDE.Analysis.Normed.Operator.PowerGrowth
public import PDE.CalculusOfVariations.EulerLagrange.Integral

/-!
# Coordinate Euler–Lagrange equations for ordinary integral minima

The value and gradient coefficients are the partial derivatives of the density.
Their separate power bounds imply the operator bound needed to differentiate the
ordinary integral. Density growth supplies integrability at every Sobolev field.

The result is the necessary condition of Evans, §8.2.3, Theorem 4, in the coordinates of his
weak formulation (37): `∫ L_p(Du, u, x) · Dv + L_z(Du, u, x) v dx = 0`.
The domain has finite measure.
The affine class uses the closure-defined zero-boundary Sobolev space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.3, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped Sobolev ENNReal

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)
local notation "S" => wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)

include q

/-- An ordinary energy minimum satisfies the scalar weak Euler–Lagrange equation
with its value and gradient partial derivatives. The three growth assumptions are the
separate density, value-derivative and gradient-derivative bounds. -/
theorem integral_eulerLagrange_eq_zero_of_mixedWkpIntegral_minimizer
    [IsFiniteMeasure μ] (hp_top : p ≠ ∞)
    {F A : ℝ^n → ℝ × ℝ^n → ℝ} {D : ℝ^n → ℝ × ℝ^n → ℝ^n}
    {C : ℝ} (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F))
    (hA : Measurable (Function.uncurry A))
    (hD : Measurable (Function.uncurry D))
    (hvalue : ∀ᵐ x ∂μ, ∀ s z, HasDerivAt (fun t ↦ F x (t, z)) (A x (s, z)) s)
    (hgradient : ∀ᵐ x ∂μ, ∀ s z,
      HasFDerivAt (fun y ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z)
    (hAcont : ∀ᵐ x ∂μ, Continuous (A x))
    (hDcont : ∀ᵐ x ∂μ, Continuous (D x))
    (hupper : ∀ᵐ x ∂μ, ∀ z,
      ‖F x z‖ ≤ C * (‖z.1‖ ^ p.toReal + ‖z.2‖ ^ p.toReal + 1))
    (hAgrowth : ∀ᵐ x ∂μ, ∀ z,
      |A x z| ≤ C * (‖z.1‖ ^ (p.toReal - 1) + ‖z.2‖ ^ (p.toReal - 1) + 1))
    (hDgrowth : ∀ᵐ x ∂μ, ∀ z,
      ‖D x z‖ ≤ C * (‖z.1‖ ^ (p.toReal - 1) + ‖z.2‖ ^ (p.toReal - 1) + 1))
    (g u : W^{1,p}(Ω)) (hu : u - g ∈ S)
    (hmin : ∀ w : W^{1,p}(Ω), w - g ∈ S →
      (∫ x, F x (B u x, ∇ u x) ∂μ) ≤ ∫ x, F x (B w x, ∇ w x) ∂μ)
    (v : W^{1,p}(Ω)) (hv : v ∈ S) :
    Integrable (fun x ↦
      (∑ i, D x (B u x, ∇ u x) i * ∇ v x i) + A x (B u x, ∇ u x) * B v x) μ ∧
      (∫ x, (∑ i, D x (B u x, ∇ u x) i * ∇ v x i) +
        A x (B u x, ∇ u x) * B v x ∂μ) = 0 := by
  let dF (x : ℝ^n) (z : ℝ × ℝ^n) :=
    (ContinuousLinearMap.toSpanSingleton ℝ (A x z)).coprod (innerSL ℝ (D x z))
  have happly (x : ℝ^n) (z w : ℝ × ℝ^n) :
      dF x z w = (∑ i, D x z i * w.2 i) + A x z * w.1 := by
    simp only [dF, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, innerSL_apply_apply,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm, add_comm]
  let T₀ := ContinuousLinearMap.fst ℝ ℝ (ℝ^n)
  let T₁ := ContinuousLinearMap.snd ℝ ℝ (ℝ^n)
  let K (r : ℝ) := C * (‖T₀‖ ^ r + ‖T₁‖ ^ r)
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top (ENNReal.HolderConjugate.one_le p q)
  have hbound (r : ℝ) (hr : 0 ≤ r) (z : ℝ × ℝ^n) :
      C * (‖z.1‖ ^ r + ‖z.2‖ ^ r + 1) ≤ C + K r * ‖z‖ ^ r :=
    T₀.mul_add_norm_rpow_le T₁ hr hC z
  have hfull : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z := by
    filter_upwards [hvalue, hgradient, hAcont, hDcont] with x hvx hgx hAx hDx
    exact hasFDerivAt_of_continuous_scalar_partials hvx hgx hAx hDx
  have hmeas : Measurable (fun z : (ℝ^n) × (ℝ × ℝ^n) × (ℝ × ℝ^n) ↦
      dF z.1 z.2.1 z.2.2) := by
    have hs : Measurable
        (fun z : (ℝ^n) × (ℝ × ℝ^n) × (ℝ × ℝ^n) ↦ (z.1, z.2.1)) :=
      measurable_fst.prodMk measurable_snd.fst
    exact measurable_toSpanSingleton_coprod_innerSL_apply
      (hA.comp hs) (hD.comp hs) measurable_snd.snd.fst measurable_snd.snd.snd
  have hupper' : ∀ᵐ x ∂μ, ∀ z, ‖F x z‖ ≤ C + K p.toReal * ‖z‖ ^ p.toReal :=
    hupper.mono fun x hx z ↦ (hx z).trans (hbound _ ENNReal.toReal_nonneg z)
  have hgrowth : ∀ᵐ x ∂μ, ∀ z,
      ‖dF x z‖ ≤ 2 * C + (2 * K (p.toReal - 1)) * ‖z‖ ^ (p.toReal - 1) := by
    filter_upwards [hAgrowth, hDgrowth] with x hAx hDx
    intro z
    have h := hbound (p.toReal - 1) (sub_nonneg.mpr hp1) z
    have hn := norm_toSpanSingleton_coprod_innerSL_le (A x z) (D x z)
    change ‖dF x z‖ ≤ _ at hn
    linarith [hAx z, hDx z]
  have h := integral_firstVariation_eq_zero_of_mixedWkpIntegral_minimizer
    (p := p) (q := q) hp_top hF hmeas hfull (integrable_const C) hupper'
    (memLp_const (2 * C)) hgrowth g u hu hmin v hv
  simpa only [happly] using h

end PDE.CalculusOfVariations
