/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ScalarPartials
public import PDE.CalculusOfVariations.EulerLagrange

/-!
# Euler–Lagrange equations from the two density derivatives

For a density `F(x,s,z)`, let `A` be its derivative in the value variable and `D` its
gradient in the gradient variable. If these partial derivatives are jointly continuous
in `(s,z)`, Mathlib's product differentiation theorem gives the full derivative
`(r,w) ↦ A r + ⟨D,w⟩`. Conjugate power growth then gives the weak equation
`∫ (A v + ⟨D,∇v⟩) = 0` at a finite extended-energy minimum.

The argument derives the derivative of the integral through the first-variation theorem.
No integrability or upper growth of the unshifted density is assumed. The boundary class
is the closure of the supported smooth core; on open sets it is `W¹ᵖ₀`. The conclusion is the
weak Euler–Lagrange equation of Evans, §8.2.3, Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.3, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal Topology

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p)
local notation "S" => wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)

/-- A finite minimum satisfies the weak equation `-div D + A = 0` when `A` and `D`
are the value and gradient derivatives of the density. Their joint continuity
in the two state variables supplies the full derivative, and conjugate power growth
makes its action on every zero-boundary Sobolev variation integrable.

Each a.e. hypothesis holds simultaneously for every state. The endpoint `p = 1, q = ∞`
is included. The measurable shift `b` need not be integrable; only the shifted energy
at the minimizer must be finite. No convexity or coercivity is required. -/
theorem integral_eulerLagrange_eq_zero_of_mixedWkpLIntegral_minimizer
    (hp_top : p ≠ ∞)
    {F A : ℝ^n → ℝ × ℝ^n → ℝ} {D : ℝ^n → ℝ × ℝ^n → ℝ^n}
    {b h : ℝ^n → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hA : Measurable (Function.uncurry A))
    (hD : Measurable (Function.uncurry D)) (hb : Measurable b)
    (hvalue : ∀ᵐ x ∂μ, ∀ (s : ℝ) (z : ℝ^n),
      HasDerivAt (fun t : ℝ ↦ F x (t, z)) (A x (s, z)) s)
    (hgradient : ∀ᵐ x ∂μ, ∀ (s : ℝ) (z : ℝ^n),
      HasFDerivAt (fun y : ℝ^n ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z)
    (hAcont : ∀ᵐ x ∂μ, Continuous (A x))
    (hDcont : ∀ᵐ x ∂μ, Continuous (D x))
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z,
      |A x z| + ‖D x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hlower : ∀ᵐ x ∂μ, ∀ z, -b x ≤ F x z)
    (g u : W^{1,p}(Ω)) (hu : u - g ∈ S)
    (hfinite : (∫⁻ x, ENNReal.ofReal (F x (B u x, ∇ u x) + b x) ∂μ) ≠ ∞)
    (hmin : ∀ w : W^{1,p}(Ω), w - g ∈ S →
      (∫⁻ x, ENNReal.ofReal (F x (B u x, ∇ u x) + b x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (F x (B w x, ∇ w x) + b x) ∂μ)
    (v : W^{1,p}(Ω)) (hv : v ∈ S) :
    Integrable (fun x ↦
      A x (B u x, ∇ u x) * B v x + inner ℝ (D x (B u x, ∇ u x)) (∇ v x)) μ ∧
      (∫ x, A x (B u x, ∇ u x) * B v x +
        inner ℝ (D x (B u x, ∇ u x)) (∇ v x) ∂μ) = 0 := by
  let dF (x : ℝ^n) (z : ℝ × ℝ^n) : (ℝ × ℝ^n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ (A x z)).coprod (innerSL ℝ (D x z))
  have happly (x : ℝ^n) (z w : ℝ × ℝ^n) :
      dF x z w = A x z * w.1 + inner ℝ (D x z) w.2 := by
    simp only [dF, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, innerSL_apply_apply, mul_comm]
  have hfull : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z := by
    filter_upwards [hvalue, hgradient, hAcont, hDcont] with x hvx hgx hAx hDx
    intro z
    exact PDE.Analysis.hasFDerivAt_of_continuous_scalar_partials hvx hgx hAx hDx z
  have hmeas : Measurable (fun z : (ℝ^n) × (ℝ × ℝ^n) × (ℝ × ℝ^n) ↦
      dF z.1 z.2.1 z.2.2) := by
    have hstate : Measurable
        (fun z : (ℝ^n) × (ℝ × ℝ^n) × (ℝ × ℝ^n) ↦ (z.1, z.2.1)) :=
      measurable_fst.prodMk measurable_snd.fst
    exact PDE.Analysis.measurable_toSpanSingleton_coprod_innerSL_apply
      (hA.comp hstate) (hD.comp hstate) measurable_snd.snd.fst measurable_snd.snd.snd
  have hnorm (x : ℝ^n) (z : ℝ × ℝ^n) : ‖dF x z‖ ≤ |A x z| + ‖D x z‖ :=
    PDE.Analysis.norm_toSpanSingleton_coprod_innerSL_le (A x z) (D x z)
  have hbound : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1) := by
    filter_upwards [hgrowth] with x hx
    intro z
    exact (hnorm x z).trans (hx z)
  simpa only [happly] using
    integral_firstVariation_eq_zero_of_mixedWkpLIntegral_minimizer
      (p := p) (q := q) hp_top hF hb hmeas hfull hh hbound hlower
      g u hu hfinite hmin v hv

end PDE.CalculusOfVariations
