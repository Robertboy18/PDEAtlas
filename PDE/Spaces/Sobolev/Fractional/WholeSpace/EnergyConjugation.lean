/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Energy

/-!
# The Sobolev energy of a complex function and of its real and imaginary parts

For real `f` and `g` in `L²(ℝⁿ; ℂ)` and every real order `σ`, `E_σ(f + i g) = E_σ(f) + E_σ(g)`,
with both sides possibly infinite. So an operator with real coefficients has the same bound on
complex functions as on real ones, and the complexification of a real Sobolev space carries the
complex Bessel norm. In particular, an energy of complex vector fields defined through the real
and imaginary parts is the Bessel energy of the complex field.

## Main results

* `besselEnergy_star`: `E_σ(conj g) = E_σ(g)` for every real `σ` and every `g ∈ L²(ℝⁿ; ℂ)`.
* `besselEnergy_add_I_smul`: `E_σ(f + i g) = E_σ(f) + E_σ(g)` for every real `σ` and all real `f`,
  `g` in `L²(ℝⁿ; ℂ)`.

## How it works

The transform of `conj g` is the reflected conjugate of `ĝ` (`fourier_star`), and the weight
`(1 + |ξ|²)^σ` is even, so conjugation does not change the energy. For real `f` and `g` the
conjugate of `f + i g` is `f - i g`, and the parallelogram law
`besselEnergy_add_add_besselEnergy_sub` then gives `2 E_σ(f + i g) = 2 (E_σ(f) + E_σ(g))`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal ComplexConjugate

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-- The weight is even. -/
theorem besselWeight_neg (σ : ℝ) (ξ : ℝ^n) : besselWeight n σ (-ξ) = besselWeight n σ ξ := by
  rw [besselWeight, besselWeight, norm_neg]

/-- **The energy is invariant under complex conjugation**: `E_σ(conj g) = E_σ(g)` for every
real `σ` and every `g ∈ L²(ℝⁿ; ℂ)`. The transform of the conjugate is the reflected conjugate of
the transform, and the weight is even. -/
theorem besselEnergy_star (σ : ℝ) (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (fun _ : Unit ↦ star g) = besselEnergy σ (fun _ : Unit ↦ g) := by
  have hF : ∀ᵐ ξ : ℝ^n, ‖(𝓕 (star g) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 =
      ‖(𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) (-ξ)‖ₑ ^ 2 := by
    rw [fourier_star]
    filter_upwards [coeFn_reflL2 (star (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n)))),
      ae_neg (Lp.coeFn_star (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))))] with ξ h1 h2
    rw [h1, h2, Pi.star_apply, ← ofReal_norm, norm_star, ofReal_norm]
  have hmeas : Measurable fun ξ : ℝ^n ↦ (besselWeight n σ ξ : ℝ≥0∞) *
      ‖(𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 :=
    (measurable_coe_nnreal_ennreal.comp (measurable_besselWeight σ)).mul
      ((Lp.stronglyMeasurable _).eNorm.pow_const 2)
  rw [besselEnergy_unit_eq_lintegral, besselEnergy_unit_eq_lintegral,
    ← (Measure.measurePreserving_neg (volume : Measure (ℝ^n))).lintegral_comp hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [hF] with ξ hξ
  rw [hξ, besselWeight_neg]

/-- **The energy of a complex function is the sum of the energies of its real and imaginary
parts**: for real `f`, `g` in `L²(ℝⁿ; ℂ)` and every real `σ`,
`E_σ(f + i g) = E_σ(f) + E_σ(g)`. Both sides may be infinite. -/
theorem besselEnergy_add_I_smul (σ : ℝ) {f g : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hf : IsRealL2 f) (hg : IsRealL2 g) :
    besselEnergy σ (fun _ : Unit ↦ f + Complex.I • g) =
      besselEnergy σ (fun _ : Unit ↦ f) + besselEnergy σ (fun _ : Unit ↦ g) := by
  -- the conjugate of `f + i g`
  have hstar : star (f + Complex.I • g) = f - Complex.I • g := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_star (f + Complex.I • g), Lp.coeFn_add f (Complex.I • g),
      Lp.coeFn_smul Complex.I g, Lp.coeFn_sub f (Complex.I • g), hf, hg] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.star_apply, h2, h4, Pi.add_apply, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul,
      RCLike.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_eq_iff_im.2 h5,
      Complex.conj_eq_iff_im.2 h6]
    ring
  have h1 := besselEnergy_star σ (f + Complex.I • g)
  rw [hstar] at h1
  -- the parallelogram law
  have h2 := besselEnergy_add_add_besselEnergy_sub σ (fun _ : Unit ↦ f)
    (fun _ : Unit ↦ Complex.I • g)
  have h3 : besselEnergy σ (fun _ : Unit ↦ Complex.I • g) = besselEnergy σ (fun _ : Unit ↦ g) := by
    have h := besselEnergy_smul σ Complex.I (fun _ : Unit ↦ g)
    rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one, one_pow, one_mul] at h
    exact h
  have h4 : besselEnergy σ (fun _ : Unit ↦ f + Complex.I • g) +
      besselEnergy σ (fun _ : Unit ↦ f + Complex.I • g) =
      2 * (besselEnergy σ (fun _ : Unit ↦ f) + besselEnergy σ (fun _ : Unit ↦ g)) := by
    rw [← h3, ← h2]
    congr 1
    exact h1.symm
  rw [← two_mul] at h4
  exact le_antisymm
    ((ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp h4.le)
    ((ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp h4.ge)

end SobolevSpace.Fractional
