/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.LpSpace
public import PDE.Analysis.Fourier.SchwartzDifferentialOperators

/-!
# The Hilbert transform on `L²(ℝ)`

The Hilbert transform `H f(x) = (1/π) p.v. ∫ f(y)/(x - y) dy` is the Fourier multiplier
with symbol `-i sgn ξ`: `𝓕(H f)(ξ) = -i sgn(ξ) 𝓕f(ξ)`. On `L²(ℝ)` we take the multiplier as
the definition. The symbol is unimodular off the origin, so by Plancherel `H` is a linear
isometry of `L²` that satisfies `H² = -I` and is skew-adjoint. The value of the symbol at
`ξ = 0` is immaterial in `L²` and is set to zero.
`hilbertPV_eq_hilbertTransform_ae_of_ae_differentiableAt` identifies this operator almost
everywhere with the principal-value integral for real `L¹ ∩ L²` functions that are
differentiable almost everywhere.

Multiplication by `hilbertSymbol` is an isometry of `L²(ℝ; ℂ)` squaring to minus the
identity. Conjugating by Mathlib's unitary `L²` Fourier transform gives `hilbertTransform`
with the same properties. Moreover `H` preserves the natural `L²` domain of the derivative
`d/dx`, defined on the Fourier side by the condition `ξ 𝓕f ∈ L²`, and commutes with the
derivative there. Both facts are immediate on the Fourier side, where `H` and `d/dx` are
multiplication operators.

## Main results

* `hilbertSymbol`: the function `-i sgn ξ`, with `hilbertSymbol_of_neg`,
  `hilbertSymbol_of_pos`, `norm_hilbertSymbol_of_ne_zero`, `hilbertSymbol_sq_of_ne_zero`.
* `hilbertMultiplier`: multiplication by the symbol as a linear isometry of `ComplexL2`,
  with `coe_hilbertMultiplier` and `hilbertMultiplier_sq`.
* `hilbertTransform`: the Hilbert transform `𝓕⁻¹ ∘ hilbertMultiplier ∘ 𝓕`, with
  `fourier_hilbertTransform`, `hilbertTransform_sq`, `norm_hilbertTransform`,
  `inner_hilbertTransform`, and the skew-adjointness `inner_hilbertTransform_left`.
* `fourierDerivativeDomain`, `fourierDerivative`: the derivative on `L²(ℝ)` as a partial
  linear map with its natural domain, realized through the multiplier
  `Fourier.fourierDerivativeSymbol1D`.
* `hilbertTransform_mem_fourierDerivativeDomain`,
  `hilbertTransformOnFourierDerivativeDomain`, `fourierDerivative_hilbertTransform`:
  `H` preserves the derivative domain and commutes with `d/dx` on it.

## Implementation notes

`ComplexL2` abbreviates `Lp ℂ 2 volume` on `ℝ`. All operators are constructed on the
Fourier side and transported by the `L²` Fourier transform. The principal-value identification
is proved in `hilbertPV_eq_hilbertTransform_ae_of_ae_differentiableAt` in
`HilbertTransform.SpectralL2`; this keeps the construction independent of its integral
representation.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics, Springer,
  2014, Chapter 5 (Singular Integrals of Convolution Type), pp. 313-417.
  <https://doi.org/10.1007/978-1-4939-1194-3_5>
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  Mathematical Series 32, Princeton University Press, 1971.
  <https://doi.org/10.1515/9781400883899>
-/

@[expose] public section

namespace PDE.Analysis

open FourierTransform MeasureTheory
open scoped FourierTransform InnerProductSpace

noncomputable section

/-- Complex-valued square-integrable functions on the real line. -/
abbrev ComplexL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Fourier multiplier of the Hilbert transform, with the conventional value zero at frequency
zero. -/
def hilbertSymbol (ξ : ℝ) : ℂ :=
  if ξ < 0 then Complex.I else if 0 < ξ then -Complex.I else 0

/-- The Hilbert symbol is measurable, being piecewise constant on `(-∞, 0)`, `{0}`, `(0, ∞)`. -/
theorem measurable_hilbertSymbol : Measurable hilbertSymbol := by
  unfold hilbertSymbol
  apply Measurable.ite measurableSet_Iio measurable_const
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

/-- The symbol is normalized to vanish at frequency zero. -/
@[simp]
theorem hilbertSymbol_zero : hilbertSymbol 0 = 0 := by
  simp [hilbertSymbol]

/-- On negative frequencies the symbol `-i sgn ξ` equals `i`. -/
theorem hilbertSymbol_of_neg {ξ : ℝ} (hξ : ξ < 0) :
    hilbertSymbol ξ = Complex.I := by
  simp [hilbertSymbol, hξ]

/-- On positive frequencies the symbol `-i sgn ξ` equals `-i`. -/
theorem hilbertSymbol_of_pos {ξ : ℝ} (hξ : 0 < ξ) :
    hilbertSymbol ξ = -Complex.I := by
  simp [hilbertSymbol, hξ, not_lt_of_ge hξ.le]

/-- The symbol is bounded by one everywhere, including at the origin; this is what makes the
multiplier a contraction on `L²` before the isometry is established. -/
theorem norm_hilbertSymbol_le_one (ξ : ℝ) : ‖hilbertSymbol ξ‖ ≤ 1 := by
  rcases lt_trichotomy ξ 0 with hξ | hξ | hξ
  · simp [hilbertSymbol_of_neg hξ]
  · subst ξ
    simp
  · simp [hilbertSymbol_of_pos hξ]

/-- Off the origin the symbol is unimodular, which by Plancherel makes the Hilbert transform
an isometry of `L²`. -/
theorem norm_hilbertSymbol_of_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖hilbertSymbol ξ‖ = 1 := by
  rcases hξ.lt_or_gt with hξ | hξ
  · simp [hilbertSymbol_of_neg hξ]
  · simp [hilbertSymbol_of_pos hξ]

/-- Off the origin the symbol squares to `-1`, since `(∓i)² = -1`; this is the Fourier-side
form of `H² = -I`. -/
theorem hilbertSymbol_sq_of_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) :
    hilbertSymbol ξ * hilbertSymbol ξ = -1 := by
  rcases hξ.lt_or_gt with hξ | hξ
  · rw [hilbertSymbol_of_neg hξ]
    norm_num
  · rw [hilbertSymbol_of_pos hξ]
    norm_num

/-- Multiplication by the Hilbert symbol preserves membership in `L²`. -/
theorem hilbertMultiplier_memLp (f : ComplexL2) :
    MemLp (fun ξ ↦ hilbertSymbol ξ * f ξ) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).of_le_mul
  · exact measurable_hilbertSymbol.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · filter_upwards with ξ
    rw [norm_mul, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_hilbertSymbol_le_one ξ)

/-- The Fourier-side Hilbert multiplier on complex `L²(ℝ)`. -/
def hilbertMultiplierLinearMap : ComplexL2 →ₗ[ℂ] ComplexL2 where
  toFun f :=
    (hilbertMultiplier_memLp f).toLp (fun ξ ↦ hilbertSymbol ξ * f ξ)
  map_add' f g := by
    apply Lp.ext
    filter_upwards
      [(hilbertMultiplier_memLp (f + g)).coeFn_toLp,
        Lp.coeFn_add f g,
        Lp.coeFn_add
          ((hilbertMultiplier_memLp f).toLp (fun ξ ↦ hilbertSymbol ξ * f ξ))
          ((hilbertMultiplier_memLp g).toLp (fun ξ ↦ hilbertSymbol ξ * g ξ)),
        (hilbertMultiplier_memLp f).coeFn_toLp,
        (hilbertMultiplier_memLp g).coeFn_toLp] with ξ hfg hfg' hadd hf hg
    simp only [Pi.add_apply] at hfg' hadd
    rw [hfg, hfg', hadd, hf, hg]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards
      [(hilbertMultiplier_memLp (c • f)).coeFn_toLp,
        Lp.coeFn_smul c f,
        Lp.coeFn_smul c
          ((hilbertMultiplier_memLp f).toLp (fun ξ ↦ hilbertSymbol ξ * f ξ)),
        (hilbertMultiplier_memLp f).coeFn_toLp] with ξ hcf hcf' hsmul hf
    simp only [Pi.smul_apply] at hcf' hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hcf', hsmul, hf]
    simp only [smul_eq_mul]
    ring

private theorem coe_hilbertMultiplierLinearMap (f : ComplexL2) :
    hilbertMultiplierLinearMap f =ᵐ[volume] fun ξ ↦ hilbertSymbol ξ * f ξ :=
  (hilbertMultiplier_memLp f).coeFn_toLp

/-- The Fourier-side Hilbert multiplier preserves the `L²` norm. -/
theorem norm_hilbertMultiplierLinearMap (f : ComplexL2) :
    ‖hilbertMultiplierLinearMap f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
    (Lp.aestronglyMeasurable (hilbertMultiplierLinearMap f)) (Lp.aestronglyMeasurable f)
  filter_upwards
    [coe_hilbertMultiplierLinearMap f, (volume : Measure ℝ).ae_ne 0] with ξ hmult hξ
  rw [hmult, norm_mul, norm_hilbertSymbol_of_ne_zero hξ, one_mul]

/-- Multiplication by `-i sign ξ` is a linear isometry on complex `L²(ℝ)`. -/
def hilbertMultiplier : ComplexL2 →ₗᵢ[ℂ] ComplexL2 where
  toLinearMap := hilbertMultiplierLinearMap
  norm_map' := norm_hilbertMultiplierLinearMap

/-- The Fourier-side map acts almost everywhere by multiplication with `hilbertSymbol`. -/
theorem coe_hilbertMultiplier (f : ComplexL2) :
    hilbertMultiplier f =ᵐ[volume] fun ξ ↦ hilbertSymbol ξ * f ξ :=
  coe_hilbertMultiplierLinearMap f

/-- Applying the Fourier-side Hilbert multiplier twice gives minus the original function. -/
theorem hilbertMultiplier_sq (f : ComplexL2) :
    hilbertMultiplier (hilbertMultiplier f) = -f := by
  apply Lp.ext
  filter_upwards
    [coe_hilbertMultiplier (hilbertMultiplier f),
      coe_hilbertMultiplier f,
      Lp.coeFn_neg f,
      (volume : Measure ℝ).ae_ne 0] with ξ houter hinner hneg hξ
  rw [houter, hinner, hneg, ← mul_assoc, hilbertSymbol_sq_of_ne_zero hξ]
  simp

/-- The Hilbert transform on complex `L²(ℝ)`, defined by the Fourier multiplier
`-i sign ξ`. -/
def hilbertTransform : ComplexL2 →ₗᵢ[ℂ] ComplexL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.comp
    (hilbertMultiplier.comp (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearIsometry)

/-- The Hilbert transform is inverse Fourier transformation after applying its multiplier. -/
theorem hilbertTransform_apply (f : ComplexL2) :
    hilbertTransform f = 𝓕⁻ (hilbertMultiplier (𝓕 f)) :=
  rfl

/-- Fourier transformation turns the Hilbert transform into multiplication by its symbol. -/
theorem fourier_hilbertTransform (f : ComplexL2) :
    𝓕 (hilbertTransform f) = hilbertMultiplier (𝓕 f) := by
  rw [hilbertTransform_apply, fourier_fourierInv_eq]

/-- Applying the `L²` Hilbert transform twice gives minus the original function. -/
theorem hilbertTransform_sq (f : ComplexL2) :
    hilbertTransform (hilbertTransform f) = -f := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (hilbertTransform (hilbertTransform f)) = 𝓕 (-f)
  rw [fourier_hilbertTransform, fourier_hilbertTransform,
    hilbertMultiplier_sq, FourierTransform.fourier_neg]

/-- The Hilbert transform preserves the complex `L²` norm. -/
theorem norm_hilbertTransform (f : ComplexL2) :
    ‖hilbertTransform f‖ = ‖f‖ :=
  hilbertTransform.norm_map f

/-- The Hilbert transform preserves the complex `L²` inner product. -/
theorem inner_hilbertTransform (f g : ComplexL2) :
    ⟪hilbertTransform f, hilbertTransform g⟫_ℂ = ⟪f, g⟫_ℂ :=
  hilbertTransform.inner_map_map f g

/-- The `L²` Hilbert transform is skew-adjoint. -/
theorem inner_hilbertTransform_left (f g : ComplexL2) :
    ⟪hilbertTransform f, g⟫_ℂ = -⟪f, hilbertTransform g⟫_ℂ := by
  have h := inner_hilbertTransform f (hilbertTransform g)
  rw [hilbertTransform_sq, inner_neg_right] at h
  apply neg_injective
  simpa using h

/-- Equivalent right-slot form of skew-adjointness. -/
theorem inner_hilbertTransform_right (f g : ComplexL2) :
    ⟪f, hilbertTransform g⟫_ℂ = -⟪hilbertTransform f, g⟫_ℂ := by
  rw [inner_hilbertTransform_left, neg_neg]

/-! ## Commutation with the `L²` derivative -/

/-- Natural `L²` domain of the derivative, characterized by its Fourier multiplier. -/
def fourierDerivativeDomain : Submodule ℂ ComplexL2 where
  carrier := {f |
    MemLp (fun ξ ↦ Fourier.fourierDerivativeSymbol1D ξ * (𝓕 f) ξ) 2 volume}
  zero_mem' := by
    simp
  add_mem' := fun {f g} hf hg ↦ by
    have hadd := hf.add hg
    apply (memLp_congr_ae ?_).mpr hadd
    filter_upwards [Lp.coeFn_add (𝓕 f) (𝓕 g)] with ξ hξ
    rw [FourierTransform.fourier_add, hξ]
    simp only [Pi.add_apply]
    ring
  smul_mem' := fun c f hf ↦ by
    have hsmul := hf.const_smul c
    apply (memLp_congr_ae ?_).mpr hsmul
    filter_upwards [Lp.coeFn_smul c (𝓕 f)] with ξ hξ
    rw [FourierTransform.fourier_smul, hξ]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Membership in the Fourier derivative domain, exposed in its defining form. -/
theorem mem_fourierDerivativeDomain_iff {f : ComplexL2} :
    f ∈ fourierDerivativeDomain ↔
      MemLp
        (fun ξ ↦ Fourier.fourierDerivativeSymbol1D ξ * (𝓕 f) ξ)
        2 volume :=
  Iff.rfl

/-- Fourier-side value of the derivative on its natural domain, as a plain function. -/
def fourierDerivativeSpectrumValue
    (f : fourierDerivativeDomain) : ComplexL2 :=
  (mem_fourierDerivativeDomain_iff.mp f.property).toLp
    (fun ξ ↦
      Fourier.fourierDerivativeSymbol1D ξ *
        (𝓕 (f : ComplexL2)) ξ)

private theorem coe_fourierDerivativeSpectrumValue
    (f : fourierDerivativeDomain) :
    fourierDerivativeSpectrumValue f =ᵐ[volume]
      fun ξ ↦
        Fourier.fourierDerivativeSymbol1D ξ *
          (𝓕 (f : ComplexL2)) ξ :=
  (mem_fourierDerivativeDomain_iff.mp f.property).coeFn_toLp

/-- Fourier-side value of the derivative on its natural domain. -/
def fourierDerivativeSpectrum :
    fourierDerivativeDomain →ₗ[ℂ] ComplexL2 where
  toFun := fourierDerivativeSpectrumValue
  map_add' f g := by
    apply Lp.ext
    filter_upwards
      [coe_fourierDerivativeSpectrumValue (f + g),
        coe_fourierDerivativeSpectrumValue f,
        coe_fourierDerivativeSpectrumValue g,
        Lp.coeFn_add (𝓕 (f : ComplexL2)) (𝓕 (g : ComplexL2)),
        Lp.coeFn_add
          (fourierDerivativeSpectrumValue f) (fourierDerivativeSpectrumValue g)]
      with ξ hfg hf hg hFourier hadd
    rw [hfg]
    change
      Fourier.fourierDerivativeSymbol1D ξ *
          (𝓕 ((f : ComplexL2) + (g : ComplexL2))) ξ =
        (fourierDerivativeSpectrumValue f +
          fourierDerivativeSpectrumValue g) ξ
    rw [FourierTransform.fourier_add, hFourier, hadd]
    simp only [Pi.add_apply]
    rw [hf, hg]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards
      [coe_fourierDerivativeSpectrumValue (c • f),
        coe_fourierDerivativeSpectrumValue f,
        Lp.coeFn_smul c (𝓕 (f : ComplexL2)),
        Lp.coeFn_smul c (fourierDerivativeSpectrumValue f)]
      with ξ hcf hf hFourier hsmul
    simp only [RingHom.id_apply]
    rw [hcf]
    change
      Fourier.fourierDerivativeSymbol1D ξ *
          (𝓕 (c • (f : ComplexL2))) ξ =
        (c • fourierDerivativeSpectrumValue f) ξ
    rw [FourierTransform.fourier_smul, hFourier, hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    ring

private theorem coe_fourierDerivativeSpectrum (f : fourierDerivativeDomain) :
    fourierDerivativeSpectrum f =ᵐ[volume]
      fun ξ ↦
        Fourier.fourierDerivativeSymbol1D ξ *
          (𝓕 (f : ComplexL2)) ξ :=
  coe_fourierDerivativeSpectrumValue f

/-- The Fourier realization of the derivative from its natural domain into `L²(ℝ)`. -/
def fourierDerivativeOnDomain :
    fourierDerivativeDomain →ₗ[ℂ] ComplexL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearEquiv.toLinearMap.comp
    fourierDerivativeSpectrum

/-- The Fourier realization of the derivative as a partial linear map on complex `L²(ℝ)`. -/
def fourierDerivative : ComplexL2 →ₗ.[ℂ] ComplexL2 :=
  LinearPMap.mk fourierDerivativeDomain fourierDerivativeOnDomain

/-- The domain of the Fourier derivative is its defining multiplier domain. -/
@[simp]
theorem fourierDerivative_domain :
    fourierDerivative.domain = fourierDerivativeDomain :=
  rfl

/-- Applying the partial Fourier derivative uses its domain-restricted linear map. -/
theorem fourierDerivative_apply (f : fourierDerivative.domain) :
    fourierDerivative f =
      fourierDerivativeOnDomain
        (show fourierDerivativeDomain from f) :=
  rfl

/-- The domain-restricted derivative is inverse Fourier transformation of its spectrum. -/
theorem fourierDerivativeOnDomain_apply (f : fourierDerivativeDomain) :
    fourierDerivativeOnDomain f = 𝓕⁻ (fourierDerivativeSpectrum f) :=
  rfl

/-- The Fourier transform of the domain-restricted derivative is its multiplier spectrum. -/
theorem fourier_fourierDerivativeOnDomain (f : fourierDerivativeDomain) :
    𝓕 (fourierDerivativeOnDomain f) = fourierDerivativeSpectrum f := by
  rw [fourierDerivativeOnDomain_apply, fourier_fourierInv_eq]

/-- Fourier transformation of the partial derivative gives its defining multiplier spectrum. -/
theorem fourier_fourierDerivative (f : fourierDerivative.domain) :
    𝓕 (fourierDerivative f) =
      fourierDerivativeSpectrum
        (show fourierDerivativeDomain from f) := by
  rw [fourierDerivative_apply, fourier_fourierDerivativeOnDomain]

/-- The Hilbert transform preserves the natural domain of the `L²` derivative. -/
theorem hilbertTransform_mem_fourierDerivativeDomain
    (f : fourierDerivativeDomain) :
    hilbertTransform (f : ComplexL2) ∈ fourierDerivativeDomain := by
  apply mem_fourierDerivativeDomain_iff.mpr
  rw [fourier_hilbertTransform]
  have hmem := hilbertMultiplier_memLp (fourierDerivativeSpectrum f)
  apply (memLp_congr_ae ?_).mpr hmem
  filter_upwards
    [coe_hilbertMultiplier (𝓕 (f : ComplexL2)),
      coe_fourierDerivativeSpectrum f] with ξ hHilbert hDerivative
  rw [hHilbert, hDerivative]
  ring

/-- The Hilbert transform restricted to the natural domain of the `L²` derivative. -/
def hilbertTransformOnFourierDerivativeDomain :
    fourierDerivativeDomain →ₗ[ℂ] fourierDerivativeDomain where
  toFun f :=
    ⟨hilbertTransform (f : ComplexL2),
      hilbertTransform_mem_fourierDerivativeDomain f⟩
  map_add' f g := by
    apply Subtype.ext
    exact hilbertTransform.map_add (f : ComplexL2) (g : ComplexL2)
  map_smul' c f := by
    apply Subtype.ext
    exact hilbertTransform.map_smul c (f : ComplexL2)

/-- The restriction of `H` to the derivative domain acts as `H` on underlying `L²` classes. -/
@[simp]
theorem coe_hilbertTransformOnFourierDerivativeDomain
    (f : fourierDerivativeDomain) :
    (hilbertTransformOnFourierDerivativeDomain f : ComplexL2) =
      hilbertTransform (f : ComplexL2) :=
  rfl

/-- The Hilbert transform commutes with the Fourier derivative on its natural `L²`
domain. -/
theorem fourierDerivative_hilbertTransform (f : fourierDerivativeDomain) :
    fourierDerivativeOnDomain
        (hilbertTransformOnFourierDerivativeDomain f) =
      hilbertTransform (fourierDerivativeOnDomain f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change
    𝓕 (fourierDerivativeOnDomain
        (hilbertTransformOnFourierDerivativeDomain f)) =
      𝓕 (hilbertTransform (fourierDerivativeOnDomain f))
  rw [fourier_fourierDerivativeOnDomain, fourier_hilbertTransform,
    fourier_fourierDerivativeOnDomain]
  apply Lp.ext
  filter_upwards
    [coe_fourierDerivativeSpectrum
        (hilbertTransformOnFourierDerivativeDomain f),
      coe_hilbertMultiplier
        (fourierDerivativeSpectrum
          (show fourierDerivativeDomain from f)),
      coe_hilbertMultiplier (𝓕 (f : ComplexL2)),
      coe_fourierDerivativeSpectrum f] with ξ hLeft hRight hHilbert hDerivative
  rw [hLeft, hRight]
  rw [coe_hilbertTransformOnFourierDerivativeDomain,
    fourier_hilbertTransform]
  rw [hHilbert, hDerivative]
  ring

end

end PDE.Analysis
