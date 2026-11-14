/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Lp.Translation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Definitions

/-!
# Translation and the Fourier transform on `L²`

On `L²(X; F)`, for a finite-dimensional real inner product space `X` and a complex Hilbert space
`F`, the Fourier transform turns the translation `u ↦ u (· + h)` into multiplication by a
character:

`𝓕 (u (· + h)) ξ = e^{2πi⟪h,ξ⟫} 𝓕u ξ`.

The case `X = ℝ^n`, `F = ℂ` is the identity used in the Fourier characterization of the
fractional Sobolev seminorm (Di Nezza, Palatucci and Valdinoci, Proposition 3.4). The Hilbert
transform on the real line uses the case `X = ℝ`.

Mathlib supplies translation as `Lp.compMeasurePreserving`, the corresponding identity for
ordinary Fourier integrals, and density of Schwartz functions in `L²`. We combine those results
here: the identity is checked on Schwartz functions and extended to `L²` by continuity of both
sides. On `ℝ^n` the sign is positive because `PDE.Analysis.translateL2 ℂ (-h) u` represents
`u (· + h)`.

## Main results

* `SobolevSpace.Fractional.charMulL2`: multiplication by `e^{2πi⟪h,ξ⟫}` as a linear isometry of
  `L²(X; F)`, for every complex normed space `F`.
* `SobolevSpace.Fractional.fourier_compMeasurePreserving_add_right`: on `L²(X; F)`, the Fourier
  transform of `u (· + h)`, written with Mathlib's `Lp.compMeasurePreserving`, is
  `charMulL2 h (𝓕 u)`.
* `PDE.Analysis.translateL2` (from `PDE.Analysis.Lp.Translation`): the shared translation
  `u (· - y)` as a linear isometry of `L²(ℝ^n; F)`.
* `SobolevSpace.Fractional.fourier_translateL2`: on `L²(ℝ^n; F)`,
  `𝓕 ∘ translateL2 ℂ (-h) = charMulL2 h ∘ 𝓕`.
* `SobolevSpace.Fractional.coeFn_fourier_translateL2_sub`,
  `SobolevSpace.Fractional.norm_translateL2_sub`: the Fourier transform of the
  difference `u(· + h) - u` is `(e^{2πi⟪h,ξ⟫} - 1) 𝓕u`, with equal `L²` norms.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, "Hitchhiker's guide to the fractional Sobolev spaces",
  *Bull. Sci. Math.* 136 (2012), 521-573, numbering of arXiv:1104.4345v3, Proposition 3.4, whose
  proof substitutes `z = x - y`, applies Plancherel's formula for each fixed `z`, and concludes with
  the kernel identity (3.12).
  <https://arxiv.org/abs/1104.4345v3>
-/

@[expose] public section

open MeasureTheory Real
open PDE.Analysis (translateL2 translateL2_ae_eq)
open scoped BesselPotentialSpace ENNReal FourierTransform RealInnerProductSpace SchwartzMap

namespace SobolevSpace.Fractional

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ## The translation character -/

/-- The character `ξ ↦ e^{2πi⟪h,ξ⟫}` associated with translation by `h`. -/
noncomputable def fourierCharFn (h : X) : X → ℂ :=
  fun ξ ↦ (𝐞 ⟪h, ξ⟫ : ℂ)

/-- Unfolding lemma for `fourierCharFn`. -/
@[simp] theorem fourierCharFn_apply (h ξ : X) :
    fourierCharFn h ξ = (𝐞 ⟪h, ξ⟫ : ℂ) :=
  rfl

private theorem continuous_fourierCharFn (h : X) :
    Continuous (fourierCharFn h) := by
  unfold fourierCharFn
  fun_prop

/-- The translation character has modulus one; this is what makes `charMulL2` an isometry. -/
theorem norm_fourierCharFn (h ξ : X) :
    ‖fourierCharFn h ξ‖ = 1 :=
  Circle.norm_coe _

/-- The character of the zero shift is `1`. -/
theorem fourierCharFn_zero (ξ : X) : fourierCharFn 0 ξ = 1 := by
  simp [fourierCharFn]

variable [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]

/-! ## Multiplication by the character on `L²` -/

section Multiplier

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Multiplication by the modulus-one Fourier character preserves square integrability. -/
theorem memLp_fourierCharFn_smul (h : X) (u : Lp F 2 (volume : Measure X)) :
    MemLp (fun ξ ↦ fourierCharFn h ξ • (u : X → F) ξ)
      2 (volume : Measure X) := by
  refine (Lp.memLp u).of_le
    (((continuous_fourierCharFn h).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable u)) ?_
  filter_upwards with ξ
  rw [norm_smul, norm_fourierCharFn, one_mul]

private theorem eLpNorm_fourierCharFn_smul (h : X) (u : Lp F 2 (volume : Measure X)) :
    eLpNorm (fun ξ ↦ fourierCharFn h ξ • (u : X → F) ξ)
        2 (volume : Measure X)
      = eLpNorm (u : X → F) 2 (volume : Measure X) := by
  refine eLpNorm_congr_norm_ae (memLp_fourierCharFn_smul h u).aestronglyMeasurable
    (Lp.aestronglyMeasurable u) ?_
  filter_upwards with ξ
  rw [norm_smul, norm_fourierCharFn, one_mul]

/-- Multiplication by `ξ ↦ e^{2πi⟪h,ξ⟫}` as an isometry of `L²(X; F)`, for every complex normed
space `F`. -/
noncomputable def charMulL2 (h : X) :
    Lp F 2 (volume : Measure X) →ₗᵢ[ℂ] Lp F 2 (volume : Measure X) where
  toFun u := (memLp_fourierCharFn_smul h u).toLp _
  map_add' u v := by
    refine Lp.ext_iff.2 ?_
    filter_upwards [
      MemLp.coeFn_toLp (memLp_fourierCharFn_smul h (u + v)),
      Lp.coeFn_add ((memLp_fourierCharFn_smul h u).toLp _)
        ((memLp_fourierCharFn_smul h v).toLp _),
      MemLp.coeFn_toLp (memLp_fourierCharFn_smul h u),
      MemLp.coeFn_toLp (memLp_fourierCharFn_smul h v),
      Lp.coeFn_add u v
    ] with ξ hsum hcoeAdd hu hv huv
    rw [hsum, hcoeAdd, Pi.add_apply, hu, hv, huv, Pi.add_apply, smul_add]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    refine Lp.ext_iff.2 ?_
    filter_upwards [
      MemLp.coeFn_toLp (memLp_fourierCharFn_smul h (c • u)),
      Lp.coeFn_smul c ((memLp_fourierCharFn_smul h u).toLp _),
      MemLp.coeFn_toLp (memLp_fourierCharFn_smul h u),
      Lp.coeFn_smul c u
    ] with ξ hscaled hcoeScaled hu hcu
    rw [hscaled, hcoeScaled, Pi.smul_apply, hu, hcu, Pi.smul_apply, smul_comm]
  norm_map' u := by
    change ‖(memLp_fourierCharFn_smul h u).toLp
      (fun ξ ↦ fourierCharFn h ξ • (u : X → F) ξ)‖ = ‖u‖
    rw [Lp.norm_toLp, eLpNorm_fourierCharFn_smul, ← Lp.norm_def]

/-- A representative of `charMulL2 h u` is pointwise multiplication by the
Fourier character associated with `h`. -/
theorem coeFn_charMulL2 (h : X) (u : Lp F 2 (volume : Measure X)) :
    (charMulL2 h u : X → F) =ᵐ[volume]
      fun ξ ↦ fourierCharFn h ξ • (u : X → F) ξ :=
  MemLp.coeFn_toLp (memLp_fourierCharFn_smul h u)

end Multiplier

/-! ## The Fourier transform of a translate -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private theorem fourier_comp_add_right (f : X → F) (h : X) :
    𝓕 (fun x ↦ f (x + h)) =
      fun ξ ↦ fourierCharFn h ξ • 𝓕 f ξ :=
  VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ X) f h

private theorem fourier_compSubConstCLM
    (h : X) (φ : 𝓢(X, F)) (ξ : X) :
    (𝓕 (SchwartzMap.compSubConstCLM ℂ (-h) φ)) ξ =
      fourierCharFn h ξ • (𝓕 φ) ξ := by
  have hcoe :
      ⇑(SchwartzMap.compSubConstCLM ℂ (-h) φ) =
        fun x : X ↦ φ (x + h) := by
    funext x
    simp [sub_neg_eq_add]
  rw [SchwartzMap.fourier_coe, hcoe, fourier_comp_add_right,
    SchwartzMap.fourier_coe]

private theorem compMeasurePreserving_add_right_toLp (h : X) (φ : 𝓢(X, F)) :
    Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h) (φ.toLp 2 volume)
      = (SchwartzMap.compSubConstCLM ℂ (-h) φ).toLp 2 volume := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (φ.toLp 2 (volume : Measure X))
      (measurePreserving_add_right volume h),
    (measurePreserving_add_right (volume : Measure X) h)
      |>.quasiMeasurePreserving.ae_eq_comp (φ.coeFn_toLp 2 (volume : Measure X)),
    (SchwartzMap.compSubConstCLM ℂ (-h) φ).coeFn_toLp
      2 (volume : Measure X)
  ] with x htranslate hφ htranslated
  rw [htranslate, htranslated, hφ, Function.comp_apply, SchwartzMap.compSubConstCLM_apply,
    sub_neg_eq_add]

variable [CompleteSpace F]

private theorem fourier_compMeasurePreserving_add_right_toLp
    (h : X) (φ : 𝓢(X, F)) :
    𝓕 (Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h)
        (φ.toLp 2 volume)) =
      charMulL2 h (𝓕 (φ.toLp 2 volume)) := by
  rw [compMeasurePreserving_add_right_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  refine Lp.ext_iff.2 ?_
  filter_upwards [
    (𝓕 (SchwartzMap.compSubConstCLM ℂ (-h) φ)).coeFn_toLp
      2 (volume : Measure X),
    coeFn_charMulL2 h ((𝓕 φ).toLp 2 (volume : Measure X)),
    (𝓕 φ).coeFn_toLp 2 (volume : Measure X)
  ] with ξ htranslated hmul hφ
  rw [htranslated, hmul, hφ, fourier_compSubConstCLM]

/-- **The Fourier transform of a translate.** On `L²(X; F)` the Fourier transform turns the
translation `u ↦ u (· + h)`, Mathlib's `Lp.compMeasurePreserving` along `x ↦ x + h`, into
multiplication by the character `ξ ↦ e^{2πi⟪h,ξ⟫}`, for every `h`. -/
theorem fourier_compMeasurePreserving_add_right (h : X) (u : Lp F 2 (volume : Measure X)) :
    𝓕 (Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h) u) =
      charMulL2 h (𝓕 u) := by
  refine DenseRange.induction_on
    (p := fun v : Lp F 2 (volume : Measure X) ↦
      𝓕 (Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h) v) =
        charMulL2 h (𝓕 v))
    (SchwartzMap.denseRange_toLpCLM
      (F := F) (p := 2) ENNReal.ofNat_ne_top) u ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact (Lp.fourierTransformₗᵢ X F).continuous.comp
        (Lp.isometry_compMeasurePreserving (measurePreserving_add_right volume h)).continuous
    · exact (charMulL2 h).continuous.comp
        (Lp.fourierTransformₗᵢ X F).continuous
  · exact fourier_compMeasurePreserving_add_right_toLp h

/-! ## Translation on `ℝ^n` -/

variable {n : ℕ}

omit [CompleteSpace F] in
private theorem translateL2_neg_eq (h : ℝ^n) (u : Lp F 2 (volume : Measure (ℝ^n))) :
    translateL2 ℂ (-h) u =
      Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h) u := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [
    translateL2_ae_eq ℂ (-h) u,
    Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume h)
  ] with x htranslate hcomp
  rw [htranslate, hcomp, Function.comp_apply, sub_neg_eq_add]

/-- The Fourier transform turns translation into multiplication by a
character on `L²(ℝ^n; F)`. -/
theorem fourier_translateL2 (h : ℝ^n) (u : Lp F 2 (volume : Measure (ℝ^n))) :
    𝓕 (translateL2 ℂ (-h) u) = charMulL2 h (𝓕 u) := by
  rw [translateL2_neg_eq]
  exact fourier_compMeasurePreserving_add_right h u

/-- Pointwise almost-everywhere form of `fourier_translateL2`. -/
theorem coeFn_fourier_translateL2 (h : ℝ^n) (u : Lp F 2 (volume : Measure (ℝ^n))) :
    ((𝓕 (translateL2 ℂ (-h) u) : Lp F 2 (volume : Measure (ℝ^n))) : ℝ^n → F) =ᵐ[volume]
      fun ξ ↦ fourierCharFn h ξ •
        ((𝓕 u : Lp F 2 (volume : Measure (ℝ^n))) : ℝ^n → F) ξ := by
  rw [fourier_translateL2]
  exact coeFn_charMulL2 h (𝓕 u)

/-- The Fourier transform of `u (· + h) - u`. -/
theorem coeFn_fourier_translateL2_sub (h : ℝ^n) (u : Lp F 2 (volume : Measure (ℝ^n))) :
    ((𝓕 (translateL2 ℂ (-h) u - u) : Lp F 2 (volume : Measure (ℝ^n))) : ℝ^n → F) =ᵐ[volume]
      fun ξ ↦ (fourierCharFn h ξ - 1) •
        ((𝓕 u : Lp F 2 (volume : Measure (ℝ^n))) : ℝ^n → F) ξ := by
  have hmap :
      (𝓕 (translateL2 ℂ (-h) u - u) : Lp F 2 (volume : Measure (ℝ^n))) =
        𝓕 (translateL2 ℂ (-h) u) - 𝓕 u :=
    (Lp.fourierTransformₗᵢ (ℝ^n) F).map_sub _ _
  rw [hmap]
  filter_upwards [
    Lp.coeFn_sub (𝓕 (translateL2 ℂ (-h) u)) (𝓕 u),
    coeFn_fourier_translateL2 h u
  ] with ξ hsub htranslate
  rw [hsub, Pi.sub_apply, htranslate, sub_smul, one_smul]

/-- Plancherel for the translated difference. -/
theorem norm_translateL2_sub (h : ℝ^n) (u : Lp F 2 (volume : Measure (ℝ^n))) :
    ‖translateL2 ℂ (-h) u - u‖ =
      ‖(𝓕 (translateL2 ℂ (-h) u - u) : Lp F 2 (volume : Measure (ℝ^n)))‖ :=
  (Lp.norm_fourier_eq _).symm

end SobolevSpace.Fractional
