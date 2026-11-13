/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Lp.Translation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Definitions

/-!
# Translation and the Fourier transform on `L²(ℝ^n)`

We prove the `L²` translation identity used in the Fourier
characterization of the fractional Sobolev seminorm (Di Nezza, Palatucci and Valdinoci,
Proposition 3.4):

`𝓕 (u (· + h)) ξ = e^{2πi⟪h,ξ⟫} 𝓕u ξ`.

Mathlib supplies translation as `Lp.compMeasurePreservingₗᵢ`, the corresponding
identity for ordinary Fourier integrals, and density of Schwartz functions in
`L²`. We combine those results here: the identity is checked on Schwartz
functions and extended to `L²` by continuity of both sides. The sign is positive
because `PDE.Analysis.translateL2 ℂ (-h) u` represents `u (· + h)`.

## Main results

* `PDE.Analysis.translateL2` (from `PDE.Analysis.Lp.Translation`): the shared translation
  `u (· - y)` as a linear isometry of `L²`.
* `SobolevSpace.Fractional.charMulL2`: multiplication by `e^{2πi⟪h,ξ⟫}` as a
  linear isometry of `L²`.
* `SobolevSpace.Fractional.fourier_translateL2`:
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

variable {n : ℕ}

/-! ## Translation and its Fourier multiplier -/

/-- The character `ξ ↦ e^{2πi⟪h,ξ⟫}` associated with translation by `h`. -/
noncomputable def fourierCharFn (h : ℝ^n) : ℝ^n → ℂ :=
  fun ξ ↦ (𝐞 ⟪h, ξ⟫ : ℂ)

/-- Unfolding lemma for `fourierCharFn`. -/
@[simp] theorem fourierCharFn_apply (h ξ : ℝ^n) :
    fourierCharFn h ξ = (𝐞 ⟪h, ξ⟫ : ℂ) :=
  rfl

private theorem continuous_fourierCharFn (h : ℝ^n) :
    Continuous (fourierCharFn h) := by
  unfold fourierCharFn
  fun_prop

/-- The translation character has modulus one; this is what makes `charMulL2` an isometry. -/
theorem norm_fourierCharFn (h ξ : ℝ^n) :
    ‖fourierCharFn h ξ‖ = 1 :=
  Circle.norm_coe _

/-- The character of the zero shift is `1`. -/
theorem fourierCharFn_zero (ξ : ℝ^n) : fourierCharFn 0 ξ = 1 := by
  simp [fourierCharFn]

private theorem translateL2_toLp (h : ℝ^n) (φ : 𝓢(ℝ^n, ℂ)) :
    translateL2 ℂ (-h) (φ.toLp 2 volume)
      = (SchwartzMap.compSubConstCLM ℂ (-h) φ).toLp 2 volume := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [
    translateL2_ae_eq ℂ (-h) (φ.toLp 2 (volume : Measure (ℝ^n))),
    (measurePreserving_add_right (volume : Measure (ℝ^n)) h)
      |>.quasiMeasurePreserving.ae_eq_comp (φ.coeFn_toLp 2 (volume : Measure (ℝ^n))),
    (SchwartzMap.compSubConstCLM ℂ (-h) φ).coeFn_toLp
      2 (volume : Measure (ℝ^n))
  ] with x htranslate hφ htranslated
  rw [htranslate, htranslated]
  simp only [Function.comp_apply, sub_neg_eq_add] at hφ ⊢
  rw [hφ, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

/-- Multiplication by the modulus-one Fourier character preserves square integrability. -/
theorem memLp_fourierCharFn_mul (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    MemLp (fun ξ ↦ fourierCharFn h ξ * (u : ℝ^n → ℂ) ξ)
      2 (volume : Measure (ℝ^n)) := by
  refine (Lp.memLp u).of_le
    (((continuous_fourierCharFn h).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable u)) ?_
  filter_upwards with ξ
  rw [norm_mul, norm_fourierCharFn, one_mul]

private theorem eLpNorm_fourierCharFn_mul (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    eLpNorm (fun ξ ↦ fourierCharFn h ξ * (u : ℝ^n → ℂ) ξ)
        2 (volume : Measure (ℝ^n))
      = eLpNorm (u : ℝ^n → ℂ) 2 (volume : Measure (ℝ^n)) := by
  refine eLpNorm_congr_norm_ae (memLp_fourierCharFn_mul h u).aestronglyMeasurable
    (Lp.aestronglyMeasurable u) ?_
  filter_upwards with ξ
  rw [norm_mul, norm_fourierCharFn, one_mul]

/-- Multiplication by `ξ ↦ e^{2πi⟪h,ξ⟫}` as an isometry of `L²(ℝ^n)`. -/
noncomputable def charMulL2 (h : ℝ^n) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) where
  toFun u := (memLp_fourierCharFn_mul h u).toLp _
  map_add' u v := by
    refine Lp.ext_iff.2 ?_
    filter_upwards [
      MemLp.coeFn_toLp (memLp_fourierCharFn_mul h (u + v)),
      Lp.coeFn_add ((memLp_fourierCharFn_mul h u).toLp _)
        ((memLp_fourierCharFn_mul h v).toLp _),
      MemLp.coeFn_toLp (memLp_fourierCharFn_mul h u),
      MemLp.coeFn_toLp (memLp_fourierCharFn_mul h v),
      Lp.coeFn_add u v
    ] with ξ hsum hcoeAdd hu hv huv
    rw [hsum, hcoeAdd, Pi.add_apply, hu, hv, huv, Pi.add_apply, mul_add]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    refine Lp.ext_iff.2 ?_
    filter_upwards [
      MemLp.coeFn_toLp (memLp_fourierCharFn_mul h (c • u)),
      Lp.coeFn_smul c ((memLp_fourierCharFn_mul h u).toLp _),
      MemLp.coeFn_toLp (memLp_fourierCharFn_mul h u),
      Lp.coeFn_smul c u
    ] with ξ hscaled hcoeScaled hu hcu
    rw [hscaled, hcoeScaled, Pi.smul_apply, hu, hcu, Pi.smul_apply]
    simp only [smul_eq_mul]
    ring
  norm_map' u := by
    change ‖(memLp_fourierCharFn_mul h u).toLp
      (fun ξ ↦ fourierCharFn h ξ * (u : ℝ^n → ℂ) ξ)‖ = ‖u‖
    rw [Lp.norm_toLp, eLpNorm_fourierCharFn_mul, ← Lp.norm_def]

/-- A representative of `charMulL2 h u` is pointwise multiplication by the
Fourier character associated with `h`. -/
theorem coeFn_charMulL2 (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (charMulL2 h u : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ fourierCharFn h ξ * (u : ℝ^n → ℂ) ξ :=
  MemLp.coeFn_toLp (memLp_fourierCharFn_mul h u)

private theorem fourier_comp_add_right (f : ℝ^n → ℂ) (h : ℝ^n) :
    𝓕 (fun x ↦ f (x + h)) =
      fun ξ ↦ fourierCharFn h ξ * 𝓕 f ξ := by
  have htranslate :
      𝓕 (fun x ↦ f (x + h)) =
        fun ξ ↦ (𝐞 ⟪h, ξ⟫ : ℂ) • 𝓕 f ξ :=
    VectorFourier.fourierIntegral_comp_add_right
      𝐞 volume (innerₗ (ℝ^n)) f h
  rw [htranslate]
  rfl

private theorem fourier_compSubConstCLM
    (h : ℝ^n) (φ : 𝓢(ℝ^n, ℂ)) (ξ : ℝ^n) :
    (𝓕 (SchwartzMap.compSubConstCLM ℂ (-h) φ)) ξ =
      fourierCharFn h ξ * (𝓕 φ) ξ := by
  have hcoe :
      ⇑(SchwartzMap.compSubConstCLM ℂ (-h) φ) =
        fun x : ℝ^n ↦ φ (x + h) := by
    funext x
    simp [sub_neg_eq_add]
  rw [SchwartzMap.fourier_coe, hcoe, fourier_comp_add_right,
    SchwartzMap.fourier_coe]

private theorem fourier_translateL2_toLp
    (h : ℝ^n) (φ : 𝓢(ℝ^n, ℂ)) :
    𝓕 (translateL2 ℂ (-h) (φ.toLp 2 volume)) =
      charMulL2 h (𝓕 (φ.toLp 2 volume)) := by
  rw [translateL2_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  refine Lp.ext_iff.2 ?_
  filter_upwards [
    (𝓕 (SchwartzMap.compSubConstCLM ℂ (-h) φ)).coeFn_toLp
      2 (volume : Measure (ℝ^n)),
    coeFn_charMulL2 h ((𝓕 φ).toLp 2 (volume : Measure (ℝ^n))),
    (𝓕 φ).coeFn_toLp 2 (volume : Measure (ℝ^n))
  ] with ξ htranslated hmul hφ
  rw [htranslated, hmul, hφ, fourier_compSubConstCLM]

/-- The Fourier transform turns translation into multiplication by a
character on `L²(ℝ^n)`. -/
theorem fourier_translateL2 (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    𝓕 (translateL2 ℂ (-h) u) = charMulL2 h (𝓕 u) := by
  refine DenseRange.induction_on
    (p := fun v : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦
      𝓕 (translateL2 ℂ (-h) v) = charMulL2 h (𝓕 v))
    (SchwartzMap.denseRange_toLpCLM
      (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) u ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).continuous.comp
        (translateL2 ℂ (-h)).continuous
    · exact (charMulL2 h).continuous.comp
        (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).continuous
  · exact fourier_translateL2_toLp h

/-- Pointwise almost-everywhere form of `fourier_translateL2`. -/
theorem coeFn_fourier_translateL2 (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ((𝓕 (translateL2 ℂ (-h) u) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ fourierCharFn h ξ *
        ((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ := by
  rw [fourier_translateL2]
  exact coeFn_charMulL2 h (𝓕 u)

/-- The Fourier transform of `u (· + h) - u`. -/
theorem coeFn_fourier_translateL2_sub (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ((𝓕 (translateL2 ℂ (-h) u - u) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ (fourierCharFn h ξ - 1) *
        ((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ := by
  have hmap :
      (𝓕 (translateL2 ℂ (-h) u - u) : Lp ℂ 2 (volume : Measure (ℝ^n))) =
        𝓕 (translateL2 ℂ (-h) u) - 𝓕 u :=
    (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).map_sub _ _
  rw [hmap]
  filter_upwards [
    Lp.coeFn_sub (𝓕 (translateL2 ℂ (-h) u)) (𝓕 u),
    coeFn_fourier_translateL2 h u
  ] with ξ hsub htranslate
  rw [hsub, Pi.sub_apply, htranslate, sub_mul, one_mul]

/-- Plancherel for the translated difference. -/
theorem norm_translateL2_sub (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ‖translateL2 ℂ (-h) u - u‖ =
      ‖(𝓕 (translateL2 ℂ (-h) u - u) : Lp ℂ 2 (volume : Measure (ℝ^n)))‖ :=
  (Lp.norm_fourier_eq _).symm

end SobolevSpace.Fractional
