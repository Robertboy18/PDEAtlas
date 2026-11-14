/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.GagliardoKernel
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij

/-!
# Fourier representation of the Gagliardo seminorm

For `1 ≤ n`, `0 < s < 1`, and `u ∈ L²(ℝ^n; ℂ)`, we prove

`∫∫ ‖u x - u y‖² / ‖x - y‖^(n + 2s) dx dy`
`  = J(e) ∫ ‖ξ‖^(2s) ‖𝓕u ξ‖² dξ`,

where `e` is any unit vector and `J(e)` is the positive finite kernel constant
from `GagliardoKernel`. Both sides are extended-real integrals, so the equality
also covers the case in which both are infinite.

## Main results

* `gagDouble`, `fourierSq`: the two extended-real integrals.
* `gagDouble_eq_lintegral_shift`: the double integral as an integral over increments `h`.
* `lintegral_enorm_translate_sub_sq`: Plancherel for `u(· + h) - u` at fixed `h`.
* `gagDouble_eq_gagJ_mul_fourierSq`: the identity `gagDouble = J(e) · fourierSq`.
* `gagDouble_lt_top_iff`: finiteness of the Gagliardo seminorm is equivalent to finiteness of
  the Fourier integral, so the Slobodeckij and Bessel-potential descriptions of `H^s(ℝ^n)`
  agree for `0 < s < 1`.
* `gagliardoSq_univ_eq_gagJ_mul_fourierSq`, `memGagliardo_univ_iff_fourierSq_lt_top`: the same
  statements for the real-valued domain definition with `Ω = univ`.

## How it works

We follow the proof of Proposition 3.4 of Di Nezza, Palatucci and Valdinoci. We write the double
integral over increments `h = y - x` (`gagDouble_eq_lintegral_shift`) and, for each fixed `h`, apply
Plancherel to `u(· + h) - u`, whose Fourier transform is `(e^{2πi⟪h, ξ⟫} - 1) 𝓕u`
(`lintegral_enorm_translate_sub_sq`). Tonelli exchanges the `h` and `ξ` integrals, the `h` integral
of the kernel is `gagJ n s ξ` (`lintegral_ofReal_gagKernel`), and `gagJ_eq_mul_rpow` writes it as
`J(e) ‖ξ‖^(2s)`. For the real-valued `gagliardoSq` on `Ω = univ` we apply the identity to the
complexification of `u` (`gagliardoSq_univ_eq_gagDouble`).

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, "Hitchhiker's guide to the fractional Sobolev spaces",
  *Bull. Sci. Math.* 136 (2012), 521-573, numbering of arXiv:1104.4345v3, Proposition 3.4 and the
  kernel identity (3.12) used in its proof.
  <https://arxiv.org/abs/1104.4345v3>
-/

@[expose] public section

open PDE.Analysis (translateL2 translateL2_ae_eq)
open MeasureTheory
open scoped BesselPotentialSpace ENNReal FourierTransform InnerProductSpace
  RealInnerProductSpace

namespace SobolevSpace.Fractional

open GagliardoKernel

variable {n : ℕ} {s : ℝ}

/-! ## The two extended-real integrals -/

/-- The complex-valued Gagliardo seminorm squared on `ℝ^n`. -/
noncomputable def gagDouble
    (n : ℕ) (s : ℝ) (f : ℝ^n → ℂ) : ℝ≥0∞ :=
  ∫⁻ p : (ℝ^n) × (ℝ^n),
    ENNReal.ofReal
      (‖f p.1 - f p.2‖ ^ 2 /
        ‖p.1 - p.2‖ ^ ((n : ℝ) + 2 * s))
      ∂((volume : Measure (ℝ^n)).prod volume)

/-- The homogeneous Fourier seminorm squared of a complex-valued function. -/
noncomputable def fourierSq
    (n : ℕ) (s : ℝ) (g : ℝ^n → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ^n,
    ENNReal.ofReal (‖ξ‖ ^ (2 * s)) * ‖g ξ‖ₑ ^ 2

/-- The Gagliardo double integral depends only on the almost-everywhere class of the
function. -/
theorem gagDouble_congr
    {f g : ℝ^n → ℂ} (hfg : f =ᵐ[volume] g) :
    gagDouble n s f = gagDouble n s g := by
  refine lintegral_congr_ae ?_
  filter_upwards [
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hfg
  ] with p hfst hsnd
  simp only [Function.comp_apply] at hfst hsnd
  rw [hfst, hsnd]

private theorem fourierSq_congr
    {f g : ℝ^n → ℂ} (hfg : f =ᵐ[volume] g) :
    fourierSq n s f = fourierSq n s g := by
  refine lintegral_congr_ae ?_
  filter_upwards [hfg] with ξ hξ
  rw [hξ]

/-! ## Change of variables -/

/-- The Gagliardo double integral written as an integral over increments. -/
theorem gagDouble_eq_lintegral_shift
    {f : ℝ^n → ℂ} (hf : Measurable f) :
    gagDouble n s f =
      ∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
        ENNReal.ofReal
          (‖f (x + h) - f x‖ ^ 2 /
            ‖h‖ ^ ((n : ℝ) + 2 * s)) := by
  rw [gagDouble, lintegral_prod _ (by fun_prop)]
  have hinner :
      ∀ x : ℝ^n,
        (∫⁻ y : ℝ^n,
          ENNReal.ofReal
            (‖f x - f y‖ ^ 2 /
              ‖x - y‖ ^ ((n : ℝ) + 2 * s))) =
        ∫⁻ h : ℝ^n,
          ENNReal.ofReal
            (‖f (x + h) - f x‖ ^ 2 /
              ‖h‖ ^ ((n : ℝ) + 2 * s)) := by
    intro x
    rw [← lintegral_add_right_eq_self
      (fun y : ℝ^n ↦
        ENNReal.ofReal
          (‖f x - f y‖ ^ 2 /
            ‖x - y‖ ^ ((n : ℝ) + 2 * s)))
      x]
    refine lintegral_congr fun h ↦ ?_
    rw [show x - (h + x) = -h by abel,
      norm_neg, norm_sub_rev, add_comm x h]
  simp_rw [hinner]
  exact lintegral_lintegral_swap (by fun_prop)

/-! ## Plancherel for each increment -/

private theorem eLpNorm_eq_ofReal_norm (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    eLpNorm (u : ℝ^n → ℂ) 2 volume =
      ENNReal.ofReal ‖u‖ := by
  rw [Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u)]

private theorem lintegral_enorm_sq_congr
    {u v : Lp ℂ 2 (volume : Measure (ℝ^n))} (h : ‖u‖ = ‖v‖) :
    (∫⁻ x, ‖(u : ℝ^n → ℂ) x‖ₑ ^ 2) =
      ∫⁻ x, ‖(v : ℝ^n → ℂ) x‖ₑ ^ 2 := by
  have hnorm (w : Lp ℂ 2 (volume : Measure (ℝ^n))) :
      (∫⁻ x, ‖(w : ℝ^n → ℂ) x‖ₑ ^ 2) =
        eLpNorm (w : ℝ^n → ℂ) 2 volume ^ 2 := by
    simpa [ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral
        (p := (2 : NNReal)) (by norm_num) (Lp.aestronglyMeasurable w)).symm
  rw [hnorm u, hnorm v,
    eLpNorm_eq_ofReal_norm, eLpNorm_eq_ofReal_norm, h]

/-- Plancherel for the translated difference at a fixed increment. -/
theorem lintegral_enorm_translate_sub_sq
    (h : ℝ^n) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∫⁻ x : ℝ^n,
      ‖(u : ℝ^n → ℂ) (x + h) -
        (u : ℝ^n → ℂ) x‖ₑ ^ 2) =
      ∫⁻ ξ : ℝ^n,
        ‖fourierCharFn h ξ - 1‖ₑ ^ 2 *
          ‖((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖ₑ ^ 2 := by
  have hphysical :
      (∫⁻ x : ℝ^n,
        ‖((translateL2 ℂ (-h) u - u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
          ℝ^n → ℂ) x‖ₑ ^ 2) =
        ∫⁻ x : ℝ^n,
          ‖(u : ℝ^n → ℂ) (x + h) -
            (u : ℝ^n → ℂ) x‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [
      Lp.coeFn_sub (translateL2 ℂ (-h) u) u,
      translateL2_ae_eq ℂ (-h) u
    ] with x hsub htranslate
    rw [hsub, Pi.sub_apply, htranslate, sub_neg_eq_add]
  have hfrequency :
      (∫⁻ ξ : ℝ^n,
        ‖((𝓕 (translateL2 ℂ (-h) u - u) : Lp ℂ 2 (volume : Measure (ℝ^n))) :
          ℝ^n → ℂ) ξ‖ₑ ^ 2) =
        ∫⁻ ξ : ℝ^n,
          ‖fourierCharFn h ξ - 1‖ₑ ^ 2 *
            ‖((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
              ℝ^n → ℂ) ξ‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [
      coeFn_fourier_translateL2_sub h u
    ] with ξ hξ
    rw [hξ, enorm_smul, mul_pow]
  rw [← hphysical, ← hfrequency]
  exact lintegral_enorm_sq_congr
    (norm_translateL2_sub h u)

/-! ## Tonelli and the radial kernel -/

private theorem measurable_gagKernel_uncurry :
    Measurable
      (fun p : (ℝ^n) × (ℝ^n) ↦
        gagKernel n s p.1 p.2) := by
  unfold gagKernel fourierCharFn
  fun_prop

private theorem enorm_char_sub_one_sq_mul
    (h ξ : ℝ^n) :
    ‖fourierCharFn h ξ - 1‖ₑ ^ 2 *
        ENNReal.ofReal
          ((‖h‖ ^ ((n : ℝ) + 2 * s))⁻¹) =
      ENNReal.ofReal (gagKernel n s ξ h) := by
  rw [gagKernel, div_eq_mul_inv,
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem lintegral_shift_eq_lintegral_kernel
    {u : Lp ℂ 2 (volume : Measure (ℝ^n))} {f g : ℝ^n → ℂ}
    (hfu : f =ᵐ[volume] (u : ℝ^n → ℂ))
    (hgu : g =ᵐ[volume]
      ((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ))
    (h : ℝ^n) :
    (∫⁻ x : ℝ^n,
      ENNReal.ofReal
        (‖f (x + h) - f x‖ ^ 2 /
          ‖h‖ ^ ((n : ℝ) + 2 * s))) =
      ∫⁻ ξ : ℝ^n,
        ENNReal.ofReal (gagKernel n s ξ h) *
          ‖g ξ‖ₑ ^ 2 := by
  have hpointwise :
      ∀ x : ℝ^n,
        ENNReal.ofReal
            (‖f (x + h) - f x‖ ^ 2 /
              ‖h‖ ^ ((n : ℝ) + 2 * s)) =
          ‖f (x + h) - f x‖ₑ ^ 2 *
            ENNReal.ofReal
              ((‖h‖ ^ ((n : ℝ) + 2 * s))⁻¹) := by
    intro x
    rw [div_eq_mul_inv,
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have htranslated :
      (fun x : ℝ^n ↦ f (x + h)) =ᵐ[volume]
        fun x : ℝ^n ↦ (u : ℝ^n → ℂ) (x + h) :=
    (measurePreserving_add_right
      (volume : Measure (ℝ^n)) h)
      |>.quasiMeasurePreserving.ae_eq_comp hfu
  have hrepresentative :
      (∫⁻ x : ℝ^n,
        ‖f (x + h) - f x‖ₑ ^ 2) =
        ∫⁻ x : ℝ^n,
          ‖(u : ℝ^n → ℂ) (x + h) -
            (u : ℝ^n → ℂ) x‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [hfu, htranslated] with x hx hxh
    rw [hx, hxh]
  simp_rw [hpointwise]
  rw [lintegral_mul_const' _ _
      ENNReal.ofReal_ne_top,
    hrepresentative,
    lintegral_enorm_translate_sub_sq h u,
    ← lintegral_mul_const' _ _
      ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hgu] with ξ hξ
  rw [hξ, mul_right_comm,
    enorm_char_sub_one_sq_mul]

/-- The Gagliardo double integral equals the Fourier integral weighted by
`GagliardoKernel.gagJ`. -/
theorem gagDouble_eq_lintegral_gagJ
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    {u : Lp ℂ 2 (volume : Measure (ℝ^n))} {f g : ℝ^n → ℂ}
    (hf : Measurable f)
    (hfu : f =ᵐ[volume] (u : ℝ^n → ℂ))
    (hg : Measurable g)
    (hgu : g =ᵐ[volume]
      ((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ)) :
    gagDouble n s f =
      ∫⁻ ξ : ℝ^n,
        ENNReal.ofReal (gagJ n s ξ) *
          ‖g ξ‖ₑ ^ 2 := by
  have hmeas :
      Measurable
        (Function.uncurry fun (h ξ : ℝ^n) ↦
          ENNReal.ofReal (gagKernel n s ξ h) *
            ‖g ξ‖ₑ ^ 2) := by
    rw [Function.uncurry_def]
    exact
      ((measurable_gagKernel_uncurry.comp measurable_swap)
        |>.ennreal_ofReal).mul
        (((hg.comp measurable_snd).enorm).pow_const 2)
  rw [gagDouble_eq_lintegral_shift hf]
  simp_rw [lintegral_shift_eq_lintegral_kernel hfu hgu]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun ξ ↦ ?_
  rw [lintegral_mul_const' _ _
      (ENNReal.pow_ne_top enorm_ne_top),
    lintegral_ofReal_gagKernel hn hs0 hs1]

/-! ## The Gagliardo-Fourier identity -/

/-- The Gagliardo seminorm squared is a positive finite constant times the
homogeneous Fourier seminorm squared. The constant is the kernel integral at
any chosen unit vector. -/
theorem gagDouble_eq_gagJ_mul_fourierSq
    (hs0 : 0 < s) (hs1 : s < 1)
    {e : ℝ^n} (he : ‖e‖ = 1) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    gagDouble n s (u : ℝ^n → ℂ) =
      ENNReal.ofReal (gagJ n s e) *
        fourierSq n s
          ((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) := by
  -- a unit vector exists only in positive dimension
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h ↦ by
    subst h
    simp [Subsingleton.elim e 0] at he
  obtain ⟨f, hf, hfu⟩ :
      ∃ f : ℝ^n → ℂ,
        Measurable f ∧
          f =ᵐ[volume] (u : ℝ^n → ℂ) :=
    ⟨(Lp.aestronglyMeasurable u).mk _,
      (Lp.aestronglyMeasurable u)
        |>.stronglyMeasurable_mk.measurable,
      ((Lp.aestronglyMeasurable u).ae_eq_mk).symm⟩
  obtain ⟨g, hg, hgu⟩ :
      ∃ g : ℝ^n → ℂ,
        Measurable g ∧
          g =ᵐ[volume]
            ((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) :=
    ⟨(Lp.aestronglyMeasurable
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n)))).mk _,
      (Lp.aestronglyMeasurable
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))))
        |>.stronglyMeasurable_mk.measurable,
      ((Lp.aestronglyMeasurable
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n)))).ae_eq_mk).symm⟩
  have hJ0 : 0 ≤ gagJ n s e :=
    gagJ_nonneg e
  rw [← gagDouble_congr (s := s) hfu,
    ← fourierSq_congr (s := s) hgu,
    gagDouble_eq_lintegral_gagJ
      hn hs0 hs1 hf hfu hg hgu,
    fourierSq,
    ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ξ ↦ ?_
  rw [gagJ_eq_mul_rpow hs0 he ξ,
    ENNReal.ofReal_mul hJ0, mul_assoc]

/-- In dimension zero the Gagliardo double integral vanishes: the two points coincide. -/
private theorem gagDouble_dim_zero (s : ℝ) (f : ℝ^0 → ℂ) : gagDouble 0 s f = 0 := by
  have h (p : (ℝ^0) × (ℝ^0)) : p.1 = p.2 := Subsingleton.elim _ _
  simp [gagDouble, h]

/-- In dimension zero the homogeneous Fourier seminorm vanishes: `‖ξ‖ = 0`. -/
private theorem fourierSq_dim_zero (hs0 : 0 < s) (g : ℝ^0 → ℂ) : fourierSq 0 s g = 0 := by
  have h (ξ : ℝ^0) : ‖ξ‖ = 0 := by simp [Subsingleton.elim ξ 0]
  simp [fourierSq, h, Real.zero_rpow (by positivity : 2 * s ≠ 0)]

/-- Finiteness of the whole-space Gagliardo seminorm is equivalent to
finiteness of the homogeneous Fourier seminorm. In dimension zero both vanish. -/
theorem gagDouble_lt_top_iff
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    gagDouble n s (u : ℝ^n → ℂ) < ⊤ ↔
      fourierSq n s
        ((𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) < ⊤ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gagDouble_dim_zero, fourierSq_dim_zero hs0]
  let e : ℝ^n :=
    EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)
  have he : ‖e‖ = 1 := by
    simp [e]
  have hene : e ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at he
    norm_num at he
  have hconstant_pos :
      0 < gagJ n s e :=
    gagJ_pos hn hs0 hs1 hene
  have hconstant_ne :
      ENNReal.ofReal (gagJ n s e) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le,
      hconstant_pos]
  rw [gagDouble_eq_gagJ_mul_fourierSq
    hs0 hs1 he u]
  constructor
  · intro hlt
    rcases ENNReal.mul_lt_top_iff.1 hlt with
      ⟨_, hfourier⟩ | hzero | hzero
    · exact hfourier
    · exact absurd hzero hconstant_ne
    · rw [hzero]
      exact ENNReal.zero_lt_top
  · intro hlt
    exact ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top hlt

/-! ## Bridge to the real-valued domain definition -/

/-- On the full space, `gagliardoSq` is the complex Gagliardo integral of the
complexification of the real-valued function. -/
theorem gagliardoSq_univ_eq_gagDouble
    (u : ℝ^n → ℝ) :
    gagliardoSq n s Set.univ u =
      gagDouble n s (fun x ↦ (u x : ℂ)) := by
  rw [gagliardoSq, gagDouble,
    gagliardoProductMeasure, Measure.restrict_univ]
  refine lintegral_congr fun p ↦ ?_
  have hnorm : (0 : ℝ) ≤ ‖p.1 - p.2‖ :=
    norm_nonneg _
  have hexponent :
      ((n : ℝ) / 2 + s) * ((2 : ℕ) : ℝ) =
        (n : ℝ) + 2 * s := by
    push_cast
    ring
  have hpow :
      (‖p.1 - p.2‖ ^ ((n : ℝ) / 2 + s)) ^ 2 =
        ‖p.1 - p.2‖ ^ ((n : ℝ) + 2 * s) := by
    rw [← Real.rpow_natCast
      (‖p.1 - p.2‖ ^ ((n : ℝ) / 2 + s)) 2,
      ← Real.rpow_mul hnorm, hexponent]
  have hnum :
      ‖(u p.1 : ℂ) - (u p.2 : ℂ)‖ ^ 2 =
        (u p.1 - u p.2) ^ 2 := by
    rw [show
      ((u p.1 : ℂ) - (u p.2 : ℂ)) =
        ((u p.1 - u p.2 : ℝ) : ℂ) by
          push_cast
          ring,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← enorm_eq_nnnorm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), hnum]
  congr 1
  rw [diffQuot_apply_real, ENNReal.toReal_ofNat, Real.norm_eq_abs, sq_abs,
    div_pow, hpow]

/-- Real-valued form of the Gagliardo-Fourier identity on `ℝ^n`. -/
theorem gagliardoSq_univ_eq_gagJ_mul_fourierSq
    (hs0 : 0 < s) (hs1 : s < 1)
    {e : ℝ^n} (he : ‖e‖ = 1)
    (u : ℝ^n → ℝ)
    (hu : MemLp (fun x ↦ (u x : ℂ)) 2
      (volume : Measure (ℝ^n))) :
    gagliardoSq n s Set.univ u =
      ENNReal.ofReal (gagJ n s e) *
        fourierSq n s
          ((𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure (ℝ^n))) :
            ℝ^n → ℂ) := by
  rw [gagliardoSq_univ_eq_gagDouble,
    ← gagDouble_congr (s := s) hu.coeFn_toLp,
    gagDouble_eq_gagJ_mul_fourierSq
      hs0 hs1 he]

/-- The real-valued Gagliardo condition on `ℝ^n`, read on the Fourier side. -/
theorem gagliardoSq_univ_lt_top_iff
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : ℝ^n → ℝ)
    (hu : MemLp (fun x ↦ (u x : ℂ)) 2
      (volume : Measure (ℝ^n))) :
    gagliardoSq n s Set.univ u < ⊤ ↔
      fourierSq n s
        ((𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure (ℝ^n))) :
          ℝ^n → ℂ) < ⊤ := by
  rw [gagliardoSq_univ_eq_gagDouble,
    ← gagDouble_congr (s := s) hu.coeFn_toLp]
  exact gagDouble_lt_top_iff
    hs0 hs1 (hu.toLp _)

/-- The full-space Gagliardo membership condition is equivalent to finiteness
of the homogeneous Fourier seminorm, provided the complexification is in
`L²`. -/
theorem memGagliardo_univ_iff_fourierSq_lt_top
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : ℝ^n → ℝ)
    (hu : MemLp (fun x ↦ (u x : ℂ)) 2
      (volume : Measure (ℝ^n))) :
    MemGagliardo n s Set.univ u ↔
      fourierSq n s
        ((𝓕 (hu.toLp _) : Lp ℂ 2 (volume : Measure (ℝ^n))) :
          ℝ^n → ℂ) < ⊤ := by
  have huReal :
      MemLp u 2 (volume : Measure (ℝ^n)) := by
    simpa using hu.re
  rw [memGagliardo_univ_iff,
    gagliardoSq_univ_lt_top_iff hs0 hs1 u hu,
    and_iff_right huReal]

end SobolevSpace.Fractional
