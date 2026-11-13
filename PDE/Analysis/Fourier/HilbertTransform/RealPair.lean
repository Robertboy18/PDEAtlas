/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform
public import PDE.Analysis.MeasureTheory.Lp.RealL2

/-!
# Real representatives of a spectral Hilbert pair

`IsHilbertPair f g` says that the two real functions represent a complex `L²`
class and its Fourier-multiplier Hilbert transform. Equality is almost everywhere;
the definition makes no pointwise choice of representative.

Linearity, isometry and skew-adjointness pass to ordinary real integrals, and `H² = -1`
turns a pair `(ω, v)` into the pair `(v, -ω)` (`IsHilbertPair.rotate`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Analysis

variable {omega v w : ℝ → ℝ}

/-- `v` represents the Hilbert transform of `ω` in the concrete complex `L²` model.
The existential witness is an `L²` class representing `ω`, not a choice of operator. -/
def IsHilbertPair (ω v : ℝ → ℝ) : Prop :=
  ∃ f : ComplexL2,
    (fun x ↦ (ω x : ℂ)) =ᵐ[volume] f ∧
      (fun x ↦ (v x : ℂ)) =ᵐ[volume] hilbertTransform f

/-- Changing a real output representative on a null set preserves the Hilbert relation. -/
theorem IsHilbertPair.congr_right_ae {f g h : ℝ → ℝ}
    (hp : IsHilbertPair f g) (heq : g =ᵐ[volume] h) : IsHilbertPair f h := by
  obtain ⟨F, hF, hG⟩ := hp
  refine ⟨F, hF, ?_⟩
  filter_upwards [hG, heq] with x hx he
  simpa only [← he] using hx

/-- A square-integrable function and a real representative of its Fourier Hilbert transform
give a Hilbert pair. This is the interface for a principal-value identification theorem. -/
theorem IsHilbertPair.of_memLp
    {ω v : ℝ → ℝ}
    (hω : MemLp (fun x ↦ (ω x : ℂ)) 2 (volume : Measure ℝ))
    (hv : (fun x ↦ (v x : ℂ)) =ᵐ[volume]
      hilbertTransform (hω.toLp (fun x ↦ (ω x : ℂ)))) :
    IsHilbertPair ω v :=
  ⟨hω.toLp _, hω.coeFn_toLp.symm, hv⟩

/-- The input of a Hilbert pair is square integrable as a real function. -/
theorem IsHilbertPair.memLp_left (h : IsHilbertPair omega v) :
    MemLp omega 2 (volume : Measure ℝ) := by
  obtain ⟨f, homega, _⟩ := h
  have hcomplex := (Lp.memLp f).ae_eq homega.symm
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
    Complex.reCLM.comp_memLp' hcomplex

/-- The real representative of the Hilbert transform is square integrable. -/
theorem IsHilbertPair.memLp_right (h : IsHilbertPair omega v) :
    MemLp v 2 (volume : Measure ℝ) := by
  obtain ⟨f, _, hv⟩ := h
  have hcomplex := (Lp.memLp (hilbertTransform f)).ae_eq hv.symm
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
    Complex.reCLM.comp_memLp' hcomplex

private theorem integral_sq_eq_norm_sq {g : ℝ → ℝ} {f : ComplexL2}
    (hf : (fun x ↦ (g x : ℂ)) =ᵐ[volume] f) :
    (∫ x, g x ^ 2) = ‖f‖ ^ 2 := by
  calc
    _ = ∫ x, (inner ℂ (f x) (f x)).re := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [← hx]
      change g x ^ 2 = RCLike.re (inner ℂ (g x : ℂ) (g x : ℂ))
      rw [inner_self_eq_norm_sq]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = (inner ℂ f f).re := by
      change (∫ x, RCLike.re (inner ℂ (f x) (f x))) = RCLike.re (inner ℂ f f)
      rw [integral_re (L2.integrable_inner (𝕜 := ℂ) f f), ← L2.inner_def]
    _ = _ := by
      change RCLike.re (inner ℂ f f) = ‖f‖ ^ 2
      exact inner_self_eq_norm_sq f

/-- Plancherel's identity for the Hilbert pair, expressed with ordinary
real integrals. Both integrands are integrable by the two `MemLp` lemmas. -/
theorem IsHilbertPair.integral_sq_eq (h : IsHilbertPair omega v) :
    (∫ x, v x ^ 2) = ∫ x, omega x ^ 2 := by
  obtain ⟨f, homega, hv⟩ := h
  rw [integral_sq_eq_norm_sq hv, integral_sq_eq_norm_sq homega, norm_hilbertTransform]

private theorem integral_eq_two_mul_integral_Ioi_of_even {g : ℝ → ℝ}
    (hg : Function.Even g) :
    (∫ x, g x) = 2 * ∫ x in Ioi 0, g x := by
  have habs : (fun x ↦ g |x|) = g := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hg x]
  rw [← integral_comp_abs, habs]

/-- Odd input and even output have equal square integrals on the
positive half-line. Reflection splits each global integral into two equal parts. -/
theorem IsHilbertPair.integral_sq_Ioi_eq (h : IsHilbertPair omega v)
    (homega : Function.Odd omega) (hv : Function.Even v) :
    (∫ x in Ioi 0, v x ^ 2) = ∫ x in Ioi 0, omega x ^ 2 := by
  have hvSq : Function.Even (fun x ↦ v x ^ 2) := by
    intro x
    change v (-x) ^ 2 = v x ^ 2
    rw [hv x]
  have homegaSq : Function.Even (fun x ↦ omega x ^ 2) := by
    intro x
    change omega (-x) ^ 2 = omega x ^ 2
    rw [homega x, neg_sq]
  have heq := h.integral_sq_eq
  rw [integral_eq_two_mul_integral_Ioi_of_even hvSq,
    integral_eq_two_mul_integral_Ioi_of_even homegaSq] at heq
  linarith

/-- Localization of Hilbert isometry depends on the parity of the squares. This
also covers even inputs and odd outputs, as needed after one division by `x`. -/
theorem IsHilbertPair.integral_sq_Ioo_le_of_even_sq
    {f v : ℝ → ℝ} {L : ℝ} (h : IsHilbertPair f v)
    (hf : Function.Even (fun x ↦ f x ^ 2))
    (hv : Function.Even (fun x ↦ v x ^ 2))
    (hsupport : ∀ x, L ≤ x → f x = 0) :
    (∫ x in Ioo 0 L, v x ^ 2) ≤ ∫ x in Ioo 0 L, f x ^ 2 := by
  have heq := h.integral_sq_eq
  rw [integral_eq_two_mul_integral_Ioi_of_even hf,
    integral_eq_two_mul_integral_Ioi_of_even hv] at heq
  have hmono : (∫ x in Ioo 0 L, v x ^ 2) ≤ ∫ x in Ioi 0, v x ^ 2 :=
    setIntegral_mono_set h.memLp_right.integrable_sq.integrableOn
      (.of_forall fun x ↦ sq_nonneg (v x)) (.of_forall fun _ hx ↦ hx.1)
  have htruncate : (∫ x in Ioi 0, f x ^ 2) = ∫ x in Ioo 0 L, f x ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hx ↦ hx.1)
    intro x hx
    rw [hsupport x (not_lt.mp fun hlt ↦ hx.2 ⟨hx.1, hlt⟩), zero_pow (by decide : 2 ≠ 0)]
  rw [htruncate] at heq
  linarith

/-- Restricting the Hilbert transform to the input's support decreases its
square integral. Oddness and evenness allow the comparison on the positive half
of the support. -/
theorem IsHilbertPair.integral_sq_Ioo_le (h : IsHilbertPair omega v)
    {L : ℝ} (homega : Function.Odd omega) (hv : Function.Even v)
    (hsupport : ∀ x, L ≤ x → omega x = 0) :
    (∫ x in Ioo 0 L, v x ^ 2) ≤ ∫ x in Ioo 0 L, omega x ^ 2 := by
  apply h.integral_sq_Ioo_le_of_even_sq _ _ hsupport
  · intro x
    dsimp only
    rw [homega x, neg_sq]
  · intro x
    dsimp only
    rw [hv x]

/-- The concrete Hilbert isometry preserves the real extended `L²` seminorm. -/
theorem IsHilbertPair.eLpNorm_eq (h : IsHilbertPair omega v) :
    eLpNorm v 2 volume = eLpNorm omega 2 volume := by
  have hleft := h.memLp_left
  have hright := h.memLp_right
  obtain ⟨f, homega, hv⟩ := h
  have hnorm {g : ℝ → ℝ} (hg : MemLp g 2 volume) (F : ComplexL2)
      (hF : (fun x ↦ (g x : ℂ)) =ᵐ[volume] F) :
      eLpNorm g 2 volume = ‖F‖ₑ := by
    rw [Lp.enorm_def]
    apply eLpNorm_congr_norm_ae hg.aestronglyMeasurable (Lp.aestronglyMeasurable F)
    filter_upwards [hF] with x hx
    rw [← hx]
    simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm hright _ hv, hnorm hleft _ homega, hilbertTransform.enorm_map]

/-- Two real representatives of the Hilbert transform of the same input agree
almost everywhere. -/
theorem IsHilbertPair.ae_eq_right (hv : IsHilbertPair omega v)
    (hw : IsHilbertPair omega w) : v =ᵐ[volume] w := by
  obtain ⟨f, hf, hv⟩ := hv
  obtain ⟨g, hg, hw⟩ := hw
  have hfg : f = g := Lp.ext (hf.symm.trans hg)
  subst g
  filter_upwards [hv, hw] with x hx hy
  exact Complex.ofReal_injective (hx.trans hy.symm)

/-- Multiplying both real representatives by the same scalar preserves a Hilbert pair. -/
theorem IsHilbertPair.const_mul {ω v : ℝ → ℝ} (h : IsHilbertPair ω v) (a : ℝ) :
    IsHilbertPair (fun x ↦ a * ω x) (fun x ↦ a * v x) := by
  obtain ⟨f, hω, hv⟩ := h
  refine ⟨(a : ℂ) • f, ?_, ?_⟩
  · filter_upwards [hω, MeasureTheory.Lp.coeFn_smul (a : ℂ) f] with x hx hsmul
    simpa only [Complex.ofReal_mul, hx, Pi.smul_apply, smul_eq_mul] using hsmul.symm
  · rw [map_smul]
    filter_upwards [hv, MeasureTheory.Lp.coeFn_smul (a : ℂ)
      (PDE.Analysis.hilbertTransform f)] with x hx hsmul
    simpa only [Complex.ofReal_mul, hx, Pi.smul_apply, smul_eq_mul] using hsmul.symm

/-- Since `H² = -1`, the Hilbert transform of `v` is `-ω` when `v` is the Hilbert transform of
`ω`: the pair `(ω, v)` rotates to `(v, -ω)`. -/
theorem IsHilbertPair.rotate {ω v : ℝ → ℝ} (h : IsHilbertPair ω v) :
    IsHilbertPair v (fun x ↦ -ω x) := by
  obtain ⟨F, hω, hv⟩ := h
  refine ⟨hilbertTransform F, hv, ?_⟩
  rw [hilbertTransform_sq]
  filter_upwards [hω, Lp.coeFn_neg F] with x hx hneg
  rw [hneg, Pi.neg_apply, ← hx, Complex.ofReal_neg]

/-- Subtraction preserves the concrete spectral Hilbert relation. -/
theorem IsHilbertPair.sub {f g u v : ℝ → ℝ}
    (hf : IsHilbertPair f u) (hg : IsHilbertPair g v) :
    IsHilbertPair (f - g) (u - v) := by
  obtain ⟨F, hF, hu⟩ := hf
  obtain ⟨G, hG, hv⟩ := hg
  refine ⟨F - G, ?_, ?_⟩
  · filter_upwards [hF, hG, Lp.coeFn_sub F G] with x hx hy hsub
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    rw [hsub, Pi.sub_apply, hx, hy]
  · rw [map_sub]
    filter_upwards [hu, hv,
      Lp.coeFn_sub (PDE.Analysis.hilbertTransform F) (PDE.Analysis.hilbertTransform G)]
      with x hx hy hsub
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    rw [hsub, Pi.sub_apply, hx, hy]

/-- Skew-adjointness for ordinary real integrals of two concrete spectral Hilbert pairs. -/
theorem IsHilbertPair.integral_mul_skew {f g Hf Hg : ℝ → ℝ}
    (hf : IsHilbertPair f Hf) (hg : IsHilbertPair g Hg) :
    (∫ x, Hf x * g x) = -∫ x, f x * Hg x := by
  obtain ⟨F, hf, hF⟩ := hf
  obtain ⟨G, hg, hG⟩ := hg
  rw [integral_mul_eq_re_inner hF hg, integral_mul_eq_re_inner hf hG,
    inner_hilbertTransform_left, Complex.neg_re]

end PDE.Analysis
