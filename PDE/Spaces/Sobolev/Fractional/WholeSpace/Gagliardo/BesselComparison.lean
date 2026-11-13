/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.GraphNorm
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The Bessel norm and the Gagliardo seminorm on `ℝ^n`

Let `1 ≤ n`, `0 < s < 1` and `C = gagliardoFourierConstant n s hn`. Every `u ∈ H^s(ℝ^n)` with
`L²` representative `f = toL2Fun hs u` satisfies

`‖u‖² ≤ ‖f‖₂² + C⁻¹ gagDouble n s f ≤ 2 ‖u‖²`.

The proof combines the Gagliardo-Fourier identity `gagDouble_eq_gagJ_mul_fourierSq` with the
weight bounds `(1 + r²)^s ≤ 1 + r^(2s) ≤ 2 (1 + r²)^s` for `0 ≤ s ≤ 1` and `r ≥ 0`. The upper
bound uses only `0 ≤ s`.

The Gagliardo double integral is finite on `H^s(ℝ^n)`, on Schwartz functions and on smooth
compactly supported functions, and a smooth bump gives a real function on `ℝ^n` whose
Gagliardo seminorm is positive and finite. The identification of the complete real Gagliardo
space on `ℝ^n` with `H^s(ℝ^n; ℝ)` is `GagliardoSpace.equivHsSpaceReal`.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, "Hitchhiker's guide to the fractional Sobolev spaces",
  *Bull. Sci. Math.* 136 (2012), 521-573, numbering of arXiv:1104.4345v3, Proposition 3.4, the
  Gagliardo-Fourier identity `[u]²_{H^s} = 2 C(n, s)⁻¹ ∫ |ξ|^{2s} |𝓕u(ξ)|² dξ` for `s ∈ (0, 1)`, in
  their Fourier convention.
  <https://arxiv.org/abs/1104.4345v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace ENNReal FourierTransform SchwartzMap ContDiff

namespace SobolevSpace.Fractional

section Symbol

variable {r s : ℝ}

/-- For `0 ≤ s ≤ 1` and `r ≥ 0`, `(1 + r²)^s ≤ 1 + r^(2s)`. -/
theorem besselSymbol_sq_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 ≤ r) :
    (1 + r ^ 2 : ℝ) ^ s ≤ 1 + r ^ (2 * s) := by
  have h := Real.rpow_add_le_add_rpow (a := (1 : ℝ)) (b := r ^ 2) zero_le_one
    (sq_nonneg r) hs0 hs1
  rw [Real.one_rpow] at h
  rw [Real.rpow_mul hr, Real.rpow_two]
  exact h

/-- For `0 ≤ s`, `1 ≤ (1 + r²)^s`. -/
theorem one_le_besselSymbol_sq (hs0 : 0 ≤ s) (r : ℝ) : (1 : ℝ) ≤ (1 + r ^ 2 : ℝ) ^ s :=
  Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg r)) hs0

/-- For `0 ≤ s` and `r ≥ 0`, `r^(2s) ≤ (1 + r²)^s`. -/
theorem rpow_two_mul_le_besselSymbol_sq (hs0 : 0 ≤ s) (hr : 0 ≤ r) :
    r ^ (2 * s) ≤ (1 + r ^ 2 : ℝ) ^ s := by
  rw [Real.rpow_mul hr, Real.rpow_two]
  exact Real.rpow_le_rpow (sq_nonneg r) (le_add_of_nonneg_left zero_le_one) hs0

/-- For `0 ≤ s` and `r ≥ 0`, `1 + r^(2s) ≤ 2 (1 + r²)^s`. -/
theorem add_rpow_le_two_mul_besselSymbol_sq (hs0 : 0 ≤ s) (hr : 0 ≤ r) :
    1 + r ^ (2 * s) ≤ 2 * (1 + r ^ 2 : ℝ) ^ s := by
  have h1 := one_le_besselSymbol_sq hs0 r
  have h2 := rpow_two_mul_le_besselSymbol_sq hs0 hr
  linarith

end Symbol

variable {n : ℕ} {s : ℝ}

private theorem lintegral_ofReal_weight_mul_mono {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {v₁ v₂ : α → ℝ} {G : α → ℝ≥0∞} (h : ∀ x, v₁ x ≤ v₂ x) :
    ∫⁻ x, ENNReal.ofReal (v₁ x) * G x ∂μ ≤ ∫⁻ x, ENNReal.ofReal (v₂ x) * G x ∂μ :=
  lintegral_mono fun x ↦ mul_le_mul_left (ENNReal.ofReal_le_ofReal (h x)) _

private theorem lintegral_enorm_sq_eq_ofReal_norm_sq (w : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ∫⁻ ξ, ‖(w : ℝ^n → ℂ) ξ‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := by
  calc ∫⁻ ξ, ‖(w : ℝ^n → ℂ) ξ‖ₑ ^ 2 = eLpNorm (w : ℝ^n → ℂ) 2 volume ^ 2 := by
        simpa [ENNReal.rpow_two] using
          (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
            (Lp.aestronglyMeasurable w)).symm
    _ = ENNReal.ofReal (‖w‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
          ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

private theorem lintegral_one_add_mul_enorm_sq (w : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ∫⁻ ξ, ENNReal.ofReal (1 + ‖ξ‖ ^ (2 * s)) * ‖(w : ℝ^n → ℂ) ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖w‖ ^ 2) + fourierSq n s w := by
  have hG : AEMeasurable (fun ξ ↦ ‖(w : ℝ^n → ℂ) ξ‖ₑ ^ 2) volume :=
    (Lp.aestronglyMeasurable w).enorm.pow_const 2
  calc ∫⁻ ξ, ENNReal.ofReal (1 + ‖ξ‖ ^ (2 * s)) * ‖(w : ℝ^n → ℂ) ξ‖ₑ ^ 2
      = ∫⁻ ξ, ‖(w : ℝ^n → ℂ) ξ‖ₑ ^ 2 +
          ENNReal.ofReal (‖ξ‖ ^ (2 * s)) * ‖(w : ℝ^n → ℂ) ξ‖ₑ ^ 2 := by
        refine lintegral_congr fun ξ ↦ ?_
        rw [ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg (norm_nonneg ξ) _),
          ENNReal.ofReal_one, add_mul, one_mul]
    _ = ENNReal.ofReal (‖w‖ ^ 2) + fourierSq n s w := by
        rw [lintegral_add_left' hG, lintegral_enorm_sq_eq_ofReal_norm_sq w, fourierSq]

/-- The squared modulus of the Bessel symbol is `(1 + ‖ξ‖²)^s`. -/
theorem enorm_besselSymbol_sq (ξ : ℝ^n) :
    ‖besselSymbol n s ξ‖ₑ ^ 2 = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s) := by
  have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have hnn : (0 : ℝ) ≤ (1 + ‖ξ‖ ^ 2 : ℝ) ^ (s / 2) := Real.rpow_nonneg hpos.le _
  have hsq : ((1 + ‖ξ‖ ^ 2 : ℝ) ^ (s / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2 : ℝ) ^ s := by
    rw [← Real.rpow_two ((1 + ‖ξ‖ ^ 2 : ℝ) ^ (s / 2)), ← Real.rpow_mul hpos.le]
    congr 1
    ring
  have hb : ‖besselSymbol n s ξ‖ = (1 + ‖ξ‖ ^ 2 : ℝ) ^ (s / 2) := by
    rw [besselSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [← ofReal_norm, hb, ← ENNReal.ofReal_pow hnn, hsq]

/-- For `0 ≤ s`, the squared Bessel norm is the Fourier integral of the `L²`
representative against the weight `(1 + ‖ξ‖²)^s`. -/
theorem norm_sq_eq_lintegral (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    ENNReal.ofReal (‖u‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s) *
        ‖(𝓕 (toL2Fun hs u) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := by
  rw [← norm_fourier_toLp_eq u, ← lintegral_enorm_sq_eq_ofReal_norm_sq]
  refine lintegral_congr_ae ?_
  filter_upwards [coeFn_fourier_toLp hs u] with ξ hξ
  rw [hξ, enorm_mul, mul_pow, enorm_besselSymbol_sq]

/-- For `0 ≤ s ≤ 1`, the squared Bessel norm is at most the squared `L²` norm of the
representative plus its homogeneous Fourier integral `fourierSq`. -/
theorem ofReal_norm_sq_le_add_fourierSq (hs : 0 ≤ s) (hs1 : s ≤ 1) (u : H^{s}(ℝ^n)) :
    ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal (‖toL2Fun hs u‖ ^ 2) +
      fourierSq n s (𝓕 (toL2Fun hs u) : Lp ℂ 2 volume) := by
  rw [norm_sq_eq_lintegral hs u, ← Lp.norm_fourier_eq (toL2Fun hs u),
    ← lintegral_one_add_mul_enorm_sq]
  exact lintegral_ofReal_weight_mul_mono fun ξ ↦ besselSymbol_sq_le hs hs1 (norm_nonneg ξ)

/-- For `0 ≤ s`, the squared `L²` norm of the representative plus its homogeneous Fourier
integral is at most twice the squared Bessel norm. -/
theorem add_fourierSq_le_two_mul_norm_sq (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    ENNReal.ofReal (‖toL2Fun hs u‖ ^ 2) + fourierSq n s (𝓕 (toL2Fun hs u) : Lp ℂ 2 volume) ≤
      2 * ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [fourierSq_eq_norm_homogeneousFourierLp_sq hs u, two_mul]
  exact add_le_add
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_toL2Fun_le hs u) 2))
    (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (norm_homogeneousFourierLp_le hs u) 2))

/-- For `1 ≤ n` and `0 < s < 1`, with `C = gagliardoFourierConstant n s hn` and `f` the `L²`
representative of `u ∈ H^s(ℝ^n)`, `‖u‖² ≤ ‖f‖₂² + C⁻¹ gagDouble n s f ≤ 2 ‖u‖²`. -/
theorem norm_sq_two_sided_gagDouble (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : H^{s}(ℝ^n)) :
    ENNReal.ofReal (‖u‖ ^ 2) ≤
        ENNReal.ofReal (‖toL2Fun hs0.le u‖ ^ 2) +
          ENNReal.ofReal (gagliardoFourierConstant n s hn)⁻¹ *
            gagDouble n s (toL2Fun hs0.le u : ℝ^n → ℂ) ∧
      ENNReal.ofReal (‖toL2Fun hs0.le u‖ ^ 2) +
          ENNReal.ofReal (gagliardoFourierConstant n s hn)⁻¹ *
            gagDouble n s (toL2Fun hs0.le u : ℝ^n → ℂ) ≤
        2 * ENNReal.ofReal (‖u‖ ^ 2) := by
  have hC0 := gagliardoFourierConstant_pos hn hs0 hs1
  have hC : GagliardoKernel.gagJ n s (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)) =
      gagliardoFourierConstant n s hn := rfl
  have key : ENNReal.ofReal (gagliardoFourierConstant n s hn)⁻¹ *
      gagDouble n s (toL2Fun hs0.le u : ℝ^n → ℂ) =
        fourierSq n s (𝓕 (toL2Fun hs0.le u) : Lp ℂ 2 volume) := by
    rw [gagDouble_eq_gagJ_mul_fourierSq hs0 hs1 (e := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))
      (by simp) (toL2Fun hs0.le u), hC, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hC0.le), inv_mul_cancel₀ hC0.ne',
      ENNReal.ofReal_one, one_mul]
  rw [key]
  exact ⟨ofReal_norm_sq_le_add_fourierSq hs0.le hs1.le u,
    add_fourierSq_le_two_mul_norm_sq hs0.le u⟩

/-- The comparison `norm_sq_two_sided_gagDouble` in the form `N / 2 ≤ ‖u‖² ≤ N`, where
`N = ‖f‖₂² + C⁻¹ gagDouble n s f`. -/
theorem norm_sq_two_sided_gagDouble_div_two (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : H^{s}(ℝ^n)) :
    (ENNReal.ofReal (‖toL2Fun hs0.le u‖ ^ 2) +
          ENNReal.ofReal (gagliardoFourierConstant n s hn)⁻¹ *
            gagDouble n s (toL2Fun hs0.le u : ℝ^n → ℂ)) / 2 ≤
        ENNReal.ofReal (‖u‖ ^ 2) ∧
      ENNReal.ofReal (‖u‖ ^ 2) ≤
        ENNReal.ofReal (‖toL2Fun hs0.le u‖ ^ 2) +
          ENNReal.ofReal (gagliardoFourierConstant n s hn)⁻¹ *
            gagDouble n s (toL2Fun hs0.le u : ℝ^n → ℂ) := by
  have h := norm_sq_two_sided_gagDouble hn hs0 hs1 u
  exact ⟨ENNReal.div_le_of_le_mul' h.2, h.1⟩

/-- For `0 < s < 1`, the `L²` representative of every `u ∈ H^s(ℝ^n)` has finite Gagliardo
double integral. -/
theorem gagDouble_toL2Fun_lt_top (hs0 : 0 < s) (hs1 : s < 1) (u : H^{s}(ℝ^n)) :
    gagDouble n s (toL2Fun hs0.le u : ℝ^n → ℂ) < ⊤ := by
  refine (gagDouble_lt_top_iff hs0 hs1 (toL2Fun hs0.le u)).2 ?_
  rw [fourierSq_eq_norm_homogeneousFourierLp_sq]
  exact ENNReal.ofReal_lt_top

/-- For `0 < s < 1`, every Schwartz function on `ℝ^n` has finite Gagliardo double
integral. -/
theorem gagDouble_schwartz_lt_top (hs0 : 0 < s) (hs1 : s < 1) (φ : 𝓢(ℝ^n, ℂ)) :
    gagDouble n s (φ : ℝ^n → ℂ) < ⊤ := by
  have h := gagDouble_toL2Fun_lt_top hs0 hs1
    (SchwartzMap.memSobolev (s := s) φ).toBesselPotentialSpace
  rw [toL2Fun_ofSchwartz hs0.le φ] at h
  rwa [gagDouble_congr (s := s) (SchwartzMap.coeFn_toLp φ 2 volume)] at h

/-- `gagDouble_schwartz_lt_top` written as the explicit double integral over `ℝ^n × ℝ^n`. -/
theorem lintegral_schwartz_diffQuot_lt_top (hs0 : 0 < s) (hs1 : s < 1) (φ : 𝓢(ℝ^n, ℂ)) :
    (∫⁻ p : (ℝ^n) × (ℝ^n), ENNReal.ofReal
        (‖φ p.1 - φ p.2‖ ^ 2 / ‖p.1 - p.2‖ ^ ((n : ℝ) + 2 * s))) < ⊤ := by
  rw [Measure.volume_eq_prod]
  exact gagDouble_schwartz_lt_top hs0 hs1 φ

/-- For `0 < s < 1`, a real function on `ℝ^n` whose complexification is a Schwartz function
has finite Gagliardo seminorm on `ℝ^n`. -/
theorem gagliardoSq_univ_lt_top_of_schwartz (hs0 : 0 < s) (hs1 : s < 1)
    (v : ℝ^n → ℝ) (φ : 𝓢(ℝ^n, ℂ)) (hv : ∀ x, ((v x : ℝ) : ℂ) = φ x) :
    gagliardoSq n s Set.univ v < ⊤ := by
  rw [gagliardoSq_univ_eq_gagDouble,
    gagDouble_congr (s := s) (Filter.Eventually.of_forall hv)]
  exact gagDouble_schwartz_lt_top hs0 hs1 φ

/-- For `0 < s < 1`, every smooth compactly supported real function on `ℝ^n` has finite
Gagliardo seminorm on `ℝ^n`. -/
theorem gagliardoSq_univ_lt_top_of_hasCompactSupport (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℝ^n → ℝ} (hcs : HasCompactSupport v) (hsm : ContDiff ℝ ∞ v) :
    gagliardoSq n s Set.univ v < ⊤ :=
  gagliardoSq_univ_lt_top_of_schwartz hs0 hs1 v
    ((hcs.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hsm)) fun _ ↦ rfl

/-- For `1 ≤ n`, there is a smooth compactly supported real function on `ℝ^n` that is not
constant. -/
theorem exists_nonconstant_contDiff_hasCompactSupport (hn : 1 ≤ n) :
    ∃ v : ℝ^n → ℝ, (∃ x y : ℝ^n, v x ≠ v y) ∧ HasCompactSupport v ∧ ContDiff ℝ ∞ v := by
  obtain ⟨f, hrIn, hrOut⟩ : ∃ f : ContDiffBump (0 : ℝ^n), f.rIn = 1 ∧ f.rOut = 2 :=
    ⟨⟨1, 2, by norm_num, by norm_num⟩, rfl, rfl⟩
  set e : ℝ^n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (2 : ℝ) with he
  refine ⟨(f : ℝ^n → ℝ), ⟨0, e, ?_⟩, f.hasCompactSupport, f.contDiff⟩
  have h1 : f 0 = 1 := f.one_of_mem_closedBall (by simp [hrIn])
  have h2 : f e = 0 := by
    refine f.zero_of_le_dist ?_
    rw [dist_zero_right, he, PiLp.norm_single, hrOut]
    norm_num
  rw [h1, h2]
  norm_num

/-- For `1 ≤ n` and `0 < s < 1`, some non-constant real function on `ℝ^n` has Gagliardo
seminorm on `ℝ^n` that is positive and finite. -/
theorem exists_gagliardoSq_univ_pos_lt_top (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ v : ℝ^n → ℝ, (∃ x y : ℝ^n, v x ≠ v y) ∧
      0 < gagliardoSq n s Set.univ v ∧ gagliardoSq n s Set.univ v < ⊤ := by
  obtain ⟨v, hne, hcs, hsm⟩ := exists_nonconstant_contDiff_hasCompactSupport (n := n) hn
  exact ⟨v, hne, gagliardoSq_univ_pos hsm.continuous hne,
    gagliardoSq_univ_lt_top_of_hasCompactSupport hs0 hs1 hcs hsm⟩

end SobolevSpace.Fractional
