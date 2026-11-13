/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarDecay
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarVector
public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple
public import PDE.Analysis.Fourier.Schwartz.Euler

/-!
# Tested identity of free self-similar heat evolution

The free self-similar evolution `S₀(s) g = a (e^{σΔ} g)(a ·)`, with `a = e^{s/2}` and
`σ = e^s - 1`, has the generator `L₀ = Δ + ½ ξ·∇ + ½`. Its formal adjoint is
`L₀^† φ = Δφ - ½ ξ·∇φ + ½ (1 - n) φ`. For every `L²` field `g` and every smooth compactly
supported test field `φ`,
`⟪S₀(t) g, φ⟫ - ⟪g, φ⟫ = ∫₀ᵗ ⟪S₀(s) g, L₀^† φ⟫ ds`.

The proof is on the Fourier side. For a Schwartz function `φ` the pairing is the integral
`⟪φ, S₀(s) g⟫ = ∫ conj(a e^{-4π²σ|k|²} φ̂(a k)) ĝ(k) dk`, in which the evolution acts on `φ̂`.
Its time derivative is the same integral with `φ̂` replaced by the adjoint symbol
`(½ - 4π²|k|²) φ̂ + ½ k·∇φ̂`, which is the Fourier transform of `L₀^† φ`. Fubini and the
fundamental theorem of calculus give the identity, and the real vector form follows through
the complexified components. A real test field is the vector `L²` field `vectorOfMemLp f` of
its components, and also the vector `H¹` field `testVectorH1 f`; forgetting the derivatives of
the second gives the first.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory FourierTransform SchwartzMap Set PDE.Analysis.Fourier LineDeriv Laplacian
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Real ComplexConjugate Sobolev

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- The Fourier-side action of free self-similar evolution at real time `s` on a function `F`
of the frequency: `a e^{-4π²σ|k|²} F(a k)` with `a = e^{s/2}` and `σ = e^s - 1`. -/
def selfsimilarTestSymbol (F : ℝ^n → ℂ) (s : ℝ) (k : ℝ^n) : ℂ :=
  (Real.exp (s / 2) : ℂ) * (Real.exp (-(4 * π ^ 2 * (Real.exp s - 1) * ‖k‖ ^ 2)) : ℂ) *
    F (Real.exp (s / 2) • k)

/-- Pairing a Schwartz function with free self-similar evolution moves the evolution onto the
Fourier transform of the test function. -/
theorem inner_toLp_selfsimilarHeat_eq_integral (φ : 𝓢(ℝ^n, ℂ)) (τ : ℝ≥0)
    (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    inner ℂ (φ.toLp 2) (selfsimilarFactor τ • Lp.compSMul volume 2 (selfsimilarFactor τ)
        (selfsimilarFactor_pos τ).ne' (heatL2 n (selfsimilarHeatTime τ) g)) =
      ∫ k, conj (selfsimilarTestSymbol (⇑(𝓕 φ : 𝓢(ℝ^n, ℂ))) τ k) *
        ((𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) k := by
  set a := selfsimilarFactor τ with ha_def
  have ha : 0 < a := selfsimilarFactor_pos τ
  set h : Lp ℂ 2 (volume : Measure (ℝ^n)) := heatSymbolLinf n (selfsimilarHeatTime τ) • 𝓕 g
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    ← (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).inner_map_map]
  change (a : ℂ) * inner ℂ (𝓕 (φ.toLp 2)) (𝓕 (Lp.compSMul volume 2 a ha.ne'
    (heatL2 n (selfsimilarHeatTime τ) g))) = _
  rw [SchwartzMap.toLp_fourier_eq, fourier_compSMul, fourier_heatL2,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, L2.inner_def]
  have h1 : (fun k ↦ inner ℂ ((((𝓕 φ).toLp 2 volume : Lp ℂ 2 volume) : ℝ^n → ℂ) k)
      (((Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') h : Lp ℂ 2 volume) : ℝ^n → ℂ) k)) =ᵐ[volume]
      fun k ↦ conj ((𝓕 φ : 𝓢(ℝ^n, ℂ)) k) * (h : ℝ^n → ℂ) (a⁻¹ • k) := by
    filter_upwards [(𝓕 φ).coeFn_toLp 2 volume,
      Lp.coeFn_compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') h] with k hk1 hk2
    rw [hk1, hk2]
    simp only [RCLike.inner_apply]
    ring
  rw [integral_congr_ae h1]
  have h2 := Measure.integral_comp_smul (volume : Measure (ℝ^n))
    (fun k ↦ conj ((𝓕 φ : 𝓢(ℝ^n, ℂ)) k) * (h : ℝ^n → ℂ) (a⁻¹ • k)) a
  simp only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h2
  have h3 : (fun k ↦ conj ((𝓕 φ : 𝓢(ℝ^n, ℂ)) (a • k)) * (h : ℝ^n → ℂ) k) =ᵐ[volume]
      fun k ↦ conj ((𝓕 φ : 𝓢(ℝ^n, ℂ)) (a • k)) * (heatSymbol n (selfsimilarHeatTime τ) k *
        ((𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) k) := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n (selfsimilarHeatTime τ)) (𝓕 g),
      (memLp_top_heatSymbol (n := n) (selfsimilarHeatTime τ)).coeFn_toLp] with k hk1 hk2
    rw [hk1]
    simp only [smul_eq_mul, Pi.mul_apply]
    rw [show (heatSymbolLinf n (selfsimilarHeatTime τ) : ℝ^n → ℂ) k =
      heatSymbol n (selfsimilarHeatTime τ) k from hk2]
  have h2' : ((|(a ^ Module.finrank ℝ (ℝ^n))⁻¹| : ℝ) : ℂ) *
      ∫ k, conj ((𝓕 φ : 𝓢(ℝ^n, ℂ)) k) * (h : ℝ^n → ℂ) (a⁻¹ • k) =
      ∫ x, conj ((𝓕 φ : 𝓢(ℝ^n, ℂ)) (a • x)) * (h : ℝ^n → ℂ) x := by
    rw [h2, Complex.real_smul]
  change (a : ℂ) * (((|(a ^ Module.finrank ℝ (ℝ^n))⁻¹| : ℝ) : ℂ) *
    ∫ k, conj ((𝓕 φ : 𝓢(ℝ^n, ℂ)) k) * (h : ℝ^n → ℂ) (a⁻¹ • k)) = _
  rw [h2', integral_congr_ae h3, ← integral_const_mul]
  congr 1
  funext k
  simp only [selfsimilarTestSymbol, heatSymbol, coe_selfsimilarHeatTime, map_mul,
    Complex.conj_ofReal]
  rw [ha_def, selfsimilarFactor]
  ring

/-- The Fourier symbol of the formal adjoint `L₀^† φ = Δφ - ½ ξ·∇φ + ½ (1 - n) φ` of the free
self-similar generator: `(½ - 4π²|k|²) F(k) + ½ k·∇F(k)`. -/
def selfsimilarAdjointSymbol (F : ℝ^n → ℂ) (k : ℝ^n) : ℂ :=
  ((1 / 2 : ℝ) - 4 * π ^ 2 * ‖k‖ ^ 2 : ℝ) * F k + (1 / 2 : ℂ) * fderiv ℝ F k k

/-- The Fourier-side action of free self-similar evolution is differentiable in time, with the
adjoint symbol as derivative. -/
theorem hasDerivAt_selfsimilarTestSymbol {F : ℝ^n → ℂ} (hF : Differentiable ℝ F)
    (s : ℝ) (k : ℝ^n) :
    HasDerivAt (fun s ↦ selfsimilarTestSymbol F s k)
      (selfsimilarTestSymbol (selfsimilarAdjointSymbol F) s k) s := by
  have ha : HasDerivAt (fun s : ℝ ↦ Real.exp (s / 2)) (Real.exp (s / 2) * (1 / 2)) s :=
    ((hasDerivAt_id s).div_const 2).exp
  have hE : HasDerivAt (fun s : ℝ ↦ Real.exp (-(4 * π ^ 2 * (Real.exp s - 1) * ‖k‖ ^ 2)))
      (Real.exp (-(4 * π ^ 2 * (Real.exp s - 1) * ‖k‖ ^ 2)) *
        (-(4 * π ^ 2 * Real.exp s * ‖k‖ ^ 2))) s :=
    ((((Real.hasDerivAt_exp s).sub_const 1).const_mul (4 * π ^ 2)).mul_const (‖k‖ ^ 2)).neg.exp
  have hpath : HasDerivAt (fun s : ℝ ↦ Real.exp (s / 2) • k)
      ((Real.exp (s / 2) * (1 / 2)) • k) s := ha.smul_const k
  have hFc : HasDerivAt (fun s : ℝ ↦ F (Real.exp (s / 2) • k))
      (fderiv ℝ F (Real.exp (s / 2) • k) ((Real.exp (s / 2) * (1 / 2)) • k)) s :=
    (hF _).hasFDerivAt.comp_hasDerivAt s hpath
  have hprod := ((ha.ofReal_comp).mul (hE.ofReal_comp)).mul hFc
  have hfun : (fun s ↦ selfsimilarTestSymbol F s k) =
      ((fun y : ℝ ↦ (Real.exp (y / 2) : ℂ)) *
        fun y : ℝ ↦ (Real.exp (-(4 * π ^ 2 * (Real.exp y - 1) * ‖k‖ ^ 2)) : ℂ)) *
        fun s ↦ F (Real.exp (s / 2) • k) :=
    rfl
  rw [hfun]
  convert hprod using 1
  have hsq : Real.exp (s / 2) ^ 2 = Real.exp s := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hnorm : ‖Real.exp (s / 2) • k‖ ^ 2 = Real.exp s * ‖k‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, hsq]
  have hlin : fderiv ℝ F (Real.exp (s / 2) • k) ((Real.exp (s / 2) * (1 / 2)) • k) =
      ((1 / 2 : ℝ) : ℂ) * fderiv ℝ F (Real.exp (s / 2) • k) (Real.exp (s / 2) • k) := by
    rw [show (Real.exp (s / 2) * (1 / 2)) • k = (1 / 2 : ℝ) • (Real.exp (s / 2) • k) by
      rw [smul_smul, mul_comm], ContinuousLinearMap.map_smul, Complex.real_smul]
  simp only [selfsimilarTestSymbol, selfsimilarAdjointSymbol, hnorm, Pi.mul_apply, hlin]
  push_cast
  ring

/-- A Schwartz function decays faster than every power. -/
theorem SchwartzMap.exists_norm_le_one_add_norm_rpow (H : 𝓢(ℝ^n, ℂ)) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ y, ‖H y‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ)) := by
  refine ⟨2 ^ N * ((Finset.Iic (N, 0)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) H,
    by positivity, fun y ↦ ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) le_rfl le_rfl H y
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖y‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ hpos, mul_comm]
  exact h

/-- On times `0 ≤ s ≤ τ` the Fourier-side evolution of a Schwartz function keeps a uniform
polynomial decay. -/
theorem norm_selfsimilarTestSymbol_le {H : ℝ^n → ℂ} {C : ℝ} {N : ℕ}
    (hH : ∀ y, ‖H y‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ))) {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s ≤ τ)
    (k : ℝ^n) :
    ‖selfsimilarTestSymbol H s k‖ ≤ Real.exp (τ / 2) * C * (1 + ‖k‖) ^ (-(N : ℝ)) := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hH 0)
    rw [norm_zero, add_zero, Real.one_rpow, mul_one] at this
    exact this
  have ha : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
  have hnorm : ‖k‖ ≤ ‖Real.exp (s / 2) • k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact le_mul_of_one_le_left (norm_nonneg _) ha
  have hdecay : (1 + ‖Real.exp (s / 2) • k‖) ^ (-(N : ℝ)) ≤ (1 + ‖k‖) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
  have hE : ‖((Real.exp (-(4 * π ^ 2 * (Real.exp s - 1) * ‖k‖ ^ 2)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ Real.exp s - 1 := by linarith [Real.one_le_exp hs]
    have : 0 ≤ 4 * π ^ 2 * (Real.exp s - 1) * ‖k‖ ^ 2 := by positivity
    linarith
  have hA : ‖((Real.exp (s / 2) : ℝ) : ℂ)‖ ≤ Real.exp (τ / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [selfsimilarTestSymbol, norm_mul, norm_mul]
  calc
    _ ≤ Real.exp (τ / 2) * 1 * (C * (1 + ‖k‖) ^ (-(N : ℝ))) := by
      apply mul_le_mul (mul_le_mul hA hE (norm_nonneg _) (Real.exp_pos _).le)
        ((hH _).trans (mul_le_mul_of_nonneg_left hdecay hC)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The polynomial weight times an `L²` function is integrable once the weight is square
integrable. -/
theorem integrable_one_add_norm_rpow_mul {ĝ : ℝ^n → ℂ} (hĝ : MemLp ĝ 2 volume) :
    Integrable (fun k ↦ (1 + ‖k‖) ^ (-((n + 1 : ℕ) : ℝ)) * ‖ĝ k‖) volume := by
  have hw : MemLp (fun k : ℝ^n ↦ (1 + ‖k‖) ^ (-((n + 1 : ℕ) : ℝ))) 2 volume := by
    have hmeas : AEStronglyMeasurable (fun k : ℝ^n ↦ (1 + ‖k‖) ^ (-((n + 1 : ℕ) : ℝ))) volume :=
      ((by fun_prop : Continuous fun k : ℝ^n ↦ 1 + ‖k‖).rpow_const
        fun k ↦ Or.inl (by positivity)).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
    have hint := integrable_one_add_norm (E := ℝ^n) (μ := volume)
      (r := 2 * ((n + 1 : ℕ) : ℝ)) (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)
    refine hint.congr (Filter.Eventually.of_forall fun k ↦ ?_)
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    ring_nf
  exact hw.integrable_mul hĝ.norm

theorem continuous_selfsimilarTestSymbol {H : ℝ^n → ℂ} (hH : Continuous H) :
    Continuous (fun p : ℝ × ℝ^n ↦ selfsimilarTestSymbol H p.1 p.2) := by
  unfold selfsimilarTestSymbol
  fun_prop

/-- Paired against an `L²` function, the Fourier-side evolution of a Schwartz function is
integrable in the frequency. -/
theorem integrable_conj_selfsimilarTestSymbol_mul {H : ℝ^n → ℂ} (hHc : Continuous H) {C : ℝ}
    (hH : ∀ y, ‖H y‖ ≤ C * (1 + ‖y‖) ^ (-((n + 1 : ℕ) : ℝ))) {ĝ : ℝ^n → ℂ}
    (hĝ : MemLp ĝ 2 volume) {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s ≤ τ) :
    Integrable (fun k ↦ conj (selfsimilarTestSymbol H s k) * ĝ k) volume := by
  refine ((integrable_one_add_norm_rpow_mul hĝ).const_mul (Real.exp (τ / 2) * C)).mono' ?_ ?_
  · exact (Complex.continuous_conj.comp ((continuous_selfsimilarTestSymbol hHc).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable.mul hĝ.aestronglyMeasurable
  · filter_upwards with k
    rw [norm_mul, RCLike.norm_conj]
    calc
      _ ≤ (Real.exp (τ / 2) * C * (1 + ‖k‖) ^ (-((n + 1 : ℕ) : ℝ))) * ‖ĝ k‖ :=
        mul_le_mul_of_nonneg_right (norm_selfsimilarTestSymbol_le hH hs hsτ k) (norm_nonneg _)
      _ = _ := by ring

/-- The tested identity of free self-similar evolution on the Fourier side: if `G` is the
adjoint symbol of `F`, the time derivative of the Fourier pairing with `F` is the Fourier
pairing with `G`. -/
theorem integral_selfsimilarTestSymbol_sub_eq (F G : 𝓢(ℝ^n, ℂ))
    (hG : ∀ k, G k = selfsimilarAdjointSymbol (⇑F) k) {ĝ : ℝ^n → ℂ} (hĝ : MemLp ĝ 2 volume)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (∫ k, conj (selfsimilarTestSymbol (⇑F) τ k) * ĝ k) -
        ∫ k, conj (selfsimilarTestSymbol (⇑F) 0 k) * ĝ k =
      ∫ s in (0 : ℝ)..τ, ∫ k, conj (selfsimilarTestSymbol (⇑G) s k) * ĝ k := by
  obtain ⟨CF, -, hF⟩ := SchwartzMap.exists_norm_le_one_add_norm_rpow F (n + 1)
  obtain ⟨CG, -, hGd⟩ := SchwartzMap.exists_norm_le_one_add_norm_rpow G (n + 1)
  have hw := integrable_one_add_norm_rpow_mul hĝ
  have hfin : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) τ)) := by
    rw [uIoc_of_le hτ]
    exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hprod : Integrable (Function.uncurry fun s k ↦ conj (selfsimilarTestSymbol (⇑G) s k) * ĝ k)
      ((volume.restrict (uIoc 0 τ)).prod volume) := by
    refine ((integrable_const (1 : ℝ)).mul_prod
      (hw.const_mul (Real.exp (τ / 2) * CG))).mono' ?_ ?_
    · exact (Complex.continuous_conj.comp
        (continuous_selfsimilarTestSymbol G.continuous)).aestronglyMeasurable.mul
        hĝ.aestronglyMeasurable.comp_snd
    · filter_upwards [QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
          (ae_restrict_mem measurableSet_uIoc)] with p (hp : p.1 ∈ uIoc (0 : ℝ) τ)
      rw [uIoc_of_le hτ] at hp
      change ‖conj (selfsimilarTestSymbol (⇑G) p.1 p.2) * ĝ p.2‖ ≤
        1 * (Real.exp (τ / 2) * CG * ((1 + ‖p.2‖) ^ (-((n + 1 : ℕ) : ℝ)) * ‖ĝ p.2‖))
      rw [norm_mul, RCLike.norm_conj]
      exact (mul_le_mul_of_nonneg_right (norm_selfsimilarTestSymbol_le hGd hp.1.le hp.2 p.2)
        (norm_nonneg _)).trans_eq (by ring)
  have hGfun : selfsimilarTestSymbol (⇑G) =
      selfsimilarTestSymbol (selfsimilarAdjointSymbol (⇑F)) := by
    funext s k
    simp only [selfsimilarTestSymbol, hG]
  have hftc (k : ℝ^n) : ∫ s in (0 : ℝ)..τ, selfsimilarTestSymbol (⇑G) s k =
      selfsimilarTestSymbol (⇑F) τ k - selfsimilarTestSymbol (⇑F) 0 k := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s _
      rw [hGfun]
      exact hasDerivAt_selfsimilarTestSymbol F.differentiable s k
    · exact ((continuous_selfsimilarTestSymbol G.continuous).comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable 0 τ
  rw [intervalIntegral_integral_swap hprod,
    ← integral_sub (integrable_conj_selfsimilarTestSymbol_mul F.continuous hF hĝ hτ le_rfl)
      (integrable_conj_selfsimilarTestSymbol_mul F.continuous hF hĝ le_rfl hτ)]
  congr 1
  funext k
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le hτ, integral_conj,
    ← intervalIntegral.integral_of_le hτ, hftc, map_sub, sub_mul]

/-- The tested identity of free self-similar evolution on complex `L²`: if the Fourier
transform of `Ψ` is the adjoint symbol of the Fourier transform of `Φ`, then
`⟪Φ, S₀(τ) h⟫ - ⟪Φ, S₀(0) h⟫ = ∫₀^τ ⟪Ψ, S₀(s) h⟫ ds`. -/
theorem inner_toLp_selfsimilarHeat_sub_eq (Φ Ψ : 𝓢(ℝ^n, ℂ))
    (hΨ : ∀ k, (𝓕 Ψ : 𝓢(ℝ^n, ℂ)) k = selfsimilarAdjointSymbol (⇑(𝓕 Φ : 𝓢(ℝ^n, ℂ))) k)
    (h : Lp ℂ 2 (volume : Measure (ℝ^n))) (τ : ℝ≥0) :
    inner ℂ (Φ.toLp 2) (selfsimilarFactor τ • Lp.compSMul volume 2 (selfsimilarFactor τ)
        (selfsimilarFactor_pos τ).ne' (heatL2 n (selfsimilarHeatTime τ) h)) -
      inner ℂ (Φ.toLp 2) (selfsimilarFactor 0 • Lp.compSMul volume 2 (selfsimilarFactor 0)
        (selfsimilarFactor_pos 0).ne' (heatL2 n (selfsimilarHeatTime 0) h)) =
      ∫ s in (0 : ℝ)..τ, inner ℂ (Ψ.toLp 2) (selfsimilarFactor s.toNNReal •
        Lp.compSMul volume 2 (selfsimilarFactor s.toNNReal) (selfsimilarFactor_pos _).ne'
          (heatL2 n (selfsimilarHeatTime s.toNNReal) h)) := by
  rw [inner_toLp_selfsimilarHeat_eq_integral, inner_toLp_selfsimilarHeat_eq_integral,
    NNReal.coe_zero, integral_selfsimilarTestSymbol_sub_eq (𝓕 Φ) (𝓕 Ψ) hΨ (Lp.memLp (𝓕 h))
      τ.coe_nonneg]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le τ.coe_nonneg] at hs
  simp only
  rw [inner_toLp_selfsimilarHeat_eq_integral, Real.coe_toNNReal _ hs.1]

/-! ### Vector fields -/

/-- Pairing with a fixed vector field through the physical `L²` rows. -/
def vectorL2Pairing (φ : VectorH n 0) : VectorH n 0 →L[ℝ] ℝ :=
  (innerSL ℝ (l2SobolevRow (baseIndex n 0) φ)).comp (l2SobolevRow (baseIndex n 0))

theorem vectorL2Pairing_apply (φ x : VectorH n 0) :
    vectorL2Pairing φ x =
      inner ℝ (l2SobolevRow (baseIndex n 0) φ) (l2SobolevRow (baseIndex n 0) x) :=
  rfl

theorem vectorL2Pairing_sub_left (φ ψ x : VectorH n 0) :
    vectorL2Pairing (φ - ψ) x = vectorL2Pairing φ x - vectorL2Pairing ψ x := by
  simp only [vectorL2Pairing_apply, map_sub, inner_sub_left]

/-- The vector pairing is the sum of the real parts of the complexified component pairings. -/
theorem vectorL2Pairing_eq_sum_re (φ x : VectorH n 0) :
    vectorL2Pairing φ x = ∑ j, (inner ℂ (baseL2 (φ j)) (baseL2 (x j))).re := by
  rw [vectorL2Pairing_apply, l2SobolevRow_apply, l2SobolevRow_apply, Lp.inner_euclideanTuple]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_eq_re_inner_complexifyL2CLM, ← complexifyL2CLM_base, ← complexifyL2CLM_base]
  rfl

/-- Complexified orbits of free self-similar evolution are continuous in real time. -/
theorem continuous_baseL2_selfsimilarHeatSobolev (u : W^{0,2}(ℝ^n)) :
    Continuous fun s : ℝ ↦ baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal u) := by
  have h : (fun s : ℝ ↦ baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal u)) =
      fun s : ℝ ↦ complexifyL2CLM n (wkpBaseCoordinateCLM
        (selfsimilarHeatSobolev n 0 s.toNNReal u)) := by
    funext s
    rw [complexifyL2CLM_base]
  rw [h]
  exact (complexifyL2CLM n).continuous.comp (wkpBaseCoordinateCLM.continuous.comp
    ((continuous_selfsimilarHeatSobolev u).comp continuous_real_toNNReal))

/-- The tested identity of free self-similar evolution on vector fields whose components are
Schwartz functions: if the Fourier transform of each component of `ψ` is the adjoint symbol of
the corresponding component of `φ`, then
`⟪S₀(t) g, φ⟫ - ⟪g, φ⟫ = ∫₀ᵗ ⟪S₀(s) g, ψ⟫ ds` for every field `g`. -/
theorem vectorSelfsimilarHeat_tested_of_schwartz {φ ψ : VectorH n 0} (Φ Ψ : Fin n → 𝓢(ℝ^n, ℂ))
    (hφ : ∀ j, baseL2 (φ j) = (Φ j).toLp 2) (hψ : ∀ j, baseL2 (ψ j) = (Ψ j).toLp 2)
    (hΨ : ∀ j k, (𝓕 (Ψ j) : 𝓢(ℝ^n, ℂ)) k =
      selfsimilarAdjointSymbol (⇑(𝓕 (Φ j) : 𝓢(ℝ^n, ℂ))) k)
    (g : VectorH n 0) (t : ℝ≥0) :
    vectorL2Pairing φ (vectorSelfsimilarHeat n 0 t g) - vectorL2Pairing φ g =
      ∫ s in (0 : ℝ)..t, vectorL2Pairing ψ (vectorSelfsimilarHeat n 0 s.toNNReal g) := by
  have hbase (τ : ℝ≥0) (j : Fin n) : baseL2 ((vectorSelfsimilarHeat n 0 τ g) j) =
      selfsimilarFactor τ • Lp.compSMul volume 2 (selfsimilarFactor τ)
        (selfsimilarFactor_pos τ).ne' (heatL2 n (selfsimilarHeatTime τ) (baseL2 (g j))) := by
    rw [vectorSelfsimilarHeat_apply, baseL2_selfsimilarHeatSobolev]
  have hcont (j : Fin n) : Continuous fun s : ℝ ↦
      (inner ℂ ((Ψ j).toLp 2) (baseL2 ((vectorSelfsimilarHeat n 0 s.toNNReal g) j))).re := by
    simp only [vectorSelfsimilarHeat_apply]
    exact Complex.continuous_re.comp (continuous_const.inner
      (continuous_baseL2_selfsimilarHeatSobolev (g j)))
  simp_rw [vectorL2Pairing_eq_sum_re, hψ]
  rw [← Finset.sum_sub_distrib, intervalIntegral.integral_finsetSum
    (fun j _ ↦ (hcont j).intervalIntegrable 0 t)]
  apply Finset.sum_congr rfl
  intro j _
  have h0 : baseL2 (g j) = selfsimilarFactor 0 • Lp.compSMul volume 2 (selfsimilarFactor 0)
      (selfsimilarFactor_pos 0).ne' (heatL2 n (selfsimilarHeatTime 0) (baseL2 (g j))) := by
    rw [← baseL2_selfsimilarHeatSobolev, selfsimilarHeatSobolev_zero]
  have hint : IntervalIntegrable (fun s : ℝ ↦ inner ℂ ((Ψ j).toLp 2)
      (selfsimilarFactor s.toNNReal • Lp.compSMul volume 2 (selfsimilarFactor s.toNNReal)
        (selfsimilarFactor_pos _).ne' (heatL2 n (selfsimilarHeatTime s.toNNReal) (baseL2 (g j)))))
      volume 0 t := by
    refine ((continuous_const (y := (Ψ j).toLp 2)).inner
      (continuous_baseL2_selfsimilarHeatSobolev (g j))).intervalIntegrable 0 t |>.congr ?_
    intro s _
    simp only
    rw [baseL2_selfsimilarHeatSobolev]
  have h0' : inner ℂ ((Φ j).toLp 2) (baseL2 (g j)) = inner ℂ ((Φ j).toLp 2)
      (selfsimilarFactor 0 • Lp.compSMul volume 2 (selfsimilarFactor 0)
        (selfsimilarFactor_pos 0).ne' (heatL2 n (selfsimilarHeatTime 0) (baseL2 (g j)))) := by
    rw [← h0]
  rw [hφ j, hbase t j, h0', ← Complex.sub_re, inner_toLp_selfsimilarHeat_sub_eq (Φ j) (Ψ j) (hΨ j),
    ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Complex.reCLM_apply]
  rw [hbase]

/-! ### The formal adjoint on Schwartz functions -/

/-- The formal adjoint `Δf - ½ x·∇f + ½ (1 - n) f` of the free self-similar generator on Schwartz
functions. -/
def selfsimilarAdjointSchwartz (f : 𝓢(ℝ^n, ℂ)) : 𝓢(ℝ^n, ℂ) :=
  Δ f - (1 / 2 : ℝ) • eulerCLM n f + ((1 - (n : ℝ)) / 2) • f

/-- The Fourier transform of the formal adjoint is the adjoint symbol. -/
theorem fourier_selfsimilarAdjointSchwartz_apply (f : 𝓢(ℝ^n, ℂ)) (k : ℝ^n) :
    (𝓕 (selfsimilarAdjointSchwartz f) : 𝓢(ℝ^n, ℂ)) k =
      selfsimilarAdjointSymbol (⇑(𝓕 f : 𝓢(ℝ^n, ℂ))) k := by
  rw [selfsimilarAdjointSchwartz, sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_add, FourierTransform.fourier_neg, fourier_smul, fourier_smul,
    add_apply, add_apply, neg_apply, smul_apply, smul_apply, fourier_laplacian_apply,
    fourier_eulerCLM_apply, selfsimilarAdjointSymbol, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-! ### Real test fields -/

/-- The complexification of a real smooth compactly supported function, as a Schwartz
function. -/
def complexTestSchwartz {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    𝓢(ℝ^n, ℂ) :=
  (hcs.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hf)

theorem complexTestSchwartz_apply {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (x : ℝ^n) : complexTestSchwartz hf hcs x = (f x : ℂ) :=
  rfl

/-- The formal adjoint of the free self-similar generator on a real smooth function:
`L₀^† f = Δf - ½ x·∇f + ½ (1 - n) f`. -/
def selfsimilarAdjoint (f : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  Δ f x - 1 / 2 * fderiv ℝ f x x + (1 - n) / 2 * f x

/-- On a complexified real test function the Schwartz adjoint is the complexified adjoint. -/
theorem selfsimilarAdjointSchwartz_complexTestSchwartz_apply {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) (x : ℝ^n) :
    selfsimilarAdjointSchwartz (complexTestSchwartz hf hcs) x = (selfsimilarAdjoint f x : ℂ) := by
  have hfun : (complexTestSchwartz hf hcs : ℝ^n → ℂ) = Complex.ofRealCLM ∘ f := rfl
  have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt.of_le (by simp)
  have hd : fderiv ℝ (Complex.ofRealCLM ∘ f) x = Complex.ofRealCLM.comp (fderiv ℝ f x) :=
    (Complex.ofRealCLM.hasFDerivAt.comp x
      ((hf.differentiable (by simp)) x).hasFDerivAt).fderiv
  rw [selfsimilarAdjointSchwartz, add_apply, sub_apply, smul_apply, smul_apply, laplacian_apply,
    eulerCLM_apply, hfun, h2.laplacian_CLM_comp_left, hd]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.real_smul, selfsimilarAdjoint]
  push_cast
  ring

theorem memLp_of_test {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    MemLp f 2 volume :=
  hf.continuous.memLp_of_hasCompactSupport hcs

/-- The adjoint of a real test function is square integrable. -/
theorem memLp_selfsimilarAdjoint {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) : MemLp (selfsimilarAdjoint f) 2 volume := by
  have h := ((selfsimilarAdjointSchwartz (complexTestSchwartz hf hcs)).memLp 2 volume).re
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun x ↦ ?_) h
  simp only [selfsimilarAdjointSchwartz_complexTestSchwartz_apply, RCLike.re_to_complex,
    Complex.ofReal_re]

/-- The vector field in `L²` with square-integrable components. -/
def vectorOfMemLp (f : Fin n → ℝ^n → ℝ) (hf : ∀ j, MemLp (f j) 2 volume) : VectorH n 0 :=
  WithLp.toLp 2 fun j ↦ lpToZeroOrder (((hf j).restrict univ).toLp (f j))

/-- The complexified components of `vectorOfMemLp` are the complexified functions. -/
theorem coeFn_baseL2_vectorOfMemLp (f : Fin n → ℝ^n → ℝ) (hf : ∀ j, MemLp (f j) 2 volume)
    (j : Fin n) :
    (baseL2 (vectorOfMemLp f hf j) : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (f j x : ℂ) := by
  have h1 : (baseL2 (vectorOfMemLp f hf j) : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ (wkpBaseCoordinateCLM (vectorOfMemLp f hf j) x : ℂ) :=
    (memLp_coordFun (vectorOfMemLp f hf j) (baseIndex n 0)).ofReal.coeFn_toLp
  have h2 : (wkpBaseCoordinateCLM (vectorOfMemLp f hf j) : ℝ^n → ℝ) =ᵐ[volume] f j := by
    change ((((hf j).restrict univ).toLp (f j) : DerivLp n 2 univ) : ℝ^n → ℝ) =ᵐ[volume] f j
    have := ((hf j).restrict univ).coeFn_toLp
    simpa only [Measure.restrict_univ] using this
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

/-- The physical row of `vectorOfMemLp` is the assembled Euclidean field. -/
theorem l2SobolevRow_vectorOfMemLp_ae (f : Fin n → ℝ^n → ℝ) (hf : ∀ j, MemLp (f j) 2 volume) :
    ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ j,
      (l2SobolevRow (baseIndex n 0) (vectorOfMemLp f hf) : ℝ^n → ℝ^n) x j = f j x := by
  have h1 := Lp.euclideanTuple_apply_ae
    (fun j ↦ wkpCoordinateCLM (baseIndex n 0) (vectorOfMemLp f hf j))
  have h2 : ∀ j, (wkpCoordinateCLM (baseIndex n 0) (vectorOfMemLp f hf j) : ℝ^n → ℝ)
      =ᵐ[volume] f j := by
    intro j
    change ((((hf j).restrict univ).toLp (f j) : DerivLp n 2 univ) : ℝ^n → ℝ) =ᵐ[volume] f j
    have := ((hf j).restrict univ).coeFn_toLp
    simpa only [Measure.restrict_univ] using this
  simp only [domainMeasure, Measure.restrict_univ] at h1
  filter_upwards [h1, ae_all_iff.mpr h2] with x hx1 hx2 j
  rw [l2SobolevRow_apply, hx1 j, hx2 j]

/-- The vector `H¹` field with smooth compactly supported components. -/
def testVectorH1 (f : Fin n → ℝ^n → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) : VectorH n 1 :=
  WithLp.toLp 2 fun j ↦
    mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2) (Ω := univ) (f j) (hf j) (hcs j)

/-- Forgetting the derivatives of the `H¹` test field gives the `L²` test field. -/
theorem vectorLower_testVectorH1 (f : Fin n → ℝ^n → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) :
    vectorLower n 0 (testVectorH1 f hf hcs) =
      vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j) := by
  apply PiLp.ext
  intro j
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  apply Lp.ext
  have h1 : (wkpBaseCoordinateCLM ((vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j)) j) :
      ℝ^n → ℝ) =ᵐ[domainMeasure n univ] f j := by
    change ((((memLp_of_test (hf j) (hcs j)).restrict univ).toLp (f j) :
      DerivLp n 2 univ) : ℝ^n → ℝ) =ᵐ[volume.restrict univ] f j
    exact ((memLp_of_test (hf j) (hcs j)).restrict univ).coeFn_toLp
  have h2 := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := univ)
    (f j) (hf j) (hcs j) (baseIndex n 1)
  simp only [baseIndex_toList, iteratedPartialDeriv] at h2
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  exact hx2

/-- The tested identity of free self-similar evolution for a real test field `φ`:
`⟪S₀(t) g, φ⟫ - ⟪g, φ⟫ = ∫₀ᵗ ⟪S₀(s) g, L₀^† φ⟫ ds` with
`L₀^† φ = Δφ - ½ ξ·∇φ + ½ (1 - n) φ`. -/
theorem vectorSelfsimilarHeat_tested (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hcs : ∀ j, HasCompactSupport (f j))
    (g : VectorH n 0) (t : ℝ≥0) :
    vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
        (vectorSelfsimilarHeat n 0 t g) -
      vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j)) g =
      ∫ s in (0 : ℝ)..t, vectorL2Pairing
        (vectorOfMemLp (fun j ↦ selfsimilarAdjoint (f j))
          fun j ↦ memLp_selfsimilarAdjoint (hf j) (hcs j))
        (vectorSelfsimilarHeat n 0 s.toNNReal g) := by
  refine vectorSelfsimilarHeat_tested_of_schwartz (fun j ↦ complexTestSchwartz (hf j) (hcs j))
    (fun j ↦ selfsimilarAdjointSchwartz (complexTestSchwartz (hf j) (hcs j))) ?_ ?_
    (fun j k ↦ fourier_selfsimilarAdjointSchwartz_apply _ k) g t
  · intro j
    apply Lp.ext
    filter_upwards [coeFn_baseL2_vectorOfMemLp f _ j,
      (complexTestSchwartz (hf j) (hcs j)).coeFn_toLp 2 volume] with x hx1 hx2
    rw [hx1, hx2, complexTestSchwartz_apply]
  · intro j
    apply Lp.ext
    filter_upwards [coeFn_baseL2_vectorOfMemLp (fun j ↦ selfsimilarAdjoint (f j)) _ j,
      (selfsimilarAdjointSchwartz (complexTestSchwartz (hf j) (hcs j))).coeFn_toLp 2 volume]
      with x hx1 hx2
    rw [hx1, hx2, selfsimilarAdjointSchwartz_complexTestSchwartz_apply]

end HeatEquation.WholeSpace
