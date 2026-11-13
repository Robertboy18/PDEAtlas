/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarResolvent
public import PDE.Analysis.Fourier.Schwartz.Euler

/-!
# The free self-similar resolvent solves the shifted equation weakly

For a Schwartz function `φ` the formal adjoint of `μ + L₀` is
`(μ + L₀)^* φ = (μ + (n - 1)/2) φ + (1/2) x·∇φ - Δφ`. Its Fourier transform is the first-order
operator `(μ - 1/2 + 4π²|ζ|²) φ̂(ζ) - (1/2) ζ·∇φ̂(ζ)`, and along the adjoint flow
`s ↦ e^{-μs} e^{s/2} e^{-(e^s - 1) 4π²|η|²} φ̂(e^{s/2} η)` it is minus the similarity-time
derivative. Pairing the Laplace integral of the free evolution with `(μ + L₀)^* φ`, changing to
the dilated frequency at every time, exchanging the two integrals and integrating the derivative
in time gives

`⟪(μ + L₀)^* φ, R_μ f⟫ = ⟪φ, f⟫`,  `μ > 1/2`.

For a smooth compactly supported real `φ` this is the distributional equation
`∫ R_μ f ((μ + (n-1)/2) φ + (1/2) x·∇φ - Δφ) = ∫ f φ`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SchwartzMap LineDeriv Laplacian Set Filter Topology
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal SchwartzMap Sobolev

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- The formal adjoint `(μ + L₀)^* = μ + (n - 1)/2 + (1/2) x·∇ - Δ` on Schwartz functions. -/
def schwartzSelfsimilarAdjoint (n : ℕ) (μ : ℝ) : 𝓢(ℝ^n, ℂ) →L[ℂ] 𝓢(ℝ^n, ℂ) :=
  ((μ + ((n : ℝ) - 1) / 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _ +
    (1 / 2 : ℂ) • eulerCLM n - laplacianCLM ℂ (ℝ^n) 𝓢(ℝ^n, ℂ)

/-- The Fourier transform of the formal adjoint is a first-order operator in frequency:
`(μ - 1/2 + 4π²|ζ|²) φ̂(ζ) - (1/2) ζ·∇φ̂(ζ)`. -/
theorem fourier_schwartzSelfsimilarAdjoint_apply (μ : ℝ) (φ : 𝓢(ℝ^n, ℂ)) (ζ : ℝ^n) :
    𝓕 (schwartzSelfsimilarAdjoint n μ φ) ζ =
      ((μ - 1 / 2 + 4 * Real.pi ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) * 𝓕 φ ζ -
        (1 / 2 : ℂ) * fderiv ℝ (fun η ↦ 𝓕 φ η) ζ ζ := by
  simp only [schwartzSelfsimilarAdjoint, sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, laplacianCLM_eq]
  rw [← fourierTransformCLM_apply ℂ, map_sub, map_add, map_smul, map_smul]
  simp only [fourierTransformCLM_apply, sub_apply, add_apply, smul_apply, smul_eq_mul,
    fourier_eulerCLM_apply, fourier_laplacian_apply]
  push_cast
  ring

/-- Schwartz functions are bounded. -/
theorem exists_norm_schwartz_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : 𝓢(E, F)) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  ⟨‖f.toBoundedContinuousFunction‖, fun x ↦ by
    simpa using f.toBoundedContinuousFunction.norm_coe_le_norm x⟩

/-- The real weight of the adjoint flow at similarity time `s` and frequency `η`. -/
def adjointFlowWeight (μ s : ℝ) (η : ℝ^n) : ℝ :=
  Real.exp (-μ * s) * Real.exp (s / 2) *
    Real.exp (-((Real.exp s - 1) * (4 * Real.pi ^ 2 * ‖η‖ ^ 2)))

theorem adjointFlowWeight_le (μ : ℝ) {s : ℝ} (hs : 0 ≤ s) (η : ℝ^n) :
    adjointFlowWeight μ s η ≤ Real.exp ((1 / 2 - μ) * s) := by
  unfold adjointFlowWeight
  have h1 : Real.exp (-((Real.exp s - 1) * (4 * Real.pi ^ 2 * ‖η‖ ^ 2))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ Real.exp s - 1 := by linarith [Real.one_le_exp_iff.mpr hs]
    have : 0 ≤ 4 * Real.pi ^ 2 * ‖η‖ ^ 2 := by positivity
    nlinarith
  calc _ ≤ Real.exp (-μ * s) * Real.exp (s / 2) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by rw [mul_one, ← Real.exp_add]; congr 1; ring

/-- The adjoint flow of a Schwartz function in frequency is differentiable in similarity time,
with derivative given by the Fourier transform of the formal adjoint. -/
theorem hasDerivAt_adjointFlow (μ : ℝ) (φ : 𝓢(ℝ^n, ℂ)) (η : ℝ^n) (s : ℝ) :
    HasDerivAt (fun s ↦ (adjointFlowWeight μ s η : ℂ) * 𝓕 φ (Real.exp (s / 2) • η))
      (-((adjointFlowWeight μ s η : ℂ) *
        𝓕 (schwartzSelfsimilarAdjoint n μ φ) (Real.exp (s / 2) • η))) s := by
  set F : 𝓢(ℝ^n, ℂ) := 𝓕 φ
  set m : ℝ := 4 * Real.pi ^ 2 * ‖η‖ ^ 2
  have hE : HasDerivAt (fun s ↦ adjointFlowWeight μ s η)
      (adjointFlowWeight μ s η * (-μ + 1 / 2 - Real.exp s * m)) s := by
    have h1 := ((hasDerivAt_id s).const_mul (-μ)).exp
    have h2 := ((hasDerivAt_id s).div_const 2).exp
    have h3 := (((Real.hasDerivAt_exp s).sub_const 1).mul_const m).neg.exp
    have h := (h1.mul h2).mul h3
    convert h using 1
    · funext s; simp [adjointFlowWeight, m]
    · simp only [adjointFlowWeight, m, id, Pi.neg_apply, Pi.mul_apply]
      ring
  have hg : HasDerivAt (fun s : ℝ ↦ Real.exp (s / 2) • η) ((1 / 2 * Real.exp (s / 2)) • η) s := by
    have := (((hasDerivAt_id' s).div_const 2).exp).smul_const η
    convert this using 2
    ring
  have hF : HasFDerivAt (fun x ↦ F x) (fderiv ℝ (fun x ↦ F x) (Real.exp (s / 2) • η))
      (Real.exp (s / 2) • η) := F.differentiableAt.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt s hg
  have hprod := (hE.ofReal_comp).mul hcomp
  refine hprod.congr_deriv ?_
  have hnorm : ‖Real.exp (s / 2) • η‖ ^ 2 = Real.exp s * ‖η‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [fourier_schwartzSelfsimilarAdjoint_apply, hnorm]
  simp only [Function.comp_apply, map_smul, Complex.real_smul]
  push_cast
  simp only [m]
  push_cast
  ring

theorem continuous_adjointFlowWeight (μ : ℝ) (η : ℝ^n) :
    Continuous fun s ↦ adjointFlowWeight μ s η := by
  unfold adjointFlowWeight; fun_prop

/-- Integrating the adjoint flow of the formal adjoint over similarity time recovers the
transform of the test function. -/
theorem integral_adjointFlow_eq {μ : ℝ} (hμ : 1 / 2 < μ) (φ : 𝓢(ℝ^n, ℂ)) (η : ℝ^n) :
    ∫ s in Ioi (0 : ℝ), (adjointFlowWeight μ s η : ℂ) *
      𝓕 (schwartzSelfsimilarAdjoint n μ φ) (Real.exp (s / 2) • η) = 𝓕 φ η := by
  set ψ := schwartzSelfsimilarAdjoint n μ φ
  obtain ⟨Cψ, hCψ⟩ := exists_norm_schwartz_le (𝓕 ψ)
  obtain ⟨CF, hCF⟩ := exists_norm_schwartz_le (𝓕 φ)
  set Φ : ℝ → ℂ := fun s ↦ (adjointFlowWeight μ s η : ℂ) * 𝓕 φ (Real.exp (s / 2) • η)
  have hbound (F : 𝓢(ℝ^n, ℂ)) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) {s : ℝ} (hs : 0 ≤ s) :
      ‖(adjointFlowWeight μ s η : ℂ) * F (Real.exp (s / 2) • η)‖ ≤
        C * Real.exp (-(μ - 1 / 2) * s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by unfold adjointFlowWeight; positivity)]
    refine (mul_le_mul (adjointFlowWeight_le μ hs η) (hC _) (norm_nonneg _)
      (Real.exp_pos _).le).trans_eq ?_
    rw [mul_comm]
    congr 2
    ring
  have hint : IntegrableOn (fun s : ℝ ↦ (adjointFlowWeight μ s η : ℂ) *
      𝓕 ψ (Real.exp (s / 2) • η)) (Ioi 0) :=
    Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < μ - 1 / 2)).const_mul Cψ)
      ((Complex.continuous_ofReal.comp (continuous_adjointFlowWeight μ η)).mul
        ((𝓕 ψ).continuous.comp (by fun_prop))).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun s hs ↦ hbound _ hCψ (le_of_lt hs)))
  have hlim : Tendsto Φ atTop (𝓝 0) := by
    have hexp : Tendsto (fun s : ℝ ↦ Real.exp (-(μ - 1 / 2) * s)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (by linarith : 0 < μ - 1 / 2)))).congr fun s ↦ ?_
      simp only [Function.comp_apply, id]
      ring_nf
    refine squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hexp.const_mul CF)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact hbound _ hCF hs
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := Φ) (f' := fun s ↦ -((adjointFlowWeight μ s η : ℂ) * 𝓕 ψ (Real.exp (s / 2) • η)))
    (a := 0) (m := 0)
    ((hasDerivAt_adjointFlow μ φ η 0).continuousAt.continuousWithinAt)
    (fun s _ ↦ hasDerivAt_adjointFlow μ φ η s) hint.neg hlim
  rw [integral_neg, show Φ 0 = 𝓕 φ η by simp [Φ, adjointFlowWeight], zero_sub, neg_inj] at hftc
  exact hftc

/-- One step of the free evolution, paired with a transformed Schwartz function and changed
to the dilated frequency variable. -/
theorem exp_mul_inner_fourier_selfsimilarHeatSobolev_eq (μ : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (f : W^{0,2}(ℝ^n)) (ψ : 𝓢(ℝ^n, ℂ)) :
    (Real.exp (-μ * s) : ℂ) * inner ℂ ((𝓕 ψ).toLp 2 (volume : Measure (ℝ^n)))
        (𝓕 (baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal f))) =
      ∫ η, (starRingEnd ℂ) ((adjointFlowWeight μ s η : ℂ) * 𝓕 ψ (Real.exp (s / 2) • η)) *
        (𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n))) η := by
  set fh := (𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n)))
  have hτ : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs
  have hformula := fourier_baseL2_selfsimilarHeatSobolev_ae (n := n) s.toNNReal f
  rw [hτ] at hformula
  set c : ℝ^n → ℝ := fun ξ ↦ Real.exp ((1 - n) * s / 2) *
    Real.exp (-(4 * Real.pi ^ 2 * (1 - Real.exp (-s)) * ‖ξ‖ ^ 2))
  have hpair : inner ℂ ((𝓕 ψ).toLp 2 (volume : Measure (ℝ^n)))
      (𝓕 (baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal f))) =
      ∫ ξ, (starRingEnd ℂ) (𝓕 ψ ξ) * ((c ξ : ℂ) * fh (Real.exp (-(s / 2)) • ξ)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(𝓕 ψ).coeFn_toLp 2 (volume : Measure (ℝ^n)), hformula] with ξ h1 h2
    rw [h1, h2, RCLike.inner_apply']
  set H : ℝ^n → ℂ := fun η ↦ (starRingEnd ℂ) (𝓕 ψ (Real.exp (s / 2) • η)) *
    ((c (Real.exp (s / 2) • η) : ℂ) * fh η)
  have hH : ∀ ξ : ℝ^n, (starRingEnd ℂ) (𝓕 ψ ξ) * ((c ξ : ℂ) * fh (Real.exp (-(s / 2)) • ξ)) =
      H (Real.exp (-(s / 2)) • ξ) := by
    intro ξ
    have : Real.exp (s / 2) • (Real.exp (-(s / 2)) • ξ) = ξ := by
      rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
    simp only [H, this]
  rw [hpair]
  simp_rw [hH]
  rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin]
  have hjac : |(Real.exp (-(s / 2)) ^ n)⁻¹| = Real.exp (n * s / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)]
    congr 1
    ring
  rw [hjac, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with η
  simp only [H, map_mul, Complex.conj_ofReal]
  have hweight : Real.exp (-μ * s) * Real.exp (n * s / 2) * c (Real.exp (s / 2) • η) =
      adjointFlowWeight μ s η := by
    have hnorm : ‖Real.exp (s / 2) • η‖ ^ 2 = Real.exp s * ‖η‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hfac : (1 - Real.exp (-s)) * Real.exp s = Real.exp s - 1 := by
      rw [sub_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    simp only [c, adjointFlowWeight, hnorm]
    have e1 : Real.exp (-μ * s) * Real.exp (n * s / 2) * Real.exp ((1 - n) * s / 2) =
        Real.exp (-μ * s) * Real.exp (s / 2) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    calc _ = (Real.exp (-μ * s) * Real.exp (n * s / 2) * Real.exp ((1 - n) * s / 2)) *
          Real.exp (-(4 * Real.pi ^ 2 * ((1 - Real.exp (-s)) * Real.exp s) * ‖η‖ ^ 2)) := by
          ring_nf
      _ = _ := by rw [e1, hfac]; ring_nf
  rw [← hweight]
  push_cast
  ring

/-- The two-variable integrand of the adjoint pairing is integrable for `μ > 1/2`. -/
theorem integrable_adjointFlow_pairing {μ : ℝ} (hμ : 1 / 2 < μ) (ψ : 𝓢(ℝ^n, ℂ))
    (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    Integrable (Function.uncurry fun (s : ℝ) (η : ℝ^n) ↦
      (starRingEnd ℂ) ((adjointFlowWeight μ s η : ℂ) * 𝓕 ψ (Real.exp (s / 2) • η)) * g η)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  set ν := (volume : Measure ℝ).restrict (Ioi 0)
  have hGc : Continuous fun p : ℝ × ℝ^n ↦
      (adjointFlowWeight μ p.1 p.2 : ℂ) * 𝓕 ψ (Real.exp (p.1 / 2) • p.2) := by
    have h1 : Continuous fun p : ℝ × ℝ^n ↦ adjointFlowWeight μ p.1 p.2 := by
      unfold adjointFlowWeight; fun_prop
    exact (Complex.continuous_ofReal.comp h1).mul ((𝓕 ψ).continuous.comp (by fun_prop))
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (s : ℝ) (η : ℝ^n) ↦
      (starRingEnd ℂ) ((adjointFlowWeight μ s η : ℂ) * 𝓕 ψ (Real.exp (s / 2) • η)) * g η)
      (ν.prod volume) :=
    ((Complex.continuous_conj.comp hGc).aestronglyMeasurable).mul
      ((Lp.stronglyMeasurable g).comp_measurable measurable_snd).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  -- the finite lower integral, by the arithmetic-geometric mean inequality
  set A := ∫⁻ ζ, ENNReal.ofReal (‖𝓕 ψ ζ‖ ^ 2)
  set B := ∫⁻ η, ENNReal.ofReal (‖g η‖ ^ 2)
  have hAB : A + B ≠ ∞ := by
    simp only [A, B]
    rw [lintegral_ofReal_norm_pow_eq_eLpNorm_pow (𝓕 ψ).continuous.aestronglyMeasurable
      two_ne_zero, lintegral_ofReal_norm_pow_eq_eLpNorm_pow (Lp.aestronglyMeasurable g) two_ne_zero]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top ((𝓕 ψ).memLp 2 volume).eLpNorm_ne_top,
      ENNReal.pow_ne_top (Lp.eLpNorm_ne_top g)⟩
  have hpoint (s : ℝ) (hs : 0 ≤ s) (η : ℝ^n) :
      ‖(starRingEnd ℂ) ((adjointFlowWeight μ s η : ℂ) * 𝓕 ψ (Real.exp (s / 2) • η)) * g η‖ₑ ≤
        ENNReal.ofReal (2⁻¹ * Real.exp ((1 / 2 - μ) * s)) *
          (ENNReal.ofReal (‖𝓕 ψ (Real.exp (s / 2) • η)‖ ^ 2) + ENNReal.ofReal (‖g η‖ ^ 2)) := by
    have hE : 0 ≤ adjointFlowWeight μ s η := by unfold adjointFlowWeight; positivity
    rw [← ofReal_norm, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, RCLike.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hE]
    have ha := norm_nonneg (𝓕 ψ (Real.exp (s / 2) • η))
    have hb := norm_nonneg (g η)
    nlinarith [mul_nonneg (sub_nonneg.2 (adjointFlowWeight_le μ hs η)) (mul_nonneg ha hb),
      mul_nonneg (Real.exp_pos ((1 / 2 - μ) * s)).le (sq_nonneg (‖𝓕 ψ (Real.exp (s / 2) • η)‖ -
        ‖g η‖))]
  have hdil (s : ℝ) (hs : 0 ≤ s) :
      ∫⁻ η, ENNReal.ofReal (‖𝓕 ψ (Real.exp (s / 2) • η)‖ ^ 2) ≤ A := by
    have hm : Measurable fun ζ : ℝ^n ↦ ENNReal.ofReal (‖𝓕 ψ ζ‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp ((𝓕 ψ).continuous.measurable.norm.pow_const 2)
    rw [lintegral_comp_smul_eq hm (Real.exp_pos _).ne']
    refine mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.mpr ?_)
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (Real.one_le_exp_iff.mpr (by linarith)))
  have hint : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2⁻¹ * Real.exp ((1 / 2 - μ) * s)) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · exact ENNReal.ofReal_ne_top
    · refine ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < μ - 1 / 2)).const_mul 2⁻¹).congr
        (Filter.Eventually.of_forall fun s ↦ ?_)
      simp only
      congr 2
      ring
    · exact Filter.Eventually.of_forall fun s ↦ by positivity
  rw [HasFiniteIntegral, lintegral_prod _ hmeas.enorm]
  calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2⁻¹ * Real.exp ((1 / 2 - μ) * s)) * (A + B) := by
        refine setLIntegral_mono' measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
        calc _ ≤ ∫⁻ η, ENNReal.ofReal (2⁻¹ * Real.exp ((1 / 2 - μ) * s)) *
              (ENNReal.ofReal (‖𝓕 ψ (Real.exp (s / 2) • η)‖ ^ 2) + ENNReal.ofReal (‖g η‖ ^ 2)) :=
              lintegral_mono fun η ↦ hpoint s hs.le η
          _ = ENNReal.ofReal (2⁻¹ * Real.exp ((1 / 2 - μ) * s)) *
              ((∫⁻ η, ENNReal.ofReal (‖𝓕 ψ (Real.exp (s / 2) • η)‖ ^ 2)) + B) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              congr 1
              exact lintegral_add_left (ENNReal.measurable_ofReal.comp (((𝓕 ψ).continuous.comp
                (continuous_const_smul _)).measurable.norm.pow_const 2)) _
          _ ≤ _ := by gcongr; exact hdil s hs.le
    _ = (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2⁻¹ * Real.exp ((1 / 2 - μ) * s))) * (A + B) :=
        lintegral_mul_const' _ _ hAB
    _ < ∞ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hint) (lt_top_iff_ne_top.mpr hAB)

/-- The resolvent inverts `μ + L₀` against Schwartz test functions:
`⟪(μ + L₀)^* φ, R_μ f⟫ = ⟪φ, f⟫` in `L²`, for every `μ > 1/2`. -/
theorem inner_schwartzSelfsimilarAdjoint_selfsimilarResolvent (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 < μ) (f : W^{0,2}(ℝ^n)) (φ : 𝓢(ℝ^n, ℂ)) :
    inner ℂ ((schwartzSelfsimilarAdjoint n μ φ).toLp 2 (volume : Measure (ℝ^n)))
        (baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f)) =
      inner ℂ (φ.toLp 2 (volume : Measure (ℝ^n))) (baseL2 f) := by
  set ψ := schwartzSelfsimilarAdjoint n μ φ
  set fh := (𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n)))
  rw [← Lp.inner_fourier_eq, ← Lp.inner_fourier_eq (φ.toLp 2 _) (baseL2 f),
    SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
    inner_fourier_baseL2_selfsimilarResolvent]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun s hs ↦ exp_mul_inner_fourier_selfsimilarHeatSobolev_eq μ (le_of_lt hs) f ψ)]
  rw [integral_integral_swap (integrable_adjointFlow_pairing hμ ψ fh), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(𝓕 φ).coeFn_toLp 2 (volume : Measure (ℝ^n))] with η hη
  rw [hη, RCLike.inner_apply', integral_mul_const, integral_conj,
    integral_adjointFlow_eq hμ φ η]

/-- The resolvent `R_μ = (μ + L₀)⁻¹` solves `(μ + L₀) z = f` in the sense of distributions:
for every smooth compactly supported real `φ`,
`∫ z ((μ + (n-1)/2) φ + (1/2) x·∇φ - Δφ) = ∫ f φ`, where `z = R_μ f` and `μ > 1/2`. -/
theorem integral_selfsimilarResolvent_mul_adjoint (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 < μ)
    (f : W^{0,2}(ℝ^n)) {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, (wkpBaseCoordinateCLM (selfsimilarResolvent n hn (by linarith : 0 < μ) f) :
        ℝ^n → ℝ) x * ((μ + ((n : ℝ) - 1) / 2) * φ x + (1 / 2) * fderiv ℝ φ x x - Δ φ x) =
      ∫ x, (wkpBaseCoordinateCLM f : ℝ^n → ℝ) x * φ x := by
  set z := selfsimilarResolvent n hn (by linarith : 0 < μ) f
  have hcs : HasCompactSupport (fun x ↦ ((φ x : ℝ) : ℂ)) :=
    hφc.comp_left (g := Complex.ofRealCLM) (by simp)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ((φ x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  set φc : 𝓢(ℝ^n, ℂ) := hcs.toSchwartzMap hsm
  have hφc_apply : ∀ x, φc x = ((φ x : ℝ) : ℂ) := fun x ↦ rfl
  have hfd : ∀ x, fderiv ℝ φc x x = ((fderiv ℝ φ x x : ℝ) : ℂ) := by
    intro x
    have hd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)).differentiableAt
    have : fderiv ℝ (fun y ↦ ((φ y : ℝ) : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ φ x) :=
      (Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    rw [show (φc : ℝ^n → ℂ) = fun y ↦ ((φ y : ℝ) : ℂ) from rfl, this]
    rfl
  have hlap (x : ℝ^n) : Δ φc x = ((Δ φ x : ℝ) : ℂ) := by
    rw [SchwartzMap.laplacian_apply, show (φc : ℝ^n → ℂ) = Complex.ofRealCLM ∘ φ from rfl]
    exact (hφ.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left
  have hψ : ∀ x, schwartzSelfsimilarAdjoint n μ φc x =
      ((((μ + ((n : ℝ) - 1) / 2) * φ x + (1 / 2) * fderiv ℝ φ x x - Δ φ x : ℝ)) : ℂ) := by
    intro x
    simp only [schwartzSelfsimilarAdjoint, sub_apply, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, laplacianCLM_eq, eulerCLM_apply, hfd, hlap,
      hφc_apply, smul_eq_mul]
    push_cast
    ring
  have key := inner_schwartzSelfsimilarAdjoint_selfsimilarResolvent hn hμ f φc
  rw [L2.inner_def, L2.inner_def] at key
  have hbase (U : W^{0,2}(ℝ^n)) : (baseL2 U : ℝ^n → ℂ) =ᵐ[volume] fun x ↦
      ((wkpBaseCoordinateCLM U : ℝ^n → ℝ) x : ℂ) := by
    rw [← complexifyL2CLM_base]
    exact complexifyL2CLM_ae _
  have hL : ∫ x, inner ℂ ((schwartzSelfsimilarAdjoint n μ φc).toLp 2 volume x)
      ((baseL2 z : ℝ^n → ℂ) x) = ((∫ x, (wkpBaseCoordinateCLM z : ℝ^n → ℝ) x *
        ((μ + ((n : ℝ) - 1) / 2) * φ x + (1 / 2) * fderiv ℝ φ x x - Δ φ x) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [(schwartzSelfsimilarAdjoint n μ φc).coeFn_toLp 2 (volume : Measure (ℝ^n)),
      hbase z] with x h1 h2
    rw [h1, h2, RCLike.inner_apply', hψ, Complex.conj_ofReal]
    push_cast
    ring
  have hR : ∫ x, inner ℂ (φc.toLp 2 volume x) ((baseL2 f : ℝ^n → ℂ) x) =
      ((∫ x, (wkpBaseCoordinateCLM f : ℝ^n → ℝ) x * φ x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [φc.coeFn_toLp 2 (volume : Measure (ℝ^n)), hbase f] with x h1 h2
    rw [h1, h2, RCLike.inner_apply', hφc_apply, Complex.conj_ofReal]
    push_cast
    ring
  rw [hL, hR] at key
  exact_mod_cast key

end HeatEquation.WholeSpace
