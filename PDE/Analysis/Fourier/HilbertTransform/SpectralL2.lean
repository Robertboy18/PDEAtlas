/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.SpectralBridge

/-!
# Removing Fourier integrability from the Hilbert principal-value bridge

The Abel multipliers converge strongly on `L²`. An almost-everywhere convergent
subsequence of their inverse transforms can therefore be compared with the
pointwise principal-value limit.
-/

@[expose] public section

namespace PDE.Analysis

open Filter FourierTransform MeasureTheory
open scoped ContDiff NNReal SchwartzMap Topology

noncomputable section

/-- Nonnegative Abel damping preserves square integrability. -/
theorem hilbertAbelMultiplier_memLp (ε : ℝ≥0) (F : ComplexL2) :
    MemLp (fun ξ ↦ hilbertAbelSymbol ε ξ * F ξ) 2 volume := by
  apply (Lp.memLp F).of_le_mul (c := 1)
  · exact (measurable_hilbertSymbol.aestronglyMeasurable.mul (by fun_prop)).mul
      (Lp.aestronglyMeasurable F)
  · filter_upwards with ξ
    rw [norm_mul, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_hilbertAbelSymbol_le_one ε.coe_nonneg ξ)

/-- The Abel-damped Hilbert multiplier as an element of the concrete `L²` space. -/
def hilbertAbelMultiplier (ε : ℝ≥0) (F : ComplexL2) : ComplexL2 :=
  (hilbertAbelMultiplier_memLp ε F).toLp (fun ξ ↦ hilbertAbelSymbol ε ξ * F ξ)

/-- The Abel multiplier has the prescribed pointwise representative almost everywhere. -/
theorem coe_hilbertAbelMultiplier (ε : ℝ≥0) (F : ComplexL2) :
    hilbertAbelMultiplier ε F =ᵐ[volume] fun ξ ↦ hilbertAbelSymbol ε ξ * F ξ :=
  (hilbertAbelMultiplier_memLp ε F).coeFn_toLp

/-- The squared norm of a concrete complex `L²` function is its square integral. -/
theorem norm_sq_ComplexL2_eq_integral (F : ComplexL2) :
    ‖F‖ ^ 2 = ∫ ξ, ‖F ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The squared distance between the damped and undamped multipliers is an ordinary
integral, with all representatives identified almost everywhere. -/
theorem norm_sq_hilbertAbelMultiplier_sub (ε : ℝ≥0) (F : ComplexL2) :
    ‖hilbertAbelMultiplier ε F - hilbertMultiplier F‖ ^ 2 =
      ∫ ξ, ‖hilbertAbelSymbol ε ξ * F ξ - hilbertSymbol ξ * F ξ‖ ^ 2 := by
  rw [norm_sq_ComplexL2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hilbertAbelMultiplier ε F) (hilbertMultiplier F),
    coe_hilbertAbelMultiplier ε F, coe_hilbertMultiplier F] with ξ hsub hε h
  simp only [hsub, Pi.sub_apply, hε, h]

/-- The pointwise multiplier error is dominated by twice the input norm. -/
theorem norm_hilbertAbelMultiplier_sub_le (ε : ℝ≥0) (F : ComplexL2) (ξ : ℝ) :
    ‖hilbertAbelSymbol ε ξ * F ξ - hilbertSymbol ξ * F ξ‖ ≤ 2 * ‖F ξ‖ := by
  calc
    _ ≤ ‖hilbertAbelSymbol ε ξ * F ξ‖ + ‖hilbertSymbol ξ * F ξ‖ := norm_sub_le _ _
    _ ≤ ‖F ξ‖ + ‖F ξ‖ := by
      gcongr
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_hilbertAbelSymbol_le_one ε.coe_nonneg ξ)
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_hilbertSymbol_le_one ξ)
    _ = _ := (two_mul _).symm

/-- Abel damping can be removed in `L²` without assuming an integrable Fourier transform. -/
theorem tendsto_hilbertAbelMultiplier (F : ComplexL2) :
    Tendsto (fun ε ↦ hilbertAbelMultiplier ε F) (𝓝 (0 : ℝ≥0)) (𝓝 (hilbertMultiplier F)) := by
  have hsq : Tendsto (fun ε : ℝ≥0 ↦
      ∫ ξ, ‖hilbertAbelSymbol ε ξ * F ξ - hilbertSymbol ξ * F ξ‖ ^ 2)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    have hzero : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
    rw [hzero]
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ ↦ 4 * ‖F ξ‖ ^ 2)
    · apply Eventually.of_forall
      intro ε
      exact (((hilbertAbelMultiplier_memLp ε F).aestronglyMeasurable.sub
        (hilbertMultiplier_memLp F).aestronglyMeasurable).norm.pow 2)
    · apply Eventually.of_forall
      intro ε
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := norm_hilbertAbelMultiplier_sub_le ε F ξ
      nlinarith [norm_nonneg (hilbertAbelSymbol ε ξ * F ξ - hilbertSymbol ξ * F ξ)]
    · exact ((Lp.memLp F).norm.integrable_sq).const_mul 4
    · filter_upwards with ξ
      have hc : Continuous (fun ε : ℝ≥0 ↦ hilbertAbelSymbol ε ξ) := by
        unfold hilbertAbelSymbol
        fun_prop
      have hlim := (((hc.tendsto 0).mul_const (F ξ)).sub_const
        (hilbertSymbol ξ * F ξ)).norm.pow 2
      simpa [hilbertAbelSymbol] using hlim
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, ← norm_sq_hilbertAbelMultiplier_sub, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] at hnorm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- The forward Fourier integral agrees with the concrete `L²` Fourier transform
on an integrable representative. -/
theorem fourier_eq_L2_ae {g : ℝ → ℂ} (hg : Integrable g)
    (G : ComplexL2) (hG : g =ᵐ[volume] G) :
    𝓕 g =ᵐ[volume] (𝓕 G : ComplexL2) :=
  Fourier.fourierIntegral_eq_L2_ae hg G hG

/-- Abel regularization of the concrete spectral Hilbert transform. -/
def hilbertAbelTransform (ε : ℝ≥0) (F : ComplexL2) : ComplexL2 :=
  𝓕⁻ (hilbertAbelMultiplier ε (𝓕 F))

/-- The regularized spectral transforms converge strongly in `L²`. -/
theorem tendsto_hilbertAbelTransform (F : ComplexL2) :
    Tendsto (fun ε ↦ hilbertAbelTransform ε F) (𝓝 (0 : ℝ≥0))
      (𝓝 (hilbertTransform F)) := by
  rw [hilbertTransform_apply]
  exact ((fourierInvCLM ℂ ComplexL2).continuous.tendsto _).comp
    (tendsto_hilbertAbelMultiplier (𝓕 F))

/-- Positive Abel damping makes the Fourier-side product integrable, even when
the Fourier transform of the input is not itself integrable. -/
theorem integrable_hilbertAbelSymbol_mul_fourier {f : ℝ → ℂ} (hf : Integrable f)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ξ ↦ hilbertAbelSymbol ε ξ * 𝓕 f ξ) := by
  have hc : Continuous (𝓕 f) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hf)]
    exact (Real.Lp.fourierTransform _).continuous
  exact (integrable_hilbertAbelSymbol hε).mul_bdd hc.aestronglyMeasurable
    (Eventually.of_forall
      (VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f))

/-- For integrable real input, the Abel kernel integral represents the
regularized spectral transform almost everywhere. -/
theorem hilbertAbelIntegral_eq_hilbertAbelTransform_ae {f : ℝ → ℝ}
    (hf : Integrable f) (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F)
    {ε : ℝ≥0} (hε : 0 < ε) :
    (fun x ↦ (hilbertAbelIntegral f x ε : ℂ)) =ᵐ[volume] hilbertAbelTransform ε F := by
  have hfourier := fourier_eq_L2_ae hf.ofReal F hF
  have hrep : (fun ξ ↦ hilbertAbelSymbol ε ξ * 𝓕 (fun x ↦ (f x : ℂ)) ξ) =ᵐ[volume]
      hilbertAbelMultiplier ε (𝓕 F) := by
    filter_upwards [hfourier, coe_hilbertAbelMultiplier ε (𝓕 F)] with ξ hξ hεξ
    exact (congrArg (fun z : ℂ ↦ hilbertAbelSymbol ε ξ * z) hξ).trans hεξ.symm
  have hbridge := fourierInv_eq_L2_ae
    (integrable_hilbertAbelSymbol_mul_fourier hf.ofReal hε) _ hrep
  filter_upwards [hbridge] with x hx
  exact (fourierInv_hilbertAbelSymbol_mul_fourier hf hε x).symm.trans hx

/-- Outside a null set, differentiability of an `L¹ ∩ L²` input at a point
identifies its convergent principal value with the spectral Hilbert transform there.
No integrability of the Fourier transform is required. -/
theorem hilbertPV_eq_hilbertTransform_ae_at_differentiable {f : ℝ → ℝ}
    (hf : Integrable f) (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F) :
    ∀ᵐ x, DifferentiableAt ℝ f x → (hilbertPV f x : ℂ) = hilbertTransform F x := by
  let ε : ℕ → ℝ≥0 := fun n ↦ 1 / ((n : ℝ≥0) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεreal : Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨NNReal.tendsto_coe.mpr hεlim, Eventually.of_forall hεpos⟩
  have hL2 := (tendsto_hilbertAbelTransform F).comp hεlim
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x, ∀ n : ℕ,
      (hilbertAbelIntegral f x (ε n) : ℂ) = hilbertAbelTransform (ε n) F x :=
    ae_all_iff.mpr (fun n ↦ hilbertAbelIntegral_eq_hilbertAbelTransform_ae hf F hF (hεpos n))
  filter_upwards [hlim, hrep] with x hx hrep
  intro hdiff
  have hpv := ((Complex.continuous_ofReal.tendsto (hilbertPV f x)).comp
    (tendsto_hilbertAbelIntegral_of_differentiableAt hf hdiff)).comp
      (hεreal.comp hns.tendsto_atTop)
  exact tendsto_nhds_unique hpv (hx.congr (fun n ↦ (hrep (ns n)).symm))

/-- The convergent principal value of an almost-everywhere differentiable real
`L¹ ∩ L²` function is the concrete spectral Hilbert transform almost everywhere. -/
theorem hilbertPV_eq_hilbertTransform_ae_of_ae_differentiableAt {f : ℝ → ℝ}
    (hf : Integrable f) (hdiff : ∀ᵐ x, DifferentiableAt ℝ f x)
    (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F) :
    (fun x ↦ (hilbertPV f x : ℂ)) =ᵐ[volume] hilbertTransform F := by
  filter_upwards [hilbertPV_eq_hilbertTransform_ae_at_differentiable hf F hF, hdiff]
    with x hx hdx
  exact hx hdx

/-- The real part of the spectral Hilbert transform is a principal value
almost everywhere, including integrability at every positive cutoff. -/
theorem hasHilbertPV_hilbertTransform_re_ae_of_ae_differentiableAt {f : ℝ → ℝ}
    (hf : Integrable f) (hdiff : ∀ᵐ x, DifferentiableAt ℝ f x)
    (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F) :
    ∀ᵐ x, HasHilbertPV f x (hilbertTransform F x).re := by
  filter_upwards [hilbertPV_eq_hilbertTransform_ae_of_ae_differentiableAt hf hdiff F hF,
    hdiff] with x hx hdx
  have hre : hilbertPV f x = (hilbertTransform F x).re := congrArg Complex.re hx
  rw [← hre]
  exact hasHilbertPV_of_differentiableAt hf hdx

/-- Compactly supported differentiable real functions have their principal
values represented by the spectral Hilbert transform. -/
theorem hilbertPV_eq_hilbertTransform_ae_of_differentiable_compactSupport {f : ℝ → ℝ}
    (hdiff : Differentiable ℝ f) (hsupp : HasCompactSupport f)
    (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F) :
    (fun x ↦ (hilbertPV f x : ℂ)) =ᵐ[volume] hilbertTransform F :=
  hilbertPV_eq_hilbertTransform_ae_of_ae_differentiableAt
    (memLp_one_iff_integrable.mp (hdiff.continuous.memLp_of_hasCompactSupport hsupp))
    (Eventually.of_forall hdiff) F hF

/-- The spectral/principal-value identification applies in particular to compact
`C¹` profiles; it does not require smoothness of all orders. -/
theorem hilbertPV_eq_hilbertTransform_ae_of_contDiff_one_compactSupport {f : ℝ → ℝ}
    (hsmooth : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f)
    (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F) :
    (fun x ↦ (hilbertPV f x : ℂ)) =ᵐ[volume] hilbertTransform F :=
  hilbertPV_eq_hilbertTransform_ae_of_differentiable_compactSupport
    (hsmooth.differentiable (by norm_num)) hsupp F hF

end

end PDE.Analysis
