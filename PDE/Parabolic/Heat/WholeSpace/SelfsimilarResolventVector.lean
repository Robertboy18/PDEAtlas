/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarResolventAdjoint
public import PDE.Fluid.Incompressible.LerayProjection.Heat
public import PDE.Fluid.Incompressible.LerayProjection.WeakDivergence
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The free self-similar resolvent on vector fields

For `μ ≥ 1/2` the shifted resolvent `R_μ = (μ + L₀)⁻¹` maps `L²(ℝⁿ)` into `H²(ℝⁿ)` with a
bound uniform in `μ`. Its first-order part is smaller: the frequency weight `|ξ|` is controlled by
`|ξ|² ≤ c/2 + |ξ|⁴/(2c)` with `c = μ/(4π²)`, so `‖|ξ| 𝓕(R_μ f)‖ ≤ ‖f‖/(2π√μ)` and the `H¹`
norm of `R_μ f` is `O(μ^{-1/2}) ‖f‖`.

Applied componentwise to vector fields, the resolvent is the Laplace transform of the vector
free evolution. The Leray projection commutes with that evolution, hence with the resolvent, so
the resolvent of a divergence-free field is a divergence-free `H¹` field. Against smooth
compactly supported test fields the vector resolvent `z = R_μ h` satisfies
`∑ᵢ ∫ zᵢ ((μ + (n-1)/2) φᵢ + (1/2) (x·∇φ)ᵢ - Δφᵢ) = ∑ᵢ ∫ hᵢ φᵢ`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open BesselPotentialSpace PDE.Analysis.Evolution Set Filter Topology IncompressibleFlow
open scoped ENNReal NNReal Sobolev BesselPotentialSpace SchwartzMap ContDiff


namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- The transform `R_μ f` has mass at most `‖f‖ / μ`. -/
private theorem eLpNorm_fourier_selfsimilarResolvent_le (hn : 2 ≤ n) {μ : ℝ} (hμ0 : 0 < μ)
    (f : W^{0,2}(ℝ^n)) :
    eLpNorm ((𝓕 (baseL2 (selfsimilarResolvent n hn hμ0 f)) :
      Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) 2 volume ≤ ENNReal.ofReal (μ⁻¹ * ‖f‖) := by
  rw [← Lp.enorm_def, ← ofReal_norm, Lp.norm_fourier_eq, ← norm_eq_norm_baseL2_of_order_zero]
  exact ENNReal.ofReal_le_ofReal (((selfsimilarResolvent n hn hμ0).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (norm_selfsimilarResolvent_le hn hμ0) (norm_nonneg _)))

/-- The frequency-weighted transform `|ξ| R_μ f` has mass at most `‖f‖ / (2π √μ)`. -/
theorem eLpNorm_norm_mul_fourier_selfsimilarResolvent_le (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) (f : W^{0,2}(ℝ^n)) :
    eLpNorm (fun ξ ↦ ((‖ξ‖ : ℝ) : ℂ) *
        (𝓕 (baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f)) :
          Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹ * ‖f‖) := by
  have hμ0 : 0 < μ := by linarith
  set z := (𝓕 (baseL2 (selfsimilarResolvent n hn hμ0 f)) :
    Lp ℂ 2 (volume : Measure (ℝ^n))) with hz
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ^n ↦ ((‖ξ‖ : ℝ) : ℂ) * z ξ) volume :=
    ((Complex.continuous_ofReal.comp continuous_norm).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable z)
  have hmeas2 : AEStronglyMeasurable (fun ξ : ℝ^n ↦ ((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ) volume :=
    ((Complex.continuous_ofReal.comp (continuous_norm.pow 2)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable z)
  have h2 := eLpNorm_sq_norm_mul_fourier_selfsimilarResolvent_le hn hμ f
  rw [← hz] at h2
  have h0 : eLpNorm (z : ℝ^n → ℂ) 2 volume ≤ ENNReal.ofReal (μ⁻¹ * ‖f‖) :=
    eLpNorm_fourier_selfsimilarResolvent_le hn hμ0 f
  set c : ℝ := μ / (4 * Real.pi ^ 2)
  have hc : 0 < c := by positivity
  -- pointwise `|ξ|² ≤ c/2 + |ξ|⁴/(2c)`
  have hpt : ∀ ξ : ℝ^n, ENNReal.ofReal (‖((‖ξ‖ : ℝ) : ℂ) * z ξ‖ ^ 2) ≤
      ENNReal.ofReal (c / 2) * ENNReal.ofReal (‖z ξ‖ ^ 2) +
        ENNReal.ofReal ((2 * c)⁻¹) * ENNReal.ofReal (‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ‖ ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      abs_of_nonneg (sq_nonneg ‖ξ‖)]
    have key : ‖ξ‖ ^ 2 ≤ c / 2 + (2 * c)⁻¹ * ‖ξ‖ ^ 4 := by
      have h := sq_nonneg (‖ξ‖ ^ 2 - c)
      field_simp
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right key (sq_nonneg ‖z ξ‖)]
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
  refine (lintegral_ofReal_norm_pow_eq_eLpNorm_pow hmeas two_ne_zero).symm.trans_le ?_
  calc ∫⁻ ξ, ENNReal.ofReal (‖((‖ξ‖ : ℝ) : ℂ) * z ξ‖ ^ 2) ≤
        ∫⁻ ξ, (ENNReal.ofReal (c / 2) * ENNReal.ofReal (‖z ξ‖ ^ 2) +
          ENNReal.ofReal ((2 * c)⁻¹) * ENNReal.ofReal (‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ‖ ^ 2)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (c / 2) * (∫⁻ ξ, ENNReal.ofReal (‖z ξ‖ ^ 2)) +
          ENNReal.ofReal ((2 * c)⁻¹) *
            ∫⁻ ξ, ENNReal.ofReal (‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ‖ ^ 2) := by
        rw [lintegral_add_left' (((Lp.aestronglyMeasurable z).aemeasurable.norm.pow_const
          2).ennreal_ofReal.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (c / 2) * ENNReal.ofReal (μ⁻¹ * ‖f‖) ^ 2 +
          ENNReal.ofReal ((2 * c)⁻¹) * ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹ * ‖f‖) ^ 2 := by
        rw [lintegral_ofReal_norm_pow_eq_eLpNorm_pow (Lp.aestronglyMeasurable z) two_ne_zero,
          lintegral_ofReal_norm_pow_eq_eLpNorm_pow hmeas2 two_ne_zero, Nat.cast_ofNat]
        gcongr
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹ * ‖f‖) ^ 2 := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
        congr 1
        have hs : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
        have hsp : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
        simp only [c]
        field_simp
        rw [hs]
        ring

/-- The first-order part of the resolvent decays like `μ^{-1/2}`. -/
theorem norm_lowerOrder_selfsimilarResolventH2_le (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    (f : W^{0,2}(ℝ^n)) :
    ‖lowerOrderCLM (n := n) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2)
        (selfsimilarResolventH2 n hn hμ f)‖ ≤
      toWkpSpaceNormBound n 1 * ((μ⁻¹ + (2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹) * ‖f‖) := by
  have hμ0 : 0 < μ := by linarith
  set z := (𝓕 (baseL2 (selfsimilarResolvent n hn hμ0 f)) :
    Lp ℂ 2 (volume : Measure (ℝ^n))) with hz
  have h1 := eLpNorm_norm_mul_fourier_selfsimilarResolvent_le hn hμ f
  rw [← hz] at h1
  have h0 : eLpNorm (z : ℝ^n → ℂ) 2 volume ≤ ENNReal.ofReal (μ⁻¹ * ‖f‖) :=
    eLpNorm_fourier_selfsimilarResolvent_le hn hμ0 f
  have hmeasB : AEStronglyMeasurable (fun ξ ↦ besselSymbol n ((1 : ℕ) : ℝ) ξ * z ξ) volume :=
    continuous_besselSymbol.aestronglyMeasurable.mul (Lp.aestronglyMeasurable z)
  have hsum : eLpNorm (fun ξ ↦ besselSymbol n ((1 : ℕ) : ℝ) ξ * z ξ) 2 volume ≤
      ENNReal.ofReal ((μ⁻¹ + (2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹) * ‖f‖) := by
    have hle : eLpNorm (fun ξ ↦ besselSymbol n ((1 : ℕ) : ℝ) ξ * z ξ) 2 volume ≤
        eLpNorm (fun ξ ↦ (z : ℝ^n → ℂ) ξ + ((‖ξ‖ : ℝ) : ℂ) * z ξ) 2 volume := by
      refine eLpNorm_mono hmeasB fun ξ ↦ ?_
      have hrw : (z : ℝ^n → ℂ) ξ + ((‖ξ‖ : ℝ) : ℂ) * z ξ = (((1 + ‖ξ‖ : ℝ)) : ℂ) * z ξ := by
        push_cast; ring
      rw [hrw, norm_mul, norm_mul, besselSymbol, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [show (((1 : ℕ) : ℝ) / 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
        Real.sqrt_le_left (by positivity)]
      nlinarith [norm_nonneg ξ]
    refine (hle.trans ((eLpNorm_add_le (f := (z : ℝ^n → ℂ))
      (g := fun ξ ↦ ((‖ξ‖ : ℝ) : ℂ) * z ξ) (by norm_num)).trans (add_le_add h0 h1))).trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
  have hmem : MemLp (fun ξ ↦ besselSymbol n ((1 : ℕ) : ℝ) ξ * z ξ) 2 volume :=
    lt_of_le_of_lt hsum ENNReal.ofReal_lt_top
  obtain ⟨V, hV, hVnorm⟩ := exists_wkpSpace_of_memLp_besselWeight 1
    (selfsimilarResolvent n hn hμ0 f) hmem
  have hVeq : lowerOrderCLM (n := n) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2)
      (selfsimilarResolventH2 n hn hμ f) = V := by
    apply baseL2_injective
    rw [baseL2_lowerOrderCLM, baseL2_selfsimilarResolventH2, hV]
  rw [hVeq]
  exact hVnorm.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_le_of_le_ofReal (by positivity) hsum) toWkpSpaceNormBound_nonneg)

/-- Equal complexified base functions give equal real base coordinates. -/
theorem wkpBaseCoordinateCLM_eq_of_baseL2_eq {k m : ℕ} {U : W^{k,2}(ℝ^n)} {V : W^{m,2}(ℝ^n)}
    (h : baseL2 U = baseL2 V) : wkpBaseCoordinateCLM U = wkpBaseCoordinateCLM V := by
  apply Lp.ext
  rw [← complexifyL2CLM_base U, ← complexifyL2CLM_base V] at h
  have hAE : ⇑(wkpBaseCoordinateCLM U) =ᵐ[volume] ⇑(wkpBaseCoordinateCLM V) := by
    filter_upwards [Lp.ext_iff.mp h, complexifyL2CLM_ae (wkpBaseCoordinateCLM U),
      complexifyL2CLM_ae (wkpBaseCoordinateCLM V)] with x he hu hv
    exact Complex.ofReal_injective (hu.symm.trans (he.trans hv))
  simpa only [domainMeasure, Measure.restrict_univ] using hAE

/-- The shifted free self-similar resolvent, componentwise on vector `L²` fields. -/
def vectorSelfsimilarResolvent (n : ℕ) (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ) :
    VectorH n 0 →L[ℝ] VectorH n 0 :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ selfsimilarResolvent n hn hμ)

theorem vectorSelfsimilarResolvent_apply (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (u : VectorH n 0) (j : Fin n) :
    vectorSelfsimilarResolvent n hn hμ u j = selfsimilarResolvent n hn hμ (u j) :=
  rfl

theorem integrable_vectorSelfsimilarResolvent_integrand (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (u : VectorH n 0) :
    Integrable (fun s : ℝ ↦ Real.exp (-μ * s) • vectorSelfsimilarHeat n 0 s.toNNReal u)
      (volume.restrict (Ioi 0)) := by
  apply Integrable.of_eval_piLp
  intro j
  have h := integrableOn_selfsimilarResolvent_integrand hn hμ (u j)
  refine h.congr (Filter.Eventually.of_forall fun s ↦ ?_)
  simp only [StronglyContinuousSemigroup.realOrbit, selfsimilarHeatSobolevSemigroup_apply,
    PiLp.smul_apply, vectorSelfsimilarHeat_apply]

/-- The vector resolvent is the Laplace transform of the vector free self-similar flow. -/
theorem vectorSelfsimilarResolvent_eq_integral (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (u : VectorH n 0) :
    vectorSelfsimilarResolvent n hn hμ u =
      ∫ s in Ioi (0 : ℝ), Real.exp (-μ * s) • vectorSelfsimilarHeat n 0 s.toNNReal u := by
  apply PiLp.ext
  intro j
  rw [eval_integral_piLp (Integrable.eval_piLp
    (integrable_vectorSelfsimilarResolvent_integrand hn hμ u)) j]
  simp only [vectorSelfsimilarResolvent_apply, selfsimilarResolvent,
    StronglyContinuousSemigroup.laplaceTransform_apply, StronglyContinuousSemigroup.realOrbit,
    selfsimilarHeatSobolevSemigroup_apply, PiLp.smul_apply, vectorSelfsimilarHeat_apply]

/-- The Leray projection commutes with the vector resolvent. -/
theorem leraySobolev_vectorSelfsimilarResolvent (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (u : VectorH n 0) :
    IncompressibleFlow.leraySobolev n 0 (vectorSelfsimilarResolvent n hn hμ u) =
      vectorSelfsimilarResolvent n hn hμ (IncompressibleFlow.leraySobolev n 0 u) := by
  rw [vectorSelfsimilarResolvent_eq_integral, vectorSelfsimilarResolvent_eq_integral,
    ← (IncompressibleFlow.leraySobolev n 0).integral_comp_comm
      (integrable_vectorSelfsimilarResolvent_integrand hn hμ u)]
  congr 1
  funext s
  rw [map_smul, leraySobolev_vectorSelfsimilarHeat]

/-- The second-order realization of the vector resolvent, for `μ ≥ 1/2`. -/
def vectorSelfsimilarResolventH2 (n : ℕ) (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ) :
    VectorH n 0 →L[ℝ] VectorH n 2 :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ selfsimilarResolventH2 n hn hμ)

theorem vectorSelfsimilarResolventH2_apply (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    (u : VectorH n 0) (j : Fin n) :
    vectorSelfsimilarResolventH2 n hn hμ u j = selfsimilarResolventH2 n hn hμ (u j) :=
  rfl

theorem wkpBaseCoordinateCLM_vectorSelfsimilarResolventH2 (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) (u : VectorH n 0) (j : Fin n) :
    wkpBaseCoordinateCLM (vectorSelfsimilarResolventH2 n hn hμ u j) =
      wkpBaseCoordinateCLM (vectorSelfsimilarResolvent n hn (by linarith : 0 < μ) u j) :=
  wkpBaseCoordinateCLM_eq_of_baseL2_eq (baseL2_selfsimilarResolventH2 hn hμ (u j))

theorem norm_vectorSelfsimilarResolventH2_apply_le (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    (u : VectorH n 0) :
    ‖vectorSelfsimilarResolventH2 n hn hμ u‖ ≤
      toWkpSpaceNormBound n 2 * (μ⁻¹ + (4 * Real.pi ^ 2)⁻¹) * ‖u‖ := by
  have hC : 0 ≤ toWkpSpaceNormBound n 2 * (μ⁻¹ + (4 * Real.pi ^ 2)⁻¹) :=
    mul_nonneg toWkpSpaceNormBound_nonneg
      (add_nonneg (inv_nonneg.mpr (by linarith)) (by positivity))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [vectorSelfsimilarResolventH2_apply, ← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((selfsimilarResolventH2 n hn hμ).le_opNorm (u j)).trans
    (mul_le_mul_of_nonneg_right (norm_selfsimilarResolventH2_le hn hμ) (norm_nonneg _))

theorem norm_lowerOrder_vectorSelfsimilarResolventH2_le (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) (u : VectorH n 0) (j : Fin n) :
    ‖lowerOrderCLM (n := n) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2)
        (vectorSelfsimilarResolventH2 n hn hμ u j)‖ ≤
      toWkpSpaceNormBound n 1 * ((μ⁻¹ + (2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹) * ‖u‖) := by
  refine (norm_lowerOrder_selfsimilarResolventH2_le hn hμ (u j)).trans ?_
  apply mul_le_mul_of_nonneg_left _ toWkpSpaceNormBound_nonneg
  apply mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u j)
  have := Real.sqrt_pos.mpr (show 0 < μ by linarith)
  have : 0 < μ := by linarith
  positivity

/-- The resolvent of a divergence-free field is a divergence-free `H¹` field: the weak
divergence `∑ⱼ ∂ⱼ zⱼ` of `z = R_μ h` vanishes when `h` is fixed by the Leray projection. -/
theorem sum_partial_vectorLower_vectorSelfsimilarResolventH2 (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) {h : VectorH n 0} (hh : IncompressibleFlow.leraySobolev n 0 h = h) :
    ∑ j, wkpCoordinateCLM (singleDerivIndex n j)
      (vectorLower n 1 (vectorSelfsimilarResolventH2 n hn hμ h) j) = 0 := by
  have hμ0 : 0 < μ := by linarith
  set U := vectorLower n 1 (vectorSelfsimilarResolventH2 n hn hμ h)
  have hrow : l2SobolevRow (baseIndex n 1) U =
      l2SobolevRow (baseIndex n 0) (vectorSelfsimilarResolvent n hn hμ0 h) := by
    rw [l2SobolevRow_apply, l2SobolevRow_apply]
    congr 1
    funext j
    change wkpBaseCoordinateCLM (U j) =
      wkpBaseCoordinateCLM (vectorSelfsimilarResolvent n hn hμ0 h j)
    rw [vectorLower_apply, wkpBaseCoordinateCLM_lowerOrderCLM,
      wkpBaseCoordinateCLM_vectorSelfsimilarResolventH2]
  have hsol : l2SobolevRow (baseIndex n 1) U ∈ IncompressibleFlow.l2Solenoidal n := by
    rw [hrow, ← hh, ← leraySobolev_vectorSelfsimilarResolvent,
      IncompressibleFlow.l2SobolevRow_leraySobolev]
    exact IncompressibleFlow.lerayProjection_mem n _
  exact IncompressibleFlow.sum_firstDerivatives_eq_zero_of_l2Solenoidal U hsol

/-- The weak form of `(μ + L₀) z = h` for the vector resolvent `z`, tested against smooth
compactly supported vector fields. -/
theorem sum_integral_vectorSelfsimilarResolventH2_mul_adjoint (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 < μ) (h : VectorH n 0) {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (vectorSelfsimilarResolventH2 n hn hμ.le h i) :
        ℝ^n → ℝ) x * ((μ + ((n : ℝ) - 1) / 2) * φ x i + (1 / 2) * fderiv ℝ φ x x i -
          PDE.laplacian (fun z ↦ φ z i) x) =
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (h i) : ℝ^n → ℝ) x * φ x i := by
  apply Finset.sum_congr rfl
  intro i _
  have hφi : ContDiff ℝ ∞ (fun x ↦ φ x i) := (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hφ
  have key := integral_selfsimilarResolvent_mul_adjoint hn hμ (h i) hφi
    (hc.comp_left (g := fun v : ℝ^n ↦ v i) (by simp))
  rw [wkpBaseCoordinateCLM_vectorSelfsimilarResolventH2]
  convert key using 3 with x
  have hfd : fderiv ℝ (fun y ↦ φ y i) x x = fderiv ℝ φ x x i := by
    have := ((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt)).fderiv
    rw [show (fun y ↦ φ y i) = (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) ∘ φ from rfl, this]
    rfl
  rw [hfd, (hφi.contDiffAt.of_le (by simp)).coordinate_laplacian_eq_laplacian]
  rfl

end HeatEquation.WholeSpace
