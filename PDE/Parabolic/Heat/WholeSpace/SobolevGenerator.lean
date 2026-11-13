/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generator
public import PDE.Parabolic.Heat.WholeSpace.VectorSemigroup
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian.HigherOrder
import PDE.Analysis.MeasureTheory.LpNorm.Convergence

/-!
# The Laplacian generates the heat semigroup on Sobolev spaces

On `L²(ℝⁿ)` the heat evolution is the Fourier multiplier `e^{-4π² t ‖ξ‖²}`. If the Fourier
transform of `g` is `-4π² ‖ξ‖²` times that of `f`, the difference quotients
`t⁻¹ (e^{tΔ} f - f) - g` have Fourier transforms `m_t(ξ) f̂(ξ)` with
`0 ≤ m_t(ξ) ≤ 4π² ‖ξ‖²` and `m_t → 0`, so they tend to zero by dominated convergence: `g` is the
generator of the heat semigroup at `f` (`hasGeneratorAt_heatL2Semigroup`). For `U ∈ H^{k+2}`
the weak Laplacian has Fourier transform `-4π² ‖ξ‖² Û` (`fourier_baseL2_higherOrderLaplacianCLM`),
and the integral characterization of the generator carries the statement from the base
functions to the whole graph: on `Hᵏ`, the generator of the heat semigroup at `U` is `ΔU`
(`hasGeneratorAt_heatSobolevSemigroup`), and the same holds componentwise on vector fields
(`hasGeneratorAt_vectorHeatSemigroup`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology FourierTransform SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Fractional PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Real Laplacian

namespace HeatEquation.WholeSpace

set_option linter.missingDocs true

variable {n k : ℕ}

/-- The heat semigroup on `L²` acts by the heat multiplier. -/
@[simp]
theorem heatL2Semigroup_apply (t : ℝ≥0) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    heatL2Semigroup n t u = heatL2 n t u :=
  rfl

/-- The difference quotient multiplier `t⁻¹ (e^{-4π² t ‖ξ‖²} - 1) + 4π² ‖ξ‖²`. -/
def heatQuotientSymbol (t : ℝ) (ξ : ℝ^n) : ℝ :=
  t⁻¹ * (Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) - 1) + 4 * π ^ 2 * ‖ξ‖ ^ 2

/-- For `t > 0` the difference quotient multiplier lies in `[0, 4π² ‖ξ‖²]`. -/
theorem heatQuotientSymbol_mem_Icc {t : ℝ} (ht : 0 < t) (ξ : ℝ^n) :
    heatQuotientSymbol t ξ ∈ Icc 0 (4 * π ^ 2 * ‖ξ‖ ^ 2) := by
  set x := 4 * π ^ 2 * t * ‖ξ‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hq : heatQuotientSymbol t ξ = t⁻¹ * (Real.exp (-x) - 1 + x) := by
    rw [heatQuotientSymbol, hx]
    field_simp
  rw [hq]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr ht.le) (by linarith)
  · calc t⁻¹ * (Real.exp (-x) - 1 + x) ≤ t⁻¹ * x :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr ht.le)
      _ = 4 * π ^ 2 * ‖ξ‖ ^ 2 := by rw [hx]; field_simp

/-- The difference quotient multiplier tends to zero as `t → 0⁺`. -/
theorem tendsto_heatQuotientSymbol (ξ : ℝ^n) :
    Tendsto (fun t ↦ heatQuotientSymbol t ξ) (𝓝[>] 0) (𝓝 0) := by
  set c := 4 * π ^ 2 * ‖ξ‖ ^ 2 with hc
  have h' := ((((hasDerivAt_id (0 : ℝ)).const_mul (4 * π ^ 2)).mul_const (‖ξ‖ ^ 2)).neg).exp
  have hval : Real.exp ((-fun y : ℝ ↦ 4 * π ^ 2 * id y * ‖ξ‖ ^ 2) 0) *
      -(4 * π ^ 2 * 1 * ‖ξ‖ ^ 2) = -c := by
    rw [Pi.neg_apply, id, mul_zero, zero_mul, neg_zero, Real.exp_zero, one_mul, mul_one, hc]
  have hd : HasDerivAt (fun t : ℝ ↦ Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2))) (-c) 0 := by
    rw [← hval]
    exact h'
  have h2 := hd.tendsto_slope_zero_right.add_const c
  rw [neg_add_cancel] at h2
  refine h2.congr fun t ↦ ?_
  simp only [heatQuotientSymbol, zero_add, mul_zero, zero_mul, neg_zero, Real.exp_zero,
    smul_eq_mul, hc]

/-- The difference quotient multiplier is continuous in the frequency. -/
theorem continuous_heatQuotientSymbol (t : ℝ) : Continuous (heatQuotientSymbol (n := n) t) := by
  unfold heatQuotientSymbol
  fun_prop

/-- **The heat generator on `L²`.** If `ĝ = -4π² ‖ξ‖² f̂`, then `g` is the generator of the heat
semigroup at `f`. -/
theorem hasGeneratorAt_heatL2Semigroup {f g : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hfg : ((𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        ((𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ) :
    (heatL2Semigroup n).HasGeneratorAt f g := by
  have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext x
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h ↦ lt_of_le_of_ne h.1 (Ne.symm h.2), fun h ↦ ⟨h.le, h.ne'⟩⟩
  rw [StronglyContinuousSemigroup.HasGeneratorAt, hasDerivWithinAt_iff_tendsto_slope, hset,
    tendsto_iff_norm_sub_tendsto_zero]
  have hAE (t : ℝ≥0) : ⇑(heatSymbolLinf n t) =ᵐ[volume] heatSymbol n t :=
    (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  have hsub : ∀ x y : Lp ℂ 2 (volume : Measure (ℝ^n)), 𝓕 (x - y) = 𝓕 x - 𝓕 y :=
    fun x y ↦ (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).map_sub x y
  have hsmul : ∀ (c : ℂ) (x : Lp ℂ 2 (volume : Measure (ℝ^n))), 𝓕 (c • x) = c • 𝓕 x :=
    fun c x ↦ (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).map_smul c x
  have hkey : ∀ t : ℝ, 0 < t → ‖slope ((heatL2Semigroup n).realOrbit f) 0 t - g‖ =
      (eLpNorm (fun ξ ↦ ((heatQuotientSymbol t ξ : ℝ) : ℂ) *
        ((𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ) 2
        volume).toReal := by
    intro t ht
    have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
    have hsl : slope ((heatL2Semigroup n).realOrbit f) 0 t - g =
        ((t⁻¹ : ℝ) : ℂ) • (heatL2 n t.toNNReal f - f) - g := by
      rw [slope_def_module, sub_zero, StronglyContinuousSemigroup.realOrbit_zero,
        Complex.coe_smul]
      rfl
    rw [hsl, ← Lp.norm_fourier_eq, Lp.norm_def, hsub, hsmul, hsub, fourier_heatL2]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (((t⁻¹ : ℝ) : ℂ) • ((heatSymbolLinf n t.toNNReal • 𝓕 f :
        Lp ℂ 2 volume) - 𝓕 f)) (𝓕 g),
      Lp.coeFn_smul ((t⁻¹ : ℝ) : ℂ) ((heatSymbolLinf n t.toNNReal • 𝓕 f : Lp ℂ 2 volume) - 𝓕 f),
      Lp.coeFn_sub (heatSymbolLinf n t.toNNReal • 𝓕 f : Lp ℂ 2 volume) (𝓕 f),
      Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t.toNNReal) (𝓕 f), hAE t.toNNReal, hfg]
      with ξ h1 h2 h3 h4 h5 h6
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, Pi.smul_apply', h5, h6,
      heatSymbol, hcoe, heatQuotientSymbol]
    push_cast
    ring
  have hlim : Tendsto (fun t ↦ eLpNorm (fun ξ ↦ ((heatQuotientSymbol t ξ : ℝ) : ℂ) *
      ((𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ) 2 volume) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_eLpNorm_zero_of_dominated_convergence (by norm_num) (by norm_num)
      (fun ξ ↦ ‖((𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ‖ₑ ^ (2 : ℝ≥0∞).toReal)
      ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t ↦
        ((Complex.continuous_ofReal.comp
          (continuous_heatQuotientSymbol t)).aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hfg] with ξ hξ
      rw [hξ]
      have hq := heatQuotientSymbol_mem_Icc (mem_Ioi.mp ht) ξ
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm, ← ofReal_norm, norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg hq.1, Real.norm_of_nonneg (by positivity)]
      gcongr
      exact hq.2
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num)
        (Lp.memLp (𝓕 g)).eLpNorm_lt_top).ne
    · exact Eventually.of_forall fun ξ ↦ by
        simpa using ((Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_heatQuotientSymbol ξ)).mul_const
          (((𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ)
  refine (ENNReal.toReal_zero ▸ (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht using (hkey t ht).symm

/-! ### The Fourier transform of the weak Laplacian -/

/-- The complexified coordinate of a whole-space Sobolev function. -/
theorem complexifyL2CLM_wkpCoordinateCLM (U : W^{k,2}(ℝ^n)) (a : DerivIndex n k) :
    complexifyL2CLM n (wkpCoordinateCLM a U) = cxL2 (memLp_coordFun U a) := by
  apply Lp.ext
  have hb : (cxL2 (memLp_coordFun U a) : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ (wkpCoordinateCLM a U x : ℂ) :=
    (memLp_coordFun U a).ofReal.coeFn_toLp
  exact (complexifyL2CLM_ae _).trans hb.symm

/-- The Fourier transform of the weak Laplacian of `U ∈ H²(ℝⁿ)` is `-4π² ‖ξ‖² Û`. -/
theorem fourier_complexifyL2CLM_laplacian (U : W^{2,2}(ℝ^n)) :
    ((𝓕 (complexifyL2CLM n (Δ U)) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        ((𝓕 (baseL2 U) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ := by
  have hsum : complexifyL2CLM n (Δ U) = ∑ i : Fin n, pureDerivL2 U i := by
    rw [laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM, sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ complexifyL2CLM_wkpCoordinateCLM U (pairDerivIndex n i i)
  have hF : 𝓕 (complexifyL2CLM n (Δ U)) = ∑ i : Fin n, 𝓕 (pureDerivL2 U i) := by
    rw [hsum]
    exact map_sum (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) _ _
  rw [hF]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n ↦ 𝓕 (pureDerivL2 U i)),
    pureSymbol_mul_fourier_ae U] with ξ h1 h2
  rw [h1, Finset.sum_apply]
  simp only [← h2, ← Finset.sum_mul, pureSymbol]
  congr 1
  have hnorm : ‖ξ‖ ^ 2 = ∑ i : Fin n, (ξ.ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Real.norm_eq_abs, sq_abs]
  have key : ∀ i : Fin n, (2 * (π : ℂ) * Complex.I * ((ξ.ofLp i : ℝ) : ℂ)) ^ 2 =
      -(4 * (π : ℂ) ^ 2 * ((ξ.ofLp i : ℝ) : ℂ) ^ 2) := fun i ↦ by
    rw [mul_pow, mul_pow, Complex.I_sq]
    ring
  rw [hnorm, Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_neg_distrib, ← Finset.mul_sum]
  push_cast
  ring

/-- The Fourier transform of the higher-order weak Laplacian of `U ∈ Hᵏ(ℝⁿ)` is
`-4π² ‖ξ‖² Û`. -/
theorem fourier_baseL2_higherOrderLaplacianCLM {r : ℕ} (h : r + 2 ≤ k) (U : W^{k,2}(ℝ^n)) :
    ((𝓕 (baseL2 (higherOrderLaplacianCLM h U)) : Lp ℂ 2 (volume : Measure (ℝ^n))) :
        ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        ((𝓕 (baseL2 U) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) ξ := by
  rw [← complexifyL2CLM_base, higherOrderLaplacianCLM_base,
    ← baseL2_lowerOrderCLM (show 2 ≤ k by omega) U]
  exact fourier_complexifyL2CLM_laplacian _

/-! ### The generator on Sobolev graphs -/

/-- The complexified base function as a continuous real-linear map. -/
def baseL2CLM (n k : ℕ) : W^{k,2}(ℝ^n) →L[ℝ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  (complexifyL2CLM n).comp wkpBaseCoordinateCLM

theorem baseL2CLM_apply (U : W^{k,2}(ℝ^n)) : baseL2CLM n k U = baseL2 U :=
  complexifyL2CLM_base U

/-- The heat semigroup on Sobolev graphs acts by the heat evolution. -/
@[simp]
theorem heatSobolevSemigroup_apply (t : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    heatSobolevSemigroup n k t u = heatSobolev n k t u :=
  rfl

/-- The base function of the integrated heat orbit is the integrated `L²` heat orbit. -/
theorem baseL2_integratedOperator (t : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    baseL2 ((heatSobolevSemigroup n k).integratedOperator t u) =
      (heatL2Semigroup n).integratedOperator t (baseL2 u) := by
  rw [← baseL2CLM_apply, StronglyContinuousSemigroup.integratedOperator_apply,
    StronglyContinuousSemigroup.integratedOperator_apply,
    ← (baseL2CLM n k).intervalIntegral_comp_comm
      (((heatSobolevSemigroup n k).continuous_realOrbit u).intervalIntegrable 0 t)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [StronglyContinuousSemigroup.realOrbit, heatSobolevSemigroup_apply, baseL2CLM_apply,
    baseL2_heatSobolev, heatL2Semigroup_apply]

/-- **The heat generator on `Hᵏ`.** For `U ∈ H^{k+2}(ℝⁿ)` the generator of the heat semigroup on
`Hᵏ` at `U` is the weak Laplacian `ΔU`. -/
theorem hasGeneratorAt_heatSobolevSemigroup (U : W^{k + 2,2}(ℝ^n)) :
    (heatSobolevSemigroup n k).HasGeneratorAt (lowerOrderCLM (by omega : k ≤ k + 2) U)
      (higherOrderLaplacianCLM (by omega : k + 2 ≤ k + 2) U) := by
  rw [StronglyContinuousSemigroup.hasGeneratorAt_iff_integratedOperator]
  intro t
  have hL2 := (StronglyContinuousSemigroup.hasGeneratorAt_iff_integratedOperator _ _ _).mp
    (hasGeneratorAt_heatL2Semigroup
      (fourier_baseL2_higherOrderLaplacianCLM (r := k) (by omega) U)) t
  apply baseL2_injective
  rw [baseL2_integratedOperator, hL2]
  change heatL2 n t (baseL2 U) - baseL2 U = baseL2 (heatSobolev n k t
    (lowerOrderCLM (by omega : k ≤ k + 2) U) - lowerOrderCLM (by omega : k ≤ k + 2) U)
  rw [← baseL2CLM_apply (heatSobolev n k t _ - _), map_sub, baseL2CLM_apply, baseL2CLM_apply,
    baseL2_heatSobolev, baseL2_lowerOrderCLM]

/-- The heat evolution commutes with the weak Laplacian. -/
theorem heatSobolev_higherOrderLaplacianCLM (t : ℝ≥0) (U : W^{k + 2,2}(ℝ^n)) :
    heatSobolev n k t (higherOrderLaplacianCLM (by omega : k + 2 ≤ k + 2) U) =
      higherOrderLaplacianCLM (by omega : k + 2 ≤ k + 2) (heatSobolev n (k + 2) t U) := by
  apply baseL2_injective
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (baseL2 (heatSobolev n k t (higherOrderLaplacianCLM _ U))) =
    𝓕 (baseL2 (higherOrderLaplacianCLM _ (heatSobolev n (k + 2) t U)))
  rw [baseL2_heatSobolev, fourier_heatL2]
  have hAE : ⇑(heatSymbolLinf n t) =ᵐ[volume] heatSymbol n t :=
    (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t)
      (𝓕 (baseL2 (higherOrderLaplacianCLM (by omega : k + 2 ≤ k + 2) U))),
    fourier_baseL2_higherOrderLaplacianCLM (r := k) (by omega) U,
    fourier_baseL2_higherOrderLaplacianCLM (r := k) (by omega) (heatSobolev n (k + 2) t U),
    Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) (𝓕 (baseL2 U)), hAE] with ξ h₁ h₂ h₃ h₄ h₅
  rw [h₁, Pi.smul_apply', h₂, h₃, baseL2_heatSobolev, fourier_heatL2, h₄, Pi.smul_apply']
  simp only [smul_eq_mul]
  ring

/-- The weak Laplacian on vector fields, from vector `H^{k+2}` to vector `Hᵏ`. -/
def vectorLaplacian (n k : ℕ) : VectorH n (k + 2) →L[ℝ] VectorH n k :=
  ContinuousLinearMap.piLpMap 2
    (fun _ : Fin n ↦ higherOrderLaplacianCLM (n := n) (p := 2) (by omega : k + 2 ≤ k + 2))

/-- Each component of the vector Laplacian is the scalar weak Laplacian. -/
@[simp]
theorem vectorLaplacian_apply (v : VectorH n (k + 2)) (j : Fin n) :
    vectorLaplacian n k v j = higherOrderLaplacianCLM (by omega : k + 2 ≤ k + 2) (v j) := by
  simp only [vectorLaplacian, ContinuousLinearMap.piLpMap_apply]

/-- **The heat generator on vector `Hᵏ`.** For `v ∈ H^{k+2}` the generator of the vector heat
semigroup on vector `Hᵏ` at `v` is the vector Laplacian `Δv`. -/
theorem hasGeneratorAt_vectorHeatSemigroup (v : VectorH n (k + 2)) :
    (vectorHeatSemigroup n k).HasGeneratorAt (vectorLowerOrderCLM (by omega : k ≤ k + 2) v)
      (vectorLaplacian n k v) := by
  rw [StronglyContinuousSemigroup.hasGeneratorAt_iff_integratedOperator]
  intro t
  refine PiLp.ext fun j ↦ ?_
  have hj := (StronglyContinuousSemigroup.hasGeneratorAt_iff_integratedOperator _ _ _).mp
    (hasGeneratorAt_heatSobolevSemigroup (v j)) t
  rw [StronglyContinuousSemigroup.integratedOperator_apply] at hj ⊢
  have hproj := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n ↦ W^{k,2}(ℝ^n)) j :
      VectorH n k →L[ℝ] W^{k,2}(ℝ^n)).intervalIntegral_comp_comm
    (((vectorHeatSemigroup n k).continuous_realOrbit (vectorLaplacian n k v)).intervalIntegrable
      (μ := volume) 0 t)
  simp only [PiLp.proj_apply] at hproj
  rw [← hproj, PiLp.sub_apply]
  refine (intervalIntegral.integral_congr fun s _ ↦ ?_).trans hj
  simp only [StronglyContinuousSemigroup.realOrbit, vectorHeatSemigroup_apply, vectorHeat_apply,
    vectorLaplacian_apply, heatSobolevSemigroup_apply]

/-- The vector heat evolution commutes with the vector Laplacian. -/
theorem vectorHeat_vectorLaplacian (t : ℝ≥0) (v : VectorH n (k + 2)) :
    vectorHeat n k t (vectorLaplacian n k v) = vectorLaplacian n k (vectorHeat n (k + 2) t v) :=
  PiLp.ext fun j ↦ by
    simp only [vectorHeat_apply, vectorLaplacian_apply, heatSobolev_higherOrderLaplacianCLM]

end HeatEquation.WholeSpace
