/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Schwartz
public import PDE.Parabolic.Heat.InitialValue
public import PDE.Analysis.Distribution.Schwartz.KernelConvolution
import PDE.Parabolic.Heat.Kernel.Scaling
import PDE.Analysis.Integration.Convolution.Young
import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation

/-!
# The Gaussian heat flow of Lᵖ data

`gaussianFlow t f` is the convolution of `f : ℝ^n → E` with the heat kernel at time `t > 0`, and `f`
itself at `t ≤ 0`. For real data it is the solution (9) of the initial-value problem in Evans's
§2.3.1. The flow of `Lᵖ` data, `1 ≤ p ≤ ∞`, is smooth at positive times and satisfies the smoothing
estimate

`‖Dᵏ (G_t * f)‖_{Lʳ} ≤ C t^(-k/2 - (n/2)(1/p - 1/r)) ‖f‖_{Lᵖ}`

for `1 ≤ p ≤ r ≤ ∞`, with `C` independent of `t` and `f`. In dimension 3 this is the estimate (2.8)
that Hou, Wang and Yang recall for the heat semigroup. Evans's §2.3.1, Theorem 1, gives smoothness
in `(x, t)` for bounded continuous data; for `Lᵖ` data the flow is smooth in `x` at each positive
time.

## Main definitions

* `gaussianFlow`: the heat flow `G_t * f` at `t > 0`, and the datum at `t ≤ 0`.

## Main results

* `initialValueSolution_eq_gaussianFlow`: for real data the flow is `initialValueSolution`.
* `gaussianFlow_scaling`, `gaussianFlow_eq_comp_smul`: parabolic scaling.
* `contDiff_gaussianFlow`: smoothness at positive times.
* `ContinuousLinearMap.map_gaussianFlow`, `gaussianFlow_component`: continuous linear maps commute
  with the flow, so vector fields flow componentwise.
* `eLpNorm_iteratedFDeriv_gaussianFlow_le`: the smoothing estimate.
* `memLp_iteratedFDeriv_gaussianFlow`, `memLp_gaussianFlow`: the flow maps `Lᵖ` into `Lʳ` with all
  derivatives.

## How it works

The parabolic scaling `gaussianFlow (a² t) f (a • x) = gaussianFlow t (f (a • ·)) x`
(`gaussianFlow_scaling`) is the flow form of the invariance of the heat equation under
`u(x, t) ↦ u(λx, λ²t)` noted in Evans's §2.3.1(a); it writes every positive time as the time-one
flow of a dilated datum, read at a dilated point (`gaussianFlow_eq_comp_smul`). At time one the
kernel is a Schwartz function (`heatKernelSchwartz`), so the flow of every polynomially weighted
integrable datum is smooth and its derivatives are convolutions with the derivatives of the kernel
(`contDiff_gaussianFlow_one`, `enorm_iteratedFDeriv_gaussianFlow_one_le`). Young's inequality gives
`‖Dᵏ (G₁ * f)‖_{Lʳ} ≤ ‖Dᵏ G₁‖_{L^q} ‖f‖_{Lᵖ}` with `1/p + 1/q = 1 + 1/r`
(`eLpNorm_iteratedFDeriv_gaussianFlow_one_le`), and the two dilations contribute the power of `t`
(`eLpNorm_iteratedFDeriv_gaussianFlow_le_of_young`). The constant is `C = ‖Dᵏ G₁‖_{L^q}`, which is
finite because the derivatives of a Schwartz function lie in every `L^q`.

## Implementation notes

The flow is Mathlib's convolution `MeasureTheory.convolution` with the bilinear map
`ContinuousLinearMap.lsmul`, so the data may take values in any real normed space `E`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(a), the scaling remark, p. 45, and §2.3.1(b), (9) and
  Theorem 1 (Solution of initial-value problem), p. 47.
  <https://doi.org/10.1090/gsm/019>
* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray-Hopf solutions to the unforced
  incompressible 3D Navier-Stokes Equation", arXiv:2509.25116v2, 2026, Section 2.2, (2.8),
  p. 12.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open PDE (polynomialWeight)
open MeasureTheory SchwartzMap Module
open scoped ENNReal Convolution SchwartzMap

attribute [local instance] secondCountableTopologyEither_of_left

namespace HeatEquation.WholeSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The heat flow `G_t * f` of data `f : ℝ^n → E`, with `G_t` the Gaussian heat kernel at time
`t > 0`; at `t ≤ 0` it is the datum. -/
def gaussianFlow (t : ℝ) (f : ℝ^n → E) : ℝ^n → E :=
  if 0 < t then (fun x ↦ fundamentalSolutionHeat x t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  else f

theorem gaussianFlow_of_nonpos {t : ℝ} (ht : t ≤ 0) (f : ℝ^n → E) : gaussianFlow t f = f := by
  simp [gaussianFlow, not_lt.mpr ht]

theorem gaussianFlow_apply {t : ℝ} (ht : 0 < t) (f : ℝ^n → E) (x : ℝ^n) :
    gaussianFlow t f x = ∫ y, fundamentalSolutionHeat (x - y) t • f y := by
  simp only [gaussianFlow, ht, ↓reduceIte]
  rw [convolution_eq_swap]
  rfl

/-- At time one the flow is the convolution with the Schwartz heat kernel. -/
theorem gaussianFlow_one_eq (f : ℝ^n → E) :
    gaussianFlow 1 f = ⇑(heatKernelSchwartz n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f := by
  simp only [gaussianFlow, one_pos, ↓reduceIte]
  rfl

/-- For real data the flow is the heat evolution `initialValueSolution`. -/
theorem initialValueSolution_eq_gaussianFlow (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ) :
    initialValueSolution g x t = gaussianFlow t g x := by
  by_cases ht : 0 < t
  · rw [gaussianFlow_apply ht]
    simp only [initialValueSolution, not_le.mpr ht, ↓reduceIte, smul_eq_mul]
  · rw [gaussianFlow_of_nonpos (not_lt.mp ht)]
    simp only [initialValueSolution, not_lt.mp ht, ↓reduceIte]

/-- Parabolic scaling of the heat flow. For real data at positive time this is
`HeatEquation.initialValueSolution_parabolic_rescale` at the origin of the rescaled datum. -/
theorem gaussianFlow_scaling {a : ℝ} (ha : 0 < a) (t : ℝ) (f : ℝ^n → E) (x : ℝ^n) :
    gaussianFlow (a ^ 2 * t) f (a • x) = gaussianFlow t (fun y ↦ f (a • y)) x := by
  by_cases ht : 0 < t
  swap
  · have hat : a ^ 2 * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp ht)
    rw [gaussianFlow_of_nonpos hat, gaussianFlow_of_nonpos (not_lt.mp ht)]
  have hat : 0 < a ^ 2 * t := by positivity
  rw [gaussianFlow_apply hat, gaussianFlow_apply ht]
  set h : ℝ^n → E := fun y ↦ fundamentalSolutionHeat (a • x - y) (a ^ 2 * t) • f y
  have hdil := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure (ℝ^n))) h a
    (hR := ha.le)
  have hpoint (y : ℝ^n) : h (a • y) =
      (a ^ n)⁻¹ • (fundamentalSolutionHeat (x - y) t • f (a • y)) := by
    simp only [h]
    rw [← smul_sub, fundamentalSolutionHeat_scaling _ t a ht ha, Real.rpow_neg ha.le,
      Real.rpow_natCast, mul_smul]
  simp_rw [hpoint, integral_smul, finrank_euclideanSpace_fin] at hdil
  exact (smul_right_injective E (inv_ne_zero (pow_ne_zero n ha.ne')) hdil).symm

/-- Every positive time is the time-one flow of a dilated datum, read at a dilated point. -/
theorem gaussianFlow_eq_comp_smul {t : ℝ} (ht : 0 < t) (f : ℝ^n → E) :
    gaussianFlow t f =
      fun x ↦ gaussianFlow 1 (fun y ↦ f (Real.sqrt t • y)) ((Real.sqrt t)⁻¹ • x) := by
  funext x
  have hs := Real.sqrt_pos.mpr ht
  have h := gaussianFlow_scaling hs 1 f ((Real.sqrt t)⁻¹ • x)
  rwa [Real.sq_sqrt ht.le, mul_one, smul_smul, mul_inv_cancel₀ hs.ne', one_smul] at h

/-- The heat flow commutes with constant multiples. -/
theorem gaussianFlow_const_smul (t c : ℝ) (f : ℝ^n → E) :
    gaussianFlow t (fun x ↦ c • f x) = c • gaussianFlow t f := by
  by_cases ht : 0 < t
  · funext x
    simp only [Pi.smul_apply, gaussianFlow_apply ht, smul_comm _ c, integral_smul]
  · rw [gaussianFlow_of_nonpos (not_lt.mp ht), gaussianFlow_of_nonpos (not_lt.mp ht)]
    rfl

variable {N : ℕ} {f : ℝ^n → E}

/-- The time-one flow of polynomially weighted integrable data is smooth. -/
theorem contDiff_gaussianFlow_one (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianFlow 1 f) := by
  rw [gaussianFlow_one_eq]
  exact contDiff_convolution _ _ hf

/-- The time-one flow is linear on polynomially weighted integrable data. -/
theorem gaussianFlow_one_sub {g : ℝ^n → E} (hf : Integrable (fun y ↦ polynomialWeight N y • f y))
    (hg : Integrable (fun y ↦ polynomialWeight N y • g y)) :
    gaussianFlow 1 (f - g) = gaussianFlow 1 f - gaussianFlow 1 g := by
  simp only [gaussianFlow_one_eq]
  exact convolution_sub _ _ hf hg

/-- The heat flow of `Lᵖ` data is smooth at positive times. -/
theorem contDiff_gaussianFlow {t : ℝ} (ht : 0 < t) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume) : ContDiff ℝ (⊤ : ℕ∞) (gaussianFlow t f) := by
  rw [gaussianFlow_eq_comp_smul ht]
  have hs := (Real.sqrt_pos.mpr ht).ne'
  exact (contDiff_gaussianFlow_one (PDE.integrable_polynomialWeight_smul_of_memLp hp
    (hf.comp_smul hs))).comp (contDiff_const_smul _)

/-- A continuous linear map commutes with the time-one flow of polynomially weighted data. -/
theorem _root_.ContinuousLinearMap.map_gaussianFlow_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) (x : ℝ^n) :
    T (gaussianFlow 1 f x) = gaussianFlow 1 (fun y ↦ T (f y)) x := by
  have hi : Integrable (fun y ↦ fundamentalSolutionHeat (x - y) 1 • f y) :=
    integrable_kernel (ContinuousLinearMap.lsmul ℝ ℝ) (heatKernelSchwartz n) hf x
  rw [gaussianFlow_apply one_pos, gaussianFlow_apply one_pos, ← T.integral_comp_comm hi]
  simp only [map_smul]

/-- A continuous linear map commutes with the heat flow of `Lᵖ` data. -/
theorem _root_.ContinuousLinearMap.map_gaussianFlow {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F) (t : ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p)
    (hf : MemLp f p volume) (x : ℝ^n) :
    T (gaussianFlow t f x) = gaussianFlow t (fun y ↦ T (f y)) x := by
  by_cases ht : 0 < t
  · rw [gaussianFlow_eq_comp_smul ht, gaussianFlow_eq_comp_smul ht]
    exact T.map_gaussianFlow_one (PDE.integrable_polynomialWeight_smul_of_memLp hp
      (hf.comp_smul (Real.sqrt_pos.mpr ht).ne')) _
  · rw [gaussianFlow_of_nonpos (not_lt.mp ht), gaussianFlow_of_nonpos (not_lt.mp ht)]

/-- The components of the heat flow of a vector field are the heat flows of its components. -/
theorem gaussianFlow_component {m : ℕ} (t : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) {g : ℝ^n → ℝ^m}
    (hg : MemLp g p volume) (x : ℝ^n) (i : Fin m) :
    gaussianFlow t g x i = gaussianFlow t (fun y ↦ g y i) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).map_gaussianFlow t hp hg x

/-- Pointwise bound for the derivatives of the time-one flow. -/
theorem enorm_iteratedFDeriv_gaussianFlow_one_le
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) (k : ℕ) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ k (gaussianFlow 1 f) x‖ₑ ≤
      ∫⁻ y, ‖iteratedFDeriv ℝ k (heatKernelSchwartz n) (x - y)‖ₑ * ‖f y‖ₑ := by
  rw [gaussianFlow_one_eq]
  refine (enorm_iteratedFDeriv_convolution_le _ _ hf k x).trans ?_
  have hL : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ₑ ≤ 1 := by
    simpa only [enorm_eq_nnnorm, ENNReal.coe_le_one_iff, ← NNReal.coe_le_one, coe_nnnorm] using
      ContinuousLinearMap.opNorm_lsmul_le (𝕜 := ℝ) (R := ℝ) (E := E)
  calc
    _ ≤ 1 * ∫⁻ y, ‖iteratedFDeriv ℝ k (heatKernelSchwartz n) (x - y)‖ₑ * ‖f y‖ₑ := by gcongr
    _ = _ := one_mul _

/-- Young's inequality for the derivatives of the time-one flow. -/
theorem eLpNorm_iteratedFDeriv_gaussianFlow_one_le {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : p⁻¹ + q⁻¹ = 1 + r⁻¹) (hf : MemLp f p volume) (k : ℕ) :
    eLpNorm (iteratedFDeriv ℝ k (gaussianFlow 1 f)) r volume ≤
      eLpNorm (iteratedFDeriv ℝ k (heatKernelSchwartz n)) q volume * eLpNorm f p volume := by
  have hw := PDE.integrable_polynomialWeight_smul_of_memLp hp hf
  have hsmooth := contDiff_gaussianFlow_one hw
  set a : ℝ^n → ℝ≥0∞ := fun z ↦ ‖iteratedFDeriv ℝ k (heatKernelSchwartz n) z‖ₑ
  have hKcont : Continuous (iteratedFDeriv ℝ k (heatKernelSchwartz n)) :=
    ((heatKernelSchwartz n).smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have ha : Measurable a := hKcont.enorm.measurable
  set g := hf.aestronglyMeasurable.mk f
  have hg : Measurable fun y ↦ ‖g y‖ₑ :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.enorm
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hpoint (x : ℝ^n) : ‖iteratedFDeriv ℝ k (gaussianFlow 1 f) x‖ₑ ≤
      ‖∫⁻ y, a (x - y) * ‖g y‖ₑ‖ₑ := by
    rw [enorm_eq_self]
    refine (enorm_iteratedFDeriv_gaussianFlow_one_le hw k x).trans (le_of_eq ?_)
    refine lintegral_congr_ae ?_
    filter_upwards [hfg] with y hy
    rw [hy]
  calc
    _ ≤ eLpNorm (fun x ↦ ∫⁻ y, a (x - y) * ‖g y‖ₑ) r volume :=
      eLpNorm_mono_enorm ((hsmooth.continuous_iteratedFDeriv
        (by exact_mod_cast le_top)).aestronglyMeasurable) hpoint
    _ ≤ eLpNorm a q volume * eLpNorm (fun y ↦ ‖g y‖ₑ) p volume :=
      ENNReal.eLpNorm_lintegral_convolution_le_of_one_le volume hq hp
        (by rwa [add_comm]) ha hg
    _ = _ := by
      rw [eLpNorm_enorm _ hKcont.aestronglyMeasurable,
        eLpNorm_enorm _ hf.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable,
        eLpNorm_congr_ae hfg.symm]

/-- Young's inequality and parabolic scaling for the derivatives of the heat flow, with the
kernel exponent `q` given by `1/p + 1/q = 1 + 1/r`. -/
theorem eLpNorm_iteratedFDeriv_gaussianFlow_le_of_young {p q r : ℝ≥0∞} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hpqr : p⁻¹ + q⁻¹ = 1 + r⁻¹) {t : ℝ} (ht : 0 < t) (hf : MemLp f p volume)
    (k : ℕ) :
    eLpNorm (iteratedFDeriv ℝ k (gaussianFlow t f)) r volume ≤
      eLpNorm (iteratedFDeriv ℝ k (heatKernelSchwartz n)) q volume *
        ENNReal.ofReal (t ^ (-(k / 2 : ℝ) - n / 2 * (p⁻¹.toReal - r⁻¹.toReal))) *
          eLpNorm f p volume := by
  set s := Real.sqrt t
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  set g := gaussianFlow 1 (fun y ↦ f (s • y))
  have hfs : MemLp (fun y ↦ f (s • y)) p volume := hf.comp_smul hs.ne'
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g :=
    contDiff_gaussianFlow_one (PDE.integrable_polynomialWeight_smul_of_memLp hp hfs)
  have hrep : gaussianFlow t f = fun x ↦ g (s⁻¹ • x) := gaussianFlow_eq_comp_smul ht f
  have hDg : Continuous (iteratedFDeriv ℝ k g) := hgs.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)
  have hstep1 : eLpNorm (iteratedFDeriv ℝ k (gaussianFlow t f)) r volume ≤
      ENNReal.ofReal (s⁻¹ ^ k) * (dilationFactor (ℝ^n) s⁻¹ r *
        eLpNorm (iteratedFDeriv ℝ k g) r volume) := by
    rw [hrep, iteratedFDeriv_comp_const_smul s⁻¹ (hgs.of_le (by exact_mod_cast le_top))]
    refine le_of_eq ?_
    change eLpNorm ((s⁻¹ ^ k) • fun x ↦ iteratedFDeriv ℝ k g (s⁻¹ • x)) r volume = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity),
      eLpNorm_comp_smul hDg.aestronglyMeasurable (inv_ne_zero hs.ne')]
  have hstep2 := eLpNorm_iteratedFDeriv_gaussianFlow_one_le hp hq hpqr hfs k
  rw [eLpNorm_comp_smul hf.aestronglyMeasurable hs.ne'] at hstep2
  have hscalar : ENNReal.ofReal (s⁻¹ ^ k) * dilationFactor (ℝ^n) s⁻¹ r *
      dilationFactor (ℝ^n) s p =
      ENNReal.ofReal (t ^ (-(k / 2 : ℝ) - n / 2 * (p⁻¹.toReal - r⁻¹.toReal))) := by
    have hsr : s = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
    have hsa (a : ℝ) : s ^ a = t ^ (a / 2) := by
      rw [hsr, ← Real.rpow_mul ht.le, one_div_mul_eq_div]
    have h1 : s⁻¹ ^ k = t ^ (-(k : ℝ) / 2) := by
      rw [← Real.rpow_natCast, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, hsa]
    have h2 : (s⁻¹ ^ n)⁻¹ ^ r⁻¹.toReal = t ^ ((n : ℝ) * r⁻¹.toReal / 2) := by
      rw [inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, hsa]
    have h3 : (s ^ n)⁻¹ ^ p⁻¹.toReal = t ^ (-(n : ℝ) * p⁻¹.toReal / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hs.le, ← Real.rpow_mul hs.le, hsa]
    have hreal : s⁻¹ ^ k * (s⁻¹ ^ n)⁻¹ ^ r⁻¹.toReal * (s ^ n)⁻¹ ^ p⁻¹.toReal =
        t ^ (-(k / 2 : ℝ) - n / 2 * (p⁻¹.toReal - r⁻¹.toReal)) := by
      rw [h1, h2, h3, ← Real.rpow_add ht, ← Real.rpow_add ht]
      congr 1
      ring
    simp only [dilationFactor, finrank_euclideanSpace_fin, one_div]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (s⁻¹ ^ n)⁻¹),
      abs_of_pos (by positivity : (0 : ℝ) < (s ^ n)⁻¹),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) ENNReal.toReal_nonneg,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hreal]
  calc
    _ ≤ ENNReal.ofReal (s⁻¹ ^ k) * (dilationFactor (ℝ^n) s⁻¹ r *
        (eLpNorm (iteratedFDeriv ℝ k (heatKernelSchwartz n)) q volume *
          (dilationFactor (ℝ^n) s p * eLpNorm f p volume))) := hstep1.trans (by gcongr)
    _ = eLpNorm (iteratedFDeriv ℝ k (heatKernelSchwartz n)) q volume *
        (ENNReal.ofReal (s⁻¹ ^ k) * dilationFactor (ℝ^n) s⁻¹ r * dilationFactor (ℝ^n) s p) *
          eLpNorm f p volume := by ring
    _ = _ := by rw [hscalar]

/-- The `Lᵖ → Lʳ` smoothing estimate of the heat flow, `1 ≤ p ≤ r ≤ ∞`:
`‖Dᵏ (G_t * f)‖_{Lʳ} ≤ C t^(-k/2 - (n/2)(1/p - 1/r)) ‖f‖_{Lᵖ}` with a finite constant `C`
independent of `t` and `f`. For `n = 3` this is (2.8) of Hou, Wang and Yang. -/
theorem eLpNorm_iteratedFDeriv_gaussianFlow_le (k : ℕ) {p r : ℝ≥0∞} (hp : 1 ≤ p)
    (hpr : p ≤ r) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {t : ℝ}, 0 < t → ∀ {f : ℝ^n → E}, MemLp f p volume →
      eLpNorm (iteratedFDeriv ℝ k (gaussianFlow t f)) r volume ≤
        C * ENNReal.ofReal (t ^ (-(k / 2 : ℝ) - n / 2 * (p⁻¹.toReal - r⁻¹.toReal))) *
          eLpNorm f p volume :=
  ⟨eLpNorm (iteratedFDeriv ℝ k (heatKernelSchwartz n)) (ENNReal.youngExponent p r) volume,
    (memLp_iteratedFDeriv _ k _).eLpNorm_ne_top,
    fun ht _ hf ↦ eLpNorm_iteratedFDeriv_gaussianFlow_le_of_young hp
      (ENNReal.one_le_youngExponent hpr) (ENNReal.inv_add_inv_youngExponent r hp) ht hf k⟩

/-- At positive times every derivative of the heat flow of `Lᵖ` data lies in `Lʳ`, `p ≤ r`. -/
theorem memLp_iteratedFDeriv_gaussianFlow {t : ℝ} (ht : 0 < t) {p r : ℝ≥0∞} (hp : 1 ≤ p)
    (hpr : p ≤ r) (hf : MemLp f p volume) (k : ℕ) :
    MemLp (iteratedFDeriv ℝ k (gaussianFlow t f)) r volume := by
  obtain ⟨C, hC, hbound⟩ := eLpNorm_iteratedFDeriv_gaussianFlow_le (n := n) (E := E) k hp hpr
  exact (hbound ht hf).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC.lt_top
    ENNReal.ofReal_lt_top) hf.eLpNorm_lt_top)

/-- At positive times the heat flow maps `Lᵖ` into `Lʳ`, `1 ≤ p ≤ r ≤ ∞`. -/
theorem memLp_gaussianFlow {t : ℝ} (ht : 0 < t) {p r : ℝ≥0∞} (hp : 1 ≤ p) (hpr : p ≤ r)
    (hf : MemLp f p volume) : MemLp (gaussianFlow t f) r volume := by
  have h := memLp_iteratedFDeriv_gaussianFlow ht hp hpr hf 0
  refine h.of_le (contDiff_gaussianFlow ht hp hf).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_iteratedFDeriv_zero]

end HeatEquation.WholeSpace
