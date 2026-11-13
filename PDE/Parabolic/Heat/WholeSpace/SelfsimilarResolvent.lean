/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarDecay
public import PDE.Analysis.Evolution.Semigroup.Resolvent
public import PDE.Analysis.MeasureTheory.Lp.IntegralPower
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.WholeSpaceClass
import CAS.ExactTactic

/-!
# The shifted resolvent of the free self-similar operator

The free self-similar operator is `L₀ = -1/2 - (1/2) x·∇ - Δ`; the free self-similar heat
semigroup has generator `-L₀`. In dimension at least two that semigroup contracts `L²`, so for
`μ > 0` its Laplace transform is the resolvent `(μ + L₀)⁻¹` with norm at most `μ⁻¹`.

The Fourier transform of one step at similarity time `s` is the heat multiplier
`exp (-(1 - e⁻ˢ) 4π²|ξ|²)` times the datum at the contracted frequency `e^{-s/2} ξ`, with the
factor `e^{(1-n)s/2}`. Splitting the pairing with a frequency-weighted test function by the
arithmetic-geometric mean inequality and integrating the two kernels exactly in `s` gives

`∫ (4π²|ξ|²)² |𝓕(R_μ f)|² ≤ ‖f‖²`,  `μ ≥ 1/2`,

that is `‖Δ R_μ f‖ ≤ ‖f‖`. No smallness and no regularity of `f` enter, and the constant does
not depend on `μ`. Consequently `R_μ` maps `L²` boundedly into `H²` with a bound uniform in
`μ ≥ 1/2` (`selfsimilarResolventH2`). This is the linear estimate of the step from `H¹` to `H²`
for weak self-similar Navier-Stokes profiles (Hou, Wang and Yang, *Nonuniqueness of Leray-Hopf
solutions to the unforced incompressible 3D Navier-Stokes equation*, arXiv:2509.25116v2,
Appendix F).
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open BesselPotentialSpace TemperedDistribution PDE.Analysis.Evolution Set Filter Topology
open scoped ENNReal NNReal Sobolev BesselPotentialSpace SchwartzMap

namespace HeatEquation.WholeSpace

variable {n : ℕ}



theorem isRealL2_baseL2 {j : ℕ} (U : W^{j,2}(ℝ^n)) : IsRealL2 (baseL2 U) := by
  have h := isRealL2_toL2Fun_ofWkpSpace U
  rwa [toL2Fun_ofWkpSpace] at h

/-- A Sobolev graph element whose weighted Fourier transform is square integrable is the
base of a higher-order graph element, with the Bessel norm bound. -/
theorem exists_wkpSpace_of_memLp_besselWeight {j : ℕ} (k : ℕ) (U : W^{j,2}(ℝ^n))
    (h : MemLp (fun ξ ↦ besselSymbol n k ξ * (𝓕 (baseL2 U) : Lp ℂ 2 volume) ξ) 2 volume) :
    ∃ V : W^{k,2}(ℝ^n), baseL2 V = baseL2 U ∧
      ‖V‖ ≤ toWkpSpaceNormBound n k *
        (eLpNorm (fun ξ ↦ besselSymbol n k ξ * (𝓕 (baseL2 U) : Lp ℂ 2 volume) ξ)
          2 volume).toReal :=
  SobolevSpace.GraphSpace.exists_wkpSpace_of_isRealL2_of_memLp_besselWeight (baseL2 U)
    (isRealL2_baseL2 U) h

/-- At order zero the graph norm is the `L²` norm of the complexified base function. -/
theorem norm_eq_norm_baseL2_of_order_zero (U : W^{0,2}(ℝ^n)) : ‖U‖ = ‖baseL2 U‖ := by
  have h1 := norm_toWkpSpace_order_zero (n := n) (ofWkpSpace U) (isRealL2_toL2Fun_ofWkpSpace U)
  rw [toWkpSpace_ofWkpSpace] at h1
  rw [h1, ← norm_fourier_toLp_eq, ← Lp.norm_fourier_eq (baseL2 U), Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [coeFn_fourier_toLp_ofWkpSpace U] with ξ hξ
  rw [hξ, besselSymbol]
  simp

/-- In dimension at least two, free self-similar evolution does not increase the `L²` norm. -/
theorem norm_baseL2_selfsimilarHeatSobolev_le (hn : 2 ≤ n) {k : ℕ} (τ : ℝ≥0)
    (u : W^{k,2}(ℝ^n)) :
    ‖baseL2 (selfsimilarHeatSobolev n k τ u)‖ ≤ ‖baseL2 u‖ := by
  rw [baseL2_selfsimilarHeatSobolev, norm_smul, Real.norm_eq_abs,
    abs_of_pos (selfsimilarFactor_pos τ), Lp.norm_compSMul, finrank_euclideanSpace_fin,
    ← mul_assoc, selfsimilar_volume_factor]
  have hexp : Real.exp (((2 : ℝ) - n) * τ / 4) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : (2 : ℝ) - n ≤ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hτ : (0 : ℝ) ≤ τ := τ.property
    nlinarith
  calc _ ≤ 1 * ‖baseL2 u‖ :=
        mul_le_mul hexp (norm_heatL2_le _ _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

@[simp]
theorem selfsimilarHeatSobolevSemigroup_apply (k : ℕ) (τ : ℝ≥0) :
    selfsimilarHeatSobolevSemigroup n k τ = selfsimilarHeatSobolev n k τ := by
  simp only [selfsimilarHeatSobolevSemigroup, MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

/-- Free self-similar evolution on `L²` is a contraction semigroup in dimension at least two. -/
theorem isContraction_selfsimilarHeatSobolevSemigroup (hn : 2 ≤ n) :
    (selfsimilarHeatSobolevSemigroup n 0).IsContraction := by
  intro τ
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [selfsimilarHeatSobolevSemigroup_apply, one_mul, norm_eq_norm_baseL2_of_order_zero,
    norm_eq_norm_baseL2_of_order_zero]
  exact norm_baseL2_selfsimilarHeatSobolev_le hn _ u

/-- The Fourier transform of one free self-similar step, in explicit exponential form:
the frequency variable is contracted by `exp (-τ / 2)` after the heat multiplier. -/
theorem fourier_baseL2_selfsimilarHeatSobolev_ae {k : ℕ} (τ : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    (𝓕 (baseL2 (selfsimilarHeatSobolev n k τ u)) : Lp ℂ 2 (volume : Measure (ℝ^n))) =ᵐ[volume]
      fun ξ ↦ ((Real.exp ((1 - n) * τ / 2) *
          Real.exp (-(4 * Real.pi ^ 2 * (1 - Real.exp (-τ)) * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        (𝓕 (baseL2 u) : Lp ℂ 2 (volume : Measure (ℝ^n))) (Real.exp (-(τ / 2)) • ξ) := by
  set a := selfsimilarFactor τ with ha_def
  set t := selfsimilarHeatTime τ with ht_def
  set J := |(a ^ n)⁻¹| with hJ_def
  have ha : 0 < a := selfsimilarFactor_pos τ
  set f := (𝓕 (baseL2 u) : Lp ℂ 2 (volume : Measure (ℝ^n))) with hf_def
  set g := (heatSymbolLinf n t • f : Lp ℂ 2 (volume : Measure (ℝ^n))) with hg_def
  have hsmul (w : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓕 (a • w) = a • 𝓕 w :=
    (fourierCLM ℂ (Lp ℂ 2 (volume : Measure (ℝ^n)))).map_smul_of_tower _ _
  have hbase :
      𝓕 (baseL2 (selfsimilarHeatSobolev n k τ u)) =
        (a * J) • Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') g := by
    rw [baseL2_selfsimilarHeatSobolev, hsmul, PDE.Analysis.Fourier.fourier_compSMul,
      fourier_heatL2, finrank_euclideanSpace_fin, smul_smul]
  have hcomp := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^n))
    (inv_ne_zero ha.ne')
  have hheat := hcomp.ae_eq_comp (Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) f)
  have hsymbol := hcomp.ae_eq_comp (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  rw [hbase]
  filter_upwards [Lp.coeFn_smul (a * J) (Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') g),
    Lp.coeFn_compSMul volume 2 a⁻¹ (inv_ne_zero ha.ne') g, hheat, hsymbol]
    with ξ hscale hg hmul hsym
  simp only [Function.comp_apply] at hmul hsym
  rw [hscale, Pi.smul_apply, hg]
  change (a * J) • g (a⁻¹ • ξ) = _
  change g (a⁻¹ • ξ) = _ at hmul
  change heatSymbolLinf n t (a⁻¹ • ξ) = _ at hsym
  rw [hmul, Pi.smul_apply', hsym, smul_eq_mul]
  have hainv : a⁻¹ = Real.exp (-(τ / 2)) := by
    rw [ha_def, selfsimilarFactor, ← Real.exp_neg]
  have haJ : a * J = Real.exp ((1 - n) * τ / 2) := by
    rw [hJ_def, ha_def, selfsimilarFactor, ← Real.exp_nat_mul, ← Real.exp_neg,
      abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    congr 1
    ring
  have hheatval : heatSymbol n t (a⁻¹ • ξ) =
      ((Real.exp (-(4 * Real.pi ^ 2 * (1 - Real.exp (-τ)) * ‖ξ‖ ^ 2)) : ℝ) : ℂ) := by
    rw [heatSymbol, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), mul_pow,
      ht_def, coe_selfsimilarHeatTime]
    congr 3
    have hsq : a⁻¹ ^ 2 = Real.exp (-τ) := by
      rw [hainv, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hsq]
    have : (Real.exp τ - 1) * Real.exp (-τ) = 1 - Real.exp (-τ) := by
      rw [sub_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [← this]
    ring
  rw [hheatval, hainv, haJ, Complex.real_smul]
  push_cast
  ring

/-- The Fourier transform of the complexified base function, as a real-linear map. -/
def fourierBaseL2CLM (n k : ℕ) : W^{k,2}(ℝ^n) →L[ℝ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  ((fourierCLM ℂ (Lp ℂ 2 (volume : Measure (ℝ^n)))).restrictScalars ℝ).comp
    ((complexifyL2CLM n).comp wkpBaseCoordinateCLM)

theorem fourierBaseL2CLM_apply {k : ℕ} (U : W^{k,2}(ℝ^n)) :
    fourierBaseL2CLM n k U = 𝓕 (baseL2 U) := by
  simp only [fourierBaseL2CLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', complexifyL2CLM_base]
  rfl

/-- The shifted resolvent `(μ + L₀)⁻¹` of the free self-similar operator
`L₀ = -1/2 - (1/2) x·∇ - Δ` on `L²(ℝⁿ)`. It is the Laplace transform of the free
self-similar heat semigroup, whose generator is `-L₀`. -/
def selfsimilarResolvent (n : ℕ) (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ) :
    W^{0,2}(ℝ^n) →L[ℝ] W^{0,2}(ℝ^n) :=
  (selfsimilarHeatSobolevSemigroup n 0).laplaceTransform
    (isContraction_selfsimilarHeatSobolevSemigroup hn) hμ

theorem norm_selfsimilarResolvent_le (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ) :
    ‖selfsimilarResolvent n hn hμ‖ ≤ μ⁻¹ :=
  StronglyContinuousSemigroup.norm_laplaceTransform_le _ _ hμ

theorem integrableOn_selfsimilarResolvent_integrand (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (f : W^{0,2}(ℝ^n)) :
    IntegrableOn (fun s : ℝ ↦ Real.exp (-μ * s) •
      (selfsimilarHeatSobolevSemigroup n 0).realOrbit f s) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hμ).mul_const ‖f‖)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((selfsimilarHeatSobolevSemigroup n 0).continuous_realOrbit f)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    ((isContraction_selfsimilarHeatSobolevSemigroup hn).norm_apply_le _ f)
    (Real.exp_pos _).le

/-- Pairings of the transformed resolvent are Laplace integrals of the transformed orbit. -/
theorem inner_fourier_baseL2_selfsimilarResolvent (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (f : W^{0,2}(ℝ^n)) (h : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    inner ℂ h (𝓕 (baseL2 (selfsimilarResolvent n hn hμ f))) =
      ∫ s in Ioi (0 : ℝ), (Real.exp (-μ * s) : ℂ) *
        inner ℂ h (𝓕 (baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal f))) := by
  have hint := integrableOn_selfsimilarResolvent_integrand hn hμ f
  have hF : 𝓕 (baseL2 (selfsimilarResolvent n hn hμ f)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-μ * s) •
        𝓕 (baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal f)) := by
    rw [← fourierBaseL2CLM_apply, selfsimilarResolvent,
      StronglyContinuousSemigroup.laplaceTransform_apply,
      ← (fourierBaseL2CLM n 0).integral_comp_comm hint]
    congr 1
    funext s
    rw [map_smul, fourierBaseL2CLM_apply, StronglyContinuousSemigroup.realOrbit,
      selfsimilarHeatSobolevSemigroup_apply]
  have hint' : IntegrableOn (fun s : ℝ ↦ Real.exp (-μ * s) •
      𝓕 (baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal f))) (Ioi 0) := by
    have := (fourierBaseL2CLM n 0).integrable_comp hint
    refine this.congr (Filter.Eventually.of_forall fun s ↦ ?_)
    simp only [map_smul, fourierBaseL2CLM_apply,
      StronglyContinuousSemigroup.realOrbit, selfsimilarHeatSobolevSemigroup_apply]
  rw [hF, ← integral_inner hint']
  congr 1
  funext s
  rw [inner_smul_right_eq_smul, Complex.real_smul]



/-- The improper integral of a nonnegative derivative, as a lower Lebesgue integral. -/
theorem lintegral_Ioi_ofReal_deriv_eq {g g' : ℝ → ℝ} {l : ℝ}
    (hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g 0) := by
  rw [← integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hg,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hg)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpos))]

/-- The frequency-side kernel integrates to at most one in similarity time. -/
theorem lintegral_resolventKernel_le_one (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    {m : ℝ} (hm : 0 ≤ m) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-μ * s) * Real.exp ((1 - n) * s / 2) *
      m * Real.exp (-((1 - Real.exp (-s)) * m))) ≤ 1 := by
  let g : ℝ → ℝ := fun s ↦ -Real.exp (-((1 - Real.exp (-s)) * m))
  let g' : ℝ → ℝ := fun s ↦ m * Real.exp (-s) * Real.exp (-((1 - Real.exp (-s)) * m))
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (g' x) x := fun x _ ↦ by
    simp only [g, g']
    cas
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g' x := fun x _ ↦ by positivity
  have hlim : Tendsto g atTop (𝓝 (-Real.exp (-m))) := by
    have h2 : Tendsto (fun s : ℝ ↦ -((1 - Real.exp (-s)) * m)) atTop (𝓝 (-((1 - 0) * m))) :=
      ((Real.tendsto_exp_neg_atTop_nhds_zero.const_sub 1).mul_const m).neg
    simpa [g] using (Real.continuous_exp.tendsto _).comp h2 |>.neg
  have hle (s : ℝ) (hs : s ∈ Ioi 0) : Real.exp (-μ * s) * Real.exp ((1 - n) * s / 2) *
      m * Real.exp (-((1 - Real.exp (-s)) * m)) ≤ g' s := by
    have hexp : Real.exp (-μ * s) * Real.exp ((1 - n) * s / 2) ≤ Real.exp (-s) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      linarith [mul_nonneg (sub_nonneg.2 hμ) hs.out.le,
        mul_nonneg (sub_nonneg.2 (by exact_mod_cast hn : (2 : ℝ) ≤ n)) hs.out.le]
    simp only [g']
    nlinarith [mul_le_mul_of_nonneg_right hexp
      (by positivity : 0 ≤ m * Real.exp (-((1 - Real.exp (-s)) * m)))]
  calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g' s) :=
        setLIntegral_mono' measurableSet_Ioi fun s hs ↦ ENNReal.ofReal_le_ofReal (hle s hs)
    _ = ENNReal.ofReal (-Real.exp (-m) - g 0) := lintegral_Ioi_ofReal_deriv_eq hderiv hpos hlim
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by
        simp only [g, Real.exp_zero, sub_self, zero_mul, neg_zero]
        linarith [Real.exp_pos (-m)])

/-- The dilated frequency-side kernel integrates to at most one in similarity time. -/
theorem lintegral_dilatedResolventKernel_le_one {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    {m : ℝ} (hm : 0 ≤ m) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp ((3 / 2 - μ) * s) * m *
      Real.exp (-((Real.exp s - 1) * m))) ≤ 1 := by
  let g : ℝ → ℝ := fun s ↦ -Real.exp (-((Real.exp s - 1) * m))
  let g' : ℝ → ℝ := fun s ↦ m * Real.exp s * Real.exp (-((Real.exp s - 1) * m))
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (g' x) x := fun x _ ↦ by
    simp only [g, g']
    cas
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g' x := fun x _ ↦ by positivity
  rcases hm.lt_or_eq with hm | hm
  · have hlim : Tendsto g atTop (𝓝 (-0)) := by
      have h1 : Tendsto (fun s : ℝ ↦ (Real.exp s - 1) * m) atTop atTop :=
        (tendsto_atTop_add_const_right _ (-1)
          (Real.tendsto_exp_atTop)).atTop_mul_const hm |>.congr fun s ↦ by ring
      exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).neg
    have hle (s : ℝ) (hs : s ∈ Ioi 0) : Real.exp ((3 / 2 - μ) * s) * m *
        Real.exp (-((Real.exp s - 1) * m)) ≤ g' s := by
      have hexp : Real.exp ((3 / 2 - μ) * s) ≤ Real.exp s :=
        Real.exp_le_exp.mpr (by nlinarith [hs.out])
      simp only [g']
      nlinarith [mul_le_mul_of_nonneg_right hexp
        (by positivity : 0 ≤ m * Real.exp (-((Real.exp s - 1) * m)))]
    calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g' s) :=
          setLIntegral_mono' measurableSet_Ioi fun s hs ↦ ENNReal.ofReal_le_ofReal (hle s hs)
      _ = ENNReal.ofReal (-0 - g 0) := lintegral_Ioi_ofReal_deriv_eq hderiv hpos hlim
      _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by simp [g])
  · subst hm
    simp

/-- The frequency-side resolvent kernel at similarity time `s` and frequency `ξ`. -/
def resolventKernel (n : ℕ) (μ s : ℝ) (ξ : ℝ^n) : ℝ :=
  Real.exp (-μ * s) * Real.exp ((1 - n) * s / 2) * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
    Real.exp (-((1 - Real.exp (-s)) * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)))

theorem resolventKernel_nonneg (n : ℕ) (μ s : ℝ) (ξ : ℝ^n) : 0 ≤ resolventKernel n μ s ξ := by
  unfold resolventKernel; positivity

theorem continuous_resolventKernel (n : ℕ) (μ : ℝ) :
    Continuous (fun p : ℝ × ℝ^n ↦ resolventKernel n μ p.1 p.2) := by
  unfold resolventKernel; fun_prop

/-- After the frequency dilation, the Jacobian times the kernel is the dilated kernel. -/
theorem jacobian_mul_resolventKernel_dilation (n : ℕ) (μ s : ℝ) (η : ℝ^n) :
    Real.exp (n * s / 2) * resolventKernel n μ s (Real.exp (s / 2) • η) =
      Real.exp ((3 / 2 - μ) * s) * (4 * Real.pi ^ 2 * ‖η‖ ^ 2) *
        Real.exp (-((Real.exp s - 1) * (4 * Real.pi ^ 2 * ‖η‖ ^ 2))) := by
  have hnorm : ‖Real.exp (s / 2) • η‖ ^ 2 = Real.exp s * ‖η‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hfac : (1 - Real.exp (-s)) * Real.exp s = Real.exp s - 1 := by
    rw [sub_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  unfold resolventKernel
  rw [hnorm]
  have e1 : Real.exp (n * s / 2) * (Real.exp (-μ * s) * Real.exp ((1 - n) * s / 2)) *
      Real.exp s = Real.exp ((3 / 2 - μ) * s) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc _ = (Real.exp (n * s / 2) * (Real.exp (-μ * s) * Real.exp ((1 - n) * s / 2)) *
        Real.exp s) * (4 * Real.pi ^ 2 * ‖η‖ ^ 2) *
        Real.exp (-(((1 - Real.exp (-s)) * Real.exp s) * (4 * Real.pi ^ 2 * ‖η‖ ^ 2))) := by
        ring_nf
    _ = _ := by rw [e1, hfac]

/-- Change of variables for a frequency dilation in a lower Lebesgue integral. -/
theorem lintegral_comp_smul_eq {H : ℝ^n → ℝ≥0∞} (hH : Measurable H) {r : ℝ}
    (hr : r ≠ 0) :
    ∫⁻ ξ, H (r • ξ) = ENNReal.ofReal |(r ^ n)⁻¹| * ∫⁻ η, H η := by
  rw [← lintegral_map hH (measurable_const_smul r),
    Measure.map_addHaar_smul (volume : Measure (ℝ^n)) hr, finrank_euclideanSpace_fin,
    lintegral_smul_measure, smul_eq_mul]

/-- The two-variable frequency estimate behind the second-order resolvent bound. The
similarity-time integral of the kernel against a product is controlled by the two `L²`
masses, with no smallness assumption and no constant depending on `μ ≥ 1/2`. -/
theorem lintegral_resolventKernel_mul_le (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    {F G : ℝ^n → ℂ} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ s in Ioi (0 : ℝ), ∫⁻ ξ, ENNReal.ofReal (resolventKernel n μ s ξ *
        (‖G ξ‖ * ‖F (Real.exp (-(s / 2)) • ξ)‖)) ≤
      2⁻¹ * (∫⁻ ξ, ENNReal.ofReal (‖G ξ‖ ^ 2)) + 2⁻¹ * ∫⁻ η, ENNReal.ofReal (‖F η‖ ^ 2) := by
  have hK := continuous_resolventKernel n μ
  have hGm : Measurable fun p : ℝ × ℝ^n ↦ ‖G p.2‖ := (hG.comp measurable_snd).norm
  have hdil : Measurable fun p : ℝ × ℝ^n ↦ Real.exp (-(p.1 / 2)) • p.2 := by fun_prop
  have hFm : Measurable fun p : ℝ × ℝ^n ↦ ‖F (Real.exp (-(p.1 / 2)) • p.2)‖ :=
    (hF.comp hdil).norm
  have hA : Measurable fun p : ℝ × ℝ^n ↦
      ENNReal.ofReal (2⁻¹ * resolventKernel n μ p.1 p.2 * ‖G p.2‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hK.measurable).mul (hGm.pow_const 2))
  have hB : Measurable fun p : ℝ × ℝ^n ↦
      ENNReal.ofReal (2⁻¹ * resolventKernel n μ p.1 p.2 *
        ‖F (Real.exp (-(p.1 / 2)) • p.2)‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hK.measurable).mul (hFm.pow_const 2))
  have hhalf (φ : ℝ^n → ℝ) :
      ∫⁻ ξ, ENNReal.ofReal (2⁻¹ * φ ξ) * 1 = 2⁻¹ * ∫⁻ ξ, ENNReal.ofReal (φ ξ) := by
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_congr fun ξ ↦ ?_
    rw [mul_one, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  -- pointwise arithmetic-geometric mean inequality
  have hpoint : ∀ s (ξ : ℝ^n), ENNReal.ofReal (resolventKernel n μ s ξ *
      (‖G ξ‖ * ‖F (Real.exp (-(s / 2)) • ξ)‖)) ≤
      ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ * ‖G ξ‖ ^ 2) +
        ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ *
          ‖F (Real.exp (-(s / 2)) • ξ)‖ ^ 2) := by
    intro s ξ
    have hk := resolventKernel_nonneg n μ s ξ
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg hk (sq_nonneg (‖G ξ‖ - ‖F (Real.exp (-(s / 2)) • ξ)‖))]
  -- the first term, by Tonelli
  have hterm1 : ∫⁻ s in Ioi (0 : ℝ), ∫⁻ ξ,
      ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ * ‖G ξ‖ ^ 2) ≤
      2⁻¹ * ∫⁻ ξ, ENNReal.ofReal (‖G ξ‖ ^ 2) := by
    rw [lintegral_lintegral_swap hA.aemeasurable]
    calc _ = ∫⁻ ξ, ENNReal.ofReal (2⁻¹ * ‖G ξ‖ ^ 2) *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventKernel n μ s ξ) := by
          refine lintegral_congr fun ξ ↦ ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun s ↦ ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (2⁻¹ * ‖G ξ‖ ^ 2) * 1 := by
          refine lintegral_mono fun ξ ↦ ?_
          gcongr
          simpa only [resolventKernel] using lintegral_resolventKernel_le_one hn hμ
            (m := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) (by positivity)
      _ = 2⁻¹ * ∫⁻ ξ, ENNReal.ofReal (‖G ξ‖ ^ 2) := hhalf _
  -- the second term, by the frequency dilation and Tonelli
  have hterm2 : ∫⁻ s in Ioi (0 : ℝ), ∫⁻ ξ,
      ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ * ‖F (Real.exp (-(s / 2)) • ξ)‖ ^ 2) ≤
      2⁻¹ * ∫⁻ η, ENNReal.ofReal (‖F η‖ ^ 2) := by
    have hinner : ∀ s : ℝ, ∫⁻ ξ, ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ *
        ‖F (Real.exp (-(s / 2)) • ξ)‖ ^ 2) =
        ∫⁻ η, ENNReal.ofReal (2⁻¹ * (Real.exp (n * s / 2) *
          resolventKernel n μ s (Real.exp (s / 2) • η)) * ‖F η‖ ^ 2) := by
      intro s
      have hHm : Measurable fun η : ℝ^n ↦ ENNReal.ofReal (2⁻¹ *
          resolventKernel n μ s (Real.exp (s / 2) • η) * ‖F η‖ ^ 2) := by
        have hc : Continuous fun η : ℝ^n ↦ 2⁻¹ *
            resolventKernel n μ s (Real.exp (s / 2) • η) := by
          unfold resolventKernel; fun_prop
        exact ENNReal.measurable_ofReal.comp (hc.measurable.mul (hF.norm.pow_const 2))
      have hcv := lintegral_comp_smul_eq hHm (r := Real.exp (-(s / 2)))
        (Real.exp_pos _).ne'
      have hsimp (ξ : ℝ^n) : Real.exp (s / 2) • (Real.exp (-(s / 2)) • ξ) = ξ := by
        rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
      simp only [hsimp] at hcv
      rw [hcv]
      have hjac : |(Real.exp (-(s / 2)) ^ n)⁻¹| = Real.exp (n * s / 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)]
        congr 1
        ring
      rw [hjac, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun η ↦ ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
    simp_rw [hinner]
    have hB' : Measurable fun p : ℝ × ℝ^n ↦ ENNReal.ofReal (2⁻¹ * (Real.exp (n * p.1 / 2) *
        resolventKernel n μ p.1 (Real.exp (p.1 / 2) • p.2)) * ‖F p.2‖ ^ 2) := by
      have hc : Continuous fun p : ℝ × ℝ^n ↦ 2⁻¹ * (Real.exp (n * p.1 / 2) *
          resolventKernel n μ p.1 (Real.exp (p.1 / 2) • p.2)) := by
        unfold resolventKernel; fun_prop
      exact ENNReal.measurable_ofReal.comp
        (hc.measurable.mul ((hF.comp measurable_snd).norm.pow_const 2))
    rw [lintegral_lintegral_swap hB'.aemeasurable]
    calc _ = ∫⁻ η, ENNReal.ofReal (2⁻¹ * ‖F η‖ ^ 2) *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (n * s / 2) *
            resolventKernel n μ s (Real.exp (s / 2) • η)) := by
          refine lintegral_congr fun η ↦ ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun s ↦ ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ ≤ ∫⁻ η, ENNReal.ofReal (2⁻¹ * ‖F η‖ ^ 2) * 1 := by
          refine lintegral_mono fun η ↦ ?_
          gcongr
          simp_rw [jacobian_mul_resolventKernel_dilation]
          exact lintegral_dilatedResolventKernel_le_one hμ (by positivity)
      _ = 2⁻¹ * ∫⁻ η, ENNReal.ofReal (‖F η‖ ^ 2) := hhalf _
  calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), ((∫⁻ ξ,
        ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ * ‖G ξ‖ ^ 2)) +
        ∫⁻ ξ, ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ *
          ‖F (Real.exp (-(s / 2)) • ξ)‖ ^ 2)) := by
        refine lintegral_mono fun s ↦ ?_
        have hc : Continuous fun ξ : ℝ^n ↦ 2⁻¹ * resolventKernel n μ s ξ := by
          unfold resolventKernel; fun_prop
        have hmeas : Measurable fun ξ : ℝ^n ↦
            ENNReal.ofReal (2⁻¹ * resolventKernel n μ s ξ * ‖G ξ‖ ^ 2) :=
          ENNReal.measurable_ofReal.comp (hc.measurable.mul (hG.norm.pow_const 2))
        dsimp only
        rw [← lintegral_add_left hmeas]
        exact lintegral_mono fun ξ ↦ hpoint s ξ
    _ = _ := lintegral_add_left hA.lintegral_prod_right' _
    _ ≤ _ := add_le_add hterm1 hterm2


/-- The pairing of the transformed resolvent with a frequency-weighted function is controlled
by the two `L²` masses. This is the frequency-side form of the second-order estimate. -/
theorem enorm_inner_fourier_selfsimilarResolvent_le (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    (f : W^{0,2}(ℝ^n)) (g h : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hgh : ∀ᵐ ξ ∂volume, h ξ = ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * g ξ) :
    ‖inner ℂ h (𝓕 (baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f)))‖ₑ ≤
      2⁻¹ * (∫⁻ ξ, ENNReal.ofReal (‖g ξ‖ ^ 2)) +
        2⁻¹ * ∫⁻ η, ENNReal.ofReal (‖(𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n))) η‖ ^ 2) := by
  set fh := (𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n))) with hfh
  rw [inner_fourier_baseL2_selfsimilarResolvent]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans ?_ (lintegral_resolventKernel_mul_le hn hμ (Lp.stronglyMeasurable fh).measurable
    (Lp.stronglyMeasurable g).measurable)
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  rw [enorm_mul, L2.inner_def]
  have hτ : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0
  have hformula := fourier_baseL2_selfsimilarHeatSobolev_ae (n := n) s.toNNReal f
  rw [hτ] at hformula
  calc ‖((Real.exp (-μ * s) : ℝ) : ℂ)‖ₑ *
        ‖∫ ξ, inner ℂ (h ξ) ((𝓕 (baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal f)) :
          Lp ℂ 2 (volume : Measure (ℝ^n))) ξ)‖ₑ ≤
        ‖((Real.exp (-μ * s) : ℝ) : ℂ)‖ₑ *
          ∫⁻ ξ, ‖inner ℂ (h ξ) ((𝓕 (baseL2 (selfsimilarHeatSobolev n 0 s.toNNReal f)) :
            Lp ℂ 2 (volume : Measure (ℝ^n))) ξ)‖ₑ := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ξ, ENNReal.ofReal (resolventKernel n μ s ξ *
          (‖g ξ‖ * ‖fh (Real.exp (-(s / 2)) • ξ)‖)) := by
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        apply lintegral_congr_ae
        filter_upwards [hformula, hgh] with ξ hξ hhξ
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        congr 1
        rw [hξ, hhξ, ← hfh, RCLike.inner_apply', norm_mul, RCLike.norm_conj, norm_mul, norm_mul,
          Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2),
          abs_of_pos (by positivity : (0 : ℝ) < Real.exp ((1 - n) * s / 2) *
            Real.exp (-(4 * Real.pi ^ 2 * (1 - Real.exp (-s)) * ‖ξ‖ ^ 2)))]
        unfold resolventKernel
        ring_nf

/-- The weighted square mass of the transformed resolvent is at most the `L²` mass of the
datum. This is `‖Δ R_μ f‖ ≤ ‖f‖` on the frequency side, for every `μ ≥ 1/2`. -/
theorem lintegral_weight_sq_fourier_selfsimilarResolvent_le (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) (f : W^{0,2}(ℝ^n)) :
    ∫⁻ ξ, ENNReal.ofReal ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 *
      ‖(𝓕 (baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f)) :
        Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) ≤
      ∫⁻ η, ENNReal.ofReal (‖(𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n))) η‖ ^ 2) := by
  set z := (𝓕 (baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f)) :
    Lp ℂ 2 (volume : Measure (ℝ^n))) with hz
  set B := ∫⁻ η, ENNReal.ofReal (‖(𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n))) η‖ ^ 2)
  let m : ℝ^n → ℝ := fun ξ ↦ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2
  have hmc : Continuous m := by fun_prop
  have hm0 : ∀ ξ, 0 ≤ m ξ := fun ξ ↦ by positivity
  have hzm : Measurable (z : ℝ^n → ℂ) := (Lp.stronglyMeasurable z).measurable
  let F : ℕ → ℝ^n → ℝ≥0∞ := fun k ↦ (Metric.closedBall (0 : ℝ^n) k).indicator
    (fun ξ ↦ ENNReal.ofReal (m ξ ^ 2 * ‖z ξ‖ ^ 2))
  have hbase : Measurable fun ξ ↦ ENNReal.ofReal (m ξ ^ 2 * ‖z ξ‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hmc.measurable.pow_const 2).mul (hzm.norm.pow_const 2))
  have hFm : ∀ k, Measurable (F k) := fun k ↦
    hbase.indicator Metric.isClosed_closedBall.measurableSet
  have hmono : Monotone F := fun j k hjk ↦ Set.indicator_le_indicator_of_subset
    (Metric.closedBall_subset_closedBall (by exact_mod_cast hjk)) fun _ ↦ zero_le
  have hsup (ξ : ℝ^n) : ⨆ k, F k ξ = ENNReal.ofReal (m ξ ^ 2 * ‖z ξ‖ ^ 2) := by
    refine le_antisymm (iSup_le fun k ↦ Set.indicator_le_self _ _ ξ) ?_
    obtain ⟨k, hk⟩ := exists_nat_ge ‖ξ‖
    exact (Set.indicator_of_mem (mem_closedBall_zero_iff.2 hk) _).symm.trans_le
      (le_iSup (fun k ↦ F k ξ) k)
  have hbound : ∀ k : ℕ, ∫⁻ ξ, F k ξ ≤ B := by
    intro k
    set E := Metric.closedBall (0 : ℝ^n) (k : ℝ)
    have hE : MeasurableSet E := Metric.isClosed_closedBall.measurableSet
    have hmE (ξ : ℝ^n) (hξ : ξ ∈ E) : m ξ ≤ 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by
      have : ‖ξ‖ ≤ k := mem_closedBall_zero_iff.1 hξ
      simp only [m]
      gcongr
    set c : ℝ := 4 * Real.pi ^ 2 * (k : ℝ) ^ 2
    have hc : 0 ≤ c := by positivity
    let gfun : ℝ^n → ℂ := E.indicator fun ξ ↦ ((m ξ : ℝ) : ℂ) * z ξ
    let hfun : ℝ^n → ℂ := E.indicator fun ξ ↦ ((m ξ ^ 2 : ℝ) : ℂ) * z ξ
    have hgmeas : Measurable gfun :=
      ((Complex.measurable_ofReal.comp hmc.measurable).mul hzm).indicator hE
    have hhmeas : Measurable hfun :=
      ((Complex.measurable_ofReal.comp (hmc.measurable.pow_const 2)).mul hzm).indicator hE
    have hgL : MemLp gfun 2 volume := by
      refine MemLp.of_le ((Lp.memLp z).norm.const_mul c) hgmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ ↦ ?_)
      by_cases hξ : ξ ∈ E
      · simp only [gfun, Set.indicator_of_mem hξ, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hm0 ξ), abs_norm, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_right (hmE ξ hξ) (norm_nonneg _)
      · simp only [gfun, Set.indicator_of_notMem hξ, norm_zero]
        positivity
    have hhL : MemLp hfun 2 volume := by
      refine MemLp.of_le ((Lp.memLp z).norm.const_mul (c ^ 2)) hhmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ ↦ ?_)
      by_cases hξ : ξ ∈ E
      · simp only [hfun, Set.indicator_of_mem hξ, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hm0 ξ) 2), abs_norm,
          abs_of_nonneg (pow_nonneg hc 2)]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hm0 ξ) (hmE ξ hξ) 2)
          (norm_nonneg _)
      · simp only [hfun, Set.indicator_of_notMem hξ, norm_zero]
        positivity
    set g := hgL.toLp gfun
    set h := hhL.toLp hfun
    have hgh : ∀ᵐ ξ ∂volume, h ξ = ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * g ξ := by
      filter_upwards [hgL.coeFn_toLp, hhL.coeFn_toLp] with ξ hg hh
      rw [hg, hh]
      by_cases hξ : ξ ∈ E
      · simp only [gfun, hfun, Set.indicator_of_mem hξ, m]
        push_cast
        ring
      · simp only [gfun, hfun, Set.indicator_of_notMem hξ, mul_zero]
    have hkey := enorm_inner_fourier_selfsimilarResolvent_le hn hμ f g h hgh
    rw [← hz] at hkey
    have hint : Integrable (fun ξ ↦ E.indicator (fun ξ ↦ m ξ ^ 2 * ‖z ξ‖ ^ 2) ξ) volume := by
      have h2 : Integrable (fun ξ ↦ ‖z ξ‖ ^ 2) volume :=
        (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable z)).mp (Lp.memLp z)
      refine Integrable.mono' (h2.const_mul (c ^ 2))
        (((hmc.measurable.pow_const 2).mul (hzm.norm.pow_const 2)).indicator
          hE).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ ↦ ?_)
      by_cases hξ : ξ ∈ E
      · rw [Set.indicator_of_mem hξ, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hm0 ξ) (hmE ξ hξ) 2)
          (by positivity)
      · rw [Set.indicator_of_notMem hξ, norm_zero]
        positivity
    have hFk : ∫⁻ ξ, F k ξ =
        ENNReal.ofReal (∫ ξ, E.indicator (fun ξ ↦ m ξ ^ 2 * ‖z ξ‖ ^ 2) ξ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun ξ ↦ Set.indicator_nonneg
          (fun ξ _ ↦ by positivity) ξ)]
      apply lintegral_congr
      intro ξ
      by_cases hξ : ξ ∈ E
      · have hξ' : ξ ∈ Metric.closedBall (0 : ℝ^n) k := hξ
        simp only [F, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ']
      · have hξ' : ξ ∉ Metric.closedBall (0 : ℝ^n) k := hξ
        simp only [F, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ',
          ENNReal.ofReal_zero]
    have hinner : ‖inner ℂ h z‖ₑ = ∫⁻ ξ, F k ξ := by
      rw [hFk, L2.inner_def]
      have hpt : (fun ξ ↦ inner ℂ (h ξ) (z ξ)) =ᵐ[volume]
          fun ξ ↦ ((E.indicator (fun ξ ↦ m ξ ^ 2 * ‖z ξ‖ ^ 2) ξ : ℝ) : ℂ) := by
        filter_upwards [hhL.coeFn_toLp] with ξ hh
        rw [hh, RCLike.inner_apply']
        by_cases hξ : ξ ∈ E
        · simp only [hfun, Set.indicator_of_mem hξ, map_mul, Complex.conj_ofReal]
          rw [mul_assoc, Complex.conj_mul']
          push_cast
          ring
        · simp only [hfun, Set.indicator_of_notMem hξ, map_zero, zero_mul,
            Complex.ofReal_zero]
      rw [integral_congr_ae hpt, integral_complex_ofReal, ← ofReal_norm,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ξ ↦
          Set.indicator_nonneg (fun ξ _ ↦ by positivity) ξ)]
    have hgsq : ∫⁻ ξ, ENNReal.ofReal (‖g ξ‖ ^ 2) = ∫⁻ ξ, F k ξ := by
      apply lintegral_congr_ae
      filter_upwards [hgL.coeFn_toLp] with ξ hg
      rw [hg]
      by_cases hξ : ξ ∈ E
      · have hξ' : ξ ∈ Metric.closedBall (0 : ℝ^n) k := hξ
        simp only [gfun, F, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ', norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm0 ξ)]
        ring_nf
      · have hξ' : ξ ∉ Metric.closedBall (0 : ℝ^n) k := hξ
        simp only [gfun, F, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ',
          norm_zero]
        norm_num
    rw [hinner, hgsq] at hkey
    have hfin : ∫⁻ ξ, F k ξ ≠ ∞ := by rw [hFk]; exact ENNReal.ofReal_ne_top
    set I := ∫⁻ ξ, F k ξ
    have hhalf : 2⁻¹ * I ≤ 2⁻¹ * B :=
      (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top (by simp) hfin)).mp
        ((by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul] :
          2⁻¹ * I + 2⁻¹ * I = I).trans_le hkey)
    calc I = 2 * (2⁻¹ * I) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]
      _ ≤ 2 * (2⁻¹ * B) := by gcongr
      _ = B := by rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]
  calc ∫⁻ ξ, ENNReal.ofReal ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 * ‖z ξ‖ ^ 2) =
        ∫⁻ ξ, ⨆ k, F k ξ := lintegral_congr fun ξ ↦ (hsup ξ).symm
    _ = ⨆ k, ∫⁻ ξ, F k ξ := lintegral_iSup hFm hmono
    _ ≤ B := iSup_le hbound

theorem baseL2_add {k : ℕ} (U V : W^{k,2}(ℝ^n)) : baseL2 (U + V) = baseL2 U + baseL2 V := by
  rw [← complexifyL2CLM_base, ← complexifyL2CLM_base, ← complexifyL2CLM_base, map_add, map_add]

/-- The frequency-weighted transform of the resolvent, `|ξ|² R_μ f`, is square integrable
with mass at most `‖f‖ / (4π²)`. -/
theorem eLpNorm_sq_norm_mul_fourier_selfsimilarResolvent_le (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) (f : W^{0,2}(ℝ^n)) :
    eLpNorm (fun ξ ↦ ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (𝓕 (baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f)) :
          Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume ≤
      ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹ * ‖f‖) := by
  set z := (𝓕 (baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f)) :
    Lp ℂ 2 (volume : Measure (ℝ^n))) with hz
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ^n ↦ ((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ) volume :=
    ((Complex.continuous_ofReal.comp (continuous_norm.pow 2)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable z)
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
  refine (lintegral_ofReal_norm_pow_eq_eLpNorm_pow hmeas two_ne_zero).symm.trans_le ?_
  have hmain := lintegral_weight_sq_fourier_selfsimilarResolvent_le hn hμ f
  rw [← hz, lintegral_ofReal_norm_pow_eq_eLpNorm_pow (Lp.aestronglyMeasurable _) two_ne_zero,
    Nat.cast_ofNat] at hmain
  have hf : eLpNorm (𝓕 (baseL2 f) : Lp ℂ 2 (volume : Measure (ℝ^n))) 2 volume =
      ENNReal.ofReal ‖f‖ := by
    rw [← Lp.enorm_def, ← ofReal_norm, Lp.norm_fourier_eq, ← norm_eq_norm_baseL2_of_order_zero]
  rw [hf] at hmain
  calc ∫⁻ ξ, ENNReal.ofReal (‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ‖ ^ 2) =
        ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹ ^ 2) *
          ∫⁻ ξ, ENNReal.ofReal ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 * ‖z ξ‖ ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro ξ
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        field_simp
    _ ≤ ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹ ^ 2) * ENNReal.ofReal ‖f‖ ^ 2 := by gcongr
    _ = ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹ * ‖f‖) ^ 2 := by
        rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_pow (by positivity), mul_pow]

/-- The resolvent of an `L²` datum has a whole-space `H²` realization, with a bound that is
uniform in `μ ≥ 1/2`. -/
theorem exists_wkpSpace_two_selfsimilarResolvent (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    (f : W^{0,2}(ℝ^n)) :
    ∃ V : W^{2,2}(ℝ^n), baseL2 V = baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f) ∧
      ‖V‖ ≤ toWkpSpaceNormBound n 2 * ((μ⁻¹ + (4 * Real.pi ^ 2)⁻¹) * ‖f‖) := by
  have hμ0 : 0 < μ := by linarith
  set z := (𝓕 (baseL2 (selfsimilarResolvent n hn hμ0 f)) :
    Lp ℂ 2 (volume : Measure (ℝ^n))) with hz
  have hsq := eLpNorm_sq_norm_mul_fourier_selfsimilarResolvent_le hn hμ f
  rw [← hz] at hsq
  have hsplit : (fun ξ ↦ besselSymbol n ((2 : ℕ) : ℝ) ξ * z ξ) =
      fun ξ ↦ z ξ + ((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ := by
    funext ξ
    rw [besselSymbol, show (((2 : ℕ) : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    push_cast
    ring
  have hzL : eLpNorm (z : ℝ^n → ℂ) 2 volume ≤ ENNReal.ofReal (μ⁻¹ * ‖f‖) := by
    rw [← Lp.enorm_def, ← ofReal_norm, hz, Lp.norm_fourier_eq, ← norm_eq_norm_baseL2_of_order_zero]
    exact ENNReal.ofReal_le_ofReal (((selfsimilarResolvent n hn hμ0).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (norm_selfsimilarResolvent_le hn hμ0) (norm_nonneg _)))
  have hsum : eLpNorm (fun ξ ↦ besselSymbol n ((2 : ℕ) : ℝ) ξ * z ξ) 2 volume ≤
      ENNReal.ofReal ((μ⁻¹ + (4 * Real.pi ^ 2)⁻¹) * ‖f‖) := by
    rw [hsplit]
    refine ((eLpNorm_add_le (f := (z : ℝ^n → ℂ)) (g := fun ξ ↦ ((‖ξ‖ ^ 2 : ℝ) : ℂ) * z ξ)
      (by norm_num)).trans (add_le_add hzL hsq)).trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
  have hmem : MemLp (fun ξ ↦ besselSymbol n ((2 : ℕ) : ℝ) ξ * z ξ) 2 volume :=
    lt_of_le_of_lt hsum ENNReal.ofReal_lt_top
  obtain ⟨V, hV, hVnorm⟩ := exists_wkpSpace_of_memLp_besselWeight 2
    (selfsimilarResolvent n hn hμ0 f) hmem
  exact ⟨V, hV, hVnorm.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_le_of_le_ofReal (by positivity) hsum) toWkpSpaceNormBound_nonneg)⟩

/-- The second-order realization `(μ + L₀)⁻¹ : L² → H²` of the shifted free self-similar
resolvent, for `μ ≥ 1/2`. Its operator norm is bounded uniformly in `μ`. -/
def selfsimilarResolventH2 (n : ℕ) (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ) :
    W^{0,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (exists_wkpSpace_two_selfsimilarResolvent hn hμ f).choose
      map_add' := fun f g ↦ by
        apply baseL2_injective
        rw [baseL2_add, (exists_wkpSpace_two_selfsimilarResolvent hn hμ (f + g)).choose_spec.1,
          (exists_wkpSpace_two_selfsimilarResolvent hn hμ f).choose_spec.1,
          (exists_wkpSpace_two_selfsimilarResolvent hn hμ g).choose_spec.1, map_add,
          baseL2_add]
      map_smul' := fun c f ↦ by
        apply baseL2_injective
        rw [RingHom.id_apply, baseL2_smul,
          (exists_wkpSpace_two_selfsimilarResolvent hn hμ (c • f)).choose_spec.1,
          (exists_wkpSpace_two_selfsimilarResolvent hn hμ f).choose_spec.1, map_smul,
          baseL2_smul] }
    (toWkpSpaceNormBound n 2 * (μ⁻¹ + (4 * Real.pi ^ 2)⁻¹))
    (fun f ↦ by
      have h := (exists_wkpSpace_two_selfsimilarResolvent hn hμ f).choose_spec.2
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using h)

/-- The second-order realization has the resolvent as its base function. -/
theorem baseL2_selfsimilarResolventH2 (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ)
    (f : W^{0,2}(ℝ^n)) :
    baseL2 (selfsimilarResolventH2 n hn hμ f) =
      baseL2 (selfsimilarResolvent n hn (by linarith : 0 < μ) f) :=
  (exists_wkpSpace_two_selfsimilarResolvent hn hμ f).choose_spec.1

/-- The second-order realization is bounded uniformly in the shift `μ ≥ 1/2`. -/
theorem norm_selfsimilarResolventH2_le (hn : 2 ≤ n) {μ : ℝ} (hμ : 1 / 2 ≤ μ) :
    ‖selfsimilarResolventH2 n hn hμ‖ ≤ toWkpSpaceNormBound n 2 * (μ⁻¹ + (4 * Real.pi ^ 2)⁻¹) :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg toWkpSpaceNormBound_nonneg
    (add_nonneg (inv_nonneg.mpr (by linarith)) (by positivity))) _

end HeatEquation.WholeSpace
