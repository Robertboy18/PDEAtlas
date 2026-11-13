/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.FundamentalSolution
public import PDE.DistributionTheory.Distribution.Operator.Laplacian
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.Distribution
import Mathlib.MeasureTheory.Integral.PeakFunction
import PDE.Analysis.Integration.Polar
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.Euclidean.Laplacian
import CAS.IntegrationTactic

/-!
# The planar Laplace fundamental solution as a distribution

We prove the pole identity `∫ Φ Δφ = -φ(0)` for the logarithmic fundamental solution
`Φ(x) = -(2π)⁻¹ log ‖x‖` in two dimensions, in the sign convention `-ΔΦ = δ₀` used throughout the
potential-theory hierarchy (`fundamentalSolution 2`). The kernel and its normalization are those of
Evans's §2.2.1, where `-ΔΦ = δ₀` is written formally after Theorem 1. For distributions, see
Lieb and Loss, Chapter 6.

## Main results

* `regularizedFundamentalSolution`, `poleApproximation`: the smooth
  regularization `Φε` and the kernel `Kε = -ΔΦε`.
* `laplacian_regularizedFundamentalSolution`: the pointwise identity
  `ΔΦε = -Kε` for every `ε ≠ 0`.
* `integral_poleApproximation`: each `Kε` with `ε > 0` is integrable with total
  mass one.
* `tendsto_integral_poleApproximation_inv`: `∫ Kε f → f(0)` for integrable `f`
  continuous at the origin (Mathlib's peak-function theorem).
* `integral_fundamentalSolution_mul_laplacian`: the test-function identity
  `∫ Φ Δφ = -φ(0)`.
* `fundamentalSolutionDistribution_isFundamentalSolution`: the
  distributional statement that `fundamentalSolutionDistribution 2` is a
  fundamental solution of `-Δ` at the origin.

## How it works

Evans's proof of §2.2.1, Theorem 1, cuts a small disc out of the integral and integrates by parts
twice. We regularize the kernel instead. The smooth family

`Φε(x) = -(4π)⁻¹ log (‖x‖² + ε²)`

has negative Laplacian equal to the nonnegative unit-mass kernel

`Kε(x) = ε² / (π (‖x‖² + ε²)²)`

(`laplacian_regularizedFundamentalSolution`), and integration by parts against a test function
`φ` (`PDE.DistributionTheory.integral_mul_laplacian_eq`) gives `∫ Φε Δφ = -∫ Kε φ`. The kernels
`Kε` form an approximate identity, so the right side tends to `-φ(0)` by Mathlib's peak-function
theorem. On the left, `Φε → Φ` under the integral by Mathlib's dominated convergence theorem
`tendsto_integral_filter_of_dominated_convergence`, with the two-sided bounds
`regularizedFundamentalSolution_bounds`. SymLean's `cas` tactic computes the derivatives of the
regularized logarithm and the radial integral `∫₀^∞ r / (1 + r²)² dr = 1 / 2`.

## Implementation notes

The limit `ε → 0` is taken along inverse scales `c⁻¹` with `c → ∞`, which is
the form in which Mathlib's `tendsto_integral_comp_smul_smul_of_integrable`
and the `atTop` filter lemmas apply most directly. The mass computation for
`K₁` is done in polar coordinates via `integral_polar_addHaar_iterated`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), the fundamental solution (6), p. 22; §2.2.1(b),
  Theorem 1 and its proof, pp. 23-25, and the interpretation `-ΔΦ = δ₀`, p. 25.
  <https://doi.org/10.1090/gsm/019>
* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, American
  Mathematical Society, 2001, Chapter 6 (Distributions).
  <https://doi.org/10.1090/gsm/014/06>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace PotentialTheory.Planar

open Bornology Filter MeasureTheory Set TopologicalSpace Topology
open PDE.Analysis
open scoped Distributions

/-- Smooth logarithmic regularization of the planar fundamental solution. -/
noncomputable def regularizedFundamentalSolution
    (ε : ℝ) (x : ℝ^2) : ℝ :=
  -(1 / (4 * Real.pi)) * Real.log (‖x‖ ^ 2 + ε ^ 2)

/-- The positive rational kernel obtained by applying `-Δ` to
`regularizedFundamentalSolution` at every nonzero regularization scale. -/
noncomputable def poleApproximation (ε : ℝ) (x : ℝ^2) : ℝ :=
  ε ^ 2 / (Real.pi * (‖x‖ ^ 2 + ε ^ 2) ^ 2)

/-- A nonzero regularization scale removes the logarithmic pole. -/
theorem contDiff_regularizedFundamentalSolution
    {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (regularizedFundamentalSolution ε) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ^2 ↦ ‖x‖ ^ 2 + ε ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  unfold regularizedFundamentalSolution
  apply contDiff_const.mul
  exact harg.log fun x ↦ by
    positivity

/-- Exact Laplacian of the smooth logarithmic regularization. -/
theorem laplacian_regularizedFundamentalSolution
    {ε : ℝ} (hε : ε ≠ 0) (x : ℝ^2) :
    laplacian (regularizedFundamentalSolution ε) x =
      -poleApproximation ε x := by
  let c : ℝ := -(1 / (4 * Real.pi))
  let f : ℝ → ℝ := fun s ↦ c * Real.log (s + ε ^ 2)
  have hargPos : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  have hf : ContDiffAt ℝ 2 f (‖x‖ ^ 2) :=
    contDiffAt_const.mul ((contDiffAt_id.add contDiffAt_const).log hargPos.ne')
  rw [show regularizedFundamentalSolution ε = fun y : ℝ^2 ↦ f (‖y‖ ^ 2) from rfl,
    EuclideanLaplacian.laplacian_comp_norm_sq (n := 2) f x hf]
  have hderivNear : deriv f =ᶠ[𝓝 (‖x‖ ^ 2)] fun s ↦ c * (s + ε ^ 2)⁻¹ := by
    filter_upwards [Ioi_mem_nhds (by linarith : -(ε ^ 2) < ‖x‖ ^ 2)] with s (hs : -(ε ^ 2) < s)
    have : 0 < s + ε ^ 2 := by linarith
    have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (y + ε ^ 2)) (s + ε ^ 2)⁻¹ s := by
      cas
    simpa [f] using (hlog.const_mul c).deriv
  have hsecondAt : deriv (deriv f) (‖x‖ ^ 2) = c * (-(‖x‖ ^ 2 + ε ^ 2) ^ 2)⁻¹ := by
    rw [hderivNear.deriv_eq, show deriv (fun s ↦ c * (s + ε ^ 2)⁻¹) (‖x‖ ^ 2) =
      c * (-1 / (‖x‖ ^ 2 + ε ^ 2) ^ 2) by cas]
    field_simp [hargPos.ne']
  rw [hderivNear.eq_of_nhds, hsecondAt]
  dsimp [poleApproximation, c]
  field_simp [hargPos.ne', Real.pi_ne_zero]
  ring

/-- The pole approximation is nonnegative. -/
theorem poleApproximation_nonneg (ε : ℝ) (x : ℝ^2) :
    0 ≤ poleApproximation ε x := by
  unfold poleApproximation
  positivity

/-- The unit-scale pole approximation is integrable on the plane. -/
theorem integrable_poleApproximation_one :
    Integrable (poleApproximation 1) := by
  have hdecay :
      Integrable (fun x : ℝ^2 ↦
        ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    norm_num [finrank_euclideanSpace_fin]
  have hpow :
      Integrable (fun x : ℝ^2 ↦
        ((1 : ℝ) + ‖x‖ ^ 2)⁻¹ ^ 2) := by
    convert hdecay using 1
    funext x
    rw [show (-(4 : ℝ) / 2) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (by positivity)]
    rw [inv_pow]
    exact congrArg Inv.inv (Real.rpow_natCast (1 + ‖x‖ ^ 2) 2).symm
  convert hpow.const_mul Real.pi⁻¹ using 1
  funext x
  unfold poleApproximation
  field_simp [Real.pi_ne_zero]
  ring

/-- The radial density underlying the planar unit-scale pole approximation has
mass `1 / 2` before multiplication by the area `2π` of the unit circle. -/
private theorem integral_Ioi_radialPoleProfile :
    (∫ r in Set.Ioi (0 : ℝ), r / (1 + r ^ 2) ^ 2) = 1 / 2 := by
  cas

/-- The unit-scale pole approximation has total mass one. -/
theorem integral_poleApproximation_one :
    (∫ x : ℝ^2, poleApproximation 1 x) = 1 := by
  have hpolar := integral_polar_addHaar_iterated
    (volume : Measure (ℝ^2)) (poleApproximation 1)
    integrable_poleApproximation_one
  have harea : unitSphereArea 2 = 2 * Real.pi := by
    rw [unitSphereArea_eq, unitBallVolume_two]
    norm_num
  have hinner (r : ℝ) (hr : 0 < r) :
      (∫ ω : Metric.sphere (0 : ℝ^2) 1,
        poleApproximation 1 (r • (ω : ℝ^2))
          ∂(volume : Measure (ℝ^2)).toSphere) =
        2 / (1 + r ^ 2) ^ 2 := by
    have hpoint :
        (fun ω : Metric.sphere (0 : ℝ^2) 1 ↦
          poleApproximation 1 (r • (ω : ℝ^2))) =
          fun _ ↦ 1 / (Real.pi * (1 + r ^ 2) ^ 2) := by
      funext ω
      have hω : ‖(ω : ℝ^2)‖ = 1 :=
        mem_sphere_zero_iff_norm.mp ω.property
      unfold poleApproximation
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hpoint, integral_const]
    change unitSphereArea 2 *
        (1 / (Real.pi * (1 + r ^ 2) ^ 2)) =
      2 / (1 + r ^ 2) ^ 2
    rw [harea]
    field_simp [Real.pi_ne_zero]
  rw [hpolar]
  have hradial :
      Set.EqOn
        (fun r : ℝ ↦
          r ^ (Module.finrank ℝ (ℝ^2) - 1) •
            ∫ ω : Metric.sphere (0 : ℝ^2) 1,
              poleApproximation 1 (r • (ω : ℝ^2))
                ∂(volume : Measure (ℝ^2)).toSphere)
        (fun r ↦ 2 * (r / (1 + r ^ 2) ^ 2))
        (Set.Ioi 0) := by
    intro r hr
    change 0 < r at hr
    change r ^ (Module.finrank ℝ (ℝ^2) - 1) *
        (∫ ω : Metric.sphere (0 : ℝ^2) 1,
          poleApproximation 1 (r • (ω : ℝ^2))
            ∂(volume : Measure (ℝ^2)).toSphere) =
      2 * (r / (1 + r ^ 2) ^ 2)
    rw [show Module.finrank ℝ (ℝ^2) = 2 by simp, hinner r hr]
    norm_num
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hradial]
  rw [integral_const_mul, integral_Ioi_radialPoleProfile]
  norm_num

/-- Scaling by the regularization length reduces every positive-scale pole
approximation to the unit profile. -/
theorem poleApproximation_smul
    {ε : ℝ} (hε : 0 < ε) (x : ℝ^2) :
    poleApproximation ε (ε • x) =
      ε⁻¹ ^ 2 * poleApproximation 1 x := by
  unfold poleApproximation
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hε0 : ε ≠ 0 := hε.ne'
  field_simp [hε0, Real.pi_ne_zero]

/-- Every positive-scale pole approximation is integrable. -/
theorem integrable_poleApproximation
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (poleApproximation ε) := by
  have hscaled :
      Integrable (fun x : ℝ^2 ↦
        poleApproximation ε (ε • x)) := by
    have hright :
        Integrable (fun x : ℝ^2 ↦
          ε⁻¹ ^ 2 * poleApproximation 1 x) :=
      integrable_poleApproximation_one.const_mul (ε⁻¹ ^ 2)
    exact hright.congr <| Filter.Eventually.of_forall fun x ↦
      (poleApproximation_smul hε x).symm
  exact (integrable_comp_smul_iff volume
    (poleApproximation ε) hε.ne').1 hscaled

/-- Every positive-scale pole approximation has total mass one. -/
theorem integral_poleApproximation
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ^2, poleApproximation ε x) = 1 := by
  have hleft :
      (∫ x : ℝ^2, poleApproximation ε (ε • x)) = ε⁻¹ ^ 2 := by
    calc
      (∫ x : ℝ^2, poleApproximation ε (ε • x)) =
          ∫ x : ℝ^2, ε⁻¹ ^ 2 * poleApproximation 1 x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦
          poleApproximation_smul hε x
      _ = ε⁻¹ ^ 2 * ∫ x : ℝ^2, poleApproximation 1 x := by
        rw [integral_const_mul]
      _ = ε⁻¹ ^ 2 := by rw [integral_poleApproximation_one, mul_one]
  have hscale := Measure.integral_comp_smul
    (volume : Measure (ℝ^2)) (poleApproximation ε) ε
  rw [hleft, show Module.finrank ℝ (ℝ^2) = 2 by simp] at hscale
  have habs : |(ε ^ 2)⁻¹| = ε⁻¹ ^ 2 := by
    rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hε))]
    exact (inv_pow ε 2).symm
  rw [habs] at hscale
  have hcoeff : ε⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hε.ne')
  apply mul_left_cancel₀ hcoeff
  simpa only [mul_one, smul_eq_mul] using hscale.symm

/-- The unit pole profile has the decay required by Mathlib's peak-kernel
theorem. -/
theorem tendsto_norm_sq_mul_poleApproximation_one :
    Tendsto (fun x : ℝ^2 ↦ ‖x‖ ^ 2 * poleApproximation 1 x)
      (cobounded (ℝ^2)) (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ^2 ↦ (1 + ‖x‖ ^ 2)⁻¹) (cobounded (ℝ^2)) (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop))
  refine (bdd_le_mul_tendsto_zero (f := fun x : ℝ^2 ↦ Real.pi⁻¹ * (‖x‖ ^ 2 / (1 + ‖x‖ ^ 2)))
    (b := 0) (B := Real.pi⁻¹) (.of_forall fun x ↦ by positivity)
    (.of_forall fun x ↦ mul_le_of_le_one_right (inv_nonneg.mpr Real.pi_pos.le)
      ((div_le_one (by positivity)).2 (by linarith))) hinv).congr' (.of_forall fun x ↦ ?_)
  unfold poleApproximation
  field_simp
  ring

/-- The rescaled unit pole profile converges to evaluation at the origin
against every integrable function continuous there. -/
theorem tendsto_integral_scaledPoleApproximation
    {g : ℝ^2 → ℝ} (hg : Integrable g) (hcontinuous : ContinuousAt g 0) :
    Tendsto
      (fun c : ℝ ↦
        ∫ x : ℝ^2, (c ^ 2 * poleApproximation 1 (c • x)) * g x)
      atTop (nhds (g 0)) := by
  have hdecay :
      Tendsto
        (fun x : ℝ^2 ↦
          ‖x‖ ^ Module.finrank ℝ (ℝ^2) * poleApproximation 1 x)
        (cobounded (ℝ^2)) (nhds 0) := by
    simpa only [show Module.finrank ℝ (ℝ^2) = 2 by simp] using
      tendsto_norm_sq_mul_poleApproximation_one
  have hpeak :
      Tendsto
        (fun c : ℝ ↦
          ∫ x : ℝ^2,
            (c ^ Module.finrank ℝ (ℝ^2) *
              poleApproximation 1 (c • x)) • g x)
        atTop (nhds (g 0)) :=
    tendsto_integral_comp_smul_smul_of_integrable
      (E := ℝ) (F := ℝ^2) (μ := volume)
      (φ := poleApproximation 1) (g := g)
      (poleApproximation_nonneg 1)
      integral_poleApproximation_one
      hdecay hg hcontinuous
  simpa only [show Module.finrank ℝ (ℝ^2) = 2 by simp, smul_eq_mul] using hpeak

/-- Inverse-scale notation for the same rescaled unit pole profile. -/
theorem poleApproximation_inv_eq_scaled
    {c : ℝ} (hc : 0 < c) (x : ℝ^2) :
    poleApproximation c⁻¹ x =
      c ^ 2 * poleApproximation 1 (c • x) := by
  unfold poleApproximation
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hc0 : c ≠ 0 := hc.ne'
  field_simp [hc0, Real.pi_ne_zero]

/-- As the regularization length tends to zero through inverse positive
scales, the pole approximation converges weakly to the Dirac mass at zero. -/
theorem tendsto_integral_poleApproximation_inv
    {g : ℝ^2 → ℝ} (hg : Integrable g) (hcontinuous : ContinuousAt g 0) :
    Tendsto
      (fun c : ℝ ↦ ∫ x : ℝ^2, poleApproximation c⁻¹ x * g x)
      atTop (nhds (g 0)) := by
  apply (tendsto_integral_scaledPoleApproximation hg hcontinuous).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa using congrArg (fun y ↦ y * g x)
      (poleApproximation_inv_eq_scaled hc x).symm

/-- Away from the pole, the smooth logarithmic regularizations converge to
the canonical planar fundamental solution. -/
theorem tendsto_regularizedFundamentalSolution_inv
    {x : ℝ^2} (hx : x ≠ 0) :
    Tendsto (fun c : ℝ ↦ regularizedFundamentalSolution c⁻¹ x)
      atTop (nhds (fundamentalSolution 2 x)) := by
  have hinv : Tendsto (fun c : ℝ ↦ c⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have harg :
      Tendsto (fun c : ℝ ↦ ‖x‖ ^ 2 + c⁻¹ ^ 2)
        atTop (nhds (‖x‖ ^ 2)) := by
    have hconst :
        Tendsto (fun _ : ℝ ↦ ‖x‖ ^ 2) atTop (nhds (‖x‖ ^ 2)) :=
      tendsto_const_nhds
    simpa using hconst.add (hinv.pow 2)
  have hnormSq : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hlog :
      Tendsto (fun c : ℝ ↦ Real.log (‖x‖ ^ 2 + c⁻¹ ^ 2))
        atTop (nhds (Real.log (‖x‖ ^ 2))) :=
    Tendsto.comp (Real.continuousAt_log hnormSq) harg
  have hscaled := hlog.const_mul (-(1 / (4 * Real.pi)))
  have hfundamental :
      fundamentalSolution 2 x =
        -(1 / (2 * Real.pi)) * Real.log ‖x‖ := by
    simp [fundamentalSolution, hx]
  convert hscaled using 1
  · rfl
  · rw [hfundamental, Real.log_pow]
    ring_nf

/-- For inverse scales at least one, the regularized logarithm lies between
the fixed scale-one kernel and the singular fundamental solution. -/
theorem regularizedFundamentalSolution_bounds
    {c : ℝ} (hc : 1 ≤ c) {x : ℝ^2} (hx : x ≠ 0) :
    regularizedFundamentalSolution 1 x ≤
        regularizedFundamentalSolution c⁻¹ x ∧
      regularizedFundamentalSolution c⁻¹ x ≤
        fundamentalSolution 2 x := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hinvSqLe : c⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.2 hcpos.le) (inv_le_one_of_one_le₀ hc)
  have hcoefficient : -(1 / (4 * Real.pi)) ≤ 0 := by
    have : 0 < 1 / (4 * Real.pi) := by positivity
    linarith
  unfold regularizedFundamentalSolution
  refine ⟨mul_le_mul_of_nonpos_left (Real.log_le_log (by positivity) (by rw [one_pow]; linarith))
    hcoefficient,
    (mul_le_mul_of_nonpos_left (Real.log_le_log (x := ‖x‖ ^ 2) (by positivity)
      (le_add_of_nonneg_right (by positivity))) hcoefficient).trans_eq ?_⟩
  rw [show fundamentalSolution 2 x = -(1 / (2 * Real.pi)) * Real.log ‖x‖ by
    simp [fundamentalSolution, hx]]
  have hnormPos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  cas

/-- The regularized logarithms converge under integration against a
continuous compactly supported multiplier. -/
theorem tendsto_integral_regularizedFundamentalSolution_inv_mul
    {h : ℝ^2 → ℝ} (hcontinuous : Continuous h)
    (hcompact : HasCompactSupport h) :
    Tendsto
      (fun c : ℝ ↦
        ∫ x : ℝ^2, regularizedFundamentalSolution c⁻¹ x * h x)
      atTop
      (nhds (∫ x : ℝ^2, fundamentalSolution 2 x * h x)) := by
  have hreg : Continuous (regularizedFundamentalSolution 1) :=
    (contDiff_regularizedFundamentalSolution one_ne_zero).continuous
  have hboundIntegrable : Integrable fun x : ℝ^2 ↦
      (|regularizedFundamentalSolution 1 x| + |fundamentalSolution 2 x|) * |h x| := by
    have hloc : LocallyIntegrable (fun x : ℝ^2 ↦ |fundamentalSolution 2 x|) volume := fun x ↦ by
      simpa only [Real.norm_eq_abs] using (locallyIntegrable_fundamentalSolution 2 x).norm
    have hΓ : Integrable fun x : ℝ^2 ↦ |fundamentalSolution 2 x| * |h x| := by
      simpa only [smul_eq_mul] using
        hloc.integrable_smul_right_of_hasCompactSupport hcontinuous.abs hcompact.abs
    simp_rw [add_mul]
    exact ((hreg.abs.mul hcontinuous.abs).integrable_of_hasCompactSupport
      hcompact.abs.mul_left).add hΓ
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hboundIntegrable ?_
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact ((contDiff_regularizedFundamentalSolution
      (inv_ne_zero hc.ne')).continuous.mul hcontinuous).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (1 : ℝ)] with c hc
    filter_upwards [Measure.ae_ne volume (0 : ℝ^2)] with x hx
    obtain ⟨hlower, hupper⟩ := regularizedFundamentalSolution_bounds hc hx
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
      linarith [neg_abs_le (regularizedFundamentalSolution 1 x),
        abs_nonneg (fundamentalSolution 2 x), le_abs_self (fundamentalSolution 2 x),
        abs_nonneg (regularizedFundamentalSolution 1 x)]
  · filter_upwards [Measure.ae_ne volume (0 : ℝ^2)] with x hx
    exact (tendsto_regularizedFundamentalSolution_inv hx).mul_const (h x)

/-- At every positive inverse scale, integration by parts converts the
regularized logarithm into the negative pole approximation. -/
private theorem integral_regularizedFundamentalSolution_inv_mul_laplacian
    {U : TopologicalSpace.Opens (ℝ^2)} (φ : 𝓓^{2}(U, ℝ))
    {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ^2,
        regularizedFundamentalSolution c⁻¹ x * laplacian φ x) =
      -∫ x : ℝ^2, poleApproximation c⁻¹ x * φ x := by
  have hparts := PDE.DistributionTheory.integral_mul_laplacian_eq (f := (φ : ℝ^2 → ℝ))
    (regularizedFundamentalSolution c⁻¹) φ.contDiff
    ((contDiff_regularizedFundamentalSolution (inv_ne_zero hc.ne')).of_le
      (WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))) φ.hasCompactSupport
  simp_rw [laplacian_regularizedFundamentalSolution (inv_ne_zero hc.ne')] at hparts
  rw [← integral_neg]
  simp_rw [mul_comm (regularizedFundamentalSolution c⁻¹ _), ← hparts, mul_neg, mul_comm (φ _)]

/-- The planar logarithmic kernel satisfies `-ΔΦ = δ₀` in the
distributional sense. -/
theorem integral_fundamentalSolution_mul_laplacian
    {U : TopologicalSpace.Opens (ℝ^2)} (φ : 𝓓^{2}(U, ℝ)) :
    (∫ x : ℝ^2, fundamentalSolution 2 x * laplacian φ x) =
      -φ 0 := by
  refine tendsto_nhds_unique (tendsto_integral_regularizedFundamentalSolution_inv_mul
    φ.continuous_laplacian_two φ.hasCompactSupport_laplacian) ?_
  refine ((tendsto_integral_poleApproximation_inv (φ.continuous.integrable_of_hasCompactSupport
    φ.hasCompactSupport) φ.continuous.continuousAt).neg).congr' ?_
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  exact (integral_regularizedFundamentalSolution_inv_mul_laplacian φ hc).symm

/-! ## The planar distribution equation -/

/-- The planar logarithmic kernel is a fundamental solution for `-Δ` at
the origin. -/
theorem fundamentalSolutionDistribution_isFundamentalSolution :
    Distribution.IsFundamentalSolutionAt
      (Distribution.negativeLaplacianCLM 2)
      (fundamentalSolutionDistribution 2) (0 : ℝ^2) := by
  rw [Distribution.isFundamentalSolutionAt_iff]
  refine ⟨by simp, ?_⟩
  intro φ
  rw [Distribution.negativeLaplacianCLM_apply,
    fundamentalSolutionDistribution_apply]
  let φ₂ : 𝓓^{2}((⊤ : TopologicalSpace.Opens (ℝ^2)), ℝ) :=
    TestFunction.monoCLM ℝ φ
  have hφ₂ : (φ₂ : ℝ^2 → ℝ) = φ := by
    simp [φ₂]
  have hpole := integral_fundamentalSolution_mul_laplacian φ₂
  rw [hφ₂] at hpole
  simp only [TestFunction.laplacianCLM_apply_eq_laplacian] at hpole ⊢
  rw [show (∫ x : ℝ^2,
      laplacian (φ : ℝ^2 → ℝ) x * fundamentalSolution 2 x) =
      ∫ x : ℝ^2,
        fundamentalSolution 2 x * laplacian (φ : ℝ^2 → ℝ) x by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change laplacian (φ : ℝ^2 → ℝ) x * fundamentalSolution 2 x =
        fundamentalSolution 2 x * laplacian (φ : ℝ^2 → ℝ) x
      rw [mul_comm]]
  linarith

end PotentialTheory.Planar
