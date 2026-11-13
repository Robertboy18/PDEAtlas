/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.FundamentalSolution
public import PDE.DistributionTheory.Distribution.Operator.Laplacian
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.Distribution
import PDE.Analysis.Calculus.SphericalMean
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Elliptic.PotentialTheory.FundamentalSolution.FluxNormalization

/-!
# The Newtonian kernel as a fundamental-solution distribution

For every `n ≥ 3`, the canonical Newtonian kernel satisfies `∫ Φₙ Δφ = -φ(0)` for every compactly
supported `C²` test function (`integral_fundamentalSolution_mul_laplacian`). Consequently its
regular distribution satisfies `-ΔΦₙ = δ₀` (`negativeLaplacian_fundamentalSolutionDistribution`),
the identity that Evans writes formally after §2.2.1, Theorem 1. The kernel, its off-pole
regularity, and its flux normalization are those of Evans's §2.2.1. No boundary identity or
distribution equation is assumed.

## How it works

Evans's proof of Theorem 1 contains the same identity for the test functions `y ↦ f(x - y)`: he
cuts a small ball `B(0, ε)` out of the integral and integrates by parts twice. We reduce to one
radial variable instead. Write `M(r)` for the spherical mean of `φ` and `B(r)` for the integral of
`Δφ` on the ball of radius `r`. The ball divergence theorem gives `B(r) = r^(n-1) |S^(n-1)| M'(r)`.
The kernel's normalized flux is `-1` (`deriv_fundamentalSolution_smul`), so the derivative of
`Φₙ(r) B(r) + M(r)` is the spherical integral of `Φₙ Δφ`. The same primitive is
`r M'(r) / (n-2) + M(r)`, which is continuous at zero with value `φ(0)` and vanishes beyond the
support of `φ`. Coarea and the fundamental theorem of calculus give the pole identity, including
its sign.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), the fundamental solution (6), p. 22; §2.2.1(b),
  Theorem 1 and its proof, pp. 23-25, and the interpretation `-ΔΦ = δ₀`, p. 25.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace PotentialTheory.Newtonian

open Filter MeasureTheory Set TopologicalSpace
open PDE.Analysis
open scoped Distributions Topology

variable {n : ℕ}

private theorem continuous_deriv_unitSphereAverage
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (deriv (unitSphereAverage n u 0)) := by
  have hformula :
      deriv (unitSphereAverage n u 0) =
        fun r ↦ (∫ ω : Metric.sphere (0 : ℝ^n) 1,
          fderiv ℝ u (r • (ω : ℝ^n)) (ω : ℝ^n)
            ∂(volume : Measure (ℝ^n)).toSphere) / unitSphereArea n := by
    funext r
    simpa using (hasDerivAt_unitSphereAverage u 0 r hu).deriv
  rw [hformula]
  apply Continuous.div_const
  have hparam : Continuous (fun r : ℝ ↦
      ∫ ω in (univ : Set (Metric.sphere (0 : ℝ^n) 1)),
        fderiv ℝ u (r • (ω : ℝ^n)) (ω : ℝ^n)
          ∂(volume : Measure (ℝ^n)).toSphere) := by
    apply continuous_parametric_integral_of_continuous _ isCompact_univ
    exact (hu.continuous_fderiv_apply (hn := by norm_num)).comp
      ((continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp continuous_snd))
  simpa only [Measure.restrict_univ] using hparam

variable [Fact (0 < n)]

private theorem kernel_mul_radialJacobian
    (hn : 3 ≤ n) (ω : Metric.sphere (0 : ℝ^n) 1)
    {r : ℝ} (hr : 0 < r) :
    fundamentalSolution n (r • (ω : ℝ^n)) *
        (r ^ (n - 1) * unitSphereArea n) = r / ((n : ℝ) - 2) := by
  have hω : ‖(ω : ℝ^n)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hk : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have harea : unitSphereArea n ≠ 0 := ne_of_gt unitSphereArea_pos
  have hkernel :
      fundamentalSolution n (r • (ω : ℝ^n)) =
        1 / (((n : ℝ) - 2) * unitSphereArea n * r ^ (n - 2)) := by
    rw [fundamentalSolution_of_three_le hn]
    simp [norm_smul, hω, abs_of_pos hr, unitSphereArea_eq, mul_assoc]
  have hpower : r ^ (n - 1) = r ^ (n - 2) * r := by
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
  rw [hkernel, hpower]
  field_simp [hk, harea, hr.ne']

private theorem sphereIntegral_kernel_mul
    (hn : 3 ≤ n) (f : ℝ^n → ℝ)
    (ω₀ : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 < r) :
    sphereIntegral n (fun x ↦ fundamentalSolution n x * f x) 0 r =
      r / ((n : ℝ) - 2) * unitSphereAverage n f 0 r := by
  have hradial (ω : Metric.sphere (0 : ℝ^n) 1) :
      fundamentalSolution n (r • (ω : ℝ^n)) =
        fundamentalSolution n (r • (ω₀ : ℝ^n)) := by
    apply fundamentalSolution_eq_of_norm_eq
    simp [norm_smul, mem_sphere_zero_iff_norm.mp ω.property,
      mem_sphere_zero_iff_norm.mp ω₀.property]
  have harea : unitSphereArea n ≠ 0 := ne_of_gt unitSphereArea_pos
  have hcoefficient := kernel_mul_radialJacobian hn ω₀ hr
  unfold sphereIntegral unitSphereAverage
  simp only [zero_add, abs_of_pos hr, hradial]
  rw [integral_const_mul, ← hcoefficient]
  field_simp [harea]

/-- The Newtonian kernel satisfies the pole identity against every compactly supported
`C²` test function, in every dimension at least three. -/
theorem integral_fundamentalSolution_mul_laplacian
    (hn : 3 ≤ n) {U : Opens (ℝ^n)} (φ : 𝓓^{2}(U, ℝ)) :
    (∫ x : ℝ^n, fundamentalSolution n x * laplacian φ x) = -φ 0 := by
  let M : ℝ → ℝ := unitSphereAverage n φ 0
  let ω₀ : Metric.sphere (0 : ℝ^n) 1 := ⟨EuclideanSpace.single ⟨0, Fact.out⟩ 1, by simp⟩
  let P : ℝ → ℝ := fun r ↦ fundamentalSolution n (r • (ω₀ : ℝ^n))
  let H : ℝ → ℝ := fun r ↦ r / ((n : ℝ) - 2) * deriv M r + M r
  let g : ℝ → ℝ := fun r ↦ r / ((n : ℝ) - 2) * unitSphereAverage n (laplacian φ) 0 r
  have hφ₁ : ContDiff ℝ 1 (φ : ℝ^n → ℝ) := φ.contDiff.of_le (by norm_num)
  have hMdiff (r : ℝ) : DifferentiableAt ℝ M r :=
    (hasDerivAt_unitSphereAverage φ 0 r hφ₁).differentiableAt
  have hHcont : Continuous H := ((continuous_id.div_const _).mul
    (continuous_deriv_unitSphereAverage hφ₁)).add (show Differentiable ℝ M from hMdiff).continuous
  have hgcont : Continuous g := by
    refine (continuous_id.div_const _).mul ?_
    unfold unitSphereAverage
    refine Continuous.div_const ?_ _
    simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (ℝ^n)).toSphere) (s := univ)
      (f := fun r (ω : Metric.sphere (0 : ℝ^n) 1) ↦ laplacian φ (0 + r • (ω : ℝ^n)))
      (φ.continuous_laplacian_two.comp (by fun_prop)) isCompact_univ
  have hflux (r : ℝ) (hr : 0 < r) :
      ballIntegral n (laplacian φ) 0 r = (r ^ (n - 1) * unitSphereArea n) * deriv M r :=
    (unitSphereAverage_radial_flux φ 0 hr φ.contDiff).symm
  have hHderiv (r : ℝ) (hr : 0 < r) : HasDerivAt H (g r) r := by
    have hP : HasDerivAt P (-1 / (r ^ (n - 1) * unitSphereArea n)) r := by
      rw [← deriv_fundamentalSolution_smul (by omega : 2 ≤ n) ω₀ hr]
      exact (((contDiffAt_fundamentalSolution n _ (smul_ne_zero hr.ne'
        (ne_zero_of_mem_unit_sphere ω₀))).differentiableAt (by simp)).comp r
          (differentiableAt_id.smul_const (ω₀ : ℝ^n))).hasDerivAt
    have hsphere : P r * sphereIntegral n (laplacian φ) 0 r = g r := by
      have := (unitSphereArea_pos (n := n)).ne'
      simp only [P, g, sphereIntegral, unitSphereAverage, abs_of_pos hr]
      rw [← kernel_mul_radialJacobian hn ω₀ hr]
      field_simp
    refine (((hP.mul (hasDerivAt_ballIntegral_radius (laplacian φ) φ.continuous_laplacian_two
      (0 : ℝ^n) hr)).add (hMdiff r).hasDerivAt).congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [hsphere, hflux r hr, ← mul_assoc, div_mul_cancel₀ (-1 : ℝ)
        (mul_ne_zero (pow_ne_zero _ hr.ne') unitSphereArea_pos.ne')]
      ring
    · filter_upwards [Ioi_mem_nhds hr] with s hs
      change H s = P s * ballIntegral n (laplacian φ) 0 s + M s
      rw [hflux s hs, ← mul_assoc, kernel_mul_radialJacobian hn ω₀ hs]
  obtain ⟨R, hR, hsupport⟩ := φ.hasCompactSupport.isBounded.subset_ball_lt 0 (0 : ℝ^n)
  have hMzero (r : ℝ) (hr : R ≤ r) : M r = 0 := by
    have hpoint (ω : Metric.sphere (0 : ℝ^n) 1) : φ (r • (ω : ℝ^n)) = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦ not_lt_of_ge (by
        simpa [norm_smul, mem_sphere_zero_iff_norm.mp ω.property, abs_of_pos (hR.trans_le hr)]
          using hr) (mem_ball_zero_iff.1 (hsupport hmem))
    simp [M, unitSphereAverage, hpoint]
  have hHend : H (R + 1) = 0 := by
    have hMnear : M =ᶠ[𝓝 (R + 1)] fun _ ↦ 0 := by
      filter_upwards [Ioi_mem_nhds (show R < R + 1 by linarith)] with r hr using hMzero r hr.le
    simp [H, hMnear.deriv_eq, hMzero (R + 1) (by linarith)]
  have hFTC : (∫ r in (0 : ℝ)..(R + 1), g r) = -φ 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hHcont.continuousOn
      (fun r hr ↦ hHderiv r hr.1) (hgcont.intervalIntegrable 0 (R + 1)), hHend]
    simp [H, M]
  have hint : Integrable (fun x : ℝ^n ↦ fundamentalSolution n x * laplacian φ x) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_fundamentalSolution n).integrable_smul_right_of_hasCompactSupport
        φ.continuous_laplacian_two φ.hasCompactSupport_laplacian
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball (0 : ℝ^n) (R + 1))
    fun x hx ↦ ?_]
  · change ballIntegral n (fun x ↦ fundamentalSolution n x * laplacian φ x) 0 (R + 1) = -φ 0
    rw [coarea_formula_ball _ _ _ hint.integrableOn, ← hFTC,
      intervalIntegral.integral_of_le (by linarith), ← setIntegral_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_congr_fun measurableSet_Ioc fun r hr ↦
      sphereIntegral_kernel_mul hn (laplacian φ) ω₀ hr.1
  have hlap : laplacian φ x = 0 := by
    by_contra hne
    have := mem_ball_zero_iff.1 (hsupport (φ.support_laplacian_subset hne))
    simp only [mem_ball_zero_iff, not_lt] at hx
    linarith
  simp [hlap]

/-- In every dimension at least three, the canonical Newtonian kernel is a fundamental
solution of the negative Laplacian at the origin. -/
theorem fundamentalSolutionDistribution_isFundamentalSolution (hn : 3 ≤ n) :
    Distribution.IsFundamentalSolutionAt
      (Distribution.negativeLaplacianCLM n)
      (fundamentalSolutionDistribution n) (0 : ℝ^n) := by
  rw [Distribution.isFundamentalSolutionAt_iff]
  refine ⟨by simp, ?_⟩
  intro φ
  rw [Distribution.negativeLaplacianCLM_apply, fundamentalSolutionDistribution_apply]
  let φ₂ : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ) := TestFunction.monoCLM ℝ φ
  have hφ₂ : (φ₂ : ℝ^n → ℝ) = φ := by simp [φ₂]
  have hpole := integral_fundamentalSolution_mul_laplacian hn φ₂
  rw [hφ₂] at hpole
  simp only [TestFunction.laplacianCLM_apply_eq_laplacian] at hpole ⊢
  have hcomm :
      (∫ x : ℝ^n, laplacian (φ : ℝ^n → ℝ) x * fundamentalSolution n x) =
        ∫ x : ℝ^n, fundamentalSolution n x * laplacian (φ : ℝ^n → ℝ) x := by
    apply integral_congr_ae
    filter_upwards with x using mul_comm _ _
  rw [hcomm]
  linarith

/-- Applying the negative Laplacian to the Newtonian kernel distribution produces the
Dirac mass at zero. -/
theorem negativeLaplacian_fundamentalSolutionDistribution (hn : 3 ≤ n) :
    Distribution.negativeLaplacianCLM n (fundamentalSolutionDistribution n) =
      Distribution.delta (0 : ℝ^n) :=
  (fundamentalSolutionDistribution_isFundamentalSolution hn).eq

end PotentialTheory.Newtonian
