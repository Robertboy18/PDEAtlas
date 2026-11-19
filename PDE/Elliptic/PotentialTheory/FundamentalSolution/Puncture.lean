/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.FluxNormalization
public import PDE.Analysis.Calculus.SphericalMean.Limit

/-!
# The singular sphere terms in Green's identity

Let `n ≥ 2` and let `Φ` be the fundamental solution. On every sphere about the pole the outward
normal derivative of `Φ` is minus the reciprocal of the sphere's area
(`inner_gradient_fundamentalSolution_smul`), so the outward flux of `Φ` weighted by `u` is minus the
spherical mean of `u` (`integral_mul_normal_gradient_fundamentalSolution`). For `u` continuous near
the pole it converges to `-u(x)` as the radius tends to zero
(`tendsto_integral_mul_normal_gradient_fundamentalSolution`). The outer normal of a punctured domain
points toward the pole, which reverses the sign. The other boundary term, `Φ` times the normal
component of a continuous field, tends to zero (`tendsto_integral_fundamentalSolution_mul_normal`):
the radial coefficient `r^(n-1) Φ` is a constant times `r log r` in dimension two and a constant
times `r` in higher dimensions (`tendsto_radialJacobian_mul_fundamentalSolution`).

These are the two limits as `ε → 0` that take Green's formula (24) on `U - B(x, ε)` to the
representation formula (25) in Evans's §2.2.4(a). Evans bounds the term with `∂u/∂ν` by `C ε^(n-1)`
times the maximum of `|Φ|` on the sphere, and takes the flux limit from the proof of §2.2.1,
Theorem 1. The kernel is logarithmic in dimension two and Newtonian in dimension at least three.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), (24)-(25), pp. 33-34.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PotentialTheory

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology Gradient

variable {n : ℕ} [Fact (0 < n)]

/-- The gradient of the kernel has the normalized outward normal
component on every sphere about the pole. -/
theorem inner_gradient_fundamentalSolution_smul
    (hn : 2 ≤ n) (ω : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 < r) :
    inner ℝ (∇ (fundamentalSolution n) (r • (ω : ℝ^n))) (ω : ℝ^n) =
      -1 / (r ^ (n - 1) * unitSphereArea n) := by
  have hω : (ω : ℝ^n) ≠ 0 := by
    have := mem_sphere_zero_iff_norm.mp ω.property
    exact norm_ne_zero_iff.mp (by simp [this])
  have hd := (contDiffAt_fundamentalSolution n _ (smul_ne_zero hr.ne' hω)).differentiableAt
    (by simp)
  have hpath := (hasDerivAt_id r).smul_const (ω : ℝ^n)
  have hchain := hd.hasFDerivAt.comp_hasDerivAt r hpath
  simp only [one_smul] at hchain
  rw [inner_gradient_left, ← hchain.deriv]
  exact deriv_fundamentalSolution_smul hn ω hr

/-- The weighted outward pole flux through a sphere equals minus the spherical mean. -/
theorem integral_mul_normal_gradient_fundamentalSolution
    (hn : 2 ≤ n) (u : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    |r| ^ (n - 1) * (∫ ω,
      u (x + r • (ω : ℝ^n)) *
        inner ℝ (∇ (fundamentalSolution n) (r • (ω : ℝ^n))) (ω : ℝ^n)
          ∂(volume : Measure (ℝ^n)).toSphere) =
      -unitSphereAverage n u x r := by
  simp_rw [inner_gradient_fundamentalSolution_smul hn _ hr]
  rw [integral_mul_const, abs_of_pos hr]
  unfold unitSphereAverage
  field_simp [hr.ne', ne_of_gt (unitSphereArea_pos (n := n))]

/-- The weighted outward pole flux tends to minus the center value under
only local continuity of the weight. -/
theorem tendsto_integral_mul_normal_gradient_fundamentalSolution
    (hn : 2 ≤ n) {u : ℝ^n → ℝ} {x : ℝ^n} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (Metric.closedBall x R)) :
    Tendsto (fun r : ℝ ↦ |r| ^ (n - 1) * (∫ ω,
      u (x + r • (ω : ℝ^n)) *
        inner ℝ (∇ (fundamentalSolution n) (r • (ω : ℝ^n))) (ω : ℝ^n)
          ∂(volume : Measure (ℝ^n)).toSphere)) (𝓝[>] 0) (𝓝 (-u x)) := by
  have ht := (tendsto_unitSphereAverage_of_continuousOn hR hu).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply Tendsto.congr' _ ht.neg
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (integral_mul_normal_gradient_fundamentalSolution hn u x hr).symm

/-- Multiplication by the sphere's radial Jacobian removes the kernel's
singularity in the limit at zero, including the logarithmic case. -/
theorem tendsto_radialJacobian_mul_fundamentalSolution
    (hn : 2 ≤ n) (ω : Metric.sphere (0 : ℝ^n) 1) :
    Tendsto (fun r : ℝ ↦ r ^ (n - 1) * fundamentalSolution n (r • (ω : ℝ^n)))
      (𝓝[>] 0) (𝓝 0) := by
  have hω : ‖(ω : ℝ^n)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  by_cases h2 : n = 2
  · subst n
    have ht := (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).const_mul
      (-(1 / (2 * Real.pi)))
    simp only [Real.rpow_one, mul_zero] at ht
    apply Tendsto.congr' _ ht
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [fundamentalSolution_two]
    simp only [Nat.reduceSub, pow_one, norm_smul, Real.norm_eq_abs,
      hω, mul_one, abs_of_pos hr]
    ring
  · have hn3 : 3 ≤ n := by omega
    have ha : unitSphereArea n ≠ 0 := ne_of_gt unitSphereArea_pos
    have hc : (n : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      linarith
    have ht : Tendsto (fun r : ℝ ↦ r / (((n : ℝ) - 2) * unitSphereArea n))
        (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hid.div_const
        (((n : ℝ) - 2) * unitSphereArea n)
    apply Tendsto.congr' _ ht
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [fundamentalSolution_of_three_le hn3]
    have hp : r ^ (n - 1) = r ^ (n - 2) * r := by
      rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
    simp only [norm_smul, Real.norm_eq_abs, hω, mul_one, abs_of_pos hr, hp]
    rw [show ((n : ℝ) - 2) * (n : ℝ) * unitBallVolume n =
      ((n : ℝ) - 2) * unitSphereArea n by rw [unitSphereArea_eq]; ring]
    field_simp [hc, ha, hr.ne']

/-- The kernel times a locally continuous normal field contributes no pole mass.
The field may be the gradient of either factor in Green's second identity. -/
theorem tendsto_integral_fundamentalSolution_mul_normal
    (hn : 2 ≤ n) {F : ℝ^n → ℝ^n} {x : ℝ^n} {R : ℝ} (hR : 0 < R)
    (hF : ContinuousOn F (Metric.closedBall x R)) :
    Tendsto (fun r : ℝ ↦ |r| ^ (n - 1) * (∫ ω,
      fundamentalSolution n (r • (ω : ℝ^n)) *
        inner ℝ (F (x + r • (ω : ℝ^n))) (ω : ℝ^n)
          ∂(volume : Measure (ℝ^n)).toSphere)) (𝓝[>] 0) (𝓝 0) := by
  have : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa using (Fact.out : 0 < n))
  obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (E := ℝ^n)).mpr zero_le_one
  let ω₀ : Metric.sphere (0 : ℝ^n) 1 := ⟨w, hw⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn hF
  have hrad (r : ℝ) (ω : Metric.sphere (0 : ℝ^n) 1) :
      fundamentalSolution n (r • (ω : ℝ^n)) =
        fundamentalSolution n (r • (ω₀ : ℝ^n)) := by
    apply fundamentalSolution_eq_of_norm_eq
    simp only [norm_smul, mem_sphere_zero_iff_norm.mp ω.property,
      mem_sphere_zero_iff_norm.mp ω₀.property]
  have ht := (tendsto_radialJacobian_mul_fundamentalSolution hn ω₀).norm.const_mul
    (C * unitSphereArea n)
  simp only [norm_zero, mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [self_mem_nhdsWithin,
    (show Set.Iio R ∈ 𝓝[>] (0 : ℝ) from nhdsWithin_le_nhds (Iio_mem_nhds hR))]
      with r hr hrR
  have hb (ω : Metric.sphere (0 : ℝ^n) 1) :
      ‖inner ℝ (F (x + r • (ω : ℝ^n))) (ω : ℝ^n)‖ ≤ C := by
    calc
      _ ≤ ‖F (x + r • (ω : ℝ^n))‖ * ‖(ω : ℝ^n)‖ := norm_inner_le_norm _ _
      _ = ‖F (x + r • (ω : ℝ^n))‖ := by
        rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one]
      _ ≤ C := hC _ (by
        rw [Metric.mem_closedBall]
        simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp ω.property,
          abs_of_pos hr] using hrR.le)
  simp_rw [hrad r]
  rw [integral_const_mul, abs_of_pos hr, ← mul_assoc, norm_mul]
  calc
    _ ≤ ‖r ^ (n - 1) * fundamentalSolution n (r • (ω₀ : ℝ^n))‖ *
        (C * unitSphereArea n) := by
      gcongr
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)
    _ = _ := mul_comm _ _

end PotentialTheory
