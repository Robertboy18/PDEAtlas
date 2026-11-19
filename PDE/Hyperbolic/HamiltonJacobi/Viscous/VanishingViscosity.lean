/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscous.UniformLaplace
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Viscosity
import PDE.Parabolic.Heat.ConvolutionSpace.Scaling

/-!
# Uniform vanishing viscosity for the quadratic Hamiltonian

For bounded uniformly continuous data on `ℝ^n`, the Cole–Hopf Cauchy solutions
converge to the quadratic Hopf–Lax value, uniformly over all space and every finite
closed time slab. The viscosity tends to zero through positive real values.

At positive time, parabolic rescaling reduces the claim to a time-one Laplace
estimate for translated and dilated data. On a fixed slab these data share a bound
and a continuity modulus. Both formulas equal the datum at time zero.

The limit is the viscosity IVP solution constructed by Hopf–Lax, with
Hamiltonian `‖p‖²/2`; comparison identifies it with any other solution in the
class. Tests are locally `C¹`; the solution itself need not be differentiable.

This is the Hamilton–Jacobi counterpart of Example 2 in Evans, §4.5.2, where Laplace's method
takes the viscous Burgers solutions (21), built from the potential formula (9) of §4.4.1(b), to
the Lax–Oleinik formula (26). For the potential the limit is the Hopf–Lax formula, which Evans
identifies with the unique viscosity solution in Theorem 3 of §10.3.4, for bounded Lipschitz
data. His general vanishing viscosity argument in §10.1 extracts a locally uniformly convergent
subsequence (3); with the explicit formulas the whole family converges, uniformly on each slab.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equation (9); §4.5.2, Example 2, equations
  (20)-(26); §10.1, equations (2)-(3); §10.3.4, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi.ColeHopf

open Set Filter
open scoped Topology

variable {n : ℕ}

/-- Scaling space by `r` reduces time `r²` to one in the Cole–Hopf formula.
The heat Jacobian cancels before the logarithm is taken. -/
theorem initialValueSolution_parabolic_rescale {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r)
    (g : ℝ^n → ℝ) (x : ℝ^n) :
    initialValueSolution ν g x (r ^ 2) = initialValueSolution ν (fun y ↦ g (x + r • y)) 0 1 := by
  have hheat := HeatEquation.initialValueSolution_parabolic_rescale
    (fun y ↦ Real.exp (-g y / (2 * ν))) x (r := r) hν hr
  simp only [initialValueSolution, logarithmicTransform, mul_one]
  rw [mul_comm ν (r ^ 2), hheat]

/-- Translations and bounded nonnegative dilations of a uniformly continuous datum
have a common continuity modulus. The translation parameter need not be bounded. -/
private theorem uniformEquicontinuous_rescaled_data {g : ℝ^n → ℝ}
    (hg : UniformContinuous g) (T : ℝ) :
    UniformEquicontinuous
    (fun (a : ℝ^n × Set.Icc (0 : ℝ) T) y ↦ g (a.1 + Real.sqrt (a.2 : ℝ) • y)) := by
  refine Metric.uniformEquicontinuous_iff.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hg ε hε
  have hD : 0 < Real.sqrt T + 1 := by positivity
  refine ⟨δ / (Real.sqrt T + 1), div_pos hδ hD, fun y w hyw a ↦ ?_⟩
  apply hclose
  have hr : Real.sqrt (a.2 : ℝ) ≤ Real.sqrt T := Real.sqrt_le_sqrt a.2.property.2
  have hsmall := (lt_div_iff₀ hD).mp hyw
  have hdist : dist (a.1 + Real.sqrt (a.2 : ℝ) • y) (a.1 + Real.sqrt (a.2 : ℝ) • w) =
        Real.sqrt (a.2 : ℝ) * dist y w := by
    have hsub : (a.1 + Real.sqrt (a.2 : ℝ) • y) - (a.1 + Real.sqrt (a.2 : ℝ) • w) =
          Real.sqrt (a.2 : ℝ) • (y - w) := by
      rw [smul_sub]
      abel
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hdist]
  calc
    _ ≤ (Real.sqrt T + 1) * dist y w :=
      mul_le_mul_of_nonneg_right (by linarith only [hr]) dist_nonneg
    _ < δ := by simpa only [mul_comm] using hsmall

/-- The quadratic viscous Cauchy solutions converge uniformly over every
finite closed time slab to the quadratic Hopf–Lax formula for bounded uniformly
continuous data. The conclusion includes the initial time and all spatial points. -/
theorem tendstoUniformlyOn_initialValueSolution {g : ℝ^n → ℝ}
    (hg : UniformContinuous g) (hgb : Bornology.IsBounded (Set.range g)) (T : ℝ) :
    TendstoUniformlyOn (fun ν (z : ℝ^n × ℝ) ↦ initialValueSolution ν g z.1 z.2)
      (fun z ↦ HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) g z.2 z.1) (𝓝[>] (0 : ℝ))
      (closedTimeSlab T) := by
  obtain ⟨M, hM, hbound⟩ := hgb.exists_pos_norm_le
  have hgb' : ∀ y, |g y| ≤ M := by
    intro y
    simpa only [Real.norm_eq_abs] using hbound (g y) ⟨y, rfl⟩
  let f : (ℝ^n × Set.Icc (0 : ℝ) T) → ℝ^n → ℝ := fun a y ↦ g (a.1 + Real.sqrt (a.2 : ℝ) • y)
  have hequi : UniformEquicontinuous f := uniformEquicontinuous_rescaled_data hg T
  have hfbound : ∀ a y, |f a y| ≤ M := fun a y ↦ hgb' _
  have hfamily := tendstoUniformly_initialValueSolution_one hequi hM.le hfbound
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  filter_upwards [Metric.tendstoUniformly_iff.mp hfamily ε hε, self_mem_nhdsWithin] with ν hν hνpos
  have hνpositive : 0 < ν := hνpos
  intro z hz
  rcases eq_or_lt_of_le hz.1 with ht | ht
  · have htime : z.2 = 0 := ht.symm
    simp only [htime, initialValueSolution_zero hνpositive.ne', HopfLax.value_zero, dist_self]
    exact hε
  · let a : ℝ^n × Set.Icc (0 : ℝ) T := ⟨z.1, ⟨z.2, hz⟩⟩
    have hr : 0 < Real.sqrt z.2 := Real.sqrt_pos.mpr ht
    have htime : (Real.sqrt z.2) ^ 2 = z.2 := Real.sq_sqrt ht.le
    have hU := initialValueSolution_parabolic_rescale hνpositive hr g z.1
    have hV := HopfLax.value_norm_sq_div_two_parabolic_rescale g z.1 hr
    rw [htime] at hU hV
    have hh := hν (a, (0 : ℝ^n))
    change dist (HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2)
        (fun y ↦ g (z.1 + Real.sqrt z.2 • y)) 1 0)
      (initialValueSolution ν (fun y ↦ g (z.1 + Real.sqrt z.2 • y)) 0 1) < ε at hh
    rw [hU, hV]
    exact hh

/-- Comparison identifies the explicit vanishing-viscosity limit with any quadratic
Hamilton–Jacobi IVP solution in the bounded, uniformly continuous slab class.
Existence of that class is supplied by the Hopf–Lax constructor. -/
theorem tendstoUniformlyOn_initialValueSolution_of_isViscosityInitialSolution {g : ℝ^n → ℝ}
    (hg : UniformContinuous g) (hgb : Bornology.IsBounded (Set.range g)) {u : (ℝ^n × ℝ) → ℝ}
    (hu : IsViscosityInitialSolution (fun p _ ↦ ‖p‖ ^ 2 / 2) g u) (T : ℝ) :
    TendstoUniformlyOn (fun ν (z : ℝ^n × ℝ) ↦ initialValueSolution ν g z.1 z.2) u (𝓝[>] (0 : ℝ))
      (closedTimeSlab T) := by
  have hu' : IsViscosityInitialSolution
      (fun p _ ↦ HopfLax.hamiltonian (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) p) g u := by
    simpa only [HopfLax.hamiltonian_norm_sq_div_two] using hu
  have hconv : ConvexOn ℝ univ (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ((convexOn_univ_norm (E := ℝ^n)).pow (fun _ _ ↦ norm_nonneg _) 2).smul
        (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
  have heq := HopfLax.eqOn_value_of_isViscosityInitialSolution
    HopfLax.superlinear_norm_sq_div_two hconv hg hgb hu'
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_initialValueSolution hg hgb T) ε hε] with ν hν
  intro z hz
  rw [heq hz.1]
  exact hν z hz

end HamiltonJacobi.ColeHopf
