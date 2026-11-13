/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
public import PDE.Common.Euclidean.CoordinateReflection
public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic

/-!
# Fundamental solution of the Laplacian

The fundamental solution of Laplace's equation on `ℝ^n`, normalized so that `-Δ Φ = δ₀`:

* `n = 1`: `Φ(x) = -|x| / 2`;
* `n = 2`: `Φ(x) = -(1 / 2π) log |x|`;
* `n ≥ 3`: `Φ(x) = 1 / ((n - 2) n α(n) |x|^{n-2})`, where `α(n) = unitBallVolume n`.

For `n ≥ 2` these are the constants of Evans's definition (6) in §2.2.1. The one-dimensional
kernel, which Evans does not list, is the corresponding fundamental solution of `-d²/dx²`. All
three are radial functions of `|x|`, harmonic away from the origin. We prove smoothness of `Φ` on
`ℝ^n \ {0}` and `Δ Φ = 0` there. For `n = 1, 2` the Euclidean Laplacian of a radial function is
reduced to the radial expression `f'' + (n - 1) f' / r` (`EuclideanLaplacian.laplacian_radial`),
and in the planar case SymLean's `cas` tactic computes the second derivative of the logarithm.
For `n ≥ 3` we use the Laplacian of a negative power of the distance
(`EuclideanLaplacian.laplacian_inv_dist_pow`).

The distributional identity `-Δ Φ = δ₀`, which makes `Φ` a fundamental solution, is proved in
`PDE.Elliptic.PotentialTheory.OneDimensional.FundamentalSolution` (`n = 1`),
`PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarDistribution` (`n = 2`), and
`PDE.Elliptic.PotentialTheory.FundamentalSolution.NewtonianDistribution` (`n ≥ 3`). Local
integrability of `Φ` near the pole and the regular distribution it defines are in the modules
under `PDE.Elliptic.PotentialTheory.FundamentalSolution`.

## Main results

* `fundamentalSolution`: the kernel, as a total function with `Φ(0) := 0`.
* `fundamentalSolution_one`, `fundamentalSolution_two`, `fundamentalSolution_of_three_le`: the
  explicit branch formulas.
* `fundamentalSolution_eq_of_norm_eq`, `fundamentalSolution_neg`,
  `fundamentalSolution_coordinateReflection`: radial symmetry and its consequences.
* `contDiffAt_fundamentalSolution`: `Φ` is `C^∞` at every `x ≠ 0` (for `0 < n`).
* `laplacian_fundamentalSolution_eq_zero`: `Δ Φ(x) = 0` for `x ≠ 0` (for `0 < n`).

## Implementation notes

`fundamentalSolution` is total: it returns `0` at the pole and for `n = 0`. Distributional
statements never evaluate it at the pole (a single point is Lebesgue-null), and the
fundamental-solution theorems carry a `Fact (0 < n)` hypothesis. In
`fundamentalSolution_of_three_le` the formula also happens to hold at `x = 0`, because Lean's
`1 / 0 = 0` agrees with the pole convention; no analytic meaning is attached to that
coincidence.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), the radial Laplacian and equation (5), pp. 21-22,
  and the definition (6) of the fundamental solution, p. 22; §2.2.1(b), harmonicity of `Φ` off the
  origin, p. 22, and the interpretation `-ΔΦ = δ₀`, p. 25.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace PotentialTheory

open Filter Topology
open PDE.Analysis

/-- Poisson-normalized fundamental-solution kernel for the convention `-Δ Φ = δ₀`.

The value at `0` is set to `0` to make a total Lean function; distributional statements ignore
that point through local integrability/test-function identities. The definition is also total at
`n = 0`, where it returns `0`; the fundamental-solution theorems assume `0 < n`. -/
noncomputable def fundamentalSolution (n : ℕ) (x : ℝ^n) : ℝ :=
  if _h : x = 0 then 0
  else
    let norm := ‖x‖  -- Euclidean norm
    if n = 1 then
      -norm / 2
    else if n = 2 then
      -(1 / (2 * Real.pi)) * Real.log norm
    else if 3 ≤ n then
      1 / (((n : ℝ) - 2) * (n : ℝ) * unitBallVolume n * norm ^ (n - 2))
    else
      0

/-- The chosen total representative vanishes at its pole. -/
@[simp]
theorem fundamentalSolution_zero (n : ℕ) :
    fundamentalSolution n (0 : ℝ^n) = 0 := by
  simp [fundamentalSolution]

/-- The one-dimensional branch of the canonical kernel. -/
theorem fundamentalSolution_one (x : ℝ^1) :
    fundamentalSolution 1 x = -‖x‖ / 2 := by
  by_cases hx : x = 0
  · subst x
    simp
  · simp [fundamentalSolution, hx]

/-- The planar logarithmic branch of the canonical kernel. -/
theorem fundamentalSolution_two (x : ℝ^2) :
    fundamentalSolution 2 x =
      -(1 / (2 * Real.pi)) * Real.log ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  · simp [fundamentalSolution, hx]

/-- The Newtonian branch of the canonical kernel in dimensions at least three.

The identity also covers `x = 0`, where both sides are `0` by the pole
convention and Lean's `1 / 0 = 0`; the singular formula is meaningful only
for `x ≠ 0`. -/
theorem fundamentalSolution_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (x : ℝ^n) :
    fundamentalSolution n x =
      1 / (((n : ℝ) - 2) * (n : ℝ) * unitBallVolume n * ‖x‖ ^ (n - 2)) := by
  by_cases hx : x = 0
  · subst x
    have hpow : n - 2 ≠ 0 := by omega
    simp [hpow]
  · have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    simp [fundamentalSolution, hx, h1, h2, hn]

/-- The fundamental solution depends only on the Euclidean norm. -/
theorem fundamentalSolution_eq_of_norm_eq
    {n : ℕ} {x y : ℝ^n} (hxy : ‖x‖ = ‖y‖) :
    fundamentalSolution n x = fundamentalSolution n y := by
  have hzero : x = 0 ↔ y = 0 := by
    constructor
    · intro hx
      apply norm_eq_zero.mp
      rw [← hxy, hx, norm_zero]
    · intro hy
      apply norm_eq_zero.mp
      rw [hxy, hy, norm_zero]
  unfold fundamentalSolution
  by_cases hx : x = 0
  · simp [hx, hzero.mp hx]
  · have hy : y ≠ 0 := fun hy ↦ hx (hzero.mpr hy)
    simp [hx, hy, hxy]

/-- The fundamental solution is an even function. -/
@[simp]
theorem fundamentalSolution_neg (n : ℕ) (x : ℝ^n) :
    fundamentalSolution n (-x) = fundamentalSolution n x := by
  exact fundamentalSolution_eq_of_norm_eq (norm_neg x)

/-- The fundamental solution is invariant under reflection in any coordinate
hyperplane. -/
theorem fundamentalSolution_coordinateReflection
    {n : ℕ} (i : Fin n) (x : ℝ^n) :
    fundamentalSolution n (PDE.Common.coordinateReflection i x) =
      fundamentalSolution n x := by
  exact fundamentalSolution_eq_of_norm_eq
    (PDE.Common.norm_coordinateReflection i x)

/-- The fundamental solution is smooth away from its pole. -/
theorem contDiffAt_fundamentalSolution (n : ℕ)
    (x : ℝ^n) (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fundamentalSolution n) x := by
  let g := fun (y : ℝ^n) ↦
    let norm := ‖y‖
    if n = 1 then -norm / 2
    else if n = 2 then -(1 / (2 * Real.pi)) * Real.log norm
    else if 3 ≤ n then 1 / (((n : ℝ) - 2) * (n : ℝ) * unitBallVolume n * norm ^ (n - 2))
    else 0
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ^n ↦ ‖y‖) x :=
    ContDiffAt.norm (𝕜 := ℝ) contDiffAt_id hx
  have hpos := norm_pos_iff.2 hx
  apply ContDiffAt.congr_of_eventuallyEq (f := g)
  · dsimp [g]
    split_ifs with h1 h2 h3
    · fun_prop
    · exact contDiffAt_const.mul (hnorm.log hpos.ne')
    · have : (3 : ℝ) ≤ n := by exact_mod_cast h3
      exact contDiffAt_const.div (contDiffAt_const.mul (hnorm.pow _)) (mul_pos (mul_pos
        (mul_pos (by linarith) (by linarith)) (unitBallVolume_pos n)) (pow_pos hpos _)).ne'
    · exact contDiffAt_const
  · filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    unfold fundamentalSolution
    rw [dite_eq_right hy]


/-- The logarithmic branch of the canonical kernel is harmonic off its pole. -/
private theorem laplacian_fundamentalSolution_two
    (x : ℝ^2) (hx : x ≠ 0) :
    laplacian (fundamentalSolution 2) x = 0 := by
  let c : ℝ := -(1 / (2 * Real.pi))
  let f : ℝ → ℝ := fun r ↦ c * Real.log r
  have hlocal : fundamentalSolution 2 =ᶠ[nhds x] f ∘ norm := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simp [fundamentalSolution, f, c, hy]
  rw [EuclideanLaplacian.laplacian_congr_nhds hlocal]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hf : ContDiffAt ℝ 2 f ‖x‖ := contDiffAt_const.mul (contDiffAt_id.log hr)
  have hderiv : deriv f = fun r ↦ c * r⁻¹ := by
    funext r
    simp [f, Real.deriv_log, deriv_const_mul_field]
  have hsecond : deriv (deriv f) ‖x‖ = c * (-(‖x‖ ^ 2)⁻¹) := by cas
  have hrad : laplacian (f ∘ norm) x = deriv (deriv f) ‖x‖ + ((2 : ℝ) - 1) / ‖x‖ * deriv f ‖x‖ :=
    EuclideanLaplacian.laplacian_radial (n := 2) f x hx hf
  rw [hrad, hsecond, hderiv]
  field_simp
  ring

/-- The Newtonian kernel is harmonic away from the origin in dimensions at least three. -/
private theorem laplacian_fundamentalSolution_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (x : ℝ^n) (hx : x ≠ 0) :
    laplacian (fundamentalSolution n) x = 0 := by
  have hkernel : fundamentalSolution n = fun y : ℝ^n ↦
      (1 / (((n : ℝ) - 2) * n * unitBallVolume n)) * (dist y 0 ^ (n - 2))⁻¹ := by
    funext y
    rw [fundamentalSolution_of_three_le hn, dist_zero_right]
    simp only [one_div, mul_inv_rev]
    ring
  rw [hkernel, PDE.laplacian_const_smul,
    EuclideanLaplacian.laplacian_inv_dist_pow hx]
  simp [show n - 2 + 2 = n by omega]

/-- The fundamental solution has zero Euclidean Laplacian away from its pole. -/
theorem laplacian_fundamentalSolution_eq_zero (n : ℕ) [Fact (0 < n)]
    (x : ℝ^n) (hx : x ≠ 0) :
    laplacian (fundamentalSolution n) x = 0 := by
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by have := Fact.out (p := 0 < n); omega) with h | h | h
  · subst n
    let f : ℝ → ℝ := fun r ↦ -r / 2
    have hkernel : fundamentalSolution 1 = f ∘ norm := by
      funext y
      exact fundamentalSolution_one y
    have hf : ContDiffAt ℝ 2 f ‖x‖ := by dsimp [f]; fun_prop
    rw [hkernel, EuclideanLaplacian.laplacian_radial f x hx hf]
    have hderiv : deriv f = fun _ : ℝ ↦ (-(1 : ℝ) / 2) := by
      funext r
      simp [f]
    simp [PDE.CoordinateSystems.radialLaplacian, hderiv]
  · subst n
    exact laplacian_fundamentalSolution_two x hx
  · exact laplacian_fundamentalSolution_of_three_le h x hx

end PotentialTheory
