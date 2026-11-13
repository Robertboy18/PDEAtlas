/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Definitions
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenKernel -- shake: keep
import CAS.ExactTactic

/-!
# Integrability of the half-space Poisson kernel

For `x` in the upper half-space and `y = (y', 0)` on the boundary hyperplane,
`‖x - y‖² = ‖x' - y'‖² + xₙ²`, so the inverse power `‖x - y‖⁻ⁿ` is integrable in `y' ∈ ℝ^(n-1)`: the
exponent `n` exceeds the boundary dimension `n - 1`. We prove that integrability and use
it to control the Poisson integrand for bounded measurable boundary data.

The comparison is with the translated Japanese-bracket weight `(1 + ‖y' - x'‖)⁻ⁿ`, whose
integrability on `ℝ^(n-1)` is Mathlib's `integrable_one_add_norm` (valid for exponents larger than
the dimension). Since both the height `xₙ` and the tangential displacement `‖x' - y'‖` are bounded
by `‖x - y‖`, one has `1 + ‖x' - y'‖ ≤ (1 + xₙ⁻¹) ‖x - y‖`, which gives a single global bound with
no compact-part/tail decomposition.

## Main results

* `integrable_inv_distance_pow`: for `x ∈ ℝ^n₊`, `y' ↦ ‖x - (y', 0)‖⁻ⁿ` is integrable on `ℝ^(n-1)`.
* `integrable_inv_distance_pow_of_le`: the same for every exponent `m ≥ n`, using the lower bound
  `xₙ ≤ ‖x - y‖`.
* `halfSpace_ne_halfSpaceEmb`: an interior point never coincides with a boundary point.
* `integrable_halfSpace_integrand_of_bounded`: for measurable `g` bounded on the boundary and
  `x ∈ ℝ^n₊`, the Poisson integrand `y' ↦ g(y', 0) / ‖x - (y', 0)‖ⁿ` is integrable.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), Poisson's kernel `K` and Poisson's formula (33),
  p. 37, and steps 2-3 of the proof of Theorem 14 (Poisson's formula for half-space), pp. 38-39.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open LaplacianEquation
open PotentialTheory
open MeasureTheory
open Set

section PoissonHalfSpaceIntegrability

open MeasureTheory Filter Topology
open scoped BigOperators
open scoped InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

private theorem integrable_inv_one_add_norm_pow :
    Integrable (fun y : ℝ^(n - 1) ↦ ((1 + ‖y‖) ^ n)⁻¹) (volume : Measure ℝ^(n - 1)) := by
  classical
  -- Use `integrable_one_add_norm` and rewrite the `rpow` as an inverse `Nat` power.
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Fact.out : 0 < n)
  have hdim : (Module.finrank ℝ ℝ^(n - 1) : ℝ) < (n : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pred_lt hn0)
    -- `simp` computes `Module.finrank ℝ ℝ^(n - 1) = n-1`.
    simpa using this
  have hint :
      Integrable (fun y : ℝ^(n - 1) ↦ (1 + ‖y‖) ^ (-(n : ℝ))) (volume : Measure ℝ^(n - 1)) := by
    -- Avoid named arguments (`μ :=`) so the term parses the same way under local notation.
    simpa using
      (@integrable_one_add_norm ℝ^(n - 1) _ _ _ _ _ (volume : Measure ℝ^(n - 1)) _ (n : ℝ) hdim)
  -- Rewrite `(1+‖y‖) ^ (-(n:ℝ))` as `((1+‖y‖)^n)⁻¹`.
  have hEq : (fun y : ℝ^(n - 1) ↦ (1 + ‖y‖) ^ (-(n : ℝ))) =
      fun y : ℝ^(n - 1) ↦ ((1 + ‖y‖) ^ n)⁻¹ := by
    cas
  simpa [hEq] using hint

private theorem integrable_inv_one_add_norm_sub_pow (a : ℝ^(n - 1)) :
    Integrable (fun y : ℝ^(n - 1) ↦ ((1 + ‖y - a‖) ^ n)⁻¹)
      (volume : Measure ℝ^(n - 1)) := by
  have h :=
    (measurePreserving_add_left (volume : Measure ℝ^(n - 1)) (-a)).integrable_comp_of_integrable
      (integrable_inv_one_add_norm_pow (n := n))
  simpa [Function.comp_def, sub_eq_add_neg, add_comm] using h

/-- The inverse `n`th power of the distance from an interior point to the boundary is integrable.

The height and tangential displacement are both bounded by the full distance. This gives a global
comparison with a translated Japanese-bracket weight, avoiding a compact-part/tail decomposition.
-/
theorem integrable_inv_distance_pow
    (x : ℝ^n) (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    Integrable (fun y : ℝ^(n - 1) ↦ (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹)
      (volume : Measure ℝ^(n - 1)) := by
  classical
  let t : ℝ := x PDE.Common.lastIndex
  let a : ℝ^(n - 1) := halfSpaceProj (n := n) x
  have ht : 0 < t := by simpa [t, SobolevSpace.HalfSpace.upper] using hx
  refine ((integrable_inv_one_add_norm_sub_pow (n := n) a).const_mul ((1 + t⁻¹) ^ n)).mono'
    ((continuous_const.dist (continuous_halfSpaceEmb (n := n))).measurable.pow_const
      n).inv.aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
  change ‖(dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹‖ ≤ (1 + t⁻¹) ^ n * ((1 + ‖y - a‖) ^ n)⁻¹
  have htd : t ≤ dist x (halfSpaceEmb (n := n) y) :=
    lastCoord_le_distance_halfSpaceEmb (n := n) x hx y
  have hrd : ‖y - a‖ ≤ dist x (halfSpaceEmb (n := n) y) :=
    norm_sub_halfSpaceProj_le_distance (n := n) x y
  have hd : 0 < dist x (halfSpaceEmb (n := n) y) := ht.trans_le htd
  have hone : 1 ≤ t⁻¹ * dist x (halfSpaceEmb (n := n) y) := by
    rw [← div_eq_inv_mul, one_le_div ht]
    exact htd
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (pow_pos hd n)), ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (pow_pos hd n) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith) n

/-!
### Integrability of the Poisson integrand with bounded boundary data
-/

/-- An interior point cannot equal a point in the boundary parametrization. -/
theorem halfSpace_ne_halfSpaceEmb {x : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) (y : ℝ^(n - 1)) :
    x ≠ halfSpaceEmb (n := n) y := by
  have hxpos : 0 < x PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx
  intro hxy
  linarith [show x PDE.Common.lastIndex = 0 by simpa [hxy] using lastCoord_halfSpaceEmb (n := n) y]

/-- Bounded measurable boundary data gives an integrable half-space Poisson integrand. -/
theorem integrable_halfSpace_integrand_of_bounded {g : ℝ^n → ℝ} (hg : Measurable g)
    (hg_bounded : ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (x : ℝ^n) (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    Integrable
        (fun y : ℝ^(n - 1) ↦ g (halfSpaceEmb (n := n) y) / dist x (halfSpaceEmb (n := n) y) ^ n)
        (volume : Measure ℝ^(n - 1)) := by
  rcases hg_bounded with ⟨M, hM⟩
  refine ((integrable_inv_distance_pow (n := n) x hx).const_mul M).mono'
    ((hg.comp (measurable_halfSpaceEmb (n := n))).div ((continuous_const.dist
      (continuous_halfSpaceEmb (n := n))).measurable.pow_const n)).aestronglyMeasurable
    (ae_of_all _ fun y ↦ ?_)
  change ‖g (halfSpaceEmb (n := n) y) / dist x (halfSpaceEmb (n := n) y) ^ n‖ ≤
    M * (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹
  rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_dist, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hM _ (halfSpaceEmb_mem_boundary (n := n) y)) (by positivity)

/-!
Higher powers are also integrable, by reduction to the `n`-th power with the uniform lower
bound `xₙ ≤ ‖x - y‖`.
-/

/-- Every higher inverse distance power is integrable at a fixed interior point. -/
theorem integrable_inv_distance_pow_of_le
    (x : ℝ^n) (hx : x ∈ SobolevSpace.HalfSpace.upper n)
    {m : ℕ} (hm : n ≤ m) :
    Integrable (fun y : ℝ^(n - 1) ↦ (dist x (halfSpaceEmb (n := n) y) ^ m)⁻¹)
      (volume : Measure ℝ^(n - 1)) := by
  have hxpos : 0 < x PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ((integrable_inv_distance_pow (n := n) x hx).const_mul
    (x PDE.Common.lastIndex ^ k)⁻¹).mono'
    ((continuous_const.dist (continuous_halfSpaceEmb (n := n))).measurable.pow_const
      _).inv.aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
  change ‖(dist x (halfSpaceEmb (n := n) y) ^ (n + k))⁻¹‖ ≤
    (x PDE.Common.lastIndex ^ k)⁻¹ * (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹
  have hd := lastCoord_le_distance_halfSpaceEmb (n := n) x hx y
  have hdpos := hxpos.trans_le hd
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (pow_pos hdpos _)), pow_add, mul_inv,
    mul_comm (_ ^ n)⁻¹]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (pow_pos hxpos k) (pow_le_pow_left₀ hxpos.le hd k))
    (by positivity)

end PoissonHalfSpaceIntegrability

end GreenFunction
