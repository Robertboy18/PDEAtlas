/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Finite propagation for the one-dimensional Hopf–Lax formula

For Lipschitz initial data, every minimizing footpoint in the Hopf–Lax
formula lies in an explicit ball around the observation point. Consequently,
the value at `(t, x)` depends only on the initial datum inside that ball.
More quantitatively, a uniform perturbation on the ball produces no larger
perturbation of the Hopf–Lax value.

The argument uses the coercive lower bound for the Hopf–Lax integrand and
comparison with the zero-displacement competitor. This localization of minimizing footpoints
gives finite speed of propagation for Lipschitz data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4, formula (21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

/-- An explicit radius containing every Hopf–Lax minimizing footpoint for
`K`-Lipschitz initial data at time `t`.

The outer maximum makes the radius nonnegative without adding a redundant
sign hypothesis to later closed-ball statements. -/
def propagationRadius (H : ℝ → ℝ) (K : NNReal) (t : ℝ) : ℝ :=
  max 0
    (t *
      (max (H ((K : ℝ) + 1)) (H (-((K : ℝ) + 1))) +
        legendreTransform H 0))

/-- The propagation radius is nonnegative at every time. -/
theorem propagationRadius_nonneg (H : ℝ → ℝ) (K : NNReal) (t : ℝ) :
    0 ≤ propagationRadius H K t :=
  le_max_left _ _

/-- The propagation radius is monotone on nonnegative times. -/
theorem propagationRadius_mono (H : ℝ → ℝ) (K : NNReal) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    propagationRadius H K s ≤ propagationRadius H K t := by
  let c := max (H ((K : ℝ) + 1)) (H (-((K : ℝ) + 1))) + legendreTransform H 0
  change max 0 (s * c) ≤ max 0 (t * c)
  refine max_le (le_max_left _ _) ?_
  rcases le_total 0 c with hc | hc
  · exact (mul_le_mul_of_nonneg_right hst hc).trans (le_max_right _ _)
  · exact (mul_nonpos_of_nonneg_of_nonpos hs hc).trans (le_max_left _ _)

/-- Every global minimizer of the Hopf–Lax integrand lies within the explicit
propagation radius. -/
theorem dist_le_propagationRadius_of_isMinOn_hopfLaxIntegrand {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) {t x y : ℝ} (ht : 0 < t)
    (hy : IsMinOn (hopfLaxIntegrand H φ t x) Set.univ y) :
    dist x y ≤ propagationRadius H K t := by
  have hlow := hopfLaxIntegrand_lower_bound_of_lipschitz (x := x) (y := y) hFin hφ ht
  have hyx : hopfLaxIntegrand H φ t x y ≤ hopfLaxIntegrand H φ t x x := hy (Set.mem_univ x)
  simp only [hopfLaxIntegrand, sub_self, zero_div] at hlow hyx
  exact le_max_of_le_right (by linarith)

/-- The Hopf–Lax infimum is attained by a footpoint inside the explicit
propagation ball. -/
theorem exists_hopfLax_eq_integrand_and_dist_le {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃ y : ℝ, hopfLax H φ t x = hopfLaxIntegrand H φ t x y ∧ dist x y ≤ propagationRadius H K t := by
  obtain ⟨y, hyMin, hyValue⟩ := exists_isMinOn_hopfLaxIntegrand_of_lipschitz (x := x) hFin hφ ht
  exact ⟨y, hyValue, dist_le_propagationRadius_of_isMinOn_hopfLaxIntegrand hFin hφ ht hyMin⟩

/-- Localized nonexpansivity of the Hopf–Lax formula: a uniform distance
bound on the common propagation ball controls the distance between the two
values at `(t, x)`. Both data must have the stated global Lipschitz bound;
their values need only be compared inside the ball. -/
theorem dist_hopfLax_le_of_dist_le_on_closedBall {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) (hψ : LipschitzWith K ψ) {t x C : ℝ} (ht : 0 < t)
    (hDist : ∀ y ∈ Metric.closedBall x (propagationRadius H K t), dist (φ y) (ψ y) ≤ C) :
    dist (hopfLax H φ t x) (hopfLax H ψ t x) ≤ C := by
  have key (f g : ℝ → ℝ) (hf : LipschitzWith K f) (hg : LipschitzWith K g)
      (hD : ∀ y ∈ Metric.closedBall x (propagationRadius H K t), |f y - g y| ≤ C) :
      hopfLax H f t x ≤ hopfLax H g t x + C := by
    obtain ⟨y, hy, hyd⟩ := exists_hopfLax_eq_integrand_and_dist_le (x := x) hFin hg ht
    have hle := hopfLax_le_integrand (y := y) (hopfLaxBddBelow_of_lipschitz (x := x) hFin hf ht)
    have hA := hD y (by simpa only [Metric.mem_closedBall, dist_comm] using hyd)
    rw [hy]
    unfold hopfLaxIntegrand at hle ⊢
    linarith [le_abs_self (f y - g y)]
  have h1 := key φ ψ hφ hψ fun y hy ↦ by simpa only [Real.dist_eq] using hDist y hy
  have h2 := key ψ φ hψ hφ fun y hy ↦ by
    simpa only [Real.dist_eq] using (dist_comm (ψ y) (φ y)).trans_le (hDist y hy)
  rw [Real.dist_eq]
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- Finite domain of dependence for the Hopf–Lax formula: two
`K`-Lipschitz initial data that agree on the propagation ball give the same
value at `(t, x)`. -/
theorem hopfLax_eq_of_eqOn_closedBall {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) (hψ : LipschitzWith K ψ) {t x : ℝ} (ht : 0 < t)
    (hEq : Set.EqOn φ ψ (Metric.closedBall x (propagationRadius H K t))) :
    hopfLax H φ t x = hopfLax H ψ t x :=
  dist_le_zero.mp (dist_hopfLax_le_of_dist_le_on_closedBall hFin hφ hψ ht fun y hy ↦ by
    simp [hEq hy])

/-- Localized stability on a finite spacetime cylinder.

If two `K`-Lipschitz initial data are uniformly within `C` on the ball
obtained by enlarging `B(center, R)` by the propagation radius at time `T`,
then their Hopf–Lax evolutions are uniformly within `C` on
`(0, T] × B(center, R)`. -/
theorem dist_hopfLax_le_on_closedBall_of_dist_le_on_expanded_closedBall {H φ ψ : ℝ → ℝ}
    (hFin : LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) (hψ : LipschitzWith K ψ)
    {T center R C : ℝ}
    (hDist : ∀ y ∈ Metric.closedBall center (R + propagationRadius H K T), dist (φ y) (ψ y) ≤ C) :
    ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ Metric.closedBall center R, dist (hopfLax H φ t x) (hopfLax H ψ t x) ≤
      C := by
  intro t ht x hx
  refine dist_hopfLax_le_of_dist_le_on_closedBall hFin hφ hψ ht.1 fun y hy ↦ hDist y ?_
  rw [Metric.mem_closedBall] at hx hy ⊢
  linarith [dist_triangle y x center, propagationRadius_mono H K ht.1.le ht.2]

/-- Finite domain of dependence on a spacetime cylinder.

Agreement of the initial data on the ball
`B(center, R + propagationRadius H K T)` implies agreement of the
Hopf–Lax evolutions on `(0, T] × B(center, R)`. -/
theorem hopfLax_eqOn_closedBall_of_eqOn_expanded_closedBall {H φ ψ : ℝ → ℝ}
    (hFin : LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) (hψ : LipschitzWith K ψ)
    {T center R : ℝ} (hEq : Set.EqOn φ ψ (Metric.closedBall center (R + propagationRadius H K T))) :
    ∀ t ∈ Set.Ioc 0 T, Set.EqOn (hopfLax H φ t) (hopfLax H ψ t) (Metric.closedBall center R) :=
  fun t ht x hx ↦ dist_le_zero.mp
    (dist_hopfLax_le_on_closedBall_of_dist_le_on_expanded_closedBall hFin hφ hψ
      (fun y hy ↦ by simp [hEq hy]) t ht x hx)

end

end HopfLax1D
