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
# Convexity of the one-dimensional Hopf–Lax evolution

We prove convexity properties of the Hopf–Lax minimization problem at
positive time:

* equality with the Hopf–Lax value characterizes global minimizing footpoints;
* a convex initial datum gives a convex footpoint integrand and a convex
  evolved profile;
* a strictly convex initial datum gives a unique minimizing footpoint.

The proof of convexity preservation combines minimizers for two observation
points using the same convex coefficients. Convexity of both the initial
datum and the Legendre transform then bounds the combined competitor. In other words, the
integrand `φ(y) + t L((x - y) / t)` is jointly convex in `(x, y)`, and an infimum over `y` of a
jointly convex function is convex in `x`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4, formula (21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

/-- A footpoint realizes the Hopf–Lax value exactly when it is a global
minimizer of the footpoint integrand. -/
theorem hopfLax_eq_integrand_iff_isMinOn {H φ : ℝ → ℝ} {t x y : ℝ} (hbb : HopfLaxBddBelow H φ t x) :
    hopfLax H φ t x = hopfLaxIntegrand H φ t x y ↔ IsMinOn (hopfLaxIntegrand H φ t x) Set.univ y :=
  ⟨fun hy z _ ↦ by rw [← hy]; exact hopfLax_le_integrand hbb, fun hy ↦ le_antisymm
    (hopfLax_le_integrand hbb)
    (le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun z ↦ hy (Set.mem_univ z)))⟩

/-- Convexity of the Legendre transform along the slope of a convex combination of
observation points and footpoints. -/
private theorem legendreTransform_slope_combo_le {H : ℝ → ℝ} (hFin : LegendreFinite H)
    {t a b x₁ x₂ y₁ y₂ : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    t * legendreTransform H ((a * x₁ + b * x₂ - (a * y₁ + b * y₂)) / t) ≤
      a * (t * legendreTransform H ((x₁ - y₁) / t)) +
        b * (t * legendreTransform H ((x₂ - y₂) / t)) := by
  have h := (convexOn_legendreTransform hFin).2 (Set.mem_univ ((x₁ - y₁) / t))
    (Set.mem_univ ((x₂ - y₂) / t)) ha hb hab
  simp only [smul_eq_mul] at h
  rw [show (a * x₁ + b * x₂ - (a * y₁ + b * y₂)) / t =
    a * ((x₁ - y₁) / t) + b * ((x₂ - y₂) / t) by ring]
  linarith [mul_le_mul_of_nonneg_left h ht.le]

/-- For fixed positive time and observation point, the Hopf–Lax footpoint
integrand is convex whenever the initial datum is convex. -/
theorem convexOn_hopfLaxIntegrand {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hφ : ConvexOn ℝ Set.univ φ) {t x : ℝ} (ht : 0 < t) :
    ConvexOn ℝ Set.univ (hopfLaxIntegrand H φ t x) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab ↦ ?_⟩
  have hφ2 := hφ.2 (Set.mem_univ y₁) (Set.mem_univ y₂) ha hb hab
  have hL := legendreTransform_slope_combo_le hFin (x₁ := x) (x₂ := x) (y₁ := y₁) (y₂ := y₂)
    ht ha hb hab
  rw [show a * x + b * x = x by linear_combination x * hab] at hL
  simp only [hopfLaxIntegrand, smul_eq_mul] at hφ2 ⊢
  linarith

/-- At positive time, Hopf–Lax evolution preserves convexity of a convex
Lipschitz initial datum. -/
theorem convexOn_hopfLax {H φ : ℝ → ℝ} (hFin : LegendreFinite H) (hφConvex : ConvexOn ℝ Set.univ φ)
    {K : NNReal} (hφLipschitz : LipschitzWith K φ) {t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ Set.univ (hopfLax H φ t) := by
  refine ⟨convex_univ, fun x₁ _ x₂ _ a b ha hb hab ↦ ?_⟩
  obtain ⟨y₁, hy₁⟩ := exists_hopfLax_eq_integrand_of_lipschitz (x := x₁) hFin hφLipschitz ht
  obtain ⟨y₂, hy₂⟩ := exists_hopfLax_eq_integrand_of_lipschitz (x := x₂) hFin hφLipschitz ht
  have hupper := hopfLax_le_integrand (y := a * y₁ + b * y₂)
    (hopfLaxBddBelow_of_lipschitz (x := a * x₁ + b * x₂) hFin hφLipschitz ht)
  have hφ2 := hφConvex.2 (Set.mem_univ y₁) (Set.mem_univ y₂) ha hb hab
  have hL := legendreTransform_slope_combo_le hFin (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂)
    ht ha hb hab
  simp only [smul_eq_mul] at hφ2 ⊢
  rw [hy₁, hy₂]
  simp only [hopfLaxIntegrand] at hupper ⊢
  linarith

/-- For fixed positive time and observation point, strict convexity of the
initial datum makes the Hopf–Lax footpoint integrand strictly convex. -/
theorem strictConvexOn_hopfLaxIntegrand_of_strictConvex_phi {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hφ : StrictConvexOn ℝ Set.univ φ) {t x : ℝ} (ht : 0 < t) :
    StrictConvexOn ℝ Set.univ (hopfLaxIntegrand H φ t x) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ hy a b ha hb hab ↦ ?_⟩
  have hφ2 := hφ.2 (Set.mem_univ y₁) (Set.mem_univ y₂) hy ha hb hab
  have hL := legendreTransform_slope_combo_le hFin (x₁ := x) (x₂ := x) (y₁ := y₁) (y₂ := y₂)
    ht ha.le hb.le hab
  rw [show a * x + b * x = x by linear_combination x * hab] at hL
  simp only [hopfLaxIntegrand, smul_eq_mul] at hφ2 ⊢
  linarith

/-- A strictly convex Lipschitz initial datum has a unique minimizing
footpoint in the Hopf–Lax formula at every positive time. -/
theorem existsUnique_isMinOn_hopfLaxIntegrand_of_strictConvex_phi {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) (hφConvex : StrictConvexOn ℝ Set.univ φ) {K : NNReal}
    (hφLipschitz : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃! y : ℝ, IsMinOn (hopfLaxIntegrand H φ t x) Set.univ y := by
  obtain ⟨y, hyMin, _⟩ := exists_isMinOn_hopfLaxIntegrand_of_lipschitz (x := x) hFin hφLipschitz ht
  exact ⟨y, hyMin, fun z hzMin ↦ (strictConvexOn_hopfLaxIntegrand_of_strictConvex_phi hFin
    hφConvex ht).eq_of_isMinOn hzMin hyMin (Set.mem_univ z) (Set.mem_univ y)⟩

/-- Equivalently, a strictly convex Lipschitz initial datum has a unique
footpoint at which the Hopf–Lax infimum is attained. -/
theorem existsUnique_hopfLax_eq_integrand_of_strictConvex_phi {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) (hφConvex : StrictConvexOn ℝ Set.univ φ) {K : NNReal}
    (hφLipschitz : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃! y : ℝ, hopfLax H φ t x = hopfLaxIntegrand H φ t x y := by
  obtain ⟨y, hyMin, hyUnique⟩ :=
    existsUnique_isMinOn_hopfLaxIntegrand_of_strictConvex_phi (x := x) hFin hφConvex hφLipschitz ht
  have hbb := hopfLaxBddBelow_of_lipschitz (x := x) hFin hφLipschitz ht
  exact ⟨y, (hopfLax_eq_integrand_iff_isMinOn hbb).2 hyMin,
    fun z hz ↦ hyUnique z ((hopfLax_eq_integrand_iff_isMinOn hbb).1 hz)⟩

end

end HopfLax1D
