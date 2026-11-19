/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Convexity
import CAS.ExactTactic

/-!
# Optimality for the one-dimensional Hopf–Lax formula

We prove the first-order condition for a minimizing Hopf–Lax
footpoint. If `y` minimizes

`y ↦ φ(y) + t L((x - y) / t)`

and `φ` and `L` are differentiable at `y` and `(x - y) / t`, respectively,
with `t ≠ 0`, then

`φ'(y) = L'((x - y) / t)`.

We also give the complementary uniqueness criterion to
`strictConvexOn_hopfLaxIntegrand_of_strictConvex_phi`: a convex initial datum
has a unique minimizing footpoint when the Legendre cost is strictly convex.
The statements use Mathlib's convexity and local-extremum predicates.
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

/-- Derivative of the Hopf–Lax footpoint integrand at a nonzero time. -/
theorem hasDerivAt_hopfLaxIntegrand {H φ : ℝ → ℝ} {t x y φ' L' : ℝ} (ht : t ≠ 0)
    (hφ : HasDerivAt φ φ' y) (hL : HasDerivAt (legendreTransform H) L' ((x - y) / t)) :
    HasDerivAt (hopfLaxIntegrand H φ t x) (φ' - L') y := by
  have hslope : HasDerivAt (fun z : ℝ ↦ (x - z) / t) (-1 / t) y := by
    cas
  convert hφ.add ((hL.scomp y hslope).const_mul t) using 1
  · rfl
  · simp only [smul_eq_mul]
    field_simp
    ring

/-- Formula for the derivative of the Hopf–Lax footpoint integrand. -/
theorem deriv_hopfLaxIntegrand {H φ : ℝ → ℝ} {t x y : ℝ} (ht : t ≠ 0) (hφ : DifferentiableAt ℝ φ y)
    (hL : DifferentiableAt ℝ (legendreTransform H) ((x - y) / t)) :
    deriv (hopfLaxIntegrand H φ t x) y = deriv φ y - deriv (legendreTransform H) ((x - y) / t) :=
  (hasDerivAt_hopfLaxIntegrand ht hφ.hasDerivAt hL.hasDerivAt).deriv

/-- At a differentiable minimizing footpoint, the initial slope equals the
Legendre-cost slope. -/
theorem deriv_eq_deriv_legendreTransform_of_isMinOn {H φ : ℝ → ℝ} {t x y : ℝ} (ht : t ≠ 0)
    (hy : IsMinOn (hopfLaxIntegrand H φ t x) Set.univ y) (hφ : DifferentiableAt ℝ φ y)
    (hL : DifferentiableAt ℝ (legendreTransform H) ((x - y) / t)) :
    deriv φ y = deriv (legendreTransform H) ((x - y) / t) :=
  sub_eq_zero.mp ((hy.isLocalMin (by simp)).hasDerivAt_eq_zero
    (hasDerivAt_hopfLaxIntegrand ht hφ.hasDerivAt hL.hasDerivAt))

/-- A differentiable footpoint attaining the Hopf–Lax infimum satisfies the
first-order optimality condition. -/
theorem deriv_eq_deriv_legendreTransform_of_hopfLax_eq_integrand {H φ : ℝ → ℝ} {t x y : ℝ}
    (hbb : HopfLaxBddBelow H φ t x) (ht : t ≠ 0) (hy : hopfLax H φ t x = hopfLaxIntegrand H φ t x y)
    (hφ : DifferentiableAt ℝ φ y) (hL : DifferentiableAt ℝ (legendreTransform H) ((x - y) / t)) :
    deriv φ y = deriv (legendreTransform H) ((x - y) / t) :=
  deriv_eq_deriv_legendreTransform_of_isMinOn ht ((hopfLax_eq_integrand_iff_isMinOn hbb).1 hy) hφ hL

/-- A convex initial datum and a strictly convex Legendre cost give a strictly
convex Hopf–Lax footpoint integrand at positive time. -/
theorem strictConvexOn_hopfLaxIntegrand_of_strictConvex_legendreTransform {H φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hL : StrictConvexOn ℝ Set.univ (legendreTransform H)) {t x : ℝ}
    (ht : 0 < t) :
    StrictConvexOn ℝ Set.univ (hopfLaxIntegrand H φ t x) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ hy a b ha hb hab ↦ ?_⟩
  have hφ2 := hφ.2 (Set.mem_univ y₁) (Set.mem_univ y₂) ha.le hb.le hab
  have hne : (x - y₁) / t ≠ (x - y₂) / t := fun h ↦ hy (by field_simp at h; linarith)
  have hL2 := hL.2 (Set.mem_univ ((x - y₁) / t)) (Set.mem_univ ((x - y₂) / t)) hne ha hb hab
  have hslope : (x - (a * y₁ + b * y₂)) / t = a * ((x - y₁) / t) + b * ((x - y₂) / t) := by
    rw [show x - (a * y₁ + b * y₂) = a * (x - y₁) + b * (x - y₂) by
      linear_combination -x * hab]
    ring
  simp only [smul_eq_mul] at hφ2 hL2 ⊢
  rw [← hslope] at hL2
  simp only [hopfLaxIntegrand]
  linarith [mul_lt_mul_of_pos_left hL2 ht]

/-- A convex Lipschitz datum has a unique minimizing Hopf–Lax footpoint when
the Legendre cost is strictly convex. -/
theorem existsUnique_isMinOn_hopfLaxIntegrand_of_strictConvex_legendreTransform {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) (hφConvex : ConvexOn ℝ Set.univ φ)
    (hLStrict : StrictConvexOn ℝ Set.univ (legendreTransform H)) {K : NNReal}
    (hφLipschitz : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃! y : ℝ, IsMinOn (hopfLaxIntegrand H φ t x) Set.univ y := by
  obtain ⟨y, hyMin, _⟩ := exists_isMinOn_hopfLaxIntegrand_of_lipschitz (x := x) hFin hφLipschitz ht
  exact ⟨y, hyMin, fun z hzMin ↦ (strictConvexOn_hopfLaxIntegrand_of_strictConvex_legendreTransform
    hφConvex hLStrict ht).eq_of_isMinOn hzMin hyMin (Set.mem_univ z) (Set.mem_univ y)⟩

/-- Equivalently, strict convexity of the Legendre cost gives a unique
footpoint at which the Hopf–Lax infimum is attained. -/
theorem existsUnique_hopfLax_eq_integrand_of_strictConvex_legendreTransform {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) (hφConvex : ConvexOn ℝ Set.univ φ)
    (hLStrict : StrictConvexOn ℝ Set.univ (legendreTransform H)) {K : NNReal}
    (hφLipschitz : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃! y : ℝ, hopfLax H φ t x = hopfLaxIntegrand H φ t x y := by
  obtain ⟨y, hyMin, hyUnique⟩ :=
    existsUnique_isMinOn_hopfLaxIntegrand_of_strictConvex_legendreTransform (x := x) hFin
      hφConvex hLStrict hφLipschitz ht
  have hbb := hopfLaxBddBelow_of_lipschitz (x := x) hFin hφLipschitz ht
  exact ⟨y, (hopfLax_eq_integrand_iff_isMinOn hbb).2 hyMin,
    fun z hz ↦ hyUnique z ((hopfLax_eq_integrand_iff_isMinOn hbb).1 hz)⟩

end

end HopfLax1D
