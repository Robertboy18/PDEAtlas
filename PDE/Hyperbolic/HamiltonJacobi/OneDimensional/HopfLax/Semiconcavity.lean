/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Strong
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.Scalar.Semiconcavity

/-!
# Semiconcavity of the one-dimensional Hopf–Lax evolution

We prove two discrete second-difference estimates. Hopf–Lax
evolution preserves a semiconcavity bound already present in the initial
datum. When the Hamiltonian is strongly convex, convex duality instead
supplies the sharp time-dependent bound `z^2 / (theta * t)`.
Positive strong convexity also gives finiteness of the Legendre transform.
These are Lemmas 3 and 4 of Evans, §3.3.3(a).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(a), Lemmas 3 and 4, (35)-(37).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

/-- Positive strong convexity gives a finite Legendre transform, without
requiring differentiability of the Hamiltonian. -/
theorem legendreFinite_of_strongConvex {H : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hH : StrongConvexOn (Set.univ : Set ℝ) θ H) :
    LegendreFinite H := by
  let g : ℝ → ℝ := fun p ↦ H p - θ / 2 * ‖p‖ ^ 2
  have hg : ConvexOn ℝ Set.univ g := strongConvexOn_iff_convex.mp hH
  have hgcont : ContinuousOn g Set.univ := ConvexOn.continuousOn isOpen_univ hg
  obtain ⟨a, b, hab⟩ := hg.exists_affine_le_real isClosed_univ hgcont.lowerSemicontinuousOn
  intro q
  refine ⟨(q - a) ^ 2 / (2 * θ) - b, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hlower : a * p + b ≤ H p - θ / 2 * p ^ 2 := by
    simpa [g, Real.norm_eq_abs, sq_abs] using hab p (Set.mem_univ p)
  -- Complete the square in `p` using the affine lower bound for `g`.
  have hquad : p * (q - a) - θ / 2 * p ^ 2 ≤ (q - a) ^ 2 / (2 * θ) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hθ)]
    nlinarith [sq_nonneg (q - a - θ * p)]
  nlinarith

/-- The Hopf–Lax operator preserves a quadratic semiconcavity bound of the initial datum. -/
theorem hopfLax_semiconcave_of_semiconcave_phi {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {C : ℝ}
    (hsemi : ∀ x z : ℝ, φ (x + z) - 2 * φ x + φ (x - z) ≤ C * z ^ 2) {t x z : ℝ} (ht : 0 < t) :
    hopfLax H φ t (x + z) - 2 * hopfLax H φ t x + hopfLax H φ t (x - z) ≤ C * z ^ 2 := by
  obtain ⟨y0, hy0⟩ := exists_hopfLax_eq_integrand_of_lipschitz hFin hφ (x := x) ht
  have hup := hopfLax_le_integrand (y := y0 + z) (hopfLaxBddBelow_of_lipschitz hFin hφ
    (x := x + z) ht)
  have hdn := hopfLax_le_integrand (y := y0 - z) (hopfLaxBddBelow_of_lipschitz hFin hφ
    (x := x - z) ht)
  -- Translating the footpoint by the same displacement leaves both slopes unchanged.
  rw [hopfLaxIntegrand, add_sub_add_right_eq_sub] at hup
  rw [hopfLaxIntegrand, sub_sub_sub_cancel_right] at hdn
  rw [hy0, hopfLaxIntegrand]
  linarith [hsemi y0 z]

/-- Strong convexity of `H` bounds the defect of concavity of its Legendre
transform along every convex combination. -/
theorem weighted_legendreTransform_sub_le_of_strongConvex {H : ℝ → ℝ} {θ a b : ℝ} (hθ : 0 < θ)
    (hHsc : StrongConvexOn (Set.univ : Set ℝ) θ H) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (q₁ q₂ : ℝ) :
    a * legendreTransform H q₁ + b * legendreTransform H q₂ -
      legendreTransform H (a * q₁ + b * q₂) ≤ a * b / (2 * θ) * (q₁ - q₂) ^ 2 := by
  have hFin := legendreFinite_of_strongConvex hθ hHsc
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Approximate the two dual suprema independently; their weighted errors
  -- still total `ε` because `a + b = 1`.
  have happrox (q : ℝ) : ∃ p, legendreTransform H q ≤ p * q - H p + ε := by
    obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty fun p : ℝ ↦ p * q - H p) (sub_lt_self (legendreTransform H q) hε)
    exact ⟨p, by linarith⟩
  obtain ⟨p₁, hL₁⟩ := happrox q₁
  obtain ⟨p₂, hL₂⟩ := happrox q₂
  have hp₀ := le_legendreTransform (p := a * p₁ + b * p₂) (hFin (a * q₁ + b * q₂))
  have hstrong := hHsc.2 (Set.mem_univ p₁) (Set.mem_univ p₂) ha hb hab
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at hstrong
  -- The remaining estimate is Young's inequality with the sharp constant,
  -- obtained by expanding `(q₁ - q₂ - θ * (p₁ - p₂))²`.
  have hbase : (p₁ - p₂) * (q₁ - q₂) - θ / 2 * (p₁ - p₂) ^ 2 ≤ (q₁ - q₂) ^ 2 / (2 * θ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((q₁ - q₂) - θ * (p₁ - p₂))]
  have hmul := mul_le_mul_of_nonneg_left hbase (mul_nonneg ha hb)
  obtain rfl : b = 1 - a := by linarith
  rw [show a * (1 - a) / (2 * θ) * (q₁ - q₂) ^ 2 = a * (1 - a) * ((q₁ - q₂) ^ 2 / (2 * θ)) by
    ring]
  linarith [mul_le_mul_of_nonneg_left hL₁ ha, mul_le_mul_of_nonneg_left hL₂ hb]

/-- The Legendre transform of a `θ`-strongly convex Hamiltonian becomes
concave after subtracting `q² / (2θ)`. -/
theorem concaveOn_legendreTransform_sub_quadratic_of_strongConvex {H : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hHsc : StrongConvexOn (Set.univ : Set ℝ) θ H) :
    ConcaveOn ℝ Set.univ (fun q : ℝ ↦ legendreTransform H q - q ^ 2 / (2 * θ)) := by
  refine ⟨convex_univ, fun q₁ _ q₂ _ a b ha hb hab ↦ ?_⟩
  have hw := weighted_legendreTransform_sub_le_of_strongConvex hθ hHsc ha hb hab q₁ q₂
  obtain rfl : b = 1 - a := by linarith
  have : a * (q₁ ^ 2 / (2 * θ)) + (1 - a) * (q₂ ^ 2 / (2 * θ)) -
      (a * q₁ + (1 - a) * q₂) ^ 2 / (2 * θ) = a * (1 - a) / (2 * θ) * (q₁ - q₂) ^ 2 := by ring
  simp only [smul_eq_mul]
  linarith

/-- Evans's inequality (37) in the proof of Lemma 4, §3.3.3(a), which he leaves as an exercise:
strong convexity of `H` controls the midpoint defect of its Legendre transform. -/
theorem legendreTransform_secondDiff_le_of_strongConvex {H : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hHsc : StrongConvexOn (Set.univ : Set ℝ) θ H) (q₁ q₂ : ℝ) :
    legendreTransform H q₁ + legendreTransform H q₂ - 2 * legendreTransform H ((q₁ + q₂) / 2) ≤
      (q₁ - q₂) ^ 2 / (4 * θ) := by
  have hw := weighted_legendreTransform_sub_le_of_strongConvex hθ hHsc
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num) q₁ q₂
  rw [show (1 : ℝ) / 2 * q₁ + 1 / 2 * q₂ = (q₁ + q₂) / 2 by ring,
    show (1 : ℝ) / 2 * (1 / 2) / (2 * θ) * (q₁ - q₂) ^ 2 = (q₁ - q₂) ^ 2 / (4 * θ) / 2 by
      field_simp; ring] at hw
  linarith

/-- The Hopf–Lax evolution inherits the weighted quadratic defect supplied by
strong convexity of the Hamiltonian. -/
theorem weighted_hopfLax_le_add_quadratic_of_strongConvex {H φ : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hHsc : StrongConvexOn (Set.univ : Set ℝ) θ H) {K : NNReal} (hφ : LipschitzWith K φ) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x₁ x₂ : ℝ) :
    a * hopfLax H φ t x₁ + b * hopfLax H φ t x₂ ≤
      hopfLax H φ t (a * x₁ + b * x₂) + a * b / (2 * θ * t) * (x₁ - x₂) ^ 2 := by
  have hFin := legendreFinite_of_strongConvex hθ hHsc
  obtain ⟨y₀, hy₀⟩ := exists_hopfLax_eq_integrand_of_lipschitz hFin hφ (x := a * x₁ + b * x₂) ht
  have hu₁ := hopfLax_le_integrand (y := y₀) (hopfLaxBddBelow_of_lipschitz hFin hφ (x := x₁) ht)
  have hu₂ := hopfLax_le_integrand (y := y₀) (hopfLaxBddBelow_of_lipschitz hFin hφ (x := x₂) ht)
  -- Evaluate both endpoint infima at the minimizing footpoint for the
  -- weighted center. The initial datum then cancels under `a + b = 1`.
  have hw := weighted_legendreTransform_sub_le_of_strongConvex hθ hHsc ha hb hab
    ((x₁ - y₀) / t) ((x₂ - y₀) / t)
  obtain rfl : b = 1 - a := by linarith
  have hmul := mul_le_mul_of_nonneg_left hw ht.le
  rw [show a * ((x₁ - y₀) / t) + (1 - a) * ((x₂ - y₀) / t) = (a * x₁ + (1 - a) * x₂ - y₀) / t by
      ring, show t * (a * (1 - a) / (2 * θ) * ((x₁ - y₀) / t - (x₂ - y₀) / t) ^ 2) =
        a * (1 - a) / (2 * θ * t) * (x₁ - x₂) ^ 2 by field_simp; ring] at hmul
  simp only [hopfLaxIntegrand] at hu₁ hu₂ hy₀
  rw [hy₀]
  linarith [mul_le_mul_of_nonneg_left hu₁ ha, mul_le_mul_of_nonneg_left hu₂ hb]

/-- At positive time, subtracting `x² / (2θt)` makes the Hopf–Lax evolution
concave in space. -/
theorem concaveOn_hopfLax_sub_quadratic_of_strongConvex {H φ : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hHsc : StrongConvexOn (Set.univ : Set ℝ) θ H) {K : NNReal} (hφ : LipschitzWith K φ) {t : ℝ}
    (ht : 0 < t) :
    ConcaveOn ℝ Set.univ (fun x : ℝ ↦ hopfLax H φ t x - x ^ 2 / (2 * θ * t)) := by
  refine ⟨convex_univ, fun x₁ _ x₂ _ a b ha hb hab ↦ ?_⟩
  have hw := weighted_hopfLax_le_add_quadratic_of_strongConvex hθ hHsc hφ ht ha hb hab x₁ x₂
  obtain rfl : b = 1 - a := by linarith
  have : a * (x₁ ^ 2 / (2 * θ * t)) + (1 - a) * (x₂ ^ 2 / (2 * θ * t)) -
      (a * x₁ + (1 - a) * x₂) ^ 2 / (2 * θ * t) = a * (1 - a) / (2 * θ * t) * (x₁ - x₂) ^ 2 := by
    ring
  simp only [smul_eq_mul]
  linarith

/-- Evans, §3.3.3(a), Lemma 4: if `H` is strongly convex with constant `θ`, then `hopfLax` is
semiconcave with constant `1/(θ*t)` for `t > 0`. -/
theorem hopfLax_semiconcave_of_strongConvex {H φ : ℝ → ℝ}
    {θ : ℝ} (hθ : 0 < θ) (hHsc : StrongConvexOn (Set.univ : Set ℝ) θ H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x z : ℝ} (ht : 0 < t) :
    hopfLax H φ t (x + z) - 2 * hopfLax H φ t x + hopfLax H φ t (x - z) ≤ z ^ 2 / (θ * t) := by
  have hw := weighted_hopfLax_le_add_quadratic_of_strongConvex hθ hHsc hφ ht
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (x + z) (x - z)
  rw [show (1 : ℝ) / 2 * (x + z) + 1 / 2 * (x - z) = x by ring,
    show (1 : ℝ) / 2 * (1 / 2) / (2 * θ * t) * (x + z - (x - z)) ^ 2 = z ^ 2 / (θ * t) / 2 by
      field_simp; ring] at hw
  linarith

/-- The spatial derivative of a differentiable Hopf–Lax profile satisfies
the Oleinik one-sided Lipschitz estimate. -/
theorem deriv_hopfLax_sub_deriv_le_of_strongConvex {H φ : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hHsc : StrongConvexOn (Set.univ : Set ℝ) θ H) {K : NNReal} (hφ : LipschitzWith K φ) {t x y : ℝ}
    (ht : 0 < t) (hxy : x ≤ y) (hx : DifferentiableAt ℝ (hopfLax H φ t) x)
    (hy : DifferentiableAt ℝ (hopfLax H φ t) y) :
    deriv (hopfLax H φ t) y - deriv (hopfLax H φ t) x ≤ (y - x) / (θ * t) := by
  have hconcave := concaveOn_hopfLax_sub_quadratic_of_strongConvex hθ hHsc hφ ht
  rw [show (fun z : ℝ ↦ hopfLax H φ t z - z ^ 2 / (2 * θ * t)) =
      fun z ↦ hopfLax H φ t z - 1 / (θ * t) / 2 * z ^ 2 by funext z; field_simp] at hconcave
  exact (PDE.Analysis.Scalar.deriv_sub_deriv_le_of_concaveOn_sub_quadratic hconcave hxy hx
    hy).trans_eq (by ring)

end

end HopfLax1D
