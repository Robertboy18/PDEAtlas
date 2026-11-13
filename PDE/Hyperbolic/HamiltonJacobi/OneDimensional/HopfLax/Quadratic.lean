/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Optimality
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Semiconcavity
import CAS.ExactTactic

/-!
# The quadratic one-dimensional Hopf–Lax formula

We specialize the one-dimensional Hopf–Lax theory to the normalized
quadratic Hamiltonian

`H(p) = p^2 / 2`.

The Legendre transform of `H` is again `H`, so the Hopf–Lax integrand becomes
the Moreau cost

`phi(y) + (x - y)^2 / (2 * t)`.

For convex Lipschitz initial data, the cost has a unique minimizing footpoint.
At a differentiable footpoint, the optimality equation is
`phi'(y) = (x - y) / t`. The unit strong-convexity constant also specializes
the general semiconcavity theorem to the sharp bound `z^2 / t`.

These are direct corollaries of the general theory.

With `H(p) = p²/2` the Hopf–Lax value is the Moreau envelope of `φ` with parameter `t`, and
`L = H` because `H` is its own Legendre transform.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4, formula (21).
  <https://doi.org/10.1090/gsm/019>
* J.-J. Moreau, *Proximité et dualité dans un espace hilbertien*, Bull. Soc. Math. France 93
  (1965), 273-299.
  <https://doi.org/10.24033/bsmf.1625>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

/-- The normalized quadratic Hamiltonian `p ↦ p^2 / 2`. -/
def quadraticHamiltonian (p : ℝ) : ℝ :=
  p ^ 2 / 2

/-- The Legendre transform of the normalized quadratic Hamiltonian is finite. -/
theorem legendreFinite_quadraticHamiltonian :
    LegendreFinite quadraticHamiltonian :=
  fun q ↦ ⟨q ^ 2 / 2, Set.forall_mem_range.2 fun p ↦ by
    dsimp [quadraticHamiltonian]
    linarith [sq_nonneg (p - q)]⟩

/-- The normalized quadratic Hamiltonian is self-dual under the Legendre transform. -/
@[simp] theorem legendreTransform_quadraticHamiltonian (q : ℝ) :
    legendreTransform quadraticHamiltonian q = quadraticHamiltonian q := by
  refine le_antisymm (csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun p ↦ ?_)) ?_
  · dsimp [quadraticHamiltonian]
    linarith [sq_nonneg (p - q)]
  · have h := le_legendreTransform (p := q) (legendreFinite_quadraticHamiltonian q)
    dsimp [quadraticHamiltonian] at h ⊢
    linarith

/-- The derivative of `p ↦ p^2 / 2` at `p` is `p`. -/
theorem hasDerivAt_quadraticHamiltonian (p : ℝ) :
    HasDerivAt quadraticHamiltonian p p := by
  cas

/-- The normalized quadratic Hamiltonian is strongly convex with optimal constant one. -/
theorem strongConvexOn_quadraticHamiltonian :
    StrongConvexOn (Set.univ : Set ℝ) 1 quadraticHamiltonian := by
  rw [strongConvexOn_iff_convex]
  have hzero : (fun p : ℝ ↦ quadraticHamiltonian p - 1 / 2 * ‖p‖ ^ 2) =
        fun _ : ℝ ↦ 0 := by
    funext p
    simp only [quadraticHamiltonian, Real.norm_eq_abs]
    cas
  rw [hzero]
  exact convexOn_const 0 convex_univ

/-- The Legendre cost of the normalized quadratic Hamiltonian is strictly convex. -/
theorem strictConvexOn_legendreTransform_quadraticHamiltonian :
    StrictConvexOn ℝ Set.univ (legendreTransform quadraticHamiltonian) := by
  rw [show legendreTransform quadraticHamiltonian = quadraticHamiltonian from
    funext legendreTransform_quadraticHamiltonian]
  exact strongConvexOn_quadraticHamiltonian.strictConvexOn zero_lt_one

/-- At nonzero time, the quadratic Hopf–Lax integrand is the Moreau cost. -/
@[simp] theorem hopfLaxIntegrand_quadraticHamiltonian
    {φ : ℝ → ℝ} {t x y : ℝ} (ht : t ≠ 0) :
    hopfLaxIntegrand quadraticHamiltonian φ t x y =
      φ y + (x - y) ^ 2 / (2 * t) := by
  rw [hopfLaxIntegrand, legendreTransform_quadraticHamiltonian, quadraticHamiltonian]
  cas

/-- The quadratic Hopf–Lax value is the infimum of the Moreau cost. -/
theorem hopfLax_quadraticHamiltonian {φ : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    hopfLax quadraticHamiltonian φ t x =
      sInf (Set.range fun y : ℝ ↦ φ y + (x - y) ^ 2 / (2 * t)) := by
  simp [hopfLax, hopfLaxIntegrand_quadraticHamiltonian ht]

/-- A convex Lipschitz datum gives a unique minimizer of the quadratic
Hopf–Lax cost at positive time. -/
theorem existsUnique_isMinOn_quadraticHamiltonian {φ : ℝ → ℝ} (hφConvex : ConvexOn ℝ Set.univ φ)
    {K : NNReal} (hφLipschitz : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃! y : ℝ, IsMinOn (fun z : ℝ ↦ φ z + (x - z) ^ 2 / (2 * t)) Set.univ y := by
  rw [← show hopfLaxIntegrand quadraticHamiltonian φ t x = fun z ↦ φ z + (x - z) ^ 2 / (2 * t)
    from funext fun z ↦ hopfLaxIntegrand_quadraticHamiltonian ht.ne']
  exact existsUnique_isMinOn_hopfLaxIntegrand_of_strictConvex_legendreTransform
    legendreFinite_quadraticHamiltonian hφConvex
      strictConvexOn_legendreTransform_quadraticHamiltonian hφLipschitz ht

/-- A convex Lipschitz datum attains its quadratic Hopf–Lax value at a unique footpoint. -/
theorem existsUnique_hopfLax_eq_quadratic_cost {φ : ℝ → ℝ} (hφConvex : ConvexOn ℝ Set.univ φ)
    {K : NNReal} (hφLipschitz : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃! y : ℝ, hopfLax quadraticHamiltonian φ t x = φ y + (x - y) ^ 2 / (2 * t) := by
  simpa only [hopfLaxIntegrand_quadraticHamiltonian ht.ne'] using
    (existsUnique_hopfLax_eq_integrand_of_strictConvex_legendreTransform
      legendreFinite_quadraticHamiltonian hφConvex
        strictConvexOn_legendreTransform_quadraticHamiltonian hφLipschitz (t := t) (x := x) ht)

/-- A differentiable minimizing footpoint satisfies
`φ'(y) = (x - y) / t`. -/
theorem deriv_eq_slope_of_isMinOn_quadraticHamiltonian {φ : ℝ → ℝ} {t x y : ℝ} (ht : t ≠ 0)
    (hy : IsMinOn (fun z : ℝ ↦ φ z + (x - z) ^ 2 / (2 * t)) Set.univ y)
    (hφ : DifferentiableAt ℝ φ y) :
    deriv φ y = (x - y) / t := by
  have hL : HasDerivAt (legendreTransform quadraticHamiltonian) ((x - y) / t) ((x - y) / t) := by
    rw [show legendreTransform quadraticHamiltonian = quadraticHamiltonian from
      funext legendreTransform_quadraticHamiltonian]
    exact hasDerivAt_quadraticHamiltonian ((x - y) / t)
  rw [deriv_eq_deriv_legendreTransform_of_isMinOn ht (by
    rwa [show hopfLaxIntegrand quadraticHamiltonian φ t x = fun z ↦ φ z + (x - z) ^ 2 / (2 * t)
      from funext fun z ↦ hopfLaxIntegrand_quadraticHamiltonian ht]) hφ hL.differentiableAt,
    hL.deriv]

/-- For the normalized quadratic Hamiltonian, the weighted Hopf–Lax defect is
bounded by the corresponding quadratic spatial variance. -/
theorem weighted_hopfLax_le_add_quadraticHamiltonian {φ : ℝ → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {t a b : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x₁ x₂ : ℝ) :
    a * hopfLax quadraticHamiltonian φ t x₁ + b * hopfLax quadraticHamiltonian φ t x₂ ≤
      hopfLax quadraticHamiltonian φ t (a * x₁ + b * x₂) + a * b / (2 * t) * (x₁ - x₂) ^ 2 := by
  simpa using weighted_hopfLax_le_add_quadratic_of_strongConvex zero_lt_one
        strongConvexOn_quadraticHamiltonian hφ ht ha hb hab x₁ x₂

/-- At positive time, subtracting `x² / (2t)` makes the quadratic Hopf–Lax
evolution concave in space. -/
theorem concaveOn_hopfLax_sub_quadraticHamiltonian {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    {t : ℝ} (ht : 0 < t) :
    ConcaveOn ℝ Set.univ (fun x : ℝ ↦ hopfLax quadraticHamiltonian φ t x - x ^ 2 / (2 * t)) := by
  simpa using concaveOn_hopfLax_sub_quadratic_of_strongConvex zero_lt_one
        strongConvexOn_quadraticHamiltonian hφ ht

/-- At positive time, the quadratic Hopf–Lax evolution has second difference
bounded above by `z^2 / t`. -/
theorem hopfLax_semiconcave_quadraticHamiltonian {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    {t x z : ℝ} (ht : 0 < t) :
    hopfLax quadraticHamiltonian φ t (x + z) - 2 * hopfLax quadraticHamiltonian φ t x +
      hopfLax quadraticHamiltonian φ t (x - z) ≤ z ^ 2 / t := by
  simpa using hopfLax_semiconcave_of_strongConvex zero_lt_one
        strongConvexOn_quadraticHamiltonian hφ ht

/-- Wherever the quadratic Hopf–Lax profile is differentiable, its derivative
satisfies the sharp Oleinik estimate with constant `1 / t`. -/
theorem deriv_hopfLax_sub_deriv_le_quadraticHamiltonian {φ : ℝ → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {t x y : ℝ} (ht : 0 < t) (hxy : x ≤ y)
    (hx : DifferentiableAt ℝ (hopfLax quadraticHamiltonian φ t) x)
    (hy : DifferentiableAt ℝ (hopfLax quadraticHamiltonian φ t) y) :
    deriv (hopfLax quadraticHamiltonian φ t) y - deriv (hopfLax quadraticHamiltonian φ t) x ≤
      (y - x) / t := by
  simpa using deriv_hopfLax_sub_deriv_le_of_strongConvex zero_lt_one
        strongConvexOn_quadraticHamiltonian hφ ht hxy hx hy

end

end HopfLax1D
