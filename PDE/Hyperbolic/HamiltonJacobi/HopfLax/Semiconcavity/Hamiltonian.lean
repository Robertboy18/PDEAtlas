/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.StrongConvex
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Hamiltonian
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Semiconcavity.StrongConvex

/-!
# Sharp semiconcavity from a uniformly convex Hamiltonian

The Legendre transform of a `θ`-strongly convex Hamiltonian has spatial
second differences bounded by `‖z‖² / θ`. The proof compares two terms in
the dual suprema and applies the midpoint convexity inequality for the
Hamiltonian. Completing a square gives the sharp constant without taking
any derivatives of the Legendre transform.

At an attained Hopf–Lax minimizer, keep its footpoint fixed while moving
the endpoint by `±z`. The dual estimate gives `‖z‖² / (θ * t)` for every
positive time and every Lipschitz initial datum, including unbounded data.

This is Lemma 4 of Evans, §3.3.3(a), and the dual estimate is his inequality (37), which he
leaves as an exercise. The uniform convexity of the Hamiltonian is Mathlib's `StrongConvexOn`
with constant `θ`; at the midpoint it is Evans's inequality (36). The final theorem
derives this condition from Evans's pointwise Hessian lower bound (35) on `H`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(a), Lemma 4 and its proof, (35)-(37).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform convexity of the original Hamiltonian gives the sharp global
second-difference bound for its Legendre transform. -/
theorem second_difference_hamiltonian_le_of_strongConvex {H : E → ℝ} (hH : Superlinear H) {θ : ℝ}
    (hθ : 0 < θ) (hconv : StrongConvexOn (Set.univ : Set E) θ H) (q z : E) :
    hamiltonian H (q + z) - 2 * hamiltonian H q + hamiltonian H (q - z) ≤ ‖z‖ ^ 2 / θ := by
  have hpair (p r : E) : (inner ℝ (q + z) p - H p) + (inner ℝ (q - z) r - H r) ≤
        2 * hamiltonian H q + ‖z‖ ^ 2 / θ := by
    have hmid := hconv.2 (Set.mem_univ p) (Set.mem_univ r)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    have hdual := le_hamiltonian hH q ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • r)
    simp only [smul_eq_mul] at hmid
    simp only [inner_add_right, inner_smul_right] at hdual
    have hinner := real_inner_le_norm z (p - r)
    have hsquare :
        ‖z‖ * ‖p - r‖ - θ / 4 * ‖p - r‖ ^ 2 ≤ ‖z‖ ^ 2 / θ := by
      rw [le_div_iff₀ hθ]
      nlinarith [sq_nonneg (‖z‖ - θ / 2 * ‖p - r‖)]
    simp only [inner_sub_right] at hinner
    simp only [inner_add_left, inner_sub_left]
    linarith
  have hupper : hamiltonian H (q + z) ≤
        2 * hamiltonian H q + ‖z‖ ^ 2 / θ - hamiltonian H (q - z) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨p, rfl⟩
    have hother : hamiltonian H (q - z) ≤
          2 * hamiltonian H q + ‖z‖ ^ 2 / θ - (inner ℝ (q + z) p - H p) := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨r, rfl⟩
      linarith [hpair p r]
    linarith
  linarith

variable [FiniteDimensional ℝ E]

/-- Evans's sharp spatial semiconcavity estimate for the Hopf–Lax value
constructed from the Legendre transform of a uniformly convex Hamiltonian.
The initial datum is arbitrary Lipschitz, with no boundedness requirement. -/
theorem second_difference_value_dual_le_of_strongConvex {H g : E → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hconv : StrongConvexOn (Set.univ : Set E) θ H) {K : NNReal} (hg : LipschitzWith K g) {t : ℝ}
    (ht : 0 < t) (x z : E) :
    value (hamiltonian H) g t (x + z) - 2 * value (hamiltonian H) g t x +
      value (hamiltonian H) g t (x - z) ≤ (1 / (θ * t)) * ‖z‖ ^ 2 := by
  have hH := superlinear_of_strongConvex hθ hconv
  have hcont : Continuous H :=
    continuousOn_univ.mp ((hconv.strictConvexOn hθ).convexOn.continuousOn isOpen_univ)
  have hL := superlinear_hamiltonian hH hcont
  obtain ⟨q, hq, _⟩ := exists_minimizer (continuous_hamiltonian hH) hL hg ht x
  calc
    value (hamiltonian H) g t (x + z) - 2 * value (hamiltonian H) g t x +
        value (hamiltonian H) g t (x - z) ≤ t * (hamiltonian H (q + t⁻¹ • z) - 2 * hamiltonian H q +
          hamiltonian H (q - t⁻¹ • z)) := second_difference_value_le_at_minimizer hL hg ht hq z
    _ ≤ t * (‖t⁻¹ • z‖ ^ 2 / θ) := mul_le_mul_of_nonneg_left
        (second_difference_hamiltonian_le_of_strongConvex hH hθ hconv q (t⁻¹ • z)) ht.le
    _ = (1 / (θ * t)) * ‖z‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
      field_simp

/-- For a given convex superlinear Lagrangian, uniform convexity of its
Hamiltonian gives the sharp spatial estimate. Double duality identifies the
original Lagrangian with the Legendre transform used in the Hamiltonian theorem. -/
theorem second_difference_value_le_of_strongConvex_hamiltonian {L g : E → ℝ} (hL : Superlinear L)
    (hconvL : ConvexOn ℝ Set.univ L) {θ : ℝ} (hθ : 0 < θ)
    (hconv : StrongConvexOn (Set.univ : Set E) θ (hamiltonian L)) {K : NNReal}
    (hg : LipschitzWith K g) {t : ℝ} (ht : 0 < t) (x z : E) :
    value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤ (1 / (θ * t)) * ‖z‖ ^ 2 := by
  have hdual : hamiltonian (hamiltonian L) = L := by
    funext q
    exact biconjugate_eq hL hconvL
  simpa only [hdual] using second_difference_value_dual_le_of_strongConvex hθ hconv hg ht x z

/-- Evans's Lemma 4 under its differential uniform convexity hypothesis (35):
the Hessian of the `C²` Hamiltonian is bounded below by `θ` times the squared
norm. Convexity, superlinearity, and all properties of the Legendre transform
needed for the estimate are derived. The datum need not be bounded. -/
theorem second_difference_value_dual_le_of_hessian_lower_bound
    {H g : E → ℝ} (hsmooth : ContDiff ℝ 2 H) {θ : ℝ} (hθ : 0 < θ)
    (hbound : ∀ p v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ H) p v v)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} (ht : 0 < t) (x z : E) :
    value (hamiltonian H) g t (x + z) - 2 * value (hamiltonian H) g t x +
      value (hamiltonian H) g t (x - z) ≤ (1 / (θ * t)) * ‖z‖ ^ 2 := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ H) := hsmooth.fderiv_right (by norm_num)
  have hconv := PDE.Analysis.strongConvexOn_univ_of_hessian_lower_bound
    (hsmooth.differentiable (by norm_num)) hdf.differentiable_one hbound
  exact second_difference_value_dual_le_of_strongConvex hθ hconv hg ht x z

end HamiltonJacobi.HopfLax
