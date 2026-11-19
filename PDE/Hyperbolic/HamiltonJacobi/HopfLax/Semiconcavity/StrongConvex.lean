/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Semiconcavity
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Approximation

/-!
# Uniformly convex Lagrangians

Mathlib expresses uniform quadratic convexity by `StrongConvexOn`.
In finite-dimensional real inner product spaces this assumption supplies
superlinearity: subtract the quadratic, find a continuous affine minorant of
the remaining convex function, and complete the square.

Thus a `C²` uniformly convex Lagrangian satisfies the spatial semiconcavity
estimate for every Lipschitz datum.

`superlinear_of_strongConvex` gives the superlinearity (12) of Evans, §3.3.2(a), for a
uniformly convex `L`. `exists_semiconcavity_constant_of_strongConvex` is an estimate of the form
of Evans, §3.3.3(a), Lemma 4, `u(x + z, t) - 2u(x, t) + u(x - z, t) ≤ (C/t)|z|²`, under a
hypothesis on `L` in place of the uniform convexity (35) of `H`: `L` is `C²` and uniformly
convex, and `g` is Lipschitz.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(a), equation (12); §3.3.3(a), equation (35)
  and Lemma 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Positive strong convexity implies superlinearity in finite dimension.
A continuous affine minorant of the convex remainder controls its possible
linear decrease, while the positive quadratic dominates every linear slope. -/
theorem superlinear_of_strongConvex {L : E → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hconv : StrongConvexOn (Set.univ : Set E) θ L) :
    Superlinear L := by
  let f : E → ℝ := fun q ↦ L q - θ / 2 * ‖q‖ ^ 2
  have hf : ConvexOn ℝ Set.univ f := strongConvexOn_iff_convex.mp hconv
  have hcont : ContinuousOn f Set.univ := hf.continuousOn isOpen_univ
  obtain ⟨ℓ, b, hminor, _⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ)
    (Set.mem_univ (0 : E)) (sub_lt_self (f 0) zero_lt_one) isClosed_univ
    hcont.lowerSemicontinuousOn hf
  intro A
  refine ⟨(A + ‖ℓ‖) ^ 2 / (2 * θ) - b, fun q ↦ ?_⟩
  have hminorant : ℓ q + b ≤ L q - θ / 2 * ‖q‖ ^ 2 := hminor ⟨q, Set.mem_univ q⟩
  have hlinear : -(‖ℓ‖ * ‖q‖) ≤ ℓ q := by
    have hnorm : |ℓ q| ≤ ‖ℓ‖ * ‖q‖ := ℓ.le_opNorm q
    linarith [(neg_le_abs (ℓ q)).trans hnorm]
  have hquadratic :
      (A + ‖ℓ‖) * ‖q‖ - θ / 2 * ‖q‖ ^ 2 ≤ (A + ‖ℓ‖) ^ 2 / (2 * θ) := by
    rw [le_div_iff₀ (mul_pos zero_lt_two hθ)]
    nlinarith [sq_nonneg (A + ‖ℓ‖ - θ * ‖q‖)]
  nlinarith

/-- A `C²` uniformly convex Lagrangian has a uniform spatial semiconcavity
constant for all data with prescribed Lipschitz constant. The datum can be
unbounded above and below. -/
theorem exists_semiconcavity_constant_of_strongConvex {L : E → ℝ} (hsmooth : ContDiff ℝ 2 L) {θ : ℝ}
    (hθ : 0 < θ) (hconv : StrongConvexOn (Set.univ : Set E) θ L) (K : NNReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : E → ℝ), LipschitzWith K g → ∀ (t : ℝ), 0 < t → ∀ x z,
      value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤ (C / t) * ‖z‖ ^ 2 :=
  exists_semiconcavity_constant (superlinear_of_strongConvex hθ hconv) hsmooth K

end HamiltonJacobi.HopfLax
