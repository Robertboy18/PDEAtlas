/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.Minty
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Finite-dimensional Galerkin equations for monotone operators

Restricting a monotone, hemicontinuous, coercive operator to a finite-dimensional
subspace gives a solution tested on that subspace. For a finite family, the solution
has coefficients in that family; neither independence nor orthonormality is
required.

A quadratic lower bound also gives an energy constant independent of the load and
the trial space. Linearity in the test variable extends the finite equations to the
span and permits testing with the Galerkin solution itself.

These are Theorems 1 and 2 of Evans, §9.1, for an abstract operator. There `A u v` is
`∫ a(Du) · Dv dx`, the trial family is `w_1, ..., w_m`, and the Galerkin equations are his (7)
for `u_m` of the form (6). His proof of Theorem 1 uses the coercivity (5) and not
monotonicity: he finds the coefficients as a zero of the vector field (10) by the Lemma (Zeros
of a vector field). We apply instead the Browder–Minty theorem
`surjective_of_monotone_of_hemicontinuous_of_coercive` on the finite-dimensional subspace,
which uses monotonicity as well. The hypothesis `hlower` is
the integrated form of (5), and `exists_pos_galerkin_norm_bound` is his energy estimate (11),
with `‖ℓ‖` in place of `‖f‖_{L²(U)}`. Its proof tests with the Galerkin solution, as he
multiplies (7) by `d_m^k` and sums over `k`.

## Main results

* `exists_galerkin_on_submodule`: on a finite-dimensional subspace `S`, some `u ∈ S` satisfies
  `A u v = ℓ v` for every `v ∈ S`.
* `exists_galerkin_coefficients`: for a finite family `w`, some coefficients `d` give
  `A (∑ i, d i • w i) v = ℓ v` for every `v` in the span of `w`.
* `exists_pos_norm_bound_of_quadratic_lower_bound`, `exists_pos_galerkin_norm_bound`: if
  `K ‖u‖² - B ≤ A u u` with `K > 0`, one `C > 0` gives `‖u‖ ≤ C (1 + ‖ℓ‖)` for every
  self-tested solution `A u u = ℓ u`, and for every solution of every finite Galerkin system.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.1, the coercivity inequality (5), p. 528, (6), (7)
  and the Lemma (Zeros of a vector field), p. 529, and Theorem 1 (Construction of approximate
  solutions) and Theorem 2 (Energy estimates), (10) and (11), p. 530.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Operator

open Set
open scoped Topology

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A monotone, hemicontinuous, coercive operator has a Galerkin solution on every
finite-dimensional subspace of a real inner product space. Completeness of the
subspace, hence its reflexivity, follows from finite dimensionality. -/
theorem exists_galerkin_on_submodule
    (A : E → StrongDual ℝ E)
    (hmono : ∀ u v, 0 ≤ (A u - A v) (u - v))
    (hhemi : ∀ u v, ContinuousWithinAt
      (fun t : ℝ ↦ A (u + t • v) v) (Ici 0) 0)
    (hcoercive : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : E, R ≤ ‖u‖ → M * ‖u‖ ≤ A u u)
    (S : Submodule ℝ E) [FiniteDimensional ℝ S] (ℓ : StrongDual ℝ E) :
    ∃ u : S, ∀ v : S, A u v = ℓ v := by
  let AS : S → StrongDual ℝ S := fun u ↦ (A u).comp S.subtypeL
  have hmonoS : ∀ u v : S, 0 ≤ (AS u - AS v) (u - v) := by
    intro u v
    exact hmono u v
  have hhemiS : ∀ u v : S, ContinuousWithinAt
      (fun t : ℝ ↦ AS (u + t • v) v) (Ici 0) 0 := by
    intro u v
    exact hhemi u v
  have hcoerciveS : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : S, R ≤ ‖u‖ → M * ‖u‖ ≤ AS u u := by
    intro M hM
    obtain ⟨R, hR, hu⟩ := hcoercive M hM
    exact ⟨R, hR, fun u ↦ hu u⟩
  obtain ⟨u, hu⟩ := surjective_of_monotone_of_hemicontinuous_of_coercive
    (PDE.Analysis.inclusionInDoubleDual_surjective (H := S))
    AS hmonoS hhemiS hcoerciveS (ℓ.comp S.subtypeL)
  exact ⟨u, fun v ↦ congrArg (fun f : StrongDual ℝ S ↦ f v) hu⟩

/-- Every finite trial family admits coefficients solving the Galerkin equations.
The conclusion includes all tests in its span, even for a dependent or empty family. -/
theorem exists_galerkin_coefficients
    (A : E → StrongDual ℝ E)
    (hmono : ∀ u v, 0 ≤ (A u - A v) (u - v))
    (hhemi : ∀ u v, ContinuousWithinAt
      (fun t : ℝ ↦ A (u + t • v) v) (Ici 0) 0)
    (hcoercive : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : E, R ≤ ‖u‖ → M * ‖u‖ ≤ A u u)
    (ℓ : StrongDual ℝ E) {ι : Type*} [Fintype ι] (w : ι → E) :
    ∃ d : ι → ℝ, ∀ v ∈ Submodule.span ℝ (range w), A (∑ i, d i • w i) v = ℓ v := by
  let S := Submodule.span ℝ (range w)
  have : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (finite_range w)
  obtain ⟨u, hu⟩ := exists_galerkin_on_submodule A hmono hhemi hcoercive S ℓ
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp u.property
  exact ⟨d, fun v hv ↦ hd ▸ hu ⟨v, hv⟩⟩

end Hilbert

section Energy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quadratic pairing lower bound gives a norm estimate for every self-tested
solution. The positive constant is chosen before the continuous load and the solution. -/
theorem exists_pos_norm_bound_of_quadratic_lower_bound
    (A : E → StrongDual ℝ E) {K B : ℝ} (hK : 0 < K)
    (hlower : ∀ u, K * ‖u‖ ^ 2 - B ≤ A u u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : StrongDual ℝ E) (u : E),
      A u u = ℓ u → ‖u‖ ≤ C * (1 + ‖ℓ‖) := by
  let C := 1 + (1 + |B|) / K
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [div_nonneg (show 0 ≤ 1 + |B| by positivity) hK.le]
  have hCK : 1 + |B| ≤ K * C := by
    dsimp [C]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hK.ne']
    linarith
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro ℓ u hu
  have henergy : K * ‖u‖ ^ 2 - B ≤ ‖ℓ‖ * ‖u‖ := by
    exact (hlower u).trans (hu ▸ (le_abs_self (ℓ u)).trans (ℓ.le_opNorm u))
  by_cases hsmall : ‖u‖ ≤ 1
  · exact hsmall.trans (hC.trans
      (le_mul_of_one_le_right (zero_le_one.trans hC) (by linarith [norm_nonneg ℓ])))
  · have hr : 1 ≤ ‖u‖ := (lt_of_not_ge hsmall).le
    have hlinear : K * ‖u‖ ≤ ‖ℓ‖ + |B| := by
      have habs := mul_le_mul_of_nonneg_left hr (abs_nonneg B)
      nlinarith [le_abs_self B]
    have hload : ‖ℓ‖ + |B| ≤ (1 + |B|) * (1 + ‖ℓ‖) := by
      nlinarith [mul_nonneg (abs_nonneg B) (norm_nonneg ℓ)]
    have hbound := hload.trans
      (mul_le_mul_of_nonneg_right hCK (by positivity : 0 ≤ 1 + ‖ℓ‖))
    nlinarith

/-- The same energy constant controls every solution of every finite Galerkin
system. Only the equations for the trial family are hypotheses: linearity in the
test variable supplies the self-test. -/
theorem exists_pos_galerkin_norm_bound
    (A : E → StrongDual ℝ E) {K B : ℝ} (hK : 0 < K)
    (hlower : ∀ u, K * ‖u‖ ^ 2 - B ≤ A u u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : StrongDual ℝ E) {ι : Type*} [Fintype ι]
      (w : ι → E) (d : ι → ℝ),
      (∀ i, A (∑ j, d j • w j) (w i) = ℓ (w i)) →
      ‖∑ i, d i • w i‖ ≤ C * (1 + ‖ℓ‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_norm_bound_of_quadratic_lower_bound A hK hlower
  refine ⟨C, hC, ?_⟩
  intro ℓ ι _ w d heq
  apply hbound ℓ
  simp only [map_sum, map_smul, heq]

end Energy

end PDE.Analysis.Operator
