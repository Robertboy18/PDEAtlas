/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.Strong
public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator

/-!
# Strong maximum principle for matrix coefficients

A classical subsolution of `Lu = -∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + Du[b] + cu` that attains its maximum over a
connected open domain is constant when `c ≥ 0` and `cM ≥ 0`, where `M` is the attained maximum. The
symmetric principal matrix is locally uniformly elliptic; its trace, the drift norm, and the
potential are locally bounded above. The domain need not be bounded, and no coefficient continuity
is required. This is the symmetric matrix-coefficient form of Evans's §6.4.2, Theorems 3 and 4.

Symmetry and ellipticity imply positive semidefiniteness. Mathlib's matrix factorization constructs
directions whose outer products sum to the principal matrix. The quadratic-form and trace identities
`sum_inner_sq_eq_matrix_quadratic` and `sum_norm_sq_eq_matrix_trace` transfer the local bounds to
these factors, and the coordinate operator identity transfers the subsolution inequality. The
factored strong maximum principle then applies without any regularity assumption on the chosen
factors.

Uniform quadratic ellipticity and continuous trace and drift supply the local coefficient bounds for
a nonnegative constant potential (`matrix_local_bounds_of_continuous_trace_drift`). This auxiliary
result needs neither symmetry nor continuity of the individual principal entries.

## Main results

* `matrix_eqOn_const_of_isPreconnected_of_isMaxOn`: the strong maximum principle for symmetric
  matrix coefficients.
* `matrix_local_bounds_of_continuous_trace_drift`: local coefficient bounds from continuity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, Theorem 3 (Strong maximum principle), pp. 349-350,
  and Theorem 4 (Strong maximum principle with `c ≥ 0`), pp. 350-351.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open Metric Set
open scoped InnerProductSpace Topology

variable {n : ℕ}

/-- The sum of squared projections onto factors of a matrix is its quadratic form.
This identity transfers a principal ellipticity bound without any regularity assumption
on a choice of factors. -/
theorem sum_inner_sq_eq_matrix_quadratic
    {ι : Type*} [Fintype ι] (a : Matrix (Fin n) (Fin n) ℝ) (σ : ι → ℝ^n)
    (hfactor : ∀ i j, a i j = ∑ k, σ k i * σ k j) (v : ℝ^n) :
    ∑ k, ⟪v, σ k⟫_ℝ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, a i j * v i * v j := by
  have hinner (k : ι) : ⟪v, σ k⟫_ℝ = ∑ i : Fin n, σ k i * v i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp_rw [hinner, pow_two, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfactor i j, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The total squared norm of factors of a principal matrix equals its trace.
An upper trace bound therefore gives exactly the factor bound used by the radial barrier. -/
theorem sum_norm_sq_eq_matrix_trace
    {ι : Type*} [Fintype ι] (a : Matrix (Fin n) (Fin n) ℝ) (σ : ι → ℝ^n)
    (hfactor : ∀ i j, a i j = ∑ k, σ k i * σ k j) :
    ∑ k, ‖σ k‖ ^ 2 = ∑ i : Fin n, a i i := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [hfactor i i]
  simp only [pow_two]

/-- The strong maximum principle for symmetric matrix coefficients with local uniform
ellipticity and locally bounded trace, drift, and nonnegative potential. The principal
factors are constructed from the matrix. A compatible attained maximum is constant on
the connected domain, including maxima of either sign when the potential vanishes. -/
theorem matrix_eqOn_const_of_isPreconnected_of_isMaxOn
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (ha : ∀ x ∈ Ω, (a x).IsHermitian)
    (hlocal : ∀ p ∈ Ω, ∃ r κ A B C : ℝ,
      0 < r ∧ 0 < κ ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ closedBall p r ⊆ Ω ∧
      ∀ x ∈ ball p r,
        (∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤
          ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j) ∧
        (∑ i : Fin n, a x i i) ≤ A ∧ ‖b x‖ ≤ B ∧ 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, matrixOperator a b c u x ≤ 0)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Ω) (hmax : IsMaxOn u Ω x₀)
    (hcM : ∀ x ∈ Ω, 0 ≤ c x * u x₀) :
    Set.EqOn u (fun _ ↦ u x₀) Ω := by
  classical
  have hpositive (x : ℝ^n) (hx : x ∈ Ω) : (a x).PosSemidef := by
    obtain ⟨r, κ, _, _, _, hr, hκ, _, _, _, _, hcoeff⟩ := hlocal x hx
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (ha x hx)
    intro v
    have hbound := (hcoeff x (mem_ball_self hr)).1 (WithLp.toLp 2 v)
    have hquad : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j :=
      (mul_nonneg hκ.le (sq_nonneg ‖WithLp.toLp 2 v‖)).trans hbound
    change 0 ≤ ∑ i : Fin n, v i * ∑ j : Fin n, a x i j * v j
    calc
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j := hquad
      _ = ∑ i : Fin n, v i * ∑ j : Fin n, a x i j * v j := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hex : ∀ x, ∃ σ : Fin n → ℝ^n,
      ∀ _ : x ∈ Ω, ∀ i j, a x i j = ∑ k, σ k i * σ k j := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨σ, hσ⟩ := exists_factors_of_posSemidef (hpositive x hx)
      exact ⟨σ, fun _ ↦ hσ⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ False.elim (hx h)⟩
  choose σ hσ using hex
  refine eqOn_const_of_isPreconnected_of_isMaxOn hΩopen hΩconn σ b c ?_
    hureg ?_ hx₀ hmax hcM
  · intro p hp
    obtain ⟨r, κ, A, B, C, hr, hκ, hA, hB, hC, hclosed, hcoeff⟩ := hlocal p hp
    refine ⟨r, κ, A, B, C, hr, hκ, hA, hB, hC, hclosed, ?_⟩
    intro x hx
    have hxΩ := hclosed (ball_subset_closedBall hx)
    obtain ⟨helliptic, htrace, hdrift, hc, hcupper⟩ := hcoeff x hx
    refine ⟨?_, ?_, hdrift, hc, hcupper⟩
    · intro v
      rw [sum_inner_sq_eq_matrix_quadratic (a x) (σ x) (hσ x hxΩ)]
      exact helliptic v
    · rw [sum_norm_sq_eq_matrix_trace (a x) (σ x) (hσ x hxΩ)]
      exact htrace
  · intro x hx
    rw [← matrixOperator_eq_factoredOperator a σ b c (hureg x hx) (hσ x hx)]
    exact hsub x hx

variable {Ω : Set (ℝ^n)}

/-- Continuous principal trace and drift are bounded on sufficiently small closed balls.
Together with uniform quadratic ellipticity and a nonnegative constant potential, these
are the local coefficient hypotheses of the matrix strong maximum principle. -/
theorem matrix_local_bounds_of_continuous_trace_drift
    (hΩ : IsOpen Ω) (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    (htrace : ContinuousOn (fun x ↦ ∑ i : Fin n, a x i i) Ω)
    (hb : ContinuousOn b Ω) {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ x ∈ Ω, ∀ v : ℝ^n,
      alpha * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j)
    (c : ℝ) (hc : 0 ≤ c) :
    ∀ p ∈ Ω, ∃ r κ A B C : ℝ,
      0 < r ∧ 0 < κ ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ closedBall p r ⊆ Ω ∧
      ∀ x ∈ ball p r,
        (∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤
          ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j) ∧
        (∑ i : Fin n, a x i i) ≤ A ∧ ‖b x‖ ≤ B ∧ 0 ≤ c ∧ c ≤ C := by
  intro p hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
  have hclosed : closedBall p (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨A, hA⟩ := (isCompact_closedBall p (r / 2)).exists_bound_of_continuousOn
    (htrace.mono hclosed)
  obtain ⟨B, hB⟩ := (isCompact_closedBall p (r / 2)).exists_bound_of_continuousOn
    (hb.mono hclosed)
  have hpclosed : p ∈ closedBall p (r / 2) := mem_closedBall_self (half_pos hr).le
  refine ⟨r / 2, alpha, A, B, c, half_pos hr, halpha,
    (norm_nonneg _).trans (hA p hpclosed), (norm_nonneg _).trans (hB p hpclosed),
    hc, hclosed, ?_⟩
  intro x hx
  have hxclosed := ball_subset_closedBall hx
  refine ⟨helliptic x (hclosed hxclosed), ?_, hB x hxclosed, hc, le_rfl⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hA x hxclosed)

end EllipticMaximum
