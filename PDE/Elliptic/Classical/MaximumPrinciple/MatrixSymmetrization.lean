/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixStrong

/-!
# Classical maximum principles without coefficient symmetry

The classical nondivergence operator only sees the symmetric part of its principal matrix: the
antisymmetric part contracts to zero against the Hessian of a `C²` function. We use Mathlib's
`selfAdjointPart ℝ`, whose value on a real matrix is half the sum of the matrix and its transpose.
Evans assumes the symmetry `aᵢⱼ = aⱼᵢ` without loss of generality after his (2) in §6.4; the
identities here carry out that reduction for classical solutions.

Symmetrization preserves the quadratic form, every diagonal entry, and the trace. The strong maximum
principle therefore extends to arbitrary real principal matrices under exactly the same local
quadratic ellipticity and trace bounds. The attained maximum must satisfy `cM ≥ 0`, and the
potential must be nonnegative. Neither coefficient continuity nor a bound on the antisymmetric part
is required.

For the weak maximum principle, nonnegativity of the quadratic form and a uniform positive lower
bound on one diagonal entry suffice, together with an upper bound for the corresponding drift
component. These are the principal and drift hypotheses of the symmetric theorem in
`MaximumPrinciple.MatrixOperator`, expressed without assuming matrix symmetry.

The Hessian symmetry comes from the coordinate mixed-partial theorem, which is proved from Mathlib's
`ContDiffAt.isSymmSndFDerivAt`.

## Main results

* `matrixOperator_selfAdjointPart`: at a `C²` point the operator is unchanged by symmetrizing the
  principal matrix.
* `matrix_quadratic_selfAdjointPart`, `matrix_trace_selfAdjointPart`,
  `matrix_selfAdjointPart_apply_diag`: symmetrization preserves the quadratic form, the trace and
  the diagonal.
* `matrix_eqOn_const_of_isPreconnected_of_isMaxOn_of_elliptic`: the strong maximum principle for
  arbitrary real principal matrices.
* `matrix_subsolution_le_of_boundary_le_of_nonneg_quadratic`: the weak maximum principle for
  arbitrary real principal matrices.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4, the nondivergence form (2) and the symmetry condition,
  p. 344; §6.4.1, Theorems 1-2, pp. 344-347; §6.4.2, Theorems 3-4, pp. 349-351.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open Metric Set
open scoped Topology

/-- The real scalar two is invertible, as needed by `selfAdjointPart ℝ`. -/
local instance invertibleRealTwo : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

variable {n : ℕ}

/-- Mathlib's self-adjoint part averages the two transposed entries of a real matrix. -/
theorem matrix_selfAdjointPart_apply (a : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i j =
      (a i j + a j i) / 2 := by
  rw [selfAdjointPart_apply_coe]
  change (⅟(2 : ℝ)) * (a i j + a j i) = (a i j + a j i) / 2
  simp only [invOf_eq_inv, div_eq_mul_inv, mul_comm]

/-- Symmetrization leaves every diagonal coefficient unchanged. -/
theorem matrix_selfAdjointPart_apply_diag (a : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i i = a i i := by
  rw [matrix_selfAdjointPart_apply, add_self_div_two]

/-- Contracting a real matrix against symmetric weights ignores its antisymmetric part. -/
theorem sum_selfAdjointPart_mul_of_isSymm
    (a H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ i : Fin n, ∑ j : Fin n,
      (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i j * H i j) =
      ∑ i : Fin n, ∑ j : Fin n, a i j * H i j := by
  have htranspose :
      (∑ i : Fin n, ∑ j : Fin n, a j i * H i j) =
        ∑ i : Fin n, ∑ j : Fin n, a i j * H i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hH.apply i j]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i j * H i j) =
        ((∑ i : Fin n, ∑ j : Fin n, a i j * H i j) +
          (∑ i : Fin n, ∑ j : Fin n, a j i * H i j)) / 2 := by
      simp only [matrix_selfAdjointPart_apply, div_mul_eq_mul_div₀, add_mul, add_div,
        Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ i : Fin n, ∑ j : Fin n, a i j * H i j := by
      rw [htranspose, add_self_div_two]

/-- A real matrix and its self-adjoint part define the same quadratic form. -/
theorem matrix_quadratic_selfAdjointPart
    (a : Matrix (Fin n) (Fin n) ℝ) (v : ℝ^n) :
    (∑ i : Fin n, ∑ j : Fin n,
      (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i j * v i * v j) =
      ∑ i : Fin n, ∑ j : Fin n, a i j * v i * v j := by
  have hweights : Matrix.IsSymm (fun i j : Fin n ↦ v i * v j) :=
    Matrix.IsSymm.ext fun i j ↦ mul_comm (v j) (v i)
  simpa only [mul_assoc] using
    sum_selfAdjointPart_mul_of_isSymm a (fun i j ↦ v i * v j) hweights

/-- The trace of a real matrix is unchanged by taking its self-adjoint part. -/
theorem matrix_trace_selfAdjointPart (a : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) = Matrix.trace a := by
  change (∑ i : Fin n, (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i i) =
    ∑ i : Fin n, a i i
  simp only [matrix_selfAdjointPart_apply_diag]

/-- At a `C²` point, the classical matrix operator is unchanged by symmetrizing the
principal coefficient. No coefficient is differentiated in this identity. -/
theorem matrixOperator_selfAdjointPart
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u : ℝ^n → ℝ} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x) :
    matrixOperator
        (fun y ↦ (selfAdjointPart ℝ (a y) : Matrix (Fin n) (Fin n) ℝ)) b c u x =
      matrixOperator a b c u x := by
  have hhessian :
      Matrix.IsSymm (fun i j : Fin n ↦ (∂[i] (∂[j] u)) x) :=
    Matrix.IsSymm.ext fun i j ↦ PDE.partialDeriv_partialDeriv_comm_at j i hu
  simp only [matrixOperator]
  rw [sum_selfAdjointPart_mul_of_isSymm (a x) _ hhessian]

/-- Nonnegativity of a real quadratic form makes the self-adjoint part of its coefficient
matrix positive semidefinite, even when the original matrix is not symmetric. -/
theorem posSemidef_selfAdjointPart_of_nonneg_quadratic
    (a : Matrix (Fin n) (Fin n) ℝ)
    (hquad : ∀ v : ℝ^n, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i j * v i * v j) :
    (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (show (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ).IsHermitian from
      (selfAdjointPart ℝ a).property)
  intro v
  have hq := hquad (WithLp.toLp 2 v)
  rw [← matrix_quadratic_selfAdjointPart a (WithLp.toLp 2 v)] at hq
  change 0 ≤ ∑ i : Fin n, v i *
    ∑ j : Fin n, (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i j * v j
  calc
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i j * v i * v j := hq
    _ = ∑ i : Fin n, v i *
        ∑ j : Fin n, (selfAdjointPart ℝ a : Matrix (Fin n) (Fin n) ℝ) i j * v j := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- Strong maximum principle for arbitrary real principal matrices. Local quadratic
ellipticity and upper bounds for the trace, drift norm, and nonnegative potential suffice.
The maximum is attained in the open connected domain and satisfies `cM ≥ 0`; no symmetry
or coefficient continuity is assumed. -/
theorem matrix_eqOn_const_of_isPreconnected_of_isMaxOn_of_elliptic
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
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
  let s : ℝ^n → Matrix (Fin n) (Fin n) ℝ :=
    fun x ↦ (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ)
  refine matrix_eqOn_const_of_isPreconnected_of_isMaxOn hΩopen hΩconn s b c ?_ ?_
    hureg ?_ hx₀ hmax hcM
  · intro x _
    exact (selfAdjointPart ℝ (a x)).property
  · intro p hp
    obtain ⟨r, κ, A, B, C, hr, hκ, hA, hB, hC, hclosed, hcoeff⟩ := hlocal p hp
    refine ⟨r, κ, A, B, C, hr, hκ, hA, hB, hC, hclosed, ?_⟩
    intro x hx
    obtain ⟨helliptic, htrace, hdrift, hc, hcupper⟩ := hcoeff x hx
    refine ⟨?_, ?_, hdrift, hc, hcupper⟩
    · intro v
      change κ * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n,
        (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ) i j * v i * v j
      rw [matrix_quadratic_selfAdjointPart]
      exact helliptic v
    · change (∑ i : Fin n,
        (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ) i i) ≤ A
      simpa only [matrix_selfAdjointPart_apply_diag] using htrace
  · intro x hx
    change matrixOperator
      (fun y ↦ (selfAdjointPart ℝ (a y) : Matrix (Fin n) (Fin n) ℝ)) b c u x ≤ 0
    rw [matrixOperator_selfAdjointPart a b c (hureg x hx)]
    exact hsub x hx

/-- Weak maximum principle for arbitrary real principal matrices whose quadratic forms
are nonnegative. A uniform positive bound on one diagonal entry and an upper bound on the
corresponding drift component suffice. The boundary bound obeys `cM ≥ 0`, so bounds of
either sign are allowed when the potential vanishes. -/
theorem matrix_subsolution_le_of_boundary_le_of_nonneg_quadratic
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (i : Fin n) {α B : ℝ} (hα : 0 < α)
    (hquad : ∀ x ∈ Ω, ∀ v : ℝ^n,
      0 ≤ ∑ j : Fin n, ∑ k : Fin n, a x j k * v j * v k)
    (hprincipal : ∀ x ∈ Ω, α ≤ a x i i)
    (hdrift : ∀ x ∈ Ω, b x i ≤ B)
    {u : ℝ^n → ℝ} {M : ℝ}
    (hc : ∀ x ∈ Ω, 0 ≤ c x) (hcM : ∀ x ∈ Ω, 0 ≤ c x * M)
    (hucont : ContinuousOn u (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, matrixOperator a b c u x ≤ 0)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, u x ≤ M := by
  let s : ℝ^n → Matrix (Fin n) (Fin n) ℝ :=
    fun x ↦ (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ)
  refine matrix_subsolution_le_of_boundary_le_of_nonneg_mul hΩopen hΩcompact s b c i hα
    (fun x hx ↦ posSemidef_selfAdjointPart_of_nonneg_quadratic (a x) (hquad x hx))
    ?_ hdrift hc hcM hucont hureg ?_ hboundary
  · intro x hx
    change α ≤ (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ) i i
    rw [matrix_selfAdjointPart_apply_diag]
    exact hprincipal x hx
  · intro x hx
    change matrixOperator
      (fun y ↦ (selfAdjointPart ℝ (a y) : Matrix (Fin n) (Fin n) ℝ)) b c u x ≤ 0
    rw [matrixOperator_selfAdjointPart a b c (hureg x hx)]
    exact hsub x hx

end EllipticMaximum
