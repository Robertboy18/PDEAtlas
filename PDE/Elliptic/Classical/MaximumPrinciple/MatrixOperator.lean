/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.Weak
public import PDE.FDeriv.Calculus.SecondDirectionalDerivative
public import PDE.Analysis.Calculus.MatrixHessian
import Mathlib.Analysis.Matrix.Order

/-!
# Maximum principles for matrix coefficients

The coordinate operator is Evans's nondivergence form (2) in §6.4,

`Lu = -∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + Du[b] + cu`.

Mathlib factors a positive semidefinite real matrix as `BᵀB`. Its rows provide the directions used
by the factored operator, and the Hessian identity identifies their residuals. The factors are
constructed, rather than required as additional coefficient data.

For the weak maximum principle, positive semidefiniteness and a uniform positive bound on one
diagonal entry suffice, together with an upper drift bound in that direction. These are the two
properties of `(aᵢⱼ)` that Evans's proof of §6.4.1, Theorem 1 uses: the sign (10) at an interior
maximum, and `a¹¹ ≥ θ` in step 4. Uniformly elliptic symmetric matrices satisfy the principal-part
assumptions. No continuity of the matrix entries or of the chosen factors is needed.

## Main definitions

* `matrixOperator`: the operator with principal matrix `a`, drift `b` and potential `c`.

## Main results

* `matrixOperator_eq_neg_sum_partialDeriv_flux`: expanding a divergence-form operator gives the
  nondivergence form with drift `bⱼ = -∑ᵢ ∂ᵢaᵢⱼ`.
* `exists_factors_of_posSemidef`, `matrixOperator_eq_factoredOperator`: the factorization and the
  operator identity.
* `matrix_subsolution_le_of_boundary_le_of_nonneg_mul`, `matrix_subsolution_le_of_boundary_le`: the
  weak maximum principles.
* `matrix_le_of_operator_le_of_boundary_le`: comparison of two classical functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4, the nondivergence form (2), p. 344, and §6.4.1,
  Theorem 1 (Weak maximum principle) and Theorem 2 (Weak maximum principle for `c ≥ 0`), with their
  proofs, pp. 344-347.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open PDE.Analysis Set
open scoped MatrixOrder Gradient

variable {n : ℕ}

/-- The classical nondivergence operator with a matrix principal coefficient.
The coefficient entries multiply the second partials; they are not differentiated. -/
def matrixOperator (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (u : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  -(∑ i : Fin n, ∑ j : Fin n, a x i j * (∂[i] (∂[j] u)) x) +
    fderiv ℝ u x (b x) + c x * u x

/-- Evaluate the matrix operator in coordinates, including its drift and potential.
This public formula supports calculations across module boundaries. -/
theorem matrixOperator_apply
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (u : ℝ^n → ℝ) (x : ℝ^n) :
    matrixOperator a b c u x =
      -(∑ i : Fin n, ∑ j : Fin n, a x i j * (∂[i] (∂[j] u)) x) +
        fderiv ℝ u x (b x) + c x * u x :=
  rfl

/-- The nondivergence operator is a weighted Hessian trace plus drift
and potential. Only the field is differentiated. -/
theorem matrixOperator_eq_neg_trace
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u : ℝ^n → ℝ} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x) :
    matrixOperator a b c u x =
      -LinearMap.trace ℝ (ℝ^n)
        ((a x).toEuclideanLin.comp (fderiv ℝ (∇ u) x).toLinearMap) +
          fderiv ℝ u x (b x) + c x * u x := by
  rw [trace_toEuclideanLin_comp_fderiv_gradient _ hu]
  rfl

/-- Expanding a classical divergence-form operator gives its nondivergence principal
part and the drift `bⱼ = -∑ᵢ ∂ᵢaᵢⱼ`. Only pointwise `C¹` coefficient regularity and
`C²` regularity of the field are needed; the matrix need not be symmetric. -/
theorem matrixOperator_eq_neg_sum_partialDeriv_flux
    (a : Fin n → Fin n → ℝ^n → ℝ) {f : ℝ^n → ℝ} {x : ℝ^n}
    (ha : ∀ i j, ContDiffAt ℝ 1 (a i j) x) (hf : ContDiffAt ℝ 2 f x) :
    matrixOperator (fun y i j ↦ a i j y)
      (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
      (fun _ ↦ 0) f x =
        -(∑ i : Fin n, ∑ j : Fin n,
          (∂[i] (fun y ↦ a i j y * (∂[j] f) y)) x) := by
  have hproduct (i j : Fin n) :
      (∂[i] (fun y ↦ a i j y * (∂[j] f) y)) x =
        (∂[i] (a i j)) x * (∂[j] f) x +
          a i j x * (∂[i] (∂[j] f)) x :=
    PDE.partialDeriv_mul ((ha i j).differentiableAt (by norm_num))
      ((PDE.contDiffAt_partialDeriv 1 hf j).differentiableAt (by norm_num))
  have hdrift :
      (∑ j : Fin n, (∂[j] f) x * -(∑ i, (∂[i] (a i j)) x)) =
        -(∑ i : Fin n, ∑ j : Fin n,
          (∂[i] (a i j)) x * (∂[j] f) x) := by
    simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  let A : ℝ^n → Matrix (Fin n) (Fin n) ℝ := fun y i j ↦ a i j y
  let b : ℝ^n → ℝ^n :=
    fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y))
  refine (matrixOperator_apply A b (fun _ ↦ 0) f x).trans ?_
  change -(∑ i : Fin n, ∑ j : Fin n, a i j x *
      (∂[i] (∂[j] f)) x) + fderiv ℝ f x (b x) + 0 * f x = _
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  change -(∑ i : Fin n, ∑ j : Fin n, a i j x *
      (∂[i] (∂[j] f)) x) +
      (∑ j : Fin n, (∂[j] f) x * -(∑ i, (∂[i] (a i j)) x)) +
      0 * f x = _
  simp only [hproduct, Finset.sum_add_distrib, hdrift, zero_mul, add_zero]
  ring

/-- A positive semidefinite real matrix is a sum of outer products of Euclidean vectors.
This is Mathlib's positive factorization, written in the coordinates used by the PDE operator. -/
theorem exists_factors_of_posSemidef {a : Matrix (Fin n) (Fin n) ℝ}
    (ha : a.PosSemidef) :
    ∃ σ : Fin n → ℝ^n, ∀ i j, a i j = ∑ k, σ k i * σ k j := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha.nonneg
  refine ⟨fun k ↦ WithLp.toLp 2 (B k), ?_⟩
  intro i j
  change (star B * B) i j = ∑ k, B k i * B k j
  simp [Matrix.mul_apply]

/-- The coordinate and factored operators have the same residual at a `C²` point whenever
the factors represent the principal matrix there. -/
theorem matrixOperator_eq_factoredOperator
    {ι : Type*} [Fintype ι] (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ)
    (σ : ℝ^n → ι → ℝ^n) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u : ℝ^n → ℝ} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x)
    (hfactor : ∀ i j, a x i j = ∑ k, σ x k i * σ x k j) :
    matrixOperator a b c u x = factoredOperator σ b c u x := by
  simp only [matrixOperator, factoredOperator, sum_secondDirectionalDerivative_eq_sum _ hu,
    hfactor]

/-- A compatible boundary bound controls a matrix subsolution on the closure.
The matrix is positive semidefinite, one diagonal entry is bounded below by a positive
constant, and the corresponding drift component is bounded above. The condition `cM ≥ 0`
allows boundary bounds of either sign when the potential vanishes. -/
theorem matrix_subsolution_le_of_boundary_le_of_nonneg_mul
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (i : Fin n) {α B : ℝ} (hα : 0 < α)
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hprincipal : ∀ x ∈ Ω, α ≤ a x i i)
    (hdrift : ∀ x ∈ Ω, b x i ≤ B)
    {u : ℝ^n → ℝ} {M : ℝ}
    (hc : ∀ x ∈ Ω, 0 ≤ c x) (hcM : ∀ x ∈ Ω, 0 ≤ c x * M)
    (hucont : ContinuousOn u (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, matrixOperator a b c u x ≤ 0)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, u x ≤ M := by
  classical
  have hex : ∀ x, ∃ σ : Fin n → ℝ^n,
      ∀ _ : x ∈ Ω, ∀ j k, a x j k = ∑ l, σ l j * σ l k := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨σ, hσ⟩ := exists_factors_of_posSemidef (ha x hx)
      exact ⟨σ, fun _ ↦ hσ⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ False.elim (hx h)⟩
  choose σ hσ using hex
  have hprincipal' : ∀ x ∈ Ω,
      α ≤ ∑ k, ((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) (σ x k)) ^ 2 := by
    intro x hx
    change α ≤ ∑ k, (σ x k i) ^ 2
    have h := hprincipal x hx
    rw [hσ x hx i i] at h
    simpa only [pow_two] using h
  apply subsolution_le_of_boundary_le_of_nonneg_mul hΩopen hΩcompact σ b c
    (EuclideanSpace.proj i) hα hprincipal' hdrift hc hcM hucont hureg
  · intro x hx
    rw [← matrixOperator_eq_factoredOperator a σ b c (hureg x hx) (hσ x hx)]
    exact hsub x hx
  · exact hboundary

/-- For nonnegative potential, any nonnegative boundary upper bound controls a matrix
subsolution on the whole closure. -/
theorem matrix_subsolution_le_of_boundary_le
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (i : Fin n) {α B : ℝ} (hα : 0 < α)
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hprincipal : ∀ x ∈ Ω, α ≤ a x i i)
    (hdrift : ∀ x ∈ Ω, b x i ≤ B)
    {u : ℝ^n → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ x ∈ Ω, 0 ≤ c x)
    (hucont : ContinuousOn u (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, matrixOperator a b c u x ≤ 0)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, u x ≤ M :=
  matrix_subsolution_le_of_boundary_le_of_nonneg_mul hΩopen hΩcompact a b c i hα
    ha hprincipal hdrift hc (fun x hx ↦ mul_nonneg (hc x hx) hM)
    hucont hureg hsub hboundary

/-- Only the potential contributes to the residual of a constant. -/
theorem matrixOperator_const
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (m : ℝ) (x : ℝ^n) :
    matrixOperator a b c (fun _ ↦ m) x = c x * m := by
  have hfirst (j : Fin n) : ∂[j] (fun _ : ℝ^n ↦ m) = fun _ ↦ 0 := by
    funext y
    exact PDE.partialDeriv_const m
  simp [matrixOperator, hfirst]

/-- The matrix operator commutes with scalar multiplication at a differentiability point. -/
theorem matrixOperator_const_mul
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u : ℝ^n → ℝ} {x : ℝ^n} (hu : DifferentiableAt ℝ u x) (m : ℝ) :
    matrixOperator a b c (fun y ↦ m * u y) x = m * matrixOperator a b c u x := by
  have hfirst (j : Fin n) :
      ∂[j] (fun y ↦ m * u y) = fun y ↦ m * (∂[j] u) y := by
    funext y
    exact PDE.partialDeriv_const_smul m
  have hderiv : fderiv ℝ (fun y ↦ m * u y) x = m • fderiv ℝ u x :=
    fderiv_fun_const_smul hu m
  have hsecond (i j : Fin n) :
      (∂[i] (∂[j] (fun y ↦ m * u y))) x =
        m * (∂[i] (∂[j] u)) x := by
    rw [hfirst]
    exact PDE.partialDeriv_const_smul m
  simp only [matrixOperator, hsecond, hderiv, smul_apply, smul_eq_mul]
  simp only [mul_left_comm _ m, ← Finset.mul_sum]
  ring

/-- The matrix operator commutes with subtraction at a common `C²` point. -/
theorem matrixOperator_sub
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u v : ℝ^n → ℝ} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x)
    (hv : ContDiffAt ℝ 2 v x) :
    matrixOperator a b c (fun y ↦ u y - v y) x =
      matrixOperator a b c u x - matrixOperator a b c v x := by
  have hd : fderiv ℝ (fun y ↦ u y - v y) x = fderiv ℝ u x - fderiv ℝ v x :=
    fderiv_sub (hu.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num))
  simp only [matrixOperator, PDE.secondPartialDeriv_sub _ _ hu hv, hd,
    sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Ordered matrix residuals and boundary values order two classical functions
throughout the closure. -/
theorem matrix_le_of_operator_le_of_boundary_le
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (i : Fin n) {α B : ℝ} (hα : 0 < α)
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hprincipal : ∀ x ∈ Ω, α ≤ a x i i)
    (hdrift : ∀ x ∈ Ω, b x i ≤ B)
    {u v : ℝ^n → ℝ} (hc : ∀ x ∈ Ω, 0 ≤ c x)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hvreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hoperator : ∀ x ∈ Ω, matrixOperator a b c u x ≤ matrixOperator a b c v x)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ closure Ω, u x ≤ v x := by
  have hsub : ∀ x ∈ Ω, matrixOperator a b c (fun y ↦ u y - v y) x ≤ 0 := by
    intro x hx
    rw [matrixOperator_sub a b c (hureg x hx) (hvreg x hx)]
    exact sub_nonpos.mpr (hoperator x hx)
  have h := matrix_subsolution_le_of_boundary_le hΩopen hΩcompact a b c i hα
    ha hprincipal hdrift (M := 0) le_rfl hc (hucont.sub hvcont)
    (fun x hx ↦ (hureg x hx).sub (hvreg x hx)) hsub
    (fun x hx ↦ sub_nonpos.mpr (hboundary x hx))
  exact fun x hx ↦ sub_nonpos.mp (h x hx)

end EllipticMaximum
