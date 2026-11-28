/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import PDE.Analysis.Operator.MethodOfContinuity

/-!
# A finite-rank determinant criterion for a real eigenvalue

## Motivation

When does the sign of one `m × m` determinant prove that a linear operator has a real negative
eigenvalue?

Let `D` be a subspace of a real normed space `E` and let `L⋆ : D → E*` be linear, for example the
weak realization of a differential operator on its domain. Let `ℓ : E → ℝ^m` be bounded and
linear, with transpose `ℓ† q = ⟪q, ℓ ·⟫` (`coordTranspose ℓ`), let `Φ : ℝ^m → D` be linear, and
let `J : E → E*` be a bounded form, the `L²` pairing when `E` is embedded in `L²`. Assume that
`L⋆ + ℓ† ℓ` maps `D` onto `E*` and that for some `a, c_F > 0`

* `⟪L⋆ h, h⟫ + ‖ℓ h‖² ≥ a ‖h‖²` for all `h` in `D`,
* `⟪L⋆ (h + Φ ℓ h), h⟫ ≥ a ‖h‖²` for all `h` in `D`,
* `‖ℓ h‖² ≤ c_F ⟪J h, h⟫` for all `h` in `E`.

If `det (1 + ℓ Φ) < 0`, then `L⋆ h = λ J h` for some `-c_F < λ < 0` and some nonzero `h` in `D`.
This is `exists_eigenvalue_of_det_neg`. The equation holds in `E*`, so it is the weak form of
the eigenvalue equation with the pairing `J` on the right.

For the self-similar Navier–Stokes linearization, `J` is the `L²` pairing and `L⋆` is the
linearized operator at the exact profile, with the sign for which an unstable eigenvalue is
negative. If the hypotheses hold for this operator, the criterion gives a real unstable
eigenvalue in `(-c_F, 0)` from the sign of one determinant. Hou, Wang and Yang obtain an unstable
eigenpair of this linearization (their Proposition 2) by a fixed-point argument built on a
finite-rank approximation (their Sections 4.2 and 4.4); the determinant criterion is a different
route to an unstable eigenvalue.

## The idea

The argument uses only `m × m` determinants.

* The third inequality makes `J` positive, in the sense that `⟪J h, h⟫ ≥ 0` for all `h`; symmetry
  of `J` is not needed. So for `μ ≥ 0` the operator `A_μ = L⋆ + ℓ† ℓ + μ J` is coercive on `D`
  with constant `a` (`coercive_shiftedOperator`).
* `A_μ` maps `D` onto `E*`. This is assumed at `μ = 0`, and the method of continuity on the
  complete space `E*` carries it to every `μ ≥ 0`: `A_μ = (1 + μ J A_0⁻¹) A_0`, and the operators
  `1 + t μ J A_0⁻¹` with `0 ≤ t ≤ 1` are bounded below with one constant
  (`surjective_add_of_coercive_add`, `surjective_shiftedOperator_of_nonneg`).
* The inverses `A_μ⁻¹` have norm at most `1 / a` (`norm_coerciveInverse_le`), and a resolvent
  estimate makes the matrix `M(μ) = ℓ A_μ⁻¹ ℓ†` (`compressionMatrix`) continuous in `μ`.
* At a zero `μ` of `d(μ) = det (1 - M(μ))` the operator `L⋆ + μ J` has a nonzero kernel vector in
  `D` (`exists_ne_zero_of_det_one_sub_compressionMatrix_eq_zero`).
* For `μ > c_F` the matrices `1 - s M(μ)` with `0 ≤ s ≤ 1` are nonsingular, so `d(μ) > 0`
  (`det_one_sub_compressionMatrix_pos`).
* At `μ = 0`, the segment from `A_0` to `L⋆ (1 + Φ ℓ)` consists of coercive maps, by the first
  two inequalities, and each of them corresponds to a nonsingular matrix on the segment from `1`
  to `(1 - M(0)) (1 + ℓ Φ)`. Hence `d(0)` has the sign of `det (1 + ℓ Φ)`, which is negative
  (`det_mul_pos_of_coercive_homotopy`).
* The intermediate value theorem gives a zero `μ > 0` of `d`. The first and third inequalities
  give `μ < c_F` (`lt_of_apply_add_smul_eq_zero`), and `λ = -μ`.

Completeness of `E` is not needed, and no eigenpair is enclosed.

## Main results

Each statement holds for all real normed spaces `E`, subspaces `D` and maps with the stated
hypotheses.

* `exists_eigenvalue_of_det_neg`: the criterion above.
* `surjective_add_of_coercive_add`: if `A` is coercive on `D` and maps `D` onto `E*`, and `A + C`
  is coercive on `D` for a bounded form `C`, then `A + C` maps `D` onto `E*`.
* `surjective_shiftedOperator_of_nonneg`: if `P + ℓ† ℓ` is coercive on `D`, `J` is positive and
  `P + ℓ† ℓ + μ J` maps `D` onto `E*` for one `μ ≥ 0`, it does so for every `μ ≥ 0`.
* `exists_kernel_of_det_neg`: the perturbative form of the criterion. Let `L⋆ = L + C` with
  `‖C‖ ≤ ε`, let `L + ℓ† ℓ` be coercive with constant `1 - θ`, let the reconstruction have
  residual `‖L Φ ℓ - ℓ† ℓ‖ ≤ δ` and amplification `‖1 + Φ ℓ‖ ≤ t_G`, let `J` be positive with
  `‖ℓ h‖² ≤ c_F ⟪J h, h⟫`, and let `L + ℓ† ℓ + μ J` map `D` onto `E*` for every `μ ≥ 0`. If the
  margins `1 - θ - ε` and `1 - θ - δ - ε t_G` are positive and `det (1 + ℓ Φ) < 0`, then
  `L⋆ + μ J` has a nonzero kernel vector in `D` for some `0 < μ < c_F`.
  `exists_pos_kernel_of_det_neg` keeps only `μ > 0` of this conclusion.
* `coordinateMap` and `reconstruction` build `ℓ` from finitely many bounded functionals `F i` and
  `Φ` from finitely many fields `φ j`. The matrix `ℓ Φ` then has entries `F i (φ j)`,
  `det_one_add_eq_det_of_apply_single` identifies the determinant of the map `1 + ℓ Φ` with the
  determinant of the matrix, and `‖Φ q‖ ≤ ‖q‖ (∑ⱼ ‖φ j‖²)^{1/2}` (`norm_reconstruction_le`).

## Relations

* `exists_kernel_of_det_neg` is `exists_eigenvalue_of_det_neg` with
  `a = min (1 - θ - ε) (1 - θ - δ - ε t_G)` and `λ = -μ`: the first inequality holds with constant
  `1 - θ - ε`, the second with `1 - θ - δ - ε t_G` (`coercive_comp_reconstruction`), and
  `L⋆ + ℓ† ℓ` maps onto `E*` because `L + ℓ† ℓ` does and `‖C‖ < 1 - θ`
  (`surjective_shiftedOperator_of_perturbation`). The minimum is `1 - θ - δ - ε t_G` when
  `ε (1 - t_G) ≤ δ`. This is the case when `ℓ` vanishes at a nonzero vector, for example when the
  dimension of `E` exceeds `m`: the amplification bound then forces `t_G ≥ 1`, and the residual
  bound forces `δ ≥ 0`.
* `surjective_add_of_coercive_add` applies the method of continuity
  `bijective_of_uniform_bound_on_segment`, which is stated for bounded operators on a complete
  space, to the operators `1 + t C A⁻¹` on the dual space. `surjective_add_of_coercive` is its
  case `‖C‖ < κ`; `surjective_shiftedOperator_of_perturbation` and
  `surjective_shiftedOperator_of_nonneg` apply the two to the shifted operators.
* `FiniteRankDeterminantBounds` proves the residual and amplification hypotheses of
  `exists_kernel_of_det_neg` from Gram matrices.
* `PDE/Examples/Analysis/Operator/FiniteRankDeterminant.lean` states the criterion for a space
  with a bounded map into an inner product space, checks every hypothesis on every real Hilbert
  space with a unit vector, and proves the statement above on the constant `a` of the
  perturbative form.

## What stays open

The criterion gives one real eigenvalue in `(-c_F, 0)`. It does not locate the eigenvalue more
precisely, and it says nothing about its multiplicity or about other eigenvalues. The third
inequality cannot be dropped; the docstring of `exists_kernel_of_det_neg` has an example. For a
given operator the ontoness of `L⋆ + ℓ† ℓ`, the two coercivity inequalities, the constant `c_F`
and the sign of the determinant have to be proved separately; this library does not prove them
for the Navier–Stokes linearization.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v3, Section 1.3 (the sign of the
  linearized operator in (1.12)), Proposition 2 in Section 1.4, and Sections 4.2 and 4.4.
  <https://arxiv.org/abs/2509.25116v3>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open Set
open scoped Matrix RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

section Transpose

/-- The transpose of a coordinate map, with `ℝ^m` identified with its dual by the
Euclidean inner product: `coordTranspose ℓ q h = ⟪q, ℓ h⟫`. -/
def coordTranspose (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] StrongDual ℝ E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q ↦ (innerSL ℝ q).comp ℓ
      map_add' := fun p q ↦ by ext h; simp
      map_smul' := fun c q ↦ by ext h; simp }

/-- The functional `coordTranspose ℓ q` sends `h` to the inner product `⟪q, ℓ h⟫`. -/
@[simp]
theorem coordTranspose_apply (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m)) (h : E) : coordTranspose ℓ q h = ⟪q, ℓ h⟫ :=
  rfl

/-- On the diagonal, the finite-rank form `ℓ† ℓ` is the squared length of the coordinates. -/
theorem coordTranspose_apply_self (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (h : E) :
    coordTranspose ℓ (ℓ h) h = ‖ℓ h‖ ^ 2 := by
  simp

end Transpose

section Coordinates

/-- The coordinate map `h ↦ (F i h)ᵢ` of finitely many bounded functionals. -/
def coordinateMap (F : Fin m → StrongDual ℝ E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi F)

/-- The `i`-th coordinate of `coordinateMap F h` is `F i h`. -/
@[simp]
theorem coordinateMap_apply (F : Fin m → StrongDual ℝ E) (h : E) (i : Fin m) :
    coordinateMap F h i = F i h :=
  rfl

/-- The squared length of the coordinates is the sum of the squared functionals. -/
theorem norm_coordinateMap_sq (F : Fin m → StrongDual ℝ E) (h : E) :
    ‖coordinateMap F h‖ ^ 2 = ∑ i, F i h ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

/-- The transpose of a coordinate map is the combination of its functionals. -/
theorem coordTranspose_coordinateMap_apply (F : Fin m → StrongDual ℝ E)
    (q : EuclideanSpace ℝ (Fin m)) (h : E) :
    coordTranspose (coordinateMap F) q h = ∑ i, q i * F i h := by
  simp [PiLp.inner_apply, mul_comm]

/-- The reconstruction `q ↦ ∑ j, q j • φ j` from finitely many fields. -/
def reconstruction (φ : Fin m → E) : EuclideanSpace ℝ (Fin m) →L[ℝ] E :=
  ∑ j, (EuclideanSpace.proj j).smulRight (φ j)

/-- The map `reconstruction φ` sends `q` to the combination `∑ j, q j • φ j`. -/
theorem reconstruction_apply (φ : Fin m → E) (q : EuclideanSpace ℝ (Fin m)) :
    reconstruction φ q = ∑ j, q j • φ j := by
  simp [reconstruction]

/-- The map `reconstruction φ` sends the standard basis vector `EuclideanSpace.single j 1` to the
field `φ j`. -/
@[simp]
theorem reconstruction_single (φ : Fin m → E) (j : Fin m) :
    reconstruction φ (EuclideanSpace.single j 1) = φ j := by
  rw [reconstruction_apply]
  simp [EuclideanSpace.single]

/-- Fields in a subspace reconstruct into that subspace. -/
theorem reconstruction_mem {D : Submodule ℝ E} {φ : Fin m → E} (hφ : ∀ j, φ j ∈ D)
    (q : EuclideanSpace ℝ (Fin m)) : reconstruction φ q ∈ D := by
  rw [reconstruction_apply]
  exact D.sum_mem fun j _ ↦ D.smul_mem _ (hφ j)

/-- The norm of a reconstruction is at most the Euclidean length of its coefficients times
`(∑ⱼ ‖φⱼ‖²)^{1/2}`: `‖∑ⱼ qⱼ φⱼ‖ ≤ ∑ⱼ |qⱼ| ‖φⱼ‖` by the triangle inequality, and the
Cauchy–Schwarz inequality bounds the sum. -/
theorem norm_reconstruction_le (φ : Fin m → E) (q : EuclideanSpace ℝ (Fin m)) :
    ‖reconstruction φ q‖ ≤ ‖q‖ * √(∑ j, ‖φ j‖ ^ 2) := by
  rw [reconstruction_apply, EuclideanSpace.norm_eq]
  calc ‖∑ j, q j • φ j‖ ≤ ∑ j, ‖q j‖ * ‖φ j‖ :=
        (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ ↦ norm_smul _ _)
    _ ≤ √(∑ j, ‖q j‖ ^ 2) * √(∑ j, ‖φ j‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The matrix `ℓ Φ` of functionals and fields has entries `F i (φ j)`. -/
theorem coordinateMap_reconstruction_single (F : Fin m → StrongDual ℝ E) (φ : Fin m → E)
    (i j : Fin m) :
    coordinateMap F (reconstruction φ (EuclideanSpace.single j 1)) i = F i (φ j) := by
  simp

end Coordinates

section MatrixFacts

/-- A matrix whose columns are the images of the standard basis vectors acts as the
linear map. -/
theorem mulVec_eq_ofLp_of_apply_single
    (F : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : ∀ i j, P i j = F (EuclideanSpace.single j 1) i)
    (v : Fin m → ℝ) : P *ᵥ v = (F (WithLp.toLp 2 v)).ofLp := by
  ext i
  have hv : WithLp.toLp 2 v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  rw [hv, map_sum]
  simp [Matrix.mulVec, dotProduct, hP, mul_comm]

/-- The determinant of a linear map of a Euclidean space is the determinant of the matrix whose
columns are the images of the standard basis vectors. -/
theorem det_eq_det_of_apply_single {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) {P : Matrix ι ι 𝕜}
    (hP : ∀ i j, P i j = F (EuclideanSpace.single j 1) i) : LinearMap.det F = P.det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun ι 𝕜).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, hP]

/-- If `Λ` is the matrix of `G` in the standard basis of a Euclidean space, the linear map `1 + G`
and the matrix `1 + Λ` have the same determinant. -/
theorem det_one_add_eq_det_of_apply_single {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (G : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) {Λ : Matrix ι ι 𝕜}
    (hΛ : ∀ i j, Λ i j = G (EuclideanSpace.single j 1) i) :
    LinearMap.det (1 + G) = (1 + Λ).det :=
  det_eq_det_of_apply_single _ fun i j ↦ by simp [Matrix.one_apply, hΛ]

/-- A real matrix that stays nonsingular along the segment from `1` to `1 + N` keeps the
positive determinant of the identity. -/
theorem det_one_add_pos_of_forall_mulVec_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ)
    (hN : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : n → ℝ, (1 + s • N) *ᵥ v = 0 → v = 0) :
    0 < (1 + N).det := by
  by_contra hle
  push Not at hle
  have hcont : ContinuousOn (fun s : ℝ ↦ (1 + s • N).det) (Icc 0 1) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det.continuousOn
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont
    (show (0 : ℝ) ∈ Icc _ _ from ⟨by simpa using hle, by simp⟩)
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs0
  exact hv (hN s hs v hv0)

end MatrixFacts

section CoerciveInverse

variable {D : Submodule ℝ E} (A : D →ₗ[ℝ] StrongDual ℝ E) {κ : ℝ}

/-- A coercive form controls the norm of its argument by the dual norm of its value. -/
theorem mul_norm_le_norm_of_coercive (hA : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ A x x) (x : D) :
    κ * ‖(x : E)‖ ≤ ‖A x‖ := by
  have hpair : A x x ≤ ‖A x‖ * ‖(x : E)‖ := by
    have h := (A x).le_opNorm x
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  rcases (norm_nonneg (x : E)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have h := (hA x).trans hpair
    rw [pow_two, ← mul_assoc] at h
    exact le_of_mul_le_mul_right h hpos

/-- The inverse form of `mul_norm_le_norm_of_coercive`. -/
theorem norm_le_inv_mul_of_coercive (hκ : 0 < κ)
    (hA : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ A x x) (x : D) :
    ‖(x : E)‖ ≤ κ⁻¹ * ‖A x‖ :=
  (le_inv_mul_iff₀ hκ).2 (mul_norm_le_norm_of_coercive A hA x)

/-- A coercive linear map from a subspace into the dual space is injective. -/
theorem injective_of_coercive (hκ : 0 < κ) (hA : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ A x x) :
    Function.Injective A := by
  refine (injective_iff_map_eq_zero A).2 fun x hx ↦ ?_
  have h := norm_le_inv_mul_of_coercive A hκ hA x
  rw [hx, norm_zero, mul_zero] at h
  exact Subtype.ext (by simpa using norm_le_zero_iff.mp h)

variable (hκ : 0 < κ) (hA : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ A x x)
  (hsurj : Function.Surjective A)

/-- A coercive linear map from a subspace onto the dual space is a linear equivalence. -/
def coerciveEquiv : D ≃ₗ[ℝ] StrongDual ℝ E :=
  LinearEquiv.ofBijective A ⟨injective_of_coercive A hκ hA, hsurj⟩

/-- The equivalence `coerciveEquiv A hκ hA hsurj` sends `x` to `A x`. -/
@[simp]
theorem coerciveEquiv_apply (x : D) : coerciveEquiv A hκ hA hsurj x = A x :=
  rfl

/-- The inverse of `coerciveEquiv` solves the equation `A x = f`. -/
theorem apply_coerciveEquiv_symm (f : StrongDual ℝ E) :
    A ((coerciveEquiv A hκ hA hsurj).symm f) = f :=
  (coerciveEquiv A hκ hA hsurj).apply_symm_apply f

/-- The solution of `A x = f` has norm at most `κ⁻¹ ‖f‖`. -/
theorem norm_coerciveEquiv_symm_le (f : StrongDual ℝ E) :
    ‖((coerciveEquiv A hκ hA hsurj).symm f : E)‖ ≤ κ⁻¹ * ‖f‖ := by
  have h := norm_le_inv_mul_of_coercive A hκ hA ((coerciveEquiv A hκ hA hsurj).symm f)
  rwa [apply_coerciveEquiv_symm] at h

/-- The bounded inverse of a coercive linear map from a subspace onto the dual space,
as an operator into the ambient space. -/
def coerciveInverse : StrongDual ℝ E →L[ℝ] E :=
  (D.subtype ∘ₗ (coerciveEquiv A hκ hA hsurj).symm.toLinearMap).mkContinuous κ⁻¹
    (norm_coerciveEquiv_symm_le A hκ hA hsurj)

/-- The value of `coerciveInverse A hκ hA hsurj` at `f` is the vector
`(coerciveEquiv A hκ hA hsurj).symm f` of `D`, viewed in `E`. -/
theorem coerciveInverse_apply (f : StrongDual ℝ E) :
    coerciveInverse A hκ hA hsurj f = (coerciveEquiv A hκ hA hsurj).symm f :=
  rfl

/-- The inverse takes values in the subspace. -/
theorem coerciveInverse_mem (f : StrongDual ℝ E) : coerciveInverse A hκ hA hsurj f ∈ D :=
  ((coerciveEquiv A hκ hA hsurj).symm f).2

/-- The inverse is a right inverse of `A`. -/
theorem apply_coerciveInverse (f : StrongDual ℝ E) :
    A ⟨coerciveInverse A hκ hA hsurj f, coerciveInverse_mem A hκ hA hsurj f⟩ = f :=
  apply_coerciveEquiv_symm A hκ hA hsurj f

/-- Every solution of `A x = f` is the value of the inverse at `f`. -/
theorem coerciveInverse_eq (x : D) {f : StrongDual ℝ E} (hx : A x = f) :
    coerciveInverse A hκ hA hsurj f = x := by
  rw [coerciveInverse_apply, ← hx, ← coerciveEquiv_apply A hκ hA hsurj,
    LinearEquiv.symm_apply_apply]

/-- The inverse has operator norm at most `κ⁻¹`. -/
theorem norm_coerciveInverse_le : ‖coerciveInverse A hκ hA hsurj‖ ≤ κ⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.2 hκ.le) _

include hκ hA hsurj in
/-- **Continuation between coercive maps.** Let `A` be coercive on `D` and map `D` onto the dual
space. If `C` is a bounded form and `A + C` is coercive on `D`, then `A + C` maps `D` onto the
dual space; the norm of `C` may be large. This is the method of continuity on the dual space,
which is complete: with `S = A⁻¹`, the map `A + t C` is `(1 + t C S) A`, and the bounded operators
`1 + t C S` with `0 ≤ t ≤ 1` satisfy `‖u‖ ≤ (1 + ‖C‖ / c) ‖(1 + t C S) u‖`, where `c` is the
smaller of the two coercivity constants, because each `A + t C` is coercive with constant `c`.
Then `bijective_of_uniform_bound_on_segment` makes `1 + C S` onto. -/
theorem surjective_add_of_coercive_add (C : E →L[ℝ] StrongDual ℝ E) {κ' : ℝ} (hκ' : 0 < κ')
    (hAC : ∀ x : D, κ' * ‖(x : E)‖ ^ 2 ≤ A x x + C x x) :
    Function.Surjective (A + C.toLinearMap ∘ₗ D.subtype) := by
  -- One constant `c` serves the whole segment from `A` to `A + C`.
  obtain ⟨c, hc, hcκ, hcκ'⟩ : ∃ c, 0 < c ∧ c ≤ κ ∧ c ≤ κ' :=
    ⟨min κ κ', lt_min hκ hκ', min_le_left _ _, min_le_right _ _⟩
  set S := coerciveInverse A hκ hA hsurj
  -- The operators `1 + t C S` on the dual space are bounded below for `0 ≤ t ≤ 1`.
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : StrongDual ℝ E,
      ‖u‖ ≤ ((⟨1 + ‖C‖ / c, by positivity⟩ : NNReal) : ℝ) *
        ‖((1 - t) • ContinuousLinearMap.id ℝ (StrongDual ℝ E) +
          t • (ContinuousLinearMap.id ℝ (StrongDual ℝ E) + C.comp S)) u‖ := by
    intro t ht u
    -- The map `B = A + t C` is coercive with constant `c`.
    set B : D →ₗ[ℝ] StrongDual ℝ E := A + (t • C).toLinearMap ∘ₗ D.subtype with hBdef
    have hB : ∀ y : D, c * ‖(y : E)‖ ^ 2 ≤ B y y := fun y ↦ by
      have h0 := (mul_le_mul_of_nonneg_right hcκ (sq_nonneg ‖(y : E)‖)).trans (hA y)
      have h1 := (mul_le_mul_of_nonneg_right hcκ' (sq_nonneg ‖(y : E)‖)).trans (hAC y)
      simp only [hBdef, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        ContinuousLinearMap.coe_coe, add_apply, smul_apply, smul_eq_mul]
      linarith [mul_le_mul_of_nonneg_left h0 (sub_nonneg.2 ht.2),
        mul_le_mul_of_nonneg_left h1 ht.1]
    -- With `x = S u`, the value of `1 + t C S` at `u = A x` is `B x`.
    set x : D := ⟨S u, coerciveInverse_mem A hκ hA hsurj u⟩ with hxdef
    have hx : A x = u := apply_coerciveInverse A hκ hA hsurj u
    have hBx : B x = u + t • C x := by
      rw [hBdef, LinearMap.add_apply, hx]
      rfl
    have hval : ((1 - t) • ContinuousLinearMap.id ℝ (StrongDual ℝ E) +
        t • (ContinuousLinearMap.id ℝ (StrongDual ℝ E) + C.comp S)) u = B x := by
      rw [hBx]
      simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, hxdef]
      module
    -- `‖t C x‖ ≤ ‖C‖ ‖x‖ ≤ (‖C‖ / c) ‖B x‖` by the coercivity of `B`.
    have hCx : ‖t • C x‖ ≤ ‖C‖ / c * ‖B x‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1, div_mul_eq_mul_div, le_div_iff₀ hc]
      calc t * ‖C x‖ * c ≤ 1 * (‖C‖ * ‖(x : E)‖) * c := by
            gcongr
            · exact ht.2
            · exact C.le_opNorm _
        _ = ‖C‖ * (c * ‖(x : E)‖) := by ring
        _ ≤ ‖C‖ * ‖B x‖ :=
            mul_le_mul_of_nonneg_left (mul_norm_le_norm_of_coercive B hB x) (norm_nonneg C)
    rw [hval]
    calc ‖u‖ = ‖B x - t • C x‖ := by rw [hBx, add_sub_cancel_right]
      _ ≤ ‖B x‖ + ‖t • C x‖ := norm_sub_le _ _
      _ ≤ ‖B x‖ + ‖C‖ / c * ‖B x‖ := by linarith
      _ = (1 + ‖C‖ / c) * ‖B x‖ := by ring
  -- The method of continuity on the dual space makes `1 + C S` onto.
  have hg := (bijective_of_uniform_bound_on_segment (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
    (ContinuousLinearMap.id ℝ (StrongDual ℝ E) + C.comp S) hbound Function.surjective_id).surjective
  intro f
  obtain ⟨y, hy⟩ := hg f
  refine ⟨⟨S y, coerciveInverse_mem A hκ hA hsurj y⟩, ?_⟩
  have h1 := apply_coerciveInverse A hκ hA hsurj y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    ContinuousLinearMap.coe_coe]
  rw [h1]
  simpa using hy

include hκ hA hsurj in
/-- A bounded perturbation whose norm is below the coercivity constant keeps a coercive map onto the
dual space. The perturbed map is coercive with constant `κ - ‖C‖`, so this is a case of
`surjective_add_of_coercive_add`. -/
theorem surjective_add_of_coercive (C : E →L[ℝ] StrongDual ℝ E) (hC : ‖C‖ < κ) :
    Function.Surjective (A + C.toLinearMap ∘ₗ D.subtype) :=
  surjective_add_of_coercive_add A hκ hA hsurj C (sub_pos.2 hC) fun x ↦ by
    have h : |C x x| ≤ ‖C‖ * ‖(x : E)‖ ^ 2 := by
      rw [← Real.norm_eq_abs, pow_two, ← mul_assoc]
      exact C.le_opNorm₂ x x
    linarith [neg_abs_le (C x x), hA x]

end CoerciveInverse

section ShiftedOperator

variable {D : Submodule ℝ E}

/-- The shifted operator `P + ℓ† ℓ + μ J` on a subspace `D`. -/
def shiftedOperator (P : D →ₗ[ℝ] StrongDual ℝ E) (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m))
    (J : E →L[ℝ] StrongDual ℝ E) (μ : ℝ) : D →ₗ[ℝ] StrongDual ℝ E :=
  P + ((coordTranspose ℓ).comp ℓ + μ • J).toLinearMap ∘ₗ D.subtype

/-- The value of `shiftedOperator P ℓ J μ` at `x` in `D` is the functional
`P x + coordTranspose ℓ (ℓ x) + μ • J x`. -/
theorem shiftedOperator_apply (P : D →ₗ[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (J : E →L[ℝ] StrongDual ℝ E) (μ : ℝ) (x : D) :
    shiftedOperator P ℓ J μ x = P x + coordTranspose ℓ (ℓ x) + μ • J x := by
  simp [shiftedOperator, add_assoc]

/-- A positive shift keeps the coercivity of `P + ℓ† ℓ`. -/
theorem coercive_shiftedOperator (P : D →ₗ[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (J : E →L[ℝ] StrongDual ℝ E) {c μ : ℝ}
    (hμ : 0 ≤ μ) (hP : ∀ h : D, c * ‖(h : E)‖ ^ 2 ≤ P h h + ‖ℓ h‖ ^ 2)
    (hJ : ∀ h, 0 ≤ J h h) (x : D) :
    c * ‖(x : E)‖ ^ 2 ≤ shiftedOperator P ℓ J μ x x := by
  rw [shiftedOperator_apply]
  simp only [add_apply, smul_apply, smul_eq_mul, coordTranspose_apply_self]
  have := mul_nonneg hμ (hJ x)
  linarith [hP x]

/-- Let `L + ℓ† ℓ` be coercive on `D` with constant `a > 0` and let `J` be positive. If
`L + ℓ† ℓ + μ J` maps `D` onto the dual space for some `μ ≥ 0` and `L⋆ = L + C` on `D` with
`‖C‖ < a`, then `L⋆ + ℓ† ℓ + μ J` maps `D` onto the dual space. The perturbation `C` is bounded on
all of `E`, so `L⋆` has the same domain as `L`. -/
theorem surjective_shiftedOperator_of_perturbation (L Lstar : D →ₗ[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (J : E →L[ℝ] StrongDual ℝ E) {a μ : ℝ}
    (ha : 0 < a) (hμ : 0 ≤ μ) (hcoer : ∀ h : D, a * ‖(h : E)‖ ^ 2 ≤ L h h + ‖ℓ h‖ ^ 2)
    (hJ : ∀ h, 0 ≤ J h h) (hsolve : Function.Surjective (shiftedOperator L ℓ J μ))
    (C : E →L[ℝ] StrongDual ℝ E) (hC : ∀ h : D, Lstar h = L h + C h) (hCnorm : ‖C‖ < a) :
    Function.Surjective (shiftedOperator Lstar ℓ J μ) := by
  have hsplit : shiftedOperator Lstar ℓ J μ =
      shiftedOperator L ℓ J μ + C.toLinearMap ∘ₗ D.subtype := by
    refine LinearMap.ext fun x ↦ ?_
    rw [shiftedOperator_apply, LinearMap.add_apply, shiftedOperator_apply, hC]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
    abel
  rw [hsplit]
  exact surjective_add_of_coercive (shiftedOperator L ℓ J μ) ha
    (coercive_shiftedOperator L ℓ J hμ hcoer hJ) hsolve C hCnorm

/-- **Solvability at one shift gives every shift.** Let `P + ℓ† ℓ` be coercive on `D` with
constant `c > 0` and let `J` be positive. If `P + ℓ† ℓ + μ₀ J` maps `D` onto the dual space for
one `μ₀ ≥ 0`, then `P + ℓ† ℓ + μ J` maps `D` onto the dual space for every `μ ≥ 0`. The two
operators are coercive and differ by the bounded form `(μ - μ₀) J`, so
`surjective_add_of_coercive_add` applies. -/
theorem surjective_shiftedOperator_of_nonneg (P : D →ₗ[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (J : E →L[ℝ] StrongDual ℝ E) {c μ₀ μ : ℝ}
    (hc : 0 < c) (hμ₀ : 0 ≤ μ₀) (hμ : 0 ≤ μ)
    (hP : ∀ h : D, c * ‖(h : E)‖ ^ 2 ≤ P h h + ‖ℓ h‖ ^ 2) (hJ : ∀ h, 0 ≤ J h h)
    (hsolve : Function.Surjective (shiftedOperator P ℓ J μ₀)) :
    Function.Surjective (shiftedOperator P ℓ J μ) := by
  have hsplit : shiftedOperator P ℓ J μ =
      shiftedOperator P ℓ J μ₀ + ((μ - μ₀) • J).toLinearMap ∘ₗ D.subtype := by
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.add_apply, shiftedOperator_apply, shiftedOperator_apply]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe,
      smul_apply]
    module
  have hcoer := coercive_shiftedOperator P ℓ J hμ hP hJ
  rw [hsplit] at hcoer ⊢
  exact surjective_add_of_coercive_add _ hc (coercive_shiftedOperator P ℓ J hμ₀ hP hJ) hsolve _ hc
    hcoer

end ShiftedOperator

section Compression

/-- The matrix of `ℓ ∘ S ∘ ℓ†` in the standard basis of `ℝ^m`. -/
def compressionMatrix (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (S : StrongDual ℝ E →L[ℝ] E) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j ↦ ℓ (S (coordTranspose ℓ (EuclideanSpace.single j 1))) i

/-- The compression matrix acts as `ℓ ∘ S ∘ ℓ†` on coordinate vectors. -/
theorem mulVec_compressionMatrix (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m))
    (S : StrongDual ℝ E →L[ℝ] E) (v : Fin m → ℝ) :
    compressionMatrix ℓ S *ᵥ v = (ℓ (S (coordTranspose ℓ (WithLp.toLp 2 v)))).ofLp :=
  mulVec_eq_ofLp_of_apply_single
    (ℓ.toLinearMap ∘ₗ S.toLinearMap ∘ₗ (coordTranspose ℓ).toLinearMap) (fun _ _ ↦ rfl) v

variable {D : Submodule ℝ E} (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m))
  (S : StrongDual ℝ E →L[ℝ] E) (hSmem : ∀ f, S f ∈ D)

/-- Let `S` invert `P + ℓ† ℓ` on `D`. A vanishing determinant of `1 - ℓ S ℓ†` gives a nonzero kernel
vector of `P`. -/
theorem exists_ne_zero_of_det_one_sub_compressionMatrix_eq_zero (P : D →ₗ[ℝ] StrongDual ℝ E)
    (hS : ∀ f, P ⟨S f, hSmem f⟩ + coordTranspose ℓ (ℓ (S f)) = f)
    (hdet : (1 - compressionMatrix ℓ S).det = 0) :
    ∃ x : D, (x : E) ≠ 0 ∧ P x = 0 := by
  classical
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set q : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 v with hqdef
  set x : D := ⟨S (coordTranspose ℓ q), hSmem _⟩ with hxdef
  have hx := hS (coordTranspose ℓ q)
  have hq : q = ℓ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, mulVec_compressionMatrix, sub_eq_zero] at hv
    rw [hqdef, hv, WithLp.toLp_ofLp]
  refine ⟨x, fun hx0 ↦ hv0 ?_, ?_⟩
  · have hq0 : q = 0 := by rw [hq, hx0, map_zero]
    have hv' : v = q.ofLp := rfl
    rw [hv', hq0]
    rfl
  · rw [← hq] at hx
    exact add_eq_right.mp hx

/-- If `S` inverts `L⋆ + ℓ† ℓ + μ J` on `D`, the form of `L⋆ + ℓ† ℓ` is nonnegative, `J` is positive
and controls the coordinates with constant `c_F < μ`, then `det (1 - ℓ S ℓ†) > 0`. -/
theorem det_one_sub_compressionMatrix_pos (Lstar : D →ₗ[ℝ] StrongDual ℝ E)
    (J : E →L[ℝ] StrongDual ℝ E) {μ cF : ℝ}
    (hS : ∀ f, shiftedOperator Lstar ℓ J μ ⟨S f, hSmem f⟩ = f)
    (hA0 : ∀ x : D, 0 ≤ (Lstar x + coordTranspose ℓ (ℓ x)) x)
    (hJ : ∀ h, 0 ≤ J h h) (hJℓ : ∀ h, ‖ℓ h‖ ^ 2 ≤ cF * J h h) (hμ : cF < μ) :
    0 < (1 - compressionMatrix ℓ S).det := by
  classical
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : Fin m → ℝ,
      (1 + s • -compressionMatrix ℓ S) *ᵥ v = 0 → v = 0 := by
    intro s hs v hv
    set q : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 v with hqdef
    set x : D := ⟨S (coordTranspose ℓ q), hSmem _⟩ with hxdef
    have hx : Lstar x + coordTranspose ℓ (ℓ x) + μ • J x = coordTranspose ℓ q := by
      rw [← shiftedOperator_apply]
      exact hS (coordTranspose ℓ q)
    have hq : q = s • ℓ x := by
      rw [smul_neg, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec,
        Matrix.smul_mulVec, mulVec_compressionMatrix, ← sub_eq_add_neg, sub_eq_zero] at hv
      rw [hqdef, hv]
      rfl
    have hpair := congrArg (fun F : StrongDual ℝ E ↦ F x) hx
    have h0 := hA0 x
    simp only [add_apply, smul_apply, smul_eq_mul, coordTranspose_apply] at hpair h0
    rw [hq, real_inner_smul_left, real_inner_self_eq_norm_sq] at hpair
    rw [real_inner_self_eq_norm_sq] at h0
    -- `μ J(x, x) ≤ s ‖ℓ x‖² ≤ ‖ℓ x‖² ≤ c_F J(x, x)` with `c_F < μ` forces `J(x, x) = 0`
    have hsl : s * ‖ℓ x‖ ^ 2 ≤ ‖ℓ x‖ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hs.2
    have hJ0 : J x x ≤ 0 := le_of_mul_le_mul_left (a := μ - cF)
      (by linarith [hJℓ x]) (sub_pos.2 hμ)
    have hlx : ℓ x = 0 := by
      have : ‖ℓ x‖ ^ 2 ≤ 0 := (hJℓ x).trans (by rw [le_antisymm hJ0 (hJ x), mul_zero])
      simpa using this
    exact congrArg WithLp.ofLp (show q = 0 by rw [hq, hlx, smul_zero])
  have hpos := det_one_add_pos_of_forall_mulVec_eq_zero _ key
  rwa [← sub_eq_add_neg] at hpos

end Compression

section Criterion

variable {D : Submodule ℝ E}

/-- If `L + ℓ† ℓ` is coercive on `D` with constant `1 - θ`, the reconstruction residual
`L Φ ℓ - ℓ† ℓ` has norm at most `δ`, the amplification `‖1 + Φ ℓ‖` is at most `t_G` and `L⋆ = L + C`
with `‖C‖ ≤ ε`, then `L⋆ (1 + Φ ℓ)` is coercive on `D` with constant `1 - θ - δ - ε t_G`. -/
theorem coercive_comp_reconstruction (L Lstar : D →ₗ[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (Φ : EuclideanSpace ℝ (Fin m) →L[ℝ] E)
    (hΦ : ∀ q, Φ q ∈ D) {θ δ ε tG : ℝ}
    (hcapture : ∀ h : D, (1 - θ) * ‖(h : E)‖ ^ 2 ≤ L h h + ‖ℓ h‖ ^ 2)
    (hres : ∀ h, ‖L ⟨Φ (ℓ h), hΦ (ℓ h)⟩ - coordTranspose ℓ (ℓ h)‖ ≤ δ * ‖h‖)
    (htG : ∀ h, ‖h + Φ (ℓ h)‖ ≤ tG * ‖h‖)
    (C : E →L[ℝ] StrongDual ℝ E) (hC : ∀ h : D, Lstar h = L h + C h) (hCnorm : ‖C‖ ≤ ε)
    (x : D) :
    (1 - θ - δ - ε * tG) * ‖(x : E)‖ ^ 2 ≤ (Lstar x + Lstar ⟨Φ (ℓ x), hΦ (ℓ x)⟩) x := by
  have hε : 0 ≤ ε := (norm_nonneg C).trans hCnorm
  have hlow : ∀ (F : StrongDual ℝ E) (y : E), -(‖F‖ * ‖y‖) ≤ F y := fun F y ↦ by
    have h1 := F.le_opNorm y
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (F y)]
  set R := L ⟨Φ (ℓ x), hΦ (ℓ x)⟩ - coordTranspose ℓ (ℓ x) with hRdef
  have h1 := hcapture x
  have h2 : -(δ * ‖(x : E)‖ ^ 2) ≤ R x := by
    have hb : ‖R‖ * ‖(x : E)‖ ≤ δ * ‖(x : E)‖ ^ 2 := by
      rw [pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hres x) (norm_nonneg _)
    linarith [hlow R x]
  have h3 : -(ε * tG * ‖(x : E)‖ ^ 2) ≤ C ((x : E) + Φ (ℓ x)) x := by
    have hn : ‖C ((x : E) + Φ (ℓ x))‖ ≤ ε * (tG * ‖(x : E)‖) :=
      (C.le_opNorm _).trans (mul_le_mul hCnorm (htG x) (norm_nonneg _) hε)
    have hb : ‖C ((x : E) + Φ (ℓ x))‖ * ‖(x : E)‖ ≤ ε * tG * ‖(x : E)‖ ^ 2 :=
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (by ring)
    linarith [hlow (C ((x : E) + Φ (ℓ x))) x]
  have hsplit : (Lstar x + Lstar ⟨Φ (ℓ x), hΦ (ℓ x)⟩) x =
      (L x x + ‖ℓ x‖ ^ 2) + R x + C ((x : E) + Φ (ℓ x)) x := by
    rw [hC, hC, hRdef, map_add]
    simp only [add_apply, sub_apply, coordTranspose_apply_self]
    ring
  rw [hsplit]
  linarith

/-- Let `S` invert `A₀ = L⋆ + ℓ† ℓ` on `D`. If `A₀` and `L⋆ (1 + Φ ℓ)` are both coercive on `D`,
then `det ((1 - ℓ S ℓ†) (1 + Λ)) > 0` for the matrix `Λ = ℓ Φ`. The segment from `A₀` to
`L⋆ (1 + Φ ℓ)` consists of coercive maps, and each corresponds to a nonsingular `m × m` matrix on
the segment from `1` to this product. -/
theorem det_mul_pos_of_coercive_homotopy (Lstar : D →ₗ[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (Φ : EuclideanSpace ℝ (Fin m) →L[ℝ] E)
    (hΦ : ∀ q, Φ q ∈ D) (S : StrongDual ℝ E →L[ℝ] E) (hSmem : ∀ f, S f ∈ D)
    (hS : ∀ f, Lstar ⟨S f, hSmem f⟩ + coordTranspose ℓ (ℓ (S f)) = f)
    {κ β : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hA : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ (Lstar x + coordTranspose ℓ (ℓ x)) x)
    (hT : ∀ x : D, β * ‖(x : E)‖ ^ 2 ≤ (Lstar x + Lstar ⟨Φ (ℓ x), hΦ (ℓ x)⟩) x)
    {Λ : Matrix (Fin m) (Fin m) ℝ} (hΛ : ∀ i j, Λ i j = ℓ (Φ (EuclideanSpace.single j 1)) i) :
    0 < ((1 - compressionMatrix ℓ S) * (1 + Λ)).det := by
  classical
  set T := coordTranspose ℓ with hTdef
  set M := compressionMatrix ℓ S with hMdef
  have hΛv : ∀ v, Λ *ᵥ v = (ℓ (Φ (WithLp.toLp 2 v))).ofLp := fun v ↦
    mulVec_eq_ofLp_of_apply_single (ℓ.toLinearMap ∘ₗ Φ.toLinearMap) hΛ v
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : Fin m → ℝ,
      (1 + s • ((1 - M) * (1 + Λ) - 1)) *ᵥ v = 0 → v = 0 := by
    intro s hs v hv
    set q : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 v with hqdef
    set p : EuclideanSpace ℝ (Fin m) := q + ℓ (Φ q) with hpdef
    set u : D := ⟨S (T p), hSmem _⟩ with hudef
    have hu : Lstar u + T (ℓ u) = T p := hS (T p)
    set φq : D := ⟨Φ q, hΦ q⟩ with hφqdef
    set h : D := φq - u with hhdef
    have hℓh : ℓ h = ℓ (Φ q) - ℓ (S (T p)) := by
      rw [hhdef, Submodule.coe_sub, map_sub]
    have hvec : (1 + s • ((1 - M) * (1 + Λ) - 1)) *ᵥ v = (q + s • ℓ h).ofLp := by
      have h1 : (1 + Λ) *ᵥ v = p.ofLp := by
        rw [Matrix.add_mulVec, Matrix.one_mulVec, hΛv]
        rfl
      have h2 : ((1 - M) * (1 + Λ) - 1) *ᵥ v = (ℓ h).ofLp := by
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, h1, Matrix.sub_mulVec,
          Matrix.one_mulVec, Matrix.one_mulVec, hMdef, mulVec_compressionMatrix,
          WithLp.toLp_ofLp, hℓh, hpdef]
        ext i
        simp only [WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply, hqdef]
        ring
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, h2]
      rfl
    have hq : q + s • ℓ h = 0 := by
      rw [hv] at hvec
      exact WithLp.ofLp_injective 2 hvec.symm
    have hsl : s • ℓ h = -q := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact hq
    set R : StrongDual ℝ E := Lstar ⟨Φ (ℓ h), hΦ (ℓ h)⟩ - T (ℓ h) with hRdef
    have hzero : Lstar h + T (ℓ h) + s • R = 0 := by
      have hD : s • (⟨Φ (ℓ h), hΦ (ℓ h)⟩ : D) = -φq := by
        ext
        simp only [hφqdef, Submodule.coe_smul, Submodule.coe_neg, ← map_smul, hsl, map_neg]
      have h1 : Lstar h + T (ℓ h) = Lstar φq - T q := by
        have hlin : Lstar h + T (ℓ h) = (Lstar φq + T (ℓ φq)) - (Lstar u + T (ℓ u)) := by
          rw [hhdef, map_sub, Submodule.coe_sub, map_sub, map_sub]
          abel
        rw [hlin, hu, hpdef, map_add]
        abel
      rw [h1, hRdef, smul_sub, ← map_smul, hD, ← map_smul, hsl, map_neg, map_neg]
      abel
    have hpair : (Lstar h + T (ℓ h) + s • R) h =
        (1 - s) * (Lstar h + T (ℓ h)) h + s * (Lstar h + Lstar ⟨Φ (ℓ h), hΦ (ℓ h)⟩) h := by
      rw [hRdef]
      simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
      ring
    rw [hzero, zero_apply] at hpair
    have k1 : (1 - s) * (κ * ‖(h : E)‖ ^ 2) ≤ (1 - s) * (Lstar h + T (ℓ h)) h :=
      mul_le_mul_of_nonneg_left (hA h) (sub_nonneg.2 hs.2)
    have k2 : s * (β * ‖(h : E)‖ ^ 2) ≤ s * (Lstar h + Lstar ⟨Φ (ℓ h), hΦ (ℓ h)⟩) h :=
      mul_le_mul_of_nonneg_left (hT h) hs.1
    have hc : 0 < (1 - s) * κ + s * β := by
      rcases hs.1.lt_or_eq with hs0 | rfl
      · linarith [mul_nonneg (sub_nonneg.2 hs.2) hκ.le, mul_pos hs0 hβ]
      · simpa using hκ
    have hh0 : (h : E) = 0 := by
      have : ‖(h : E)‖ ^ 2 ≤ 0 := le_of_mul_le_mul_left (a := (1 - s) * κ + s * β)
        (by linarith) hc
      simpa using this
    rw [hh0, map_zero, smul_zero, add_zero] at hq
    exact congrArg WithLp.ofLp hq
  have hpos := det_one_add_pos_of_forall_mulVec_eq_zero _ key
  rwa [add_sub_cancel] at hpos

/-- If `L⋆ + ℓ† ℓ` is coercive on `D` and `J` is a positive form with `‖ℓ h‖² ≤ c_F ⟪J h, h⟫`, every
`μ` for which `L⋆ + μ J` has a nonzero kernel vector in `D` satisfies `μ < c_F`. -/
theorem lt_of_apply_add_smul_eq_zero (Lstar : D →ₗ[ℝ] StrongDual ℝ E)
    (J : E →L[ℝ] StrongDual ℝ E) (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) {κ μ cF : ℝ}
    (hκ : 0 < κ) (hA : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ (Lstar x + coordTranspose ℓ (ℓ x)) x)
    (hJ : ∀ h, 0 ≤ J h h) (hJℓ : ∀ h, ‖ℓ h‖ ^ 2 ≤ cF * J h h)
    {x : D} (hx0 : (x : E) ≠ 0) (hx : Lstar x + μ • J x = 0) : μ < cF := by
  have hpair := congrArg (fun F : StrongDual ℝ E ↦ F x) hx
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply] at hpair
  have h1 := hA x
  simp only [add_apply, coordTranspose_apply_self] at h1
  have hpos : 0 < κ * ‖(x : E)‖ ^ 2 := mul_pos hκ (pow_pos (norm_pos_iff.2 hx0) 2)
  by_contra hle
  push Not at hle
  have := mul_le_mul_of_nonneg_right hle (hJ x)
  linarith [hJℓ x]

/-- **Finite-rank determinant criterion.** Let `L⋆ : D → E*` be linear on a subspace `D` of a
real normed space `E`, let `ℓ : E → ℝ^m` be bounded and linear with transpose `ℓ†`, let
`Φ : ℝ^m → D` be linear and let `J : E → E*` be a bounded form, the `L²` pairing when `E` is
embedded in `L²`. Assume that `L⋆ + ℓ† ℓ` maps `D` onto `E*` and that for some `a, c_F > 0`

* `⟪L⋆ h, h⟫ + ‖ℓ h‖² ≥ a ‖h‖²` for all `h` in `D`,
* `⟪L⋆ (h + Φ ℓ h), h⟫ ≥ a ‖h‖²` for all `h` in `D`,
* `‖ℓ h‖² ≤ c_F ⟪J h, h⟫` for all `h` in `E`.

If `det (1 + ℓ Φ) < 0`, then `L⋆ h = λ J h` for some `λ` in `(-c_F, 0)` and some nonzero `h` in
`D`. The equation holds in `E*`: `⟪L⋆ h, g⟫ = λ ⟪J h, g⟫` for every `g` in `E`.

The sign of one `m × m` determinant thus gives a real negative eigenvalue, an unstable one when
`L⋆` is a linearized operator with the sign for which unstable eigenvalues are negative, and no
eigenpair has to be enclosed. The third inequality gives `⟪J h, h⟫ ≥ 0`, so
`A_μ = L⋆ + ℓ† ℓ + μ J` is coercive for `μ ≥ 0` and maps `D` onto `E*` by the method of
continuity from `μ = 0`. The determinant `d(μ) = det (1 - ℓ A_μ⁻¹ ℓ†)` is continuous, it is
positive for `μ > c_F`, and `d(0)` has the sign of `det (1 + ℓ Φ)` because the segment from `A_0`
to `L⋆ (1 + Φ ℓ)` consists of coercive maps; a zero `μ` of `d` gives a kernel vector of
`L⋆ + μ J`, and `λ = -μ`. -/
theorem exists_eigenvalue_of_det_neg (D : Submodule ℝ E)
    (Lstar : D →ₗ[ℝ] StrongDual ℝ E) (J : E →L[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (Φ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] D)
    {a cF : ℝ} (ha : 0 < a) (hcF : 0 < cF)
    (hsurj : ∀ f : StrongDual ℝ E, ∃ h : D, Lstar h + coordTranspose ℓ (ℓ h) = f)
    (hcoer : ∀ h : D, a * ‖(h : E)‖ ^ 2 ≤ Lstar h h + ‖ℓ h‖ ^ 2)
    (hcoerΦ : ∀ h : D, a * ‖(h : E)‖ ^ 2 ≤ Lstar (h + Φ (ℓ h)) h)
    (hJℓ : ∀ h : E, ‖ℓ h‖ ^ 2 ≤ cF * J h h)
    (hdet : LinearMap.det (1 + ℓ.toLinearMap ∘ₗ D.subtype ∘ₗ Φ) < 0) :
    ∃ lambda ∈ Ioo (-cF) 0, ∃ h : D, h ≠ 0 ∧ Lstar h = lambda • J h := by
  classical
  -- The form `J` is nonnegative on the diagonal, since `c_F > 0`.
  have hJ : ∀ h, 0 ≤ J h h := fun h ↦
    nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (hJℓ h)) hcF
  set A := shiftedOperator Lstar ℓ J with hAdef
  -- Coercivity of `A μ = L⋆ + ℓ† ℓ + μ J` with constant `a`.
  have hA0coer : ∀ x : D, a * ‖(x : E)‖ ^ 2 ≤ (Lstar x + coordTranspose ℓ (ℓ x)) x := by
    intro x
    rw [add_apply, coordTranspose_apply_self]
    exact hcoer x
  have hAcoer : ∀ μ, 0 ≤ μ → ∀ x : D, a * ‖(x : E)‖ ^ 2 ≤ A μ x x := fun μ hμ ↦
    coercive_shiftedOperator Lstar ℓ J hμ hcoer hJ
  -- Solvability for every `μ ≥ 0` follows from solvability at `μ = 0`.
  have hAsurj : ∀ μ, 0 ≤ μ → Function.Surjective (A μ) := fun μ hμ ↦
    surjective_shiftedOperator_of_nonneg Lstar ℓ J ha le_rfl hμ hcoer hJ fun f ↦ by
      obtain ⟨h, hh⟩ := hsurj f
      exact ⟨h, by rw [shiftedOperator_apply, zero_smul, add_zero]; exact hh⟩
  -- The solution operators, extended to negative parameters by their value at zero.
  let S : ℝ → StrongDual ℝ E →L[ℝ] E := fun μ ↦
    coerciveInverse (A (max μ 0)) ha (hAcoer _ (le_max_right μ 0)) (hAsurj _ (le_max_right μ 0))
  have hSmem : ∀ μ f, S μ f ∈ D := fun μ f ↦ coerciveInverse_mem _ _ _ _ f
  have hSeq : ∀ μ f, A (max μ 0) ⟨S μ f, hSmem μ f⟩ = f := fun μ f ↦
    apply_coerciveInverse _ _ _ _ f
  have hSeq' : ∀ μ, 0 ≤ μ → ∀ f, A μ ⟨S μ f, hSmem μ f⟩ = f := fun μ hμ f ↦ by
    simpa only [max_eq_left hμ] using hSeq μ f
  have hSnorm : ∀ μ f, ‖S μ f‖ ≤ a⁻¹ * ‖f‖ := fun μ f ↦
    (ContinuousLinearMap.le_opNorm _ f).trans
      (mul_le_mul_of_nonneg_right (norm_coerciveInverse_le _ _ _ _) (norm_nonneg f))
  -- Resolvent estimate: the solutions depend Lipschitz continuously on the parameter.
  have hSlip : ∀ μ ν f, ‖S μ f - S ν f‖ ≤ a⁻¹ * (‖J‖ * (a⁻¹ * ‖f‖)) * |μ - ν| := by
    intro μ ν f
    set x : D := ⟨S μ f, hSmem μ f⟩
    set y : D := ⟨S ν f, hSmem ν f⟩
    have hy := hSeq ν f
    have hdiff : A (max μ 0) (x - y) = (max ν 0 - max μ 0) • J y := by
      rw [map_sub, hSeq μ f, hAdef, shiftedOperator_apply]
      rw [hAdef, shiftedOperator_apply] at hy
      rw [← hy]
      module
    have hb := norm_le_inv_mul_of_coercive (A (max μ 0)) ha (hAcoer _ (le_max_right μ 0))
      (x - y)
    rw [hdiff, norm_smul, Real.norm_eq_abs] at hb
    have hJy : ‖J y‖ ≤ ‖J‖ * (a⁻¹ * ‖f‖) :=
      (J.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hSnorm ν f) (norm_nonneg J))
    have hmax : |max ν 0 - max μ 0| ≤ |μ - ν| := by
      rw [abs_sub_comm]
      exact abs_max_sub_max_le_abs μ ν 0
    calc ‖S μ f - S ν f‖ = ‖((x - y : D) : E)‖ := rfl
      _ ≤ a⁻¹ * (|max ν 0 - max μ 0| * ‖J y‖) := hb
      _ ≤ a⁻¹ * (|μ - ν| * (‖J‖ * (a⁻¹ * ‖f‖))) := by
        gcongr
      _ = a⁻¹ * (‖J‖ * (a⁻¹ * ‖f‖)) * |μ - ν| := by ring
  have hScont : ∀ f, Continuous fun μ ↦ S μ f := fun f ↦
    (LipschitzWith.of_dist_le' fun μ ν ↦ by
      rw [dist_eq_norm, Real.dist_eq]
      exact hSlip μ ν f).continuous
  -- The determinant `det (1 - ℓ A_μ⁻¹ ℓ†)` is continuous in `μ`.
  have hMcont : Continuous fun μ ↦ compressionMatrix ℓ (S μ) := continuous_matrix fun i j ↦
    ((EuclideanSpace.proj i).comp ℓ).continuous.comp (hScont _)
  have hDcont : Continuous fun μ ↦ (1 - compressionMatrix ℓ (S μ)).det :=
    (continuous_const.sub hMcont).matrix_det
  -- The sign at `μ = 0` is the sign of `det (1 + ℓ Φ)`, by the coercivity of `L⋆ (1 + Φ ℓ)`.
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Matrix (Fin m) (Fin m) ℝ,
      ∀ i j, Λ i j = ℓ (Φ (EuclideanSpace.single j 1)) i := ⟨.of fun i j ↦ _, fun _ _ ↦ rfl⟩
  have hD0 : (1 - compressionMatrix ℓ (S 0)).det < 0 := by
    have hpos := det_mul_pos_of_coercive_homotopy Lstar ℓ
      (LinearMap.toContinuousLinearMap (D.subtype ∘ₗ Φ)) (fun q ↦ (Φ q).2) (S 0) (hSmem 0)
      (fun f ↦ by simpa [hAdef, shiftedOperator_apply] using hSeq' 0 le_rfl f) ha ha hA0coer
      (fun x ↦ by simpa using hcoerΦ x) hΛ
    rw [Matrix.det_mul] at hpos
    rw [det_one_add_eq_det_of_apply_single (ℓ.toLinearMap ∘ₗ D.subtype ∘ₗ Φ) hΛ] at hdet
    exact neg_of_mul_pos_left hpos hdet.le
  -- The sign for a parameter above `c_F`.
  have hDp : 0 < (1 - compressionMatrix ℓ (S (cF + 1))).det :=
    det_one_sub_compressionMatrix_pos ℓ (S (cF + 1)) (hSmem (cF + 1)) Lstar J
      (hSeq' (cF + 1) (by linarith))
      (fun x ↦ (mul_nonneg ha.le (sq_nonneg _)).trans (hA0coer x)) hJ hJℓ (lt_add_one cF)
  -- The intermediate value theorem gives a zero of the determinant, and with it a kernel vector
  -- of `L⋆ + μ J`.
  obtain ⟨μs, hμs, hDμs⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ cF + 1 by linarith)
    hDcont.continuousOn (show (0 : ℝ) ∈ Icc _ _ from ⟨hD0.le, hDp.le⟩)
  have hμspos : 0 < μs := hμs.1.lt_of_ne (by rintro rfl; exact hD0.ne hDμs)
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_of_det_one_sub_compressionMatrix_eq_zero ℓ (S μs)
    (hSmem μs) (Lstar + (μs • J).toLinearMap ∘ₗ D.subtype)
    (fun f ↦ by
      convert hSeq' μs hμspos.le f using 1
      rw [hAdef, shiftedOperator_apply]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        ContinuousLinearMap.coe_coe, smul_apply]
      abel) hDμs
  have hx' : Lstar x + μs • J x = 0 := by simpa using hx
  -- The eigenvalue is `-μ`, and `μ < c_F` by the coercivity of `L⋆ + ℓ† ℓ`.
  refine ⟨-μs, ⟨neg_lt_neg (lt_of_apply_add_smul_eq_zero Lstar J ℓ ha hA0coer hJ hJℓ hx0 hx'),
    neg_lt_zero.2 hμspos⟩, x, fun h0 ↦ hx0 (by rw [h0]; rfl), ?_⟩
  rw [eq_neg_of_add_eq_zero_left hx']
  module

/-- **Finite-rank determinant criterion, perturbative form.** Let `L` and `L⋆ = L + C` with
`‖C‖ ≤ ε` act from a subspace `D` into the dual space. Suppose `L + ℓ† ℓ` is coercive on `D` with
constant `1 - θ`, the reconstruction `Φ` with values in `D` has residual `‖L Φ ℓ - ℓ† ℓ‖ ≤ δ` and
amplification `‖1 + Φ ℓ‖ ≤ t_G`, and `J` is a positive form with `‖ℓ h‖² ≤ c_F ⟪J h, h⟫`. If
`L + ℓ† ℓ + μ J` maps `D` onto the dual space for every `μ ≥ 0`, the margins `1 - θ - ε` and
`1 - θ - δ - ε t_G` are positive and `det (1 + Λ) < 0` for the matrix `Λ = ℓ Φ`, then `L⋆ + μ J`
has a nonzero kernel vector in `D` for some `0 < μ < c_F`.

This is `exists_eigenvalue_of_det_neg` with `a = min (1 - θ - ε) (1 - θ - δ - ε t_G)` and
`λ = -μ`: `L⋆ + ℓ† ℓ` is coercive with constant `1 - θ - ε` and maps `D` onto the dual space
because `‖C‖ < 1 - θ`, `L⋆ (1 + Φ ℓ)` is coercive with constant `1 - θ - δ - ε t_G`, and
`c_F > 0` because otherwise `ℓ = 0` and `det (1 + Λ) = 1`. Of the solvability hypothesis only the
case `μ = 0` is used.

The coordinate bound `hJℓ` cannot be dropped. For `E = ℝ`, `m = 1`, `ℓ = 1`, `Φ = -2`,
`L = L⋆ = -1/2`, `C = 0` and `J = 0`, every other hypothesis holds with `θ = 1/2`, `δ = ε = 0` and
`t_G = 1`, but `L⋆ + μ J` is injective for every `μ`. -/
theorem exists_kernel_of_det_neg (D : Submodule ℝ E)
    (L Lstar : D →ₗ[ℝ] StrongDual ℝ E) (J : E →L[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (Φ : EuclideanSpace ℝ (Fin m) →L[ℝ] E)
    (hΦ : ∀ q, Φ q ∈ D) {θ δ ε tG cF : ℝ}
    (hcapture : ∀ h : D, (1 - θ) * ‖(h : E)‖ ^ 2 ≤ L h h + ‖ℓ h‖ ^ 2)
    (hres : ∀ h, ‖L ⟨Φ (ℓ h), hΦ (ℓ h)⟩ - coordTranspose ℓ (ℓ h)‖ ≤ δ * ‖h‖)
    (htG : ∀ h, ‖h + Φ (ℓ h)‖ ≤ tG * ‖h‖)
    (C : E →L[ℝ] StrongDual ℝ E) (hC : ∀ h : D, Lstar h = L h + C h) (hCnorm : ‖C‖ ≤ ε)
    (hJ : ∀ h, 0 ≤ J h h) (hJℓ : ∀ h, ‖ℓ h‖ ^ 2 ≤ cF * J h h)
    (hsolveL : ∀ μ : ℝ, 0 ≤ μ → ∀ f, ∃ h : D, L h + coordTranspose ℓ (ℓ h) + μ • J h = f)
    (hκ : 0 < 1 - θ - ε) (hβ : 0 < 1 - θ - δ - ε * tG)
    {Λ : Matrix (Fin m) (Fin m) ℝ} (hΛ : ∀ i j, Λ i j = ℓ (Φ (EuclideanSpace.single j 1)) i)
    (hdet : (1 + Λ).det < 0) :
    ∃ μ ∈ Ioo 0 cF, ∃ h : D, (h : E) ≠ 0 ∧ Lstar h + μ • J h = 0 := by
  -- The constant `c_F` is positive: otherwise `ℓ = 0` and `det (1 + Λ) = 1`.
  have hcF : 0 < cF := by
    by_contra hle
    have hℓ : ∀ h, ℓ h = 0 := fun h ↦ by
      have : ‖ℓ h‖ ^ 2 ≤ 0 :=
        (hJℓ h).trans (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hle) (hJ h))
      simpa using this
    have hΛ0 : Λ = 0 := by
      ext i j
      simp [hΛ, hℓ]
    norm_num [hΛ0] at hdet
  -- Coercivity of `L⋆ + ℓ† ℓ` with constant `1 - θ - ε`.
  have hcaptureStar : ∀ x : D, (1 - θ - ε) * ‖(x : E)‖ ^ 2 ≤ Lstar x x + ‖ℓ x‖ ^ 2 := fun x ↦ by
    have h1 : |C x x| ≤ ε * ‖(x : E)‖ ^ 2 := by
      rw [← Real.norm_eq_abs, pow_two, ← mul_assoc]
      exact (C.le_opNorm₂ x x).trans (by gcongr)
    rw [hC, add_apply]
    linarith [neg_abs_le (C x x), hcapture x]
  -- Solvability for `L⋆ + ℓ† ℓ` follows from solvability for `L + ℓ† ℓ`, since `‖C‖ < 1 - θ`.
  have hsurj : ∀ f : StrongDual ℝ E, ∃ h : D, Lstar h + coordTranspose ℓ (ℓ h) = f := fun f ↦ by
    obtain ⟨h, hh⟩ := surjective_shiftedOperator_of_perturbation L Lstar ℓ J (a := 1 - θ)
      (by linarith [(norm_nonneg C).trans hCnorm]) le_rfl hcapture hJ
      (fun g ↦ by
        obtain ⟨h, hh⟩ := hsolveL 0 le_rfl g
        exact ⟨h, by rw [shiftedOperator_apply]; exact hh⟩) C hC (by linarith) f
    exact ⟨h, by rw [shiftedOperator_apply, zero_smul, add_zero] at hh; exact hh⟩
  -- The criterion with `a = min (1 - θ - ε) (1 - θ - δ - ε t_G)`; the eigenvalue is `-μ`.
  obtain ⟨lambda, hlambda, h, hh0, hh⟩ := exists_eigenvalue_of_det_neg D Lstar J ℓ
    (Φ.toLinearMap.codRestrict D hΦ) (lt_min hκ hβ) hcF hsurj
    (fun x ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
      (hcaptureStar x))
    (fun x ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (by
      rw [map_add]
      exact coercive_comp_reconstruction L Lstar ℓ Φ hΦ hcapture hres htG C hC hCnorm x))
    hJℓ (by
      rwa [det_one_add_eq_det_of_apply_single
        (ℓ.toLinearMap ∘ₗ D.subtype ∘ₗ Φ.toLinearMap.codRestrict D hΦ) hΛ])
  exact ⟨-lambda, ⟨neg_pos.2 hlambda.2, neg_lt.1 hlambda.1⟩, h, fun h0 ↦ hh0 (Subtype.ext h0), by
    rw [hh]
    module⟩

/-- Under the hypotheses of `exists_kernel_of_det_neg`, the operator `L⋆ + μ J` has a nonzero kernel
vector in `D` for some `μ > 0`. The coordinate bound `hJℓ` cannot be dropped; see
`exists_kernel_of_det_neg`. -/
theorem exists_pos_kernel_of_det_neg (D : Submodule ℝ E)
    (L Lstar : D →ₗ[ℝ] StrongDual ℝ E) (J : E →L[ℝ] StrongDual ℝ E)
    (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m)) (Φ : EuclideanSpace ℝ (Fin m) →L[ℝ] E)
    (hΦ : ∀ q, Φ q ∈ D) {θ δ ε tG cF : ℝ}
    (hcapture : ∀ h : D, (1 - θ) * ‖(h : E)‖ ^ 2 ≤ L h h + ‖ℓ h‖ ^ 2)
    (hres : ∀ h, ‖L ⟨Φ (ℓ h), hΦ (ℓ h)⟩ - coordTranspose ℓ (ℓ h)‖ ≤ δ * ‖h‖)
    (htG : ∀ h, ‖h + Φ (ℓ h)‖ ≤ tG * ‖h‖)
    (C : E →L[ℝ] StrongDual ℝ E) (hC : ∀ h : D, Lstar h = L h + C h) (hCnorm : ‖C‖ ≤ ε)
    (hJ : ∀ h, 0 ≤ J h h) (hJℓ : ∀ h, ‖ℓ h‖ ^ 2 ≤ cF * J h h)
    (hsolveL : ∀ μ : ℝ, 0 ≤ μ → ∀ f, ∃ h : D, L h + coordTranspose ℓ (ℓ h) + μ • J h = f)
    (hκ : 0 < 1 - θ - ε) (hβ : 0 < 1 - θ - δ - ε * tG)
    {Λ : Matrix (Fin m) (Fin m) ℝ} (hΛ : ∀ i j, Λ i j = ℓ (Φ (EuclideanSpace.single j 1)) i)
    (hdet : (1 + Λ).det < 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ h : D, (h : E) ≠ 0 ∧ Lstar h + μ • J h = 0 := by
  obtain ⟨μ, hμ, h, hh⟩ := exists_kernel_of_det_neg D L Lstar J ℓ Φ hΦ hcapture hres htG C hC
    hCnorm hJ hJℓ hsolveL hκ hβ hΛ hdet
  exact ⟨μ, hμ.1, h, hh⟩

end Criterion

end PDE.Analysis.Operator
