/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import PDE.Analysis.Operator.MethodOfContinuity

/-!
# A finite-rank determinant criterion for a positive eigenvalue

Let `D` be a subspace of a real normed space `E` and let `L, L⋆ : D → E*` be linear maps,
for example weak realizations of differential operators on a graph domain. A bounded
coordinate map `ℓ : E → ℝ^m` defines the finite-rank form `ℓ† ℓ`, where `ℓ† q = ⟪q, ℓ ·⟫`
is `coordTranspose ℓ`. Suppose that `L + ℓ† ℓ` is coercive on `D` with constant `1 - θ`, that a
reconstruction `Φ : ℝ^m → D` satisfies `‖L Φ ℓ - ℓ† ℓ‖ ≤ δ` and `‖1 + Φ ℓ‖ ≤ t_G`, that
`L⋆ = L + C` with `‖C‖ ≤ ε`, and that `J : E → E*` is a positive form with
`‖ℓ h‖² ≤ c_F ⟪J h, h⟫`. If `L + ℓ† ℓ + μ J` maps `D` onto `E*` for every `μ ≥ 0`, the margins
`1 - θ - ε` and `1 - θ - δ - ε t_G` are positive and `det (1 + ℓ Φ) < 0`, then `L⋆ + μ J` has a
nonzero kernel vector in `D` for some `0 < μ < c_F`. This is `exists_kernel_of_det_neg`.

The argument uses only `m × m` determinants. For `μ ≥ 0` the operator `A_μ = L⋆ + ℓ† ℓ + μ J` is
coercive on `D` with constant `1 - θ - ε`. It maps onto `E*` because `C` is smaller than the
coercivity constant `1 - θ` of `L + ℓ† ℓ + μ J`, so solvability for `L⋆` follows from solvability
for `L` by a contraction in the dual space. A resolvent estimate makes the matrix
`M(μ) = ℓ A_μ⁻¹ ℓ†` continuous in `μ`, and at a zero `μ` of `det (1 - M(μ))` the operator `L⋆ + μ J`
has a nonzero kernel vector in `D`. For `μ > c_F` the matrices `1 - s M(μ)` with `0 ≤ s ≤ 1` are
nonsingular, so `det (1 - M(μ)) > 0`. At `μ = 0`, the segment from `A_0` to `L⋆ (1 + Φ ℓ)` consists
of coercive maps, and each corresponds to a nonsingular matrix on the segment from `1` to
`(1 - M(0)) (1 + ℓ Φ)`. Hence `det (1 - M(0))` has the sign of `det (1 + ℓ Φ)`, and the intermediate
value theorem gives a zero. Completeness of `E` is not needed.

In applications the coordinates are finitely many bounded functionals `F i` and the
reconstruction combines finitely many fields `φ j`; `coordinateMap` and `reconstruction` build
`ℓ` and `Φ` from them, and the matrix `ℓ Φ` has entries `F i (φ j)`.

For the self-similar Navier–Stokes linearization, `J` is the `L²` pairing, `L` is the
linearization at an approximate profile and `L⋆` the linearization at the exact profile. The
criterion gives a real eigenvalue in `(0, c_F)` from the sign of one determinant. Hou, Wang and
Yang obtain the unstable eigenpair of this linearization (their Proposition 2) by a fixed-point
argument built on a finite-rank approximation (their Section 4.4); the determinant criterion
is a different route to the eigenvalue.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 1.3, Proposition 2,
  and Section 4.4. <https://arxiv.org/abs/2509.25116v2>
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

theorem reconstruction_apply (φ : Fin m → E) (q : EuclideanSpace ℝ (Fin m)) :
    reconstruction φ q = ∑ j, q j • φ j := by
  simp [reconstruction]

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
/-- A bounded perturbation whose norm is below the coercivity constant keeps a coercive map onto the
dual space. The perturbed map is coercive with constant `κ - ‖C‖`; the proof inverts it by a
contraction in the dual space. -/
theorem surjective_add_of_coercive (C : E →L[ℝ] StrongDual ℝ E) (hC : ‖C‖ < κ) :
    Function.Surjective (A + C.toLinearMap ∘ₗ D.subtype) := by
  set S := coerciveInverse A hκ hA hsurj
  have hsmall : ‖C.comp S‖ < 1 := by
    calc ‖C.comp S‖ ≤ ‖C‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖C‖ * κ⁻¹ :=
        mul_le_mul_of_nonneg_left (norm_coerciveInverse_le A hκ hA hsurj) (norm_nonneg C)
      _ < κ * κ⁻¹ := mul_lt_mul_of_pos_right hC (inv_pos.2 hκ)
      _ = 1 := mul_inv_cancel₀ hκ.ne'
  have hg : Function.Surjective (ContinuousLinearMap.id ℝ (StrongDual ℝ E) + C.comp S) :=
    surjective_of_uniform_bound_of_norm_sub_mul_lt_one (ContinuousLinearMap.id ℝ _) _ (C := 1)
      (fun u ↦ by simp) (fun u ↦ ⟨u, rfl⟩) (by simpa using hsmall)
  intro f
  obtain ⟨y, hy⟩ := hg f
  refine ⟨⟨S y, coerciveInverse_mem A hκ hA hsurj y⟩, ?_⟩
  have h1 := apply_coerciveInverse A hκ hA hsurj y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    ContinuousLinearMap.coe_coe]
  rw [h1]
  simpa using hy

end CoerciveInverse

section ShiftedOperator

variable {D : Submodule ℝ E}

/-- The shifted operator `P + ℓ† ℓ + μ J` on a subspace `D`. -/
def shiftedOperator (P : D →ₗ[ℝ] StrongDual ℝ E) (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m))
    (J : E →L[ℝ] StrongDual ℝ E) (μ : ℝ) : D →ₗ[ℝ] StrongDual ℝ E :=
  P + ((coordTranspose ℓ).comp ℓ + μ • J).toLinearMap ∘ₗ D.subtype

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

/-- **Finite-rank determinant criterion.** Let `L` and `L⋆ = L + C` with `‖C‖ ≤ ε` act from a
subspace `D` into the dual space. Suppose `L + ℓ† ℓ` is coercive on `D` with constant `1 - θ`, the
reconstruction `Φ` with values in `D` has residual `‖L Φ ℓ - ℓ† ℓ‖ ≤ δ` and amplification
`‖1 + Φ ℓ‖ ≤ t_G`, and `J` is a positive form with `‖ℓ h‖² ≤ c_F ⟪J h, h⟫`. If `L + ℓ† ℓ + μ J` maps
`D` onto the dual space for every `μ ≥ 0`, the margins `1 - θ - ε` and `1 - θ - δ - ε t_G` are
positive and `det (1 + Λ) < 0` for the matrix `Λ = ℓ Φ`, then `L⋆ + μ J` has a nonzero kernel vector
in `D` for some `0 < μ < c_F`.

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
  classical
  set κ := 1 - θ - ε with hκdef
  have hε : 0 ≤ ε := (norm_nonneg C).trans hCnorm
  set A := shiftedOperator Lstar ℓ J with hAdef
  -- Coercivity of `A μ = L⋆ + ℓ† ℓ + μ J` with constant `1 - θ - ε`.
  have hcaptureStar : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ Lstar x x + ‖ℓ x‖ ^ 2 := fun x ↦ by
    have h1 : |C x x| ≤ ε * ‖(x : E)‖ ^ 2 := by
      rw [← Real.norm_eq_abs, pow_two, ← mul_assoc]
      exact (C.le_opNorm₂ x x).trans (by gcongr)
    rw [hC, add_apply]
    linarith [neg_abs_le (C x x), hcapture x]
  have hA0coer : ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ (Lstar x + coordTranspose ℓ (ℓ x)) x := by
    intro x
    rw [add_apply, coordTranspose_apply_self]
    exact hcaptureStar x
  have hAcoer : ∀ μ, 0 ≤ μ → ∀ x : D, κ * ‖(x : E)‖ ^ 2 ≤ A μ x x := fun μ hμ ↦
    coercive_shiftedOperator Lstar ℓ J hμ hcaptureStar hJ
  -- Solvability for `L⋆` follows from solvability for `L`, since `‖C‖ < 1 - θ`.
  have hAsurj : ∀ μ, 0 ≤ μ → Function.Surjective (A μ) := fun μ hμ ↦
    surjective_shiftedOperator_of_perturbation L Lstar ℓ J (by linarith) hμ hcapture hJ
      (fun f ↦ by
        obtain ⟨h, hh⟩ := hsolveL μ hμ f
        exact ⟨h, by rw [shiftedOperator_apply]; exact hh⟩) C hC (by linarith)
  -- The solution operators, extended to negative parameters by their value at zero.
  let S : ℝ → StrongDual ℝ E →L[ℝ] E := fun μ ↦
    coerciveInverse (A (max μ 0)) hκ (hAcoer _ (le_max_right μ 0)) (hAsurj _ (le_max_right μ 0))
  have hSmem : ∀ μ f, S μ f ∈ D := fun μ f ↦ coerciveInverse_mem _ _ _ _ f
  have hSeq : ∀ μ f, A (max μ 0) ⟨S μ f, hSmem μ f⟩ = f := fun μ f ↦
    apply_coerciveInverse _ _ _ _ f
  have hSeq' : ∀ μ, 0 ≤ μ → ∀ f, A μ ⟨S μ f, hSmem μ f⟩ = f := fun μ hμ f ↦ by
    simpa only [max_eq_left hμ] using hSeq μ f
  have hSnorm : ∀ μ f, ‖S μ f‖ ≤ κ⁻¹ * ‖f‖ := fun μ f ↦
    (ContinuousLinearMap.le_opNorm _ f).trans
      (mul_le_mul_of_nonneg_right (norm_coerciveInverse_le _ _ _ _) (norm_nonneg f))
  -- Resolvent estimate: the solutions depend Lipschitz continuously on the parameter.
  have hSlip : ∀ μ ν f, ‖S μ f - S ν f‖ ≤ κ⁻¹ * (‖J‖ * (κ⁻¹ * ‖f‖)) * |μ - ν| := by
    intro μ ν f
    set x : D := ⟨S μ f, hSmem μ f⟩
    set y : D := ⟨S ν f, hSmem ν f⟩
    have hy := hSeq ν f
    have hdiff : A (max μ 0) (x - y) = (max ν 0 - max μ 0) • J y := by
      rw [map_sub, hSeq μ f, hAdef, shiftedOperator_apply]
      rw [hAdef, shiftedOperator_apply] at hy
      rw [← hy]
      module
    have hb := norm_le_inv_mul_of_coercive (A (max μ 0)) hκ (hAcoer _ (le_max_right μ 0))
      (x - y)
    rw [hdiff, norm_smul, Real.norm_eq_abs] at hb
    have hJy : ‖J y‖ ≤ ‖J‖ * (κ⁻¹ * ‖f‖) :=
      (J.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hSnorm ν f) (norm_nonneg J))
    have hmax : |max ν 0 - max μ 0| ≤ |μ - ν| := by
      rw [abs_sub_comm]
      exact abs_max_sub_max_le_abs μ ν 0
    calc ‖S μ f - S ν f‖ = ‖((x - y : D) : E)‖ := rfl
      _ ≤ κ⁻¹ * (|max ν 0 - max μ 0| * ‖J y‖) := hb
      _ ≤ κ⁻¹ * (|μ - ν| * (‖J‖ * (κ⁻¹ * ‖f‖))) := by
        gcongr
      _ = κ⁻¹ * (‖J‖ * (κ⁻¹ * ‖f‖)) * |μ - ν| := by ring
  have hScont : ∀ f, Continuous fun μ ↦ S μ f := fun f ↦
    (LipschitzWith.of_dist_le' fun μ ν ↦ by
      rw [dist_eq_norm, Real.dist_eq]
      exact hSlip μ ν f).continuous
  -- The determinant `det (1 - ℓ A_μ⁻¹ ℓ†)` is continuous in `μ`.
  have hMcont : Continuous fun μ ↦ compressionMatrix ℓ (S μ) := continuous_matrix fun i j ↦
    ((EuclideanSpace.proj i).comp ℓ).continuous.comp (hScont _)
  have hDcont : Continuous fun μ ↦ (1 - compressionMatrix ℓ (S μ)).det :=
    (continuous_const.sub hMcont).matrix_det
  -- The sign at `μ = 0`.
  have hD0 : (1 - compressionMatrix ℓ (S 0)).det < 0 := by
    have hpos := det_mul_pos_of_coercive_homotopy Lstar ℓ Φ hΦ (S 0) (hSmem 0)
      (fun f ↦ by simpa [hAdef, shiftedOperator_apply] using hSeq' 0 le_rfl f) hκ hβ hA0coer
      (coercive_comp_reconstruction L Lstar ℓ Φ hΦ hcapture hres htG C hC hCnorm) hΛ
    rw [Matrix.det_mul] at hpos
    exact neg_of_mul_pos_left hpos hdet.le
  -- The sign for a large parameter.
  set μp := max cF 0 + 1 with hμpdef
  have hμp0 : 0 < μp := by linarith [le_max_right cF 0]
  have hμpc : cF < μp := by linarith [le_max_left cF 0]
  have hDp : 0 < (1 - compressionMatrix ℓ (S μp)).det :=
    det_one_sub_compressionMatrix_pos ℓ (S μp) (hSmem μp) Lstar J (hSeq' μp hμp0.le)
      (fun x ↦ (mul_nonneg hκ.le (sq_nonneg _)).trans (hA0coer x)) hJ hJℓ hμpc
  -- The intermediate value theorem gives a zero, which is a kernel vector.
  obtain ⟨μs, hμs, hDμs⟩ := intermediate_value_Icc hμp0.le hDcont.continuousOn
    (show (0 : ℝ) ∈ Icc _ _ from ⟨hD0.le, hDp.le⟩)
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
  exact ⟨μs, ⟨hμspos, lt_of_apply_add_smul_eq_zero Lstar J ℓ hκ hA0coer hJ hJℓ hx0 hx'⟩,
    x, hx0, hx'⟩

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
