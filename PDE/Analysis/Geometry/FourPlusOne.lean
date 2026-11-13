/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
public import PDE.Analysis.Integration.Polar
public import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Four-plus-one Euclidean coordinates

Coordinate inclusions, orthogonal actions, and first and iterated chain rules for
ℝ⁴ × ℝ and the two-coordinate plane inside ℝ⁵. The function need not be radially
symmetric.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv SobolevSpace
open scoped ENNReal RealInnerProductSpace Topology

namespace PDE.Analysis

/-- Embed `ℝ⁴ × ℝ` as the Cartesian coordinates of `ℝ⁵`.
-/
def fourPlusOnePoint (y : ℝ^4) (z : ℝ) :
    ℝ^5 :=
  WithLp.toLp 2 (fun i : Fin 5 ↦
    if h : i.val < 4 then y ⟨i.val, h⟩ else z)

/-- Apply an orthogonal transformation to the first four coordinates of
`ℝ⁵`, leaving the axial coordinate fixed.
-/
def firstFourLinearIsometryEquiv
    (e : ℝ^4 ≃ₗᵢ[ℝ] ℝ^4) :
    ℝ^5 ≃ₗᵢ[ℝ] ℝ^5 :=
  let split := PDE.Analysis.euclideanSumLinearIsometry 4 1
  let product :
      WithLp 2 (ℝ^4 × ℝ^1) ≃ₗᵢ[ℝ]
        WithLp 2 (ℝ^4 × ℝ^1) :=
    { toLinearEquiv :=
        (WithLp.linearEquiv 2 ℝ _).trans
          ((LinearEquiv.prodCongr e.toLinearEquiv
            (LinearEquiv.refl ℝ (ℝ^1))).trans
              (WithLp.linearEquiv 2 ℝ _).symm)
      norm_map' := by
        intro p
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        simp only [WithLp.prod_norm_sq_eq_of_L2]
        simp }
  split.trans (product.trans split.symm)

/-- Linear inclusion of the first four Cartesian coordinates into `ℝ⁵`. -/
def firstFourEmbeddingFive :
    ℝ^4 →L[ℝ] ℝ^5 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ fourPlusOnePoint y 0
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [fourPlusOnePoint]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [fourPlusOnePoint] }

/-- The inclusion of `ℝ⁴` is `fourPlusOnePoint y 0`: axial coordinate zero.
-/
@[simp]
theorem firstFourEmbeddingFive_apply (y : ℝ^4) :
    firstFourEmbeddingFive y = fourPlusOnePoint y 0 := rfl

/-- The inclusion sends the `i`-th standard basis vector of `ℝ⁴` to the
`i.castSucc`-th standard basis vector of `ℝ⁵`.
-/
theorem firstFourEmbeddingFive_basis (i : Fin 4) :
    firstFourEmbeddingFive (EuclideanSpace.single i 1) =
      EuclideanSpace.single i.castSucc 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [firstFourEmbeddingFive, fourPlusOnePoint, PiLp.single_apply]

/-- Affine slice of `ℝ⁵` at a fixed axial coordinate: `y ↦ (y, z)`.
-/
def firstFourSliceFive (z : ℝ) (y : ℝ^4) :
    ℝ^5 := fourPlusOnePoint y z

/-- A first derivative along a fixed-`z` four-dimensional slice is the
corresponding Cartesian derivative in `ℝ⁵`, by the chain rule for the affine
slice map (differentiability of `F` at the slice point is the only hypothesis).
-/
theorem partialDeriv_comp_firstFourSliceFive
    (F : ℝ^5 → ℝ) (z : ℝ)
    (y : ℝ^4) (i : Fin 4)
    (hF : DifferentiableAt ℝ F (firstFourSliceFive z y)) :
    (∂[i] (F ∘ firstFourSliceFive z)) y =
      (∂[i.castSucc] F) (firstFourSliceFive z y) := by
  have hslice : HasFDerivAt (firstFourSliceFive z) firstFourEmbeddingFive y := by
    have h := (firstFourEmbeddingFive.hasFDerivAt (x := y)).add_const
      (fourPlusOnePoint (0 : ℝ^4) z)
    convert h using 1
    all_goals (funext v; ext j; fin_cases j <;>
      simp [firstFourSliceFive, fourPlusOnePoint])
  have hc := hF.hasFDerivAt.comp y hslice
  change fderiv ℝ (F ∘ firstFourSliceFive z) y
      (EuclideanSpace.single i 1) =
    fderiv ℝ F (firstFourSliceFive z y)
      (EuclideanSpace.single i.castSucc 1)
  rw [hc.fderiv]
  change fderiv ℝ F (firstFourSliceFive z y)
      (firstFourEmbeddingFive (EuclideanSpace.single i 1)) = _
  rw [firstFourEmbeddingFive_basis]

/-- Two derivatives along a fixed-`z` slice give the corresponding diagonal
entry of the five-dimensional Hessian. Smoothness of `F` is assumed so that the
first derivative is again differentiable and the chain rule can be applied
twice.
-/
theorem iteratedPartialDeriv_comp_firstFourSliceFive
    (F : ℝ^5 → ℝ) (z : ℝ)
    (y : ℝ^4) (i : Fin 4)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    iteratedPartialDeriv (n := 4) [i, i]
        (F ∘ firstFourSliceFive z) y =
      iteratedPartialDeriv (n := 5) [i.castSucc, i.castSucc] F
        (firstFourSliceFive z y) := by
  have hfirst : (fun v : ℝ^4 ↦
      (∂[i] (F ∘ firstFourSliceFive z)) v) =
      fun v ↦ (∂[i.castSucc] F) (firstFourSliceFive z v) := by
    funext v
    exact partialDeriv_comp_firstFourSliceFive F z v i
      ((hF.differentiable (by simp)).differentiableAt)
  have hFi : ContDiff ℝ (⊤ : ℕ∞)
      (fun X ↦ (∂[i.castSucc] F) X) := by
    simpa [iteratedPartialDeriv] using
      (contDiff_top_iteratedPartialDeriv hF [i.castSucc])
  simp only [iteratedPartialDeriv]
  rw [hfirst]
  exact partialDeriv_comp_firstFourSliceFive
    (fun X ↦ (∂[i.castSucc] F) X) z y i
      ((hFi.differentiable (by simp)).differentiableAt)

/-- Restricting a differentiable profile to a radial coordinate line gives
its radial partial derivative. No continuity of the derivative is needed. -/
theorem deriv_profileRadialSlice_of_differentiable
    (ψ : (ℝ^2 → ℝ)) (r z : ℝ) (hψ : Differentiable ℝ ψ) :
    deriv (fun s ↦ ψ (EuclideanSpace.single 0 s +
      EuclideanSpace.single 1 z)) r =
      (∂[0] ψ)
        (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z) := by
  let x : (ℝ^2) := EuclideanSpace.single 0 r + EuclideanSpace.single 1 z
  have h := partialDeriv_eq_deriv_coordinateLine 0 x
    (hψ x)
  have hx0 : x 0 = r := by simp [x]
  rw [h, hx0]
  congr 1
  funext s
  congr 1
  ext i
  fin_cases i <;> simp [x, coordinateLine]

/-- Ordinary differentiation of the radial slice `s ↦ ψ(s, z)` agrees with the
first-coordinate partial derivative `∂_r ψ` at `(r, z)`.
-/
theorem deriv_profileRadialSlice
    (ψ : (ℝ^2 → ℝ)) (r z : ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    deriv (fun s ↦ ψ (EuclideanSpace.single 0 s +
      EuclideanSpace.single 1 z)) r =
      (∂[0] ψ)
        (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z) := by
  exact deriv_profileRadialSlice_of_differentiable ψ r z
    (hψ.differentiable (by simp))

/-- The second ordinary derivative of the radial slice `s ↦ ψ(s, z)` is the
iterated partial derivative `∂_r ∂_r ψ` at `(r, z)`.
-/
theorem deriv_deriv_profileRadialSlice
    (ψ : (ℝ^2 → ℝ)) (r z : ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    deriv (deriv (fun s ↦ ψ (EuclideanSpace.single 0 s +
      EuclideanSpace.single 1 z))) r =
      iteratedPartialDeriv (n := 2) [0, 0] ψ
        (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z) := by
  have hfirst : deriv (fun s ↦ ψ (EuclideanSpace.single 0 s +
      EuclideanSpace.single 1 z)) =
      fun s ↦ (∂[0] ψ)
        (EuclideanSpace.single 0 s + EuclideanSpace.single 1 z) := by
    funext s
    exact deriv_profileRadialSlice ψ s z hψ
  rw [hfirst]
  have hψ0 : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (∂[0] ψ) x) := by
    simpa [iteratedPartialDeriv] using
      (contDiff_top_iteratedPartialDeriv hψ [0])
  simpa [iteratedPartialDeriv] using
    deriv_profileRadialSlice (fun x ↦ (∂[0] ψ) x)
      r z hψ0

/-- Linear embedding of the profile plane into `ℝ⁵`, `(r, z) ↦ (r, 0, 0, 0, z)`:
the radial coordinate becomes the first Cartesian coordinate and the axial
coordinate the fifth. Restricting a function on `ℝ⁵` that is radial in the
first four coordinates along this embedding recovers its profile.
-/
def profileAxisEmbeddingFive :
    (ℝ^2) →L[ℝ] ℝ^5 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦
        fourPlusOnePoint (EuclideanSpace.single 0 (x 0)) (x 1)
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [fourPlusOnePoint]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [fourPlusOnePoint] }

/-- Unfolding lemma: the profile-axis embedding of `x` is
`fourPlusOnePoint (single 0 (x 0)) (x 1)`.
-/
@[simp]
theorem profileAxisEmbeddingFive_apply (x : (ℝ^2)) :
    profileAxisEmbeddingFive x =
      fourPlusOnePoint (EuclideanSpace.single 0 (x 0)) (x 1) := rfl

/-- The profile-plane embedding preserves the Euclidean norm. -/
theorem norm_profileAxisEmbeddingFive (x : (ℝ^2)) :
    ‖profileAxisEmbeddingFive x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, profileAxisEmbeddingFive_apply,
    fourPlusOnePoint, Fin.sum_univ_succ, PiLp.single_apply]

/-- The radial basis vector of the profile plane maps to the first basis vector
of `ℝ⁵`.
-/
theorem profileAxisEmbeddingFive_basis_zero :
    profileAxisEmbeddingFive (EuclideanSpace.single 0 1) =
      EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [profileAxisEmbeddingFive, fourPlusOnePoint,
    PiLp.single_apply]

/-- The axial basis vector of the profile plane maps to the fifth basis vector
of `ℝ⁵`.
-/
theorem profileAxisEmbeddingFive_basis_one :
    profileAxisEmbeddingFive (EuclideanSpace.single 1 1) =
      EuclideanSpace.single 4 1 := by
  ext i
  fin_cases i <;> simp [profileAxisEmbeddingFive, fourPlusOnePoint,
    PiLp.single_apply]

/-- Chain rule for the radial profile coordinate along the axis embedding:
`∂_r (F ∘ ι) = (∂_0 F) ∘ ι`, where `ι = profileAxisEmbeddingFive`.
-/
theorem partialDeriv_comp_profileAxisEmbeddingFive_zero
    (F : ℝ^5 → ℝ) (x : (ℝ^2))
    (hF : DifferentiableAt ℝ F (profileAxisEmbeddingFive x)) :
    (∂[0] (F ∘ profileAxisEmbeddingFive)) x =
      (∂[0] F) (profileAxisEmbeddingFive x) := by
  have hc := hF.hasFDerivAt.comp x profileAxisEmbeddingFive.hasFDerivAt
  change fderiv ℝ (F ∘ profileAxisEmbeddingFive) x
      (EuclideanSpace.single 0 1) =
    fderiv ℝ F (profileAxisEmbeddingFive x)
      (EuclideanSpace.single 0 1)
  rw [hc.fderiv]
  change fderiv ℝ F (profileAxisEmbeddingFive x)
      (profileAxisEmbeddingFive (EuclideanSpace.single 0 1)) = _
  rw [profileAxisEmbeddingFive_basis_zero]

/-- Chain rule for the axial profile coordinate along the axis embedding:
`∂_z (F ∘ ι) = (∂_4 F) ∘ ι`, where `ι = profileAxisEmbeddingFive`.
-/
theorem partialDeriv_comp_profileAxisEmbeddingFive_one
    (F : ℝ^5 → ℝ) (x : (ℝ^2))
    (hF : DifferentiableAt ℝ F (profileAxisEmbeddingFive x)) :
    (∂[1] (F ∘ profileAxisEmbeddingFive)) x =
      (∂[4] F) (profileAxisEmbeddingFive x) := by
  have hc := hF.hasFDerivAt.comp x profileAxisEmbeddingFive.hasFDerivAt
  change fderiv ℝ (F ∘ profileAxisEmbeddingFive) x
      (EuclideanSpace.single 1 1) =
    fderiv ℝ F (profileAxisEmbeddingFive x)
      (EuclideanSpace.single 4 1)
  rw [hc.fderiv]
  change fderiv ℝ F (profileAxisEmbeddingFive x)
      (profileAxisEmbeddingFive (EuclideanSpace.single 1 1)) = _
  rw [profileAxisEmbeddingFive_basis_one]

/-- A profile derivative along the axis embedding is the corresponding
Cartesian derivative: index `0` stays `0`, and index `1` becomes `4`.
Only differentiability of the function is required. -/
theorem partialDeriv_comp_profileAxisEmbeddingFive
    (F : ℝ^5 → ℝ) (i : Fin 2) (hF : Differentiable ℝ F) :
    (∂[i] (F ∘ profileAxisEmbeddingFive)) =
      (∂[(if i = 0 then (0 : Fin 5) else 4)] F) ∘
        profileAxisEmbeddingFive := by
  funext x
  fin_cases i
  · exact partialDeriv_comp_profileAxisEmbeddingFive_zero F x (hF _)
  · exact partialDeriv_comp_profileAxisEmbeddingFive_one F x (hF _)

/-- Two axial profile derivatives are the `(4,4)` Cartesian Hessian entry of
the five-dimensional function restricted to the profile axis, for smooth `F`.
-/
theorem iteratedPartialDeriv_comp_profileAxisEmbeddingFive_one_one
    (F : ℝ^5 → ℝ) (x : (ℝ^2))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    iteratedPartialDeriv (n := 2) [1, 1]
        (F ∘ profileAxisEmbeddingFive) x =
      iteratedPartialDeriv (n := 5) [4, 4] F
        (profileAxisEmbeddingFive x) := by
  have hfirst : (fun y : (ℝ^2) ↦ (∂[1] (F ∘ profileAxisEmbeddingFive)) y) =
      fun y ↦ (∂[4] F) (profileAxisEmbeddingFive y) := by
    funext y
    exact partialDeriv_comp_profileAxisEmbeddingFive_one F y
      ((hF.differentiable (by simp)).differentiableAt)
  have hF4 : ContDiff ℝ (⊤ : ℕ∞)
      (fun Y ↦ (∂[4] F) Y) := by
    simpa [iteratedPartialDeriv] using
      (contDiff_top_iteratedPartialDeriv hF [4])
  simp only [iteratedPartialDeriv]
  rw [hfirst]
  exact partialDeriv_comp_profileAxisEmbeddingFive_one
    (fun Y ↦ (∂[4] F) Y) x
      ((hF4.differentiable (by simp)).differentiableAt)

/-- Any finite block of axial profile derivatives becomes the same-size block
of fifth-coordinate derivatives after restriction to the profile-axis
embedding.
-/
theorem iteratedPartialDeriv_comp_profileAxisEmbeddingFive_axial
    (ell : ℕ) (F : ℝ^5 → ℝ) (x : (ℝ^2))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    iteratedPartialDeriv (n := 2) (List.replicate ell 1)
        (F ∘ profileAxisEmbeddingFive) x =
      iteratedPartialDeriv (n := 5) (List.replicate ell 4) F
        (profileAxisEmbeddingFive x) := by
  induction ell generalizing x with
  | zero => simp [iteratedPartialDeriv]
  | succ ell ih =>
      have ihfun :
          (fun y : (ℝ^2) ↦ iteratedPartialDeriv (n := 2)
            (List.replicate ell 1) (F ∘ profileAxisEmbeddingFive) y) =
          fun y ↦ iteratedPartialDeriv (n := 5)
            (List.replicate ell 4) F (profileAxisEmbeddingFive y) := by
        funext y
        exact ih y
      have hFell : ContDiff ℝ (⊤ : ℕ∞)
          (fun Y ↦ iteratedPartialDeriv (n := 5)
            (List.replicate ell 4) F Y) :=
        contDiff_top_iteratedPartialDeriv hF (List.replicate ell 4)
      simp only [List.replicate_succ, iteratedPartialDeriv]
      rw [ihfun]
      exact partialDeriv_comp_profileAxisEmbeddingFive_one
        (fun Y ↦ iteratedPartialDeriv (n := 5)
          (List.replicate ell 4) F Y) x
        ((hFell.differentiable (by simp)).differentiableAt)

/-- General coordinate-word chain rule for the profile-axis embedding.  A
radial profile index `0` maps to Cartesian index `0`, while the axial profile
index `1` maps to Cartesian index `4`.
-/
theorem iteratedPartialDeriv_comp_profileAxisEmbeddingFive
    (alpha : List (Fin 2)) (F : ℝ^5 → ℝ) (x : (ℝ^2))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    iteratedPartialDeriv (n := 2) alpha
        (F ∘ profileAxisEmbeddingFive) x =
      iteratedPartialDeriv (n := 5)
        (alpha.map fun i ↦ if i = 0 then (0 : Fin 5) else 4) F
        (profileAxisEmbeddingFive x) := by
  induction alpha generalizing x with
  | nil => simp [iteratedPartialDeriv]
  | cons i rest ih =>
      have ihfun :
          (fun y : (ℝ^2) ↦ iteratedPartialDeriv (n := 2) rest
            (F ∘ profileAxisEmbeddingFive) y) =
          fun y ↦ iteratedPartialDeriv (n := 5)
            (rest.map fun j ↦ if j = 0 then (0 : Fin 5) else 4) F
            (profileAxisEmbeddingFive y) := by
        funext y
        exact ih y
      have hFrest : ContDiff ℝ (⊤ : ℕ∞)
          (fun Y ↦ iteratedPartialDeriv (n := 5)
            (rest.map fun j ↦ if j = 0 then (0 : Fin 5) else 4) F Y) :=
        contDiff_top_iteratedPartialDeriv hF _
      simp only [List.map_cons, iteratedPartialDeriv]
      rw [ihfun]
      fin_cases i
      · change (∂[0] ((fun Y ↦ iteratedPartialDeriv (n := 5)
            (rest.map fun j ↦ if j = 0 then (0 : Fin 5) else 4) F Y) ∘
            profileAxisEmbeddingFive)) x = _
        exact partialDeriv_comp_profileAxisEmbeddingFive_zero
          (fun Y ↦ iteratedPartialDeriv (n := 5)
            (rest.map fun j ↦ if j = 0 then (0 : Fin 5) else 4) F Y) x
          ((hFrest.differentiable (by simp)).differentiableAt)
      · change (∂[1] ((fun Y ↦ iteratedPartialDeriv (n := 5)
            (rest.map fun j ↦ if j = 0 then (0 : Fin 5) else 4) F Y) ∘
            profileAxisEmbeddingFive)) x = _
        exact partialDeriv_comp_profileAxisEmbeddingFive_one
          (fun Y ↦ iteratedPartialDeriv (n := 5)
            (rest.map fun j ↦ if j = 0 then (0 : Fin 5) else 4) F Y) x
          ((hFrest.differentiable (by simp)).differentiableAt)

/-- The mixed profile derivative `∂_z ∂_r (F ∘ ι)` is the `(4,0)` Cartesian
Hessian entry of the smooth five-dimensional function `F` along the axis
embedding `ι`. (The list `[1, 0]` applies the radial derivative first.)
-/
theorem iteratedPartialDeriv_comp_profileAxisEmbeddingFive_one_zero
    (F : ℝ^5 → ℝ) (x : (ℝ^2))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    iteratedPartialDeriv (n := 2) [1, 0]
        (F ∘ profileAxisEmbeddingFive) x =
      iteratedPartialDeriv (n := 5) [4, 0] F
        (profileAxisEmbeddingFive x) := by
  have hfirst : (fun y : (ℝ^2) ↦ (∂[0] (F ∘ profileAxisEmbeddingFive)) y) =
      fun y ↦ (∂[0] F) (profileAxisEmbeddingFive y) := by
    funext y
    exact partialDeriv_comp_profileAxisEmbeddingFive_zero F y
      ((hF.differentiable (by simp)).differentiableAt)
  have hF0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun Y ↦ (∂[0] F) Y) := by
    simpa [iteratedPartialDeriv] using
      (contDiff_top_iteratedPartialDeriv hF [0])
  simp only [iteratedPartialDeriv]
  rw [hfirst]
  exact partialDeriv_comp_profileAxisEmbeddingFive_one
    (fun Y ↦ (∂[0] F) Y) x
      ((hF0.differentiable (by simp)).differentiableAt)

/-- The orthogonal coordinate split sends `fourPlusOnePoint y z` to `(y, z)`,
with `z` represented in one-dimensional Euclidean space. -/
theorem euclideanSumMeasurableEquiv_fourPlusOnePoint
    (y : ℝ^4) (z : ℝ) :
    PDE.Analysis.euclideanSumMeasurableEquiv 4 1 (fourPlusOnePoint y z) =
      (y, EuclideanSpace.single 0 z) := by
  ext i
  · simp only [Nat.reduceAdd, PDE.Analysis.euclideanSumMeasurableEquiv,
      PDE.Analysis.euclideanSumLinearIsometry, fourPlusOnePoint,
      MeasurableEquiv.trans_apply,
      LinearIsometryEquiv.coe_toMeasurableEquiv,
      LinearIsometryEquiv.trans_apply, MeasurableEquiv.toLp_symm_apply,
      PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
      LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply, Equiv.symm_symm]
    have hv :
        (finSumFinEquiv (Sum.inl i : Fin 4 ⊕ Fin 1)).val = i.val :=
      congrArg Fin.val (finSumFinEquiv_apply_left i)
    split_ifs with h
    · exact congrArg (fun k : Fin 4 ↦ y k) (Fin.ext hv)
    · omega
  · fin_cases i
    simp only [Nat.reduceAdd, PDE.Analysis.euclideanSumMeasurableEquiv,
      PDE.Analysis.euclideanSumLinearIsometry, fourPlusOnePoint,
      MeasurableEquiv.trans_apply,
      LinearIsometryEquiv.coe_toMeasurableEquiv,
      LinearIsometryEquiv.trans_apply, MeasurableEquiv.toLp_symm_apply,
      PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
      LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply, Equiv.symm_symm, Fin.zero_eta,
      Fin.isValue, PiLp.single_eq_same, dite_eq_right_iff]
    have hv :
        (finSumFinEquiv (Sum.inr (0 : Fin 1) : Fin 4 ⊕ Fin 1)).val = 4 :=
      congrArg Fin.val (finSumFinEquiv_apply_right (0 : Fin 1))
    intro h
    omega

/-- The isometry `firstFourLinearIsometryEquiv e` acts on `ℝ⁴ × ℝ` coordinates
by `(y, z) ↦ (e y, z)`: it rotates the first four coordinates and fixes the
axial one.
-/
@[simp]
theorem firstFourLinearIsometryEquiv_fourPlusOnePoint
    (e : ℝ^4 ≃ₗᵢ[ℝ] ℝ^4)
    (y : ℝ^4) (z : ℝ) :
    firstFourLinearIsometryEquiv e (fourPlusOnePoint y z) =
      fourPlusOnePoint (e y) z := by
  let split := PDE.Analysis.euclideanSumLinearIsometry 4 1
  have hs (v : ℝ^4) :
      split (fourPlusOnePoint v z) =
        WithLp.toLp 2 (v, EuclideanSpace.single 0 z) := by
    apply WithLp.ofLp_injective 2
    have h := euclideanSumMeasurableEquiv_fourPlusOnePoint v z
    change (split (fourPlusOnePoint v z)).ofLp =
      (v, EuclideanSpace.single 0 z) at h
    exact h
  apply split.injective
  simp [firstFourLinearIsometryEquiv, split, hs]

/-- Inverse coordinate form of the four-plus-one split: the library's
`ℝ⁴ × ℝ¹ ≃ ℝ⁵` measurable equivalence sends `(y, w)` back to
`fourPlusOnePoint y (w 0)`.
-/
theorem euclideanSumMeasurableEquiv_symm_fourOne
    (p : ℝ^4 × ℝ^1) :
    (PDE.Analysis.euclideanSumMeasurableEquiv 4 1).symm p =
      fourPlusOnePoint p.1 (p.2 0) := by
  apply (PDE.Analysis.euclideanSumMeasurableEquiv 4 1).injective
  rw [MeasurableEquiv.apply_symm_apply,
    euclideanSumMeasurableEquiv_fourPlusOnePoint]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i
    simp

end PDE.Analysis
