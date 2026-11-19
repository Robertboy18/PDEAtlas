/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.Frame
public import CAS.Analysis.Matrix.QuadraticForm
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Spherical matrices as Cartesian operators

Conjugation by the spherical frame turns a component matrix into its
Cartesian continuous linear operator. The construction preserves the
operator norm, self-adjointness, and the scalar quadratic form used by
energy estimates.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open scoped RealInnerProductSpace Matrix BigOperators

/-- The Cartesian operator whose component matrix in the spherical frame is `A`. -/
def matrixInFrame (θ φ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ^3 →L[ℝ] ℝ^3 :=
  (frameBasis θ φ).repr.symm.conjStarAlgEquiv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) A)

/-- Applying the Cartesian operator means transforming to frame coordinates, multiplying,
and transforming back. -/
theorem matrixInFrame_apply (θ φ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ^3) :
    matrixInFrame θ φ A v =
      (frameBasis θ φ).repr.symm
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) A ((frameBasis θ φ).repr v)) := by
  simp only [matrixInFrame, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]

/-- The Cartesian operator has precisely the Euclidean operator norm of its component matrix. -/
theorem norm_matrixInFrame (θ φ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖matrixInFrame θ φ A‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) A‖ := by
  rw [matrixInFrame, LinearIsometryEquiv.conjStarAlgEquiv_apply]
  simp only [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- A symmetric real matrix gives a self-adjoint Cartesian operator. -/
theorem isSelfAdjoint_matrixInFrame (θ φ : ℝ) {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.IsSymm) : IsSelfAdjoint (matrixInFrame θ φ A) := by
  have h : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) A) :=
    (Matrix.isHermitian_iff_isSymm.mpr hA).isSelfAdjoint.map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3))
  exact h.map (frameBasis θ φ).repr.symm.conjStarAlgEquiv

/-- Cartesian pairing is the component quadratic pairing in the orthonormal frame. -/
theorem inner_matrixInFrame (θ φ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (v w : ℝ^3) :
    ⟪matrixInFrame θ φ A v, w⟫ =
      (frameBasis θ φ).repr w ⬝ᵥ (A *ᵥ (frameBasis θ φ).repr v) := by
  rw [matrixInFrame_apply, LinearIsometryEquiv.inner_map_eq_flip,
    LinearIsometryEquiv.symm_symm, real_inner_comm, Matrix.inner_toEuclideanCLM]

/-- Frame coordinate self-pairing is the original vector's squared Euclidean norm. -/
theorem dotProduct_frameBasis_repr_self (θ φ : ℝ) (v : ℝ^3) :
    (frameBasis θ φ).repr v ⬝ᵥ (frameBasis θ φ).repr v = ‖v‖ ^ 2 := by
  have h := EuclideanSpace.real_norm_sq_eq ((frameBasis θ φ).repr v)
  rw [norm_frameBasis_repr] at h
  simpa only [dotProduct, pow_two] using h.symm

/-- A component matrix quadratic-form bound transfers with exactly the same scalar constant. -/
theorem inner_matrixInFrame_le_of_quadFormLE (θ φ : ℝ)
    {A : Matrix (Fin 3) (Fin 3) ℝ} {μ : ℝ} (hA : CAS.Analysis.Matrix.QuadFormLE A μ)
    (v : ℝ^3) : ⟪matrixInFrame θ φ A v, v⟫ ≤ μ * ‖v‖ ^ 2 := by
  rw [inner_matrixInFrame]
  simpa only [dotProduct_frameBasis_repr_self] using hA ((frameBasis θ φ).repr v)

/-- The operator is the finite sum of the frame outer products with the matrix entries. -/
theorem matrixInFrame_eq_sum_rankOne (θ φ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixInFrame θ φ A = ∑ i : Fin 3, ∑ j : Fin 3,
      A i j • InnerProductSpace.rankOne ℝ (frame θ φ i) (frame θ φ j) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixInFrame_apply, ← OrthonormalBasis.sum_repr_symm]
  simp only [sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul, frameBasis_apply]
  change (∑ i : Fin 3, (∑ j : Fin 3, A i j * (frameBasis θ φ).repr v j) • frame θ φ i) = _
  simp only [Finset.sum_smul, frameBasis_repr_apply]

/-- Absolute summation of all nine entries bounds the Cartesian operator norm. -/
theorem norm_matrixInFrame_le_sum (θ φ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖matrixInFrame θ φ A‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |A i j| := by
  rw [matrixInFrame_eq_sum_rankOne]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  simp [norm_smul, Real.norm_eq_abs, InnerProductSpace.norm_rankOne,
    (orthonormal_frame θ φ).norm_eq_one, mul_one]

/-- Each frame vector depends continuously on its two angles. -/
theorem continuous_frame (i : Fin 3) :
    Continuous (fun p : ℝ × ℝ ↦ frame p.1 p.2 i) := by
  fin_cases i
  · exact continuous_radialFrame
  all_goals unfold frame
  all_goals dsimp only [Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  all_goals apply continuous_pi
  all_goals intro j
  all_goals fin_cases j <;> dsimp [polarFrame, azimuthalFrame] <;> fun_prop

/-- The Cartesian operator depends continuously on the angles and component matrix. -/
theorem continuous_matrixInFrame :
    Continuous (fun p : (ℝ × ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦
      matrixInFrame p.1.1 p.1.2 p.2) := by
  simp_rw [matrixInFrame_eq_sum_rankOne]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hi : Continuous (fun p : (ℝ × ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦
      frame p.1.1 p.1.2 i) := (continuous_frame i).comp continuous_fst
  have hj : Continuous (fun p : (ℝ × ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦
      frame p.1.1 p.1.2 j) := (continuous_frame j).comp continuous_fst
  have hr := ((InnerProductSpace.rankOne ℝ :
    ℝ^3 →L[ℝ] ℝ^3 →L⋆[ℝ] ℝ^3 →L[ℝ] ℝ^3).continuous.comp hi).clm_apply hj
  exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).smul hr

end PDE.CoordinateSystems.Spherical
