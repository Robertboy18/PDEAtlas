/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Spectral.Frame
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A rotating nonsymmetric coefficient field

The matrix is the rotation conjugate of `[[a, 1], [0, a + 2]]`. Its first unit
eigenvector `(cos z₀, sin z₀)` rotates through every direction, so no fixed coordinate
of it is nonzero everywhere. `exists_smooth_unit_matrix_spectral_frame` gives smooth
unit right and left eigenvector frames (`exists_smooth_frames`), and
`existsUnique_contDiff_unit_eigenvector` identifies the smooth unit eigenvector field
with value `(1, 0)` at the origin as `first` (`exists_unique_first_section`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Quasilinear.Spectral.Rotating

open PDE.Common
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise

/-- A nonsymmetric coefficient field with rotating eigenspaces and variable speeds. -/
def coefficient (z : ℝ^2) : Matrix (Fin 2) (Fin 2) ℝ :=
  let c := Real.cos (z 0)
  let s := Real.sin (z 0)
  !![z 1 - c * s + 2 * s ^ 2, c ^ 2 - 2 * s * c;
    -s ^ 2 - 2 * s * c, z 1 + s * c + 2 * c ^ 2]

/-- The unit vector in the first eigenline. -/
def first (z : ℝ^2) : ℝ^2 := !₂[Real.cos (z 0), Real.sin (z 0)]

/-- A nonzero vector in the second eigenline. -/
def second (z : ℝ^2) : ℝ^2 :=
  !₂[Real.cos (z 0) - 2 * Real.sin (z 0), Real.sin (z 0) + 2 * Real.cos (z 0)]

/-- The coefficient field is smooth. -/
theorem contDiff_coefficient : ContDiff ℝ ∞ coefficient := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [coefficient] <;> cas

/-- `first` is smooth. -/
theorem contDiff_first : ContDiff ℝ ∞ first := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> dsimp [first] <;> cas

/-- `first z` is a unit vector. -/
theorem norm_first (z : ℝ^2) : ‖first z‖ = 1 := by
  have h : ‖first z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    exact Real.cos_sq_add_sin_sq (z 0)
  nlinarith [norm_nonneg (first z)]

/-- `‖second z‖² = 5`. -/
theorem norm_sq_second (z : ℝ^2) : ‖second z‖ ^ 2 = 5 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change (Real.cos (z 0) - 2 * Real.sin (z 0)) ^ 2 +
    (Real.sin (z 0) + 2 * Real.cos (z 0)) ^ 2 = 5
  cas using Real.cos_sq_add_sin_sq (z 0)

/-- `first z` is an eigenvector with eigenvalue `z₁`. -/
theorem coefficient_first (z : ℝ^2) :
    (coefficient z).toEuclideanLin (first z) = z 1 • first z := by
  ext i
  fin_cases i <;>
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul] <;>
    dsimp [coefficient, first] <;> cas using Real.cos_sq_add_sin_sq (z 0)

/-- `second z` is an eigenvector with eigenvalue `z₁ + 2`. -/
theorem coefficient_second (z : ℝ^2) :
    (coefficient z).toEuclideanLin (second z) = (z 1 + 2) • second z := by
  ext i
  fin_cases i <;>
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul] <;>
    dsimp [coefficient, second] <;> cas using Real.cos_sq_add_sin_sq (z 0)

/-- The eigenvalues `z₁` and `z₁ + 2`. -/
def speed (z : ℝ^2) (k : Fin 2) : ℝ := z 1 + 2 * k.val

private theorem strictMono_speed (z : ℝ^2) : StrictMono (speed z) := by
  intro i j hij
  have h : (i.val : ℝ) < j.val := Nat.cast_lt.mpr hij
  change z 1 + 2 * (i.val : ℝ) < z 1 + 2 * (j.val : ℝ)
  linarith

private def eigenvector (z : ℝ^2) (k : Fin 2) : ℝ^2 :=
  if k = 0 then first z else second z

private theorem hasEigenvector (z : ℝ^2) (k : Fin 2) :
    Module.End.HasEigenvector (coefficient z).toEuclideanLin
      (speed z k) (eigenvector z k) := by
  have hf : Module.End.HasEigenvector (coefficient z).toEuclideanLin (z 1) (first z) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr (coefficient_first z), ?_⟩
    intro hz
    have hn := norm_first z
    simp [hz] at hn
  have hs : Module.End.HasEigenvector (coefficient z).toEuclideanLin
      (z 1 + 2) (second z) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr (coefficient_second z), ?_⟩
    intro hz
    have hn := norm_sq_second z
    simp [hz] at hn
  fin_cases k
  · simpa [eigenvector, speed] using hf
  · simpa [eigenvector, speed] using hs

private def eigenbasis (z : ℝ^2) : Module.Basis (Fin 2) ℝ (ℝ^2) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (eigenvector z)
    (Module.End.eigenvectors_linearIndependent' (coefficient z).toEuclideanLin
      (speed z) (strictMono_speed z).injective (eigenvector z) (hasEigenvector z))
    (by simp)

private theorem eigenbasis_equation (z : ℝ^2) (k : Fin 2) :
    (coefficient z).toEuclideanLin (eigenbasis z k) = speed z k • eigenbasis z k := by
  simpa only [eigenbasis, coe_basisOfLinearIndependentOfCardEqFinrank'] using
    (hasEigenvector z k).apply_eq_smul

/-- The coefficient field has smooth unit right and left eigenvector frames with
eigenvalues `speed z`, and the left and right frames are biorthogonal. -/
theorem exists_smooth_frames :
    ∃ r l : Fin 2 → ℝ^2 → ℝ^2,
      (∀ k, ContDiff ℝ ∞ (r k) ∧ ContDiff ℝ ∞ (l k)) ∧
      (∀ z k, (coefficient z).toEuclideanLin (r k z) = speed z k • r k z ∧
        (coefficient z).transpose.toEuclideanLin (l k z) = speed z k • l k z ∧
        ‖r k z‖ = 1 ∧ ‖l k z‖ = 1) ∧
      (∀ z, ∃ br bl : Module.Basis (Fin 2) ℝ (ℝ^2),
        (∀ k, br k = r k z) ∧ ∀ k, bl k = l k z) ∧
      ∀ z i j, ⟪l i z, r j z⟫_ℝ = 0 ↔ i ≠ j := by
  obtain ⟨eig, r, l, hreg, hord, heigen, hb, hpair⟩ :=
    PDE.Hyperbolic.Quasilinear.exists_smooth_unit_matrix_spectral_frame
      contDiff_coefficient (fun z ↦ ⟨speed z, (strictMono_speed z).injective,
        fun k ↦ Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector z k)⟩)
  have hs (z : ℝ^2) : (fun k ↦ eig k z) = speed z := by
    obtain ⟨br, _, hbr, _⟩ := hb z
    exact br.eq_eigenvalues_of_strictMono (eigenbasis z) (coefficient z).toEuclideanLin
      (hord z) (strictMono_speed z)
      (fun k ↦ by rw [hbr k]; exact (heigen z k).1) (eigenbasis_equation z)
  refine ⟨r, l, fun k ↦ (hreg k).2, ?_, hb, hpair⟩
  intro z k
  simpa only [congrFun (hs z) k] using heigen z k

private def operator (z : ℝ^2) : ℝ^2 →L[ℝ] ℝ^2 :=
  (coefficient z).toEuclideanLin.toContinuousLinearMap

private theorem contDiff_operator : ContDiff ℝ ∞ operator := by
  let e : Matrix (Fin 2) (Fin 2) ℝ ≃L[ℝ] (ℝ^2 →L[ℝ] ℝ^2) :=
    (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  exact e.contDiff.comp contDiff_coefficient

private theorem ordered_operator (z : ℝ^2) :
    ContinuousLinearMap.HasOrderedEigenbasis 2 (operator z) :=
  ⟨speed z, strictMono_speed z, eigenbasis z, eigenbasis_equation z⟩

private theorem orderedEigenvalue_operator (z : ℝ^2) :
    ContinuousLinearMap.orderedEigenvalue 2 (operator z) = speed z :=
  ContinuousLinearMap.orderedEigenvalue_eq_of_eigenbasis
    (eigenbasis z) (strictMono_speed z) (eigenbasis_equation z)

/-- The unique smooth unit eigenvector field for the first eigenvalue with value `(1, 0)`
at the origin is `first`. Its first coordinate vanishes at `(π/2, 0)`. -/
theorem exists_unique_first_section :
    ∃! v : C(ℝ^2, ℝ^2), ContDiff ℝ ∞ v ∧ v 0 = first 0 ∧
      (∀ z, (coefficient z).toEuclideanLin (v z) = z 1 • v z ∧ ‖v z‖ = 1) ∧
      v = ⟨first, contDiff_first.continuous⟩ ∧
      v !₂[Real.pi / 2, 0] 0 = 0 := by
  have hv (z : ℝ^2) :
      Module.End.HasEigenvector (operator z).toLinearMap
        (ContinuousLinearMap.orderedEigenvalue 2 (operator z) 0) (first z) := by
    rw [orderedEigenvalue_operator]
    simpa [eigenvector, operator] using hasEigenvector z 0
  obtain ⟨v, hreg, huniq⟩ :=
    ContinuousLinearMap.existsUnique_contDiff_unit_eigenvector
      contDiff_operator ordered_operator 0 0 (first 0) (hv 0) (norm_first 0)
  have heq : (⟨first, contDiff_first.continuous⟩ : C(ℝ^2, ℝ^2)) = v :=
    huniq _ ⟨contDiff_first, rfl, fun z ↦ ⟨hv z, norm_first z⟩⟩
  refine ⟨v, ⟨hreg.1, hreg.2.1, ?_, heq.symm, ?_⟩, ?_⟩
  · intro z
    have he := (hreg.2.2 z).1.apply_eq_smul
    rw [orderedEigenvalue_operator] at he
    exact ⟨by simpa [operator, speed] using he, (hreg.2.2 z).2⟩
  · rw [← heq]
    simp [first]
  · rintro w ⟨_, _, _, hw, _⟩
    exact hw.trans heq

/-- The coefficient is not symmetric at the origin. -/
theorem coefficient_zero_not_symmetric : (coefficient 0).transpose ≠ coefficient 0 := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ ↦ A 0 1) h
  norm_num [coefficient, Matrix.transpose_apply] at he

/-- The left unit eigenvector in the first family at the origin is not the
right unit eigenvector, so their pairing is not one. -/
theorem left_unit_at_zero :
    let w : ℝ^2 := !₂[2, -1]
    ‖NormedSpace.normalize w‖ = 1 ∧
      (coefficient 0).transpose.toEuclideanLin (NormedSpace.normalize w) = 0 ∧
      ⟪NormedSpace.normalize w, first 0⟫_ℝ ≠ 1 := by
  dsimp only
  let w : ℝ^2 := !₂[2, -1]
  have hw : w ≠ 0 := by
    intro h
    have := congrArg (fun v : ℝ^2 ↦ v 0) h
    norm_num [w] at this
  have hn := NormedSpace.norm_normalize hw
  refine ⟨hn, ?_, ?_⟩
  · have he : (coefficient 0).transpose.toEuclideanLin w = 0 := by
      ext i
      fin_cases i <;>
        norm_num [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_two, coefficient, w]
    rw [NormedSpace.normalize, map_smul, he, smul_zero]
  · intro h
    have he := (inner_eq_one_iff_of_norm_eq_one hn (norm_first 0)).mp h
    have hc := congrArg (fun v : ℝ^2 ↦ v 1) he
    have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    simp [NormedSpace.normalize, first, w, hnorm] at hc

end PDE.Examples.Hyperbolic.Quasilinear.Spectral.Rotating
