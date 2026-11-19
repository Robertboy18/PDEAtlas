/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Basic
public import PDE.Analysis.Spectral.FiniteDimensional.UnitFrame
public import Mathlib.Analysis.Matrix.Normed

/-!
# Global characteristic frames of quasilinear systems

A smooth strictly hyperbolic coefficient field on the whole state space has
globally smooth ordered speeds and right and left unit eigenframes. The state
space is contractible; arbitrary open subsets are not covered.
The coefficients need not arise from a flux. The matrix statement uses transpose eigenvectors.
-/

@[expose] public section

noncomputable section

open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise

namespace PDE.Hyperbolic.Quasilinear

variable {m : ℕ}

/-- The strict-hyperbolicity predicate supplies the ordered spectrum. -/
theorem IsStrictlyHyperbolicAt.hasOrderedEigenbasis
    {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m} {z : ℝ^m} (h : IsStrictlyHyperbolicAt B z) :
    ContinuousLinearMap.HasOrderedEigenbasis m (B z) := by
  obtain ⟨b, a, ha, hb⟩ := h
  obtain ⟨c, s, hs, hc⟩ := b.exists_ordered_eigenbasis (B z).toLinearMap a ha
    (fun k ↦ (hb k).apply_eq_smul)
  exact ⟨s, hs, c, hc⟩

/-- Global ordered speeds and left and right unit eigenframes of a strictly
hyperbolic coefficient field, with its finite or infinite regularity. -/
theorem exists_contDiff_unit_spectral_frame {q : WithTop ℕ∞} {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m}
    (hB : ContDiff ℝ q B) (hhyper : ∀ z, IsStrictlyHyperbolicAt B z) :
    ∃ eig : Fin m → ℝ^m → ℝ, ∃ r l : Fin m → ℝ^m → ℝ^m,
      (∀ k, ContDiff ℝ q (eig k) ∧ ContDiff ℝ q (r k) ∧ ContDiff ℝ q (l k)) ∧
      (∀ z, StrictMono (fun k ↦ eig k z)) ∧
      (∀ z k, B z (r k z) = eig k z • r k z ∧
        ContinuousLinearMap.adjoint (B z) (l k z) = eig k z • l k z ∧
        ‖r k z‖ = 1 ∧ ‖l k z‖ = 1) ∧
      (∀ z, ∃ br bl : Module.Basis (Fin m) ℝ (ℝ^m),
        (∀ k, br k = r k z) ∧ ∀ k, bl k = l k z) ∧
      ∀ z i j, ⟪l i z, r j z⟫_ℝ = 0 ↔ i ≠ j := by
  have h := fun z ↦ (hhyper z).hasOrderedEigenbasis
  obtain ⟨r, l, hreg, heigen, hb, hpair⟩ :=
    ContinuousLinearMap.exists_contDiff_unit_spectral_frame hB h
  exact ⟨fun k z ↦ ContinuousLinearMap.orderedEigenvalue m (B z) k,
    r, l, hreg, fun z ↦ (ContinuousLinearMap.orderedEigenvalue_spec (h z)).1, heigen, hb, hpair⟩

/-- Smooth matrix coefficients with `m` distinct real eigenvalues everywhere
admit global smooth ordered left and right unit eigenframes, including `m = 0`.
Left eigenvectors are eigenvectors of the transposed matrix. Distinct
families pair to zero, whereas matching families have a nonzero pairing. -/
theorem exists_smooth_unit_matrix_spectral_frame {M : ℝ^m → Matrix (Fin m) (Fin m) ℝ}
    (hM : ContDiff ℝ ∞ M)
    (hhyper : ∀ z, ∃ s : Fin m → ℝ, Function.Injective s ∧ ∀ k,
      Module.End.HasEigenvalue (M z).toEuclideanLin (s k)) :
    ∃ eig : Fin m → ℝ^m → ℝ, ∃ r l : Fin m → ℝ^m → ℝ^m,
      (∀ k, ContDiff ℝ ∞ (eig k) ∧ ContDiff ℝ ∞ (r k) ∧ ContDiff ℝ ∞ (l k)) ∧
      (∀ z, StrictMono (fun k ↦ eig k z)) ∧
      (∀ z k, (M z).toEuclideanLin (r k z) = eig k z • r k z ∧
        (M z).transpose.toEuclideanLin (l k z) = eig k z • l k z ∧
        ‖r k z‖ = 1 ∧ ‖l k z‖ = 1) ∧
      (∀ z, ∃ br bl : Module.Basis (Fin m) ℝ (ℝ^m),
        (∀ k, br k = r k z) ∧ ∀ k, bl k = l k z) ∧
      ∀ z i j, ⟪l i z, r j z⟫_ℝ = 0 ↔ i ≠ j := by
  let e : Matrix (Fin m) (Fin m) ℝ ≃L[ℝ] (ℝ^m →L[ℝ] ℝ^m) :=
    (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  let B : ℝ^m → ℝ^m →L[ℝ] ℝ^m := fun z ↦ e (M z)
  have hB : ContDiff ℝ ∞ B := e.contDiff.comp hM
  have hBh : ∀ z, IsStrictlyHyperbolicAt B z :=
    fun z ↦ isStrictlyHyperbolicAt_iff_hasEigenvalue.mpr (hhyper z)
  have htranspose (z : ℝ^m) : (M z).transpose.toEuclideanLin =
        (ContinuousLinearMap.adjoint (B z)).toLinearMap := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap]
    change (M z).transpose.toEuclideanLin = (M z).toEuclideanLin.adjoint
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (M z).toEuclideanLin_conjTranspose_eq_adjoint
  obtain ⟨eig, r, l, hreg, hord, heigen, hb, hpair⟩ := exists_contDiff_unit_spectral_frame hB hBh
  refine ⟨eig, r, l, hreg, hord, ?_, hb, hpair⟩
  intro z k
  refine ⟨(heigen z k).1, ?_, (heigen z k).2.2⟩
  rw [htranspose z]
  exact (heigen z k).2.1

end PDE.Hyperbolic.Quasilinear
