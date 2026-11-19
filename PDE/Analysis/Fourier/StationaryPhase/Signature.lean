/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.Hessian
public import PDE.Analysis.Fourier.StationaryPhase.Normalization

/-!
# Intrinsic Hessian signature in the quadratic asymptotic

Sylvester's law of inertia identifies the sum of spectral signs with the
positive index minus the negative index of the Hessian quadratic form.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- The sum of signs counts positive coefficients minus negative coefficients. -/
theorem sum_sign_eq_card_sub (b : Fin n → ℝ) :
    ∑ i, Real.sign (b i) =
      ({i | 0 < b i}.ncard : ℝ) - ({i | b i < 0}.ncard : ℝ) := by
  classical
  have hs (r : ℝ) :
      Real.sign r = (if 0 < r then 1 else 0) - (if r < 0 then 1 else 0) := by
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · simp [Real.sign_of_neg hr, hr, not_lt.mpr hr.le]
    · simp
    · simp [Real.sign_of_pos hr, hr, not_lt.mpr hr.le]
  simp only [hs, Finset.sum_sub_distrib, Set.ncard_eq_toFinset_card']
  simp

/-- An orthonormal eigenbasis computes the intrinsic signature of the Hessian. -/
theorem sum_sign_eigenvalues_eq_hessianSignature {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiffAt ℝ 2 f p) :
    ∑ i, Real.sign ((hessianMatrix_isHermitian hf).eigenvalues i) =
      (hessianSignature f p : ℝ) := by
  let hA := hessianMatrix_isHermitian hf
  let Q := (fderiv ℝ (fderiv ℝ f) p).toBilinForm.toQuadraticMap
  let e : ℝ^n ≃ₗ[ℝ] (Fin n → ℝ) :=
    hA.eigenvectorBasis.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ _)
  have heq : QuadraticMap.Equivalent Q
      (QuadraticMap.weightedSumSquares ℝ hA.eigenvalues) := by
    refine ⟨{ e with map_app' := ?_ }⟩
    intro x
    have h := PDE.Analysis.inner_toEuclideanLin_eigenbasis hA
      (hA.eigenvectorBasis.repr x)
    rw [hA.eigenvectorBasis.repr.symm_apply_apply, PDE.Analysis.inner_hessianMatrix] at h
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Q,
      LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply]
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    change hA.eigenvalues i * (_ * _) = _
    simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, e,
      LinearEquiv.trans_apply, WithLp.coe_linearEquiv,
      LinearIsometryEquiv.coe_toLinearEquiv]
    ring
  rw [sum_sign_eq_card_sub]
  simp only [hessianSignature, Int.cast_sub, Int.cast_natCast]
  change _ = (sigPos Q : ℝ) - (sigNeg Q : ℝ)
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares heq,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares heq]

/-- The leading coefficient uses the determinant magnitude and intrinsic signature
of the Hessian. -/
def hessianFresnel (f : ℝ^n → ℝ) (p : ℝ^n) : ℂ :=
  ((2 * Real.pi) ^ ((n : ℝ) / 2) /
    Real.sqrt |(PDE.Analysis.hessianMatrix f p).det| : ℝ) *
      Complex.exp ((Real.pi / 4 * (hessianSignature f p : ℝ) : ℝ) * I)

/-- The quadratic leading term for a nondegenerate Hessian. -/
theorem tendsto_integral_hessian_quadratic {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiffAt ℝ 2 f p)
    (hdet : (PDE.Analysis.hessianMatrix f p).det ≠ 0)
    {a : ℝ^n → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a) :
    Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
      ∫ x : ℝ^n, Complex.exp
        ((fderiv ℝ (fderiv ℝ f) p x x / 2 / ε ^ 2 : ℝ) * I) * a x)
      (𝓝[>] 0) (𝓝 (hessianFresnel f p * a 0)) := by
  simpa only [PDE.Analysis.inner_hessianMatrix,
    sum_sign_eigenvalues_eq_hessianSignature hf, hessianFresnel] using
      tendsto_integral_matrix_quadratic (hessianMatrix_isHermitian hf) hdet ha hc

end PDE.Analysis.StationaryPhase
