/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.Coercivity
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Hilbert norm of a symmetric coercive form

A continuous symmetric coercive bilinear form defines an equivalent Hilbert norm.
The type synonym separates that norm from the original norm. Completeness follows
from the uniform equivalence given by the two norm bounds. Coercivity is Mathlib's
`IsCoercive`. This is the observation in the Remark after the Lax–Milgram theorem in Evans,
§6.2.1: for a symmetric form, `((u, v)) := B[u, v]` is a new inner product, to which the Riesz
representation theorem applies directly.

## Main definitions

* `WithCoerciveForm`: a type synonym for `V` with the inner product `B`.
* `WithCoerciveForm.continuousLinearEquiv`: the identity of `V`, as a continuous linear
  equivalence from the form norm to the original norm.

## Main results

* `WithCoerciveForm.norm_sq_eq`: the square of the form norm of `x` is `B x x`.
* `WithCoerciveForm.norm_le`, `WithCoerciveForm.exists_norm_linearEquiv_le`: the form norm is
  at most `√‖B‖` times the original norm, and the original norm is at most a constant times
  the form norm.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, the Remark after Theorem 1 (Lax–Milgram
  Theorem), p. 317. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The underlying vectors equipped with the norm of a symmetric coercive form. -/
def WithCoerciveForm (B : V →L[ℝ] V →L[ℝ] ℝ) (_hB : IsCoercive B)
    (_hsymm : ∀ x y, B x y = B y x) := V

namespace WithCoerciveForm

variable (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
  (hsymm : ∀ x y, B x y = B y x)

instance : AddCommGroup (WithCoerciveForm B hB hsymm) := inferInstanceAs (AddCommGroup V)

instance : Module ℝ (WithCoerciveForm B hB hsymm) := inferInstanceAs (Module ℝ V)

/-- Forgetting the form norm is a linear equivalence. -/
def linearEquiv : WithCoerciveForm B hB hsymm ≃ₗ[ℝ] V := LinearEquiv.refl ℝ V

instance : InnerProductSpace.Core ℝ (WithCoerciveForm B hB hsymm) where
  inner x y := B (linearEquiv B hB hsymm x) (linearEquiv B hB hsymm y)
  conj_inner_symm x y := by
    simpa using hsymm (linearEquiv B hB hsymm y) (linearEquiv B hB hsymm x)
  re_inner_nonneg x := hB.self_nonneg _
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    have hcoercive := hB
    obtain ⟨c, hc, hbound⟩ := hcoercive
    have h := hbound (linearEquiv B hB hsymm x)
    rw [hx] at h
    have hz : ‖linearEquiv B hB hsymm x‖ = 0 := by
      by_contra hne
      have hpos := (norm_nonneg (linearEquiv B hB hsymm x)).lt_of_ne' hne
      exact (not_lt_of_ge h) (mul_pos (mul_pos hc hpos) hpos)
    exact (linearEquiv B hB hsymm).injective (by simpa using norm_eq_zero.mp hz)

instance : NormedAddCommGroup (WithCoerciveForm B hB hsymm) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance : InnerProductSpace ℝ (WithCoerciveForm B hB hsymm) :=
  InnerProductSpace.ofCore _

/-- The new inner product is the original bilinear form. -/
@[simp] theorem inner_eq (x y : WithCoerciveForm B hB hsymm) :
    inner ℝ x y = B (linearEquiv B hB hsymm x) (linearEquiv B hB hsymm y) := rfl

/-- The square of the form norm is its quadratic energy. -/
theorem norm_sq_eq (x : WithCoerciveForm B hB hsymm) :
    ‖x‖ ^ 2 = B (linearEquiv B hB hsymm x) (linearEquiv B hB hsymm x) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]

/-- Continuity of the bilinear form bounds its norm by the original norm. -/
theorem norm_le (x : WithCoerciveForm B hB hsymm) :
    ‖x‖ ≤ √‖B‖ * ‖linearEquiv B hB hsymm x‖ := by
  have hbound := B.le_opNorm₂ (linearEquiv B hB hsymm x) (linearEquiv B hB hsymm x)
  rw [Real.norm_eq_abs, abs_of_nonneg (hB.self_nonneg _)] at hbound
  have hnonneg := mul_nonneg (Real.sqrt_nonneg ‖B‖)
    (norm_nonneg (linearEquiv B hB hsymm x))
  apply (sq_le_sq₀ (norm_nonneg x) hnonneg).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg B), norm_sq_eq]
  simpa only [pow_two, mul_assoc] using hbound

/-- Coercivity bounds the original norm by the form norm. -/
theorem exists_norm_linearEquiv_le :
    ∃ C : ℝ, ∀ x : WithCoerciveForm B hB hsymm,
      ‖linearEquiv B hB hsymm x‖ ≤ C * ‖x‖ := by
  have hcoercive := hB
  obtain ⟨c, hc, hbound⟩ := hcoercive
  refine ⟨(√c)⁻¹, fun x ↦ ?_⟩
  have hsqrt : 0 < √c := Real.sqrt_pos.mpr hc
  have hb := hbound (linearEquiv B hB hsymm x)
  rw [← norm_sq_eq B hB hsymm x] at hb
  have hle : √c * ‖linearEquiv B hB hsymm x‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (mul_nonneg hsqrt.le (norm_nonneg _)) (norm_nonneg x)).mp
    rw [mul_pow, Real.sq_sqrt hc.le]
    simpa only [pow_two, mul_assoc] using hb
  calc
    ‖linearEquiv B hB hsymm x‖ ≤ ‖x‖ / √c :=
      (le_div_iff₀ hsqrt).mpr (by simpa [mul_comm] using hle)
    _ = (√c)⁻¹ * ‖x‖ := by rw [div_eq_mul_inv, mul_comm]

/-- The form norm and the original norm give continuously equivalent vector spaces. -/
def continuousLinearEquiv : WithCoerciveForm B hB hsymm ≃L[ℝ] V where
  toLinearEquiv := linearEquiv B hB hsymm
  continuous_toFun :=
    ((linearEquiv B hB hsymm).toLinearMap.mkContinuousOfExistsBound
      (exists_norm_linearEquiv_le B hB hsymm)).continuous
  continuous_invFun :=
    ((linearEquiv B hB hsymm).symm.toLinearMap.mkContinuous (√‖B‖)
      (fun x ↦ by
        simpa using norm_le B hB hsymm ((linearEquiv B hB hsymm).symm x))).continuous

/-- The equivalence of norms also preserves the uniform structures. -/
def uniformEquiv : WithCoerciveForm B hB hsymm ≃ᵤ V where
  toEquiv := (continuousLinearEquiv B hB hsymm).toEquiv
  uniformContinuous_toFun :=
    (continuousLinearEquiv B hB hsymm).toContinuousLinearMap.uniformContinuous
  uniformContinuous_invFun :=
    (continuousLinearEquiv B hB hsymm).symm.toContinuousLinearMap.uniformContinuous

instance [CompleteSpace V] : CompleteSpace (WithCoerciveForm B hB hsymm) :=
  (uniformEquiv B hB hsymm).completeSpace_iff.mpr inferInstance

end WithCoerciveForm

end PDE.Analysis.Variational
