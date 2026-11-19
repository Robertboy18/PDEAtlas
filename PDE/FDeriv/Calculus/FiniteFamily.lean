/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Derivatives of finite linear families

A finite family of spatially smooth functions is jointly smooth in its coefficients and
position. Mathlib's finite-dimensional criterion for operator-valued smoothness proves this
without choosing a basis. Evaluating any fixed spatial derivative also gives a continuous
linear function of the coefficients.

The coefficient space must be finite dimensional here. Spatial regularity alone gives no
operator bound on an infinite-dimensional family.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace LinearMap

variable {V X E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a finite-dimensional linear family, spatial regularity of each member gives joint
regularity in its coefficients and spatial argument. -/
theorem contDiff_uncurry_of_finiteDimensional {p : WithTop ℕ∞}
    (A : V →ₗ[ℝ] (X → E)) (hA : ∀ v, ContDiff ℝ p (A v)) :
    ContDiff ℝ p (fun q : V × X ↦ A q.1 q.2) := by
  let B : X → V →L[ℝ] E := fun x ↦
    ((LinearMap.proj x).comp A).toContinuousLinearMap
  have hB : ContDiff ℝ p B := contDiff_clm_apply_iff.mpr hA
  exact (hB.comp contDiff_snd).clm_apply contDiff_fst

/-- A spatial derivative evaluated at a point is a continuous linear function of finite
coefficients. It needs `C^k` regularity, where `k` is the length of the derivative word. -/
def iteratedPartialDerivEval {n : ℕ} (A : V →ₗ[ℝ] (ℝ^n → E))
    (indices : List (Fin n)) (hA : ∀ v, ContDiff ℝ indices.length (A v))
    (x : ℝ^n) : V →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ iteratedPartialDeriv indices (A v) x
      map_add' := by
        intro v w
        rw [map_add]
        exact congrFun (PDE.iteratedPartialDeriv_add_of_contDiff indices (hA v) (hA w)) x
      map_smul' := by
        intro c v
        rw [map_smul]
        exact congrFun (PDE.iteratedPartialDeriv_const_smul c indices (A v)) x }

/-- `iteratedPartialDerivEval` evaluates to the iterated coordinate derivative. -/
@[simp] theorem iteratedPartialDerivEval_apply {n : ℕ}
    (A : V →ₗ[ℝ] (ℝ^n → E)) (indices : List (Fin n))
    (hA : ∀ v, ContDiff ℝ indices.length (A v)) (x : ℝ^n) (v : V) :
    A.iteratedPartialDerivEval indices hA x v = iteratedPartialDeriv indices (A v) x :=
  rfl

end LinearMap
