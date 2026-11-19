/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.StrictUpperTriangular
public import PDE.Analysis.ODE.LinearVolterra
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite time-ordered matrix expansion

A continuous strictly upper triangular coefficient gives a nilpotent Volterra
operator. The proof pushes a fixed product of coefficients through each integral.
After `m` factors, the mixed-product theorem makes the integrand zero.

Consequently, every differentiable solution of the corresponding matrix equation
is its finite Picard expansion. The coefficient bound and the initial norm give an
explicit polynomial bound of degree at most `m - 1`, with factorial denominators.
No diagonalizability is assumed.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {m : ℕ}

/-- Multiplying an iterated integral by enough strictly upper triangular factors
makes it zero. The last factor inside an integral can be evaluated at a different
time from every earlier factor. -/
private theorem prod_mul_volterraLinearMap_pow_eq_zero
    (K f : C(ℝ, Matrix (Fin m) (Fin m) ℂ))
    (hK : ∀ t i j, j ≤ i → K t i j = 0)
    (k : ℕ) (L : List (Matrix (Fin m) (Fin m) ℂ))
    (hL : ∀ A ∈ L, ∀ i j, j ≤ i → A i j = 0)
    (hlen : m ≤ L.length + k) (t : ℝ) :
    L.prod * (PDE.Analysis.ODE.volterraLinearMap K ^ k) f t = 0 := by
  induction k generalizing L t with
  | zero =>
      rw [list_prod_eq_zero_of_strictUpperTriangular L hL
        (by simpa only [Nat.add_zero] using hlen), zero_mul]
  | succ k ih =>
      rw [PDE.Analysis.ODE.volterraLinearMap_pow_succ_apply]
      let M : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
        ContinuousLinearMap.mul ℝ _ L.prod
      have hint : IntervalIntegrable
          (fun s ↦ K s * (PDE.Analysis.ODE.volterraLinearMap K ^ k) f s) volume 0 t :=
        (K.continuous.mul
          ((PDE.Analysis.ODE.volterraLinearMap K ^ k) f).continuous).intervalIntegrable
            (μ := volume) 0 t
      change M (∫ s in 0..t, K s * (PDE.Analysis.ODE.volterraLinearMap K ^ k) f s) = 0
      rw [← M.intervalIntegral_comp_comm hint]
      have hz (s : ℝ) : M (K s * (PDE.Analysis.ODE.volterraLinearMap K ^ k) f s) = 0 := by
        have hLs : ∀ A ∈ L ++ [K s], ∀ i j, j ≤ i → A i j = 0 := by
          intro A hA
          rcases List.mem_append.mp hA with hA | hA
          · exact hL A hA
          · have hA' : A = K s := List.mem_singleton.mp hA
            subst A
            exact hK s
        have hlength : m ≤ (L ++ [K s]).length + k := by
          simpa only [List.length_append, List.length_singleton, Nat.add_assoc,
            Nat.add_comm 1 k] using hlen
        simpa only [List.prod_append, List.prod_singleton, mul_assoc, M,
          ContinuousLinearMap.mul_apply'] using ih (L ++ [K s]) hLs hlength s
      simp only [hz, intervalIntegral.integral_zero]

/-- Strict upper triangularity makes the Volterra operator nilpotent in dimension
`m`. This includes the zero-dimensional matrix algebra. -/
theorem volterraLinearMap_pow_eq_zero
    (K : C(ℝ, Matrix (Fin m) (Fin m) ℂ))
    (hK : ∀ t i j, j ≤ i → K t i j = 0) :
    PDE.Analysis.ODE.volterraLinearMap K ^ m = 0 := by
  apply LinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro t
  change (PDE.Analysis.ODE.volterraLinearMap K ^ m) f t = 0
  have h := prod_mul_volterraLinearMap_pow_eq_zero K f hK m []
    (by simp) (by simp) t
  simpa only [List.prod_nil, one_mul] using h

/-- The finite interaction expansion follows from the differential equation and
entrywise triangularity. Its constant curve is the initial matrix. -/
theorem eq_sum_volterraLinearMap_pow_of_hasDerivAt
    (K X : C(ℝ, Matrix (Fin m) (Fin m) ℂ))
    (hK : ∀ t i j, j ≤ i → K t i j = 0)
    (hX : ∀ t, HasDerivAt X (K t * X t) t) :
    X = ∑ k ∈ Finset.range m,
      (PDE.Analysis.ODE.volterraLinearMap K ^ k) (ContinuousMap.const ℝ (X 0)) :=
  PDE.Analysis.ODE.eq_sum_volterraLinearMap_pow_of_eq_add K X _ m
    (volterraLinearMap_pow_eq_zero K hK)
    (PDE.Analysis.ODE.eq_const_add_volterraLinearMap_of_hasDerivAt K X hX)

/-- The norm of a solution with a strictly upper triangular coefficient has a
finite factorial bound. The norm is the Euclidean operator norm. -/
theorem norm_le_sum_of_strictUpperTriangular_hasDerivAt
    (K X : C(ℝ, Matrix (Fin m) (Fin m) ℂ))
    (hK : ∀ t i j, j ≤ i → K t i j = 0)
    (hX : ∀ t, HasDerivAt X (K t * X t) t)
    {B t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Icc 0 t, ‖K s‖ ≤ B) :
    ‖X t‖ ≤ ∑ k ∈ Finset.range m, ‖X 0‖ * B ^ k * t ^ k / k.factorial := by
  have h := congrArg (fun f : C(ℝ, Matrix (Fin m) (Fin m) ℂ) ↦ f t)
    (eq_sum_volterraLinearMap_pow_of_hasDerivAt K X hK hX)
  rw [ContinuousMap.sum_apply] at h
  rw [h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  exact PDE.Analysis.ODE.norm_volterraLinearMap_pow_apply_le K (ContinuousMap.const ℝ (X 0))
    hB ht hbound (fun _ _ ↦ le_rfl) k

end Matrix
