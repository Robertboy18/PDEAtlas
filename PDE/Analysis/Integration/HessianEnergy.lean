/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import CAS.ExactTactic

/-!
# Global Hessian energy

For a real C³ function on Euclidean space, two integrations by parts give
`∫ (∂ᵢ∂ⱼu)² = ∫ ∂ᵢ²u ∂ⱼ²u`. Summing this identity identifies the squared L² norm
of the Hessian with that of the Laplacian.

We assume that the first, second, and third coordinate derivatives belong to L².
Hölder then gives all three integrable products in Mathlib's global integration
by parts theorem. No boundary term at infinity has to be prescribed, and `u` itself
need not belong to L².

Separating the last coordinate gives a sharper estimate for the mixed derivatives:
their combined L² norm is at most half the L² norm of the Laplacian. The estimate
comes from the nonnegative square of the transverse Laplacian minus the last
second derivative.
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory
open scoped BigOperators

variable {n : ℕ} {u : ℝ^n → ℝ}

/-- Two integrations by parts turn a mixed second derivative squared into the
product of the corresponding diagonal derivatives. C³ regularity lets the three
coordinate derivatives commute; their L² bounds make every product integrable. -/
theorem integral_partialDeriv_sq_eq_diagonal_product
    (hu : ContDiff ℝ 3 u)
    (h1 : ∀ i : Fin n, MemLp (∂[i] u) 2 volume)
    (h2 : ∀ i j : Fin n, MemLp (∂[i] (∂[j] u)) 2 volume)
    (h3 : ∀ i j k : Fin n,
      MemLp (∂[i] (∂[j] (∂[k] u))) 2 volume)
    (i j : Fin n) :
    (∫ x, ((∂[i] (∂[j] u)) x) ^ 2) =
      ∫ x, (∂[i] (∂[i] u)) x *
        (∂[j] (∂[j] u)) x := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hfirst (k : Fin n) : ContDiff ℝ 2 (∂[k] u) :=
    contDiff_partialDeriv_of_succ (m := 2) hu
  have hsecond (k l : Fin n) : ContDiff ℝ 1 (∂[k] (∂[l] u)) :=
    contDiff_partialDeriv_of_succ (m := 1) (hfirst l)
  have hIBP1 :
      (∫ x, (∂[i] u) x *
        (∂[j] (∂[i] (∂[j] u))) x) =
        - ∫ x, (∂[j] (∂[i] u)) x *
          (∂[i] (∂[j] u)) x := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := (∂[i] u)) (g := (∂[i] (∂[j] u)))
      (v := EuclideanSpace.single j (1 : ℝ))
      (memLp_one_iff_integrable.mp ((h2 j i).fun_mul (h2 i j)))
      (memLp_one_iff_integrable.mp ((h1 i).fun_mul (h3 j i j)))
      (memLp_one_iff_integrable.mp ((h1 i).fun_mul (h2 i j)))
      (fun x _ ↦ (hfirst i).differentiable (by norm_num) x)
      (fun x _ ↦ (hsecond i j).differentiable (by norm_num) x)
  have hIBP2 :
      (∫ x, (∂[i] u) x *
        (∂[i] (∂[j] (∂[j] u))) x) =
        - ∫ x, (∂[i] (∂[i] u)) x *
          (∂[j] (∂[j] u)) x := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := (∂[i] u)) (g := (∂[j] (∂[j] u)))
      (v := EuclideanSpace.single i (1 : ℝ))
      (memLp_one_iff_integrable.mp ((h2 i i).fun_mul (h2 j j)))
      (memLp_one_iff_integrable.mp ((h1 i).fun_mul (h3 i j j)))
      (memLp_one_iff_integrable.mp ((h1 i).fun_mul (h2 j j)))
      (fun x _ ↦ (hfirst i).differentiable (by norm_num) x)
      (fun x _ ↦ (hsecond j j).differentiable (by norm_num) x)
  have hthird :
      (∫ x, (∂[i] u) x *
        (∂[j] (∂[i] (∂[j] u))) x) =
        ∫ x, (∂[i] u) x *
          (∂[i] (∂[j] (∂[j] u))) x := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [partialDeriv_partialDeriv_comm j i (hfirst j) x]
  have hsecondProduct :
      (∫ x, (∂[j] (∂[i] u)) x *
        (∂[i] (∂[j] u)) x) =
        ∫ x, ((∂[i] (∂[j] u)) x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [partialDeriv_partialDeriv_comm j i hu2 x, pow_two]
  rw [hthird, hsecondProduct] at hIBP1
  exact neg_injective (hIBP1.symm.trans hIBP2)

/-- The squared L² norm of the full Hessian equals the squared L² norm of the
Laplacian. The sum includes both orders of each mixed derivative. -/
theorem sum_integral_partialDeriv_sq_eq_laplacian_sq
    (hu : ContDiff ℝ 3 u)
    (h1 : ∀ i : Fin n, MemLp (∂[i] u) 2 volume)
    (h2 : ∀ i j : Fin n, MemLp (∂[i] (∂[j] u)) 2 volume)
    (h3 : ∀ i j k : Fin n,
      MemLp (∂[i] (∂[j] (∂[k] u))) 2 volume) :
    (∑ i : Fin n, ∑ j : Fin n,
      ∫ x, ((∂[i] (∂[j] u)) x) ^ 2) =
      ∫ x, (∑ i : Fin n, (∂[i] (∂[i] u)) x) ^ 2 := by
  have hprod (i j : Fin n) : Integrable
      (fun x ↦ (∂[i] (∂[i] u)) x *
        (∂[j] (∂[j] u)) x) volume :=
    memLp_one_iff_integrable.mp ((h2 i i).fun_mul (h2 j j))
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, (∂[i] (∂[i] u)) x *
          (∂[j] (∂[j] u)) x := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact integral_partialDeriv_sq_eq_diagonal_product hu h1 h2 h3 i j
    _ = ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (∂[i] (∂[i] u)) x *
          (∂[j] (∂[j] u)) x := by
      rw [integral_finsetSum Finset.univ
        (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hprod i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum Finset.univ (fun j _ ↦ hprod i j)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- The transverse derivatives of the last first derivative carry at most one
quarter of the squared L² norm of the Laplacian. The constant follows by integrating
`(A - B)² ≥ 0`, with `A` the transverse Laplacian and `B` the last second derivative. -/
theorem sum_integral_axial_mixed_sq_le {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 3 u)
    (h1 : ∀ i : Fin (n + 1), MemLp (∂[i] u) 2 volume)
    (h2 : ∀ i j : Fin (n + 1),
      MemLp (∂[i] (∂[j] u)) 2 volume)
    (h3 : ∀ i j k : Fin (n + 1),
      MemLp (∂[i] (∂[j] (∂[k] u))) 2 volume) :
    (∑ i : Fin n,
      ∫ x, ((∂[i.castSucc] (∂[(Fin.last n)] u)) x) ^ 2) ≤
      (1 / 4 : ℝ) *
        ∫ x, (∑ i : Fin (n + 1), (∂[i] (∂[i] u)) x) ^ 2 := by
  let A : ℝ^(n + 1) → ℝ :=
    fun x ↦ ∑ i : Fin n, (∂[i.castSucc] (∂[i.castSucc] u)) x
  let B : ℝ^(n + 1) → ℝ := (∂[(Fin.last n)] (∂[(Fin.last n)] u))
  have hA : MemLp A 2 volume :=
    memLp_finsetSum Finset.univ (fun i _ ↦ h2 i.castSucc i.castSucc)
  have hB : MemLp B 2 volume := h2 (Fin.last n) (Fin.last n)
  have hAB : Integrable (fun x ↦ A x * B x) volume :=
    memLp_one_iff_integrable.mp (hA.fun_mul hB)
  have hcross :
      (∑ i : Fin n,
        ∫ x, ((∂[i.castSucc] (∂[(Fin.last n)] u)) x) ^ 2) =
        ∫ x, A x * B x := by
    calc
      _ = ∑ i : Fin n, ∫ x,
          (∂[i.castSucc] (∂[i.castSucc] u)) x * B x := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_partialDeriv_sq_eq_diagonal_product hu h1 h2 h3
          i.castSucc (Fin.last n)
      _ = ∫ x, ∑ i : Fin n,
          (∂[i.castSucc] (∂[i.castSucc] u)) x * B x := by
        exact (integral_finsetSum Finset.univ
          (fun i _ ↦ memLp_one_iff_integrable.mp
            ((h2 i.castSucc i.castSucc).fun_mul hB))).symm
      _ = ∫ x, A x * B x := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (Finset.sum_mul Finset.univ
          (fun i : Fin n ↦ (∂[i.castSucc] (∂[i.castSucc] u)) x)
          (B x)).symm
  have hsplit :
      (∫ x, (∑ i : Fin (n + 1), (∂[i] (∂[i] u)) x) ^ 2) =
        ∫ x, (A x + B x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Fin.sum_univ_castSucc]
  have hnonneg : 0 ≤ ∫ x, (A x - B x) ^ 2 :=
    integral_nonneg (fun x ↦ sq_nonneg (A x - B x))
  have hsquare :
      (∫ x, (A x + B x) ^ 2) =
        (∫ x, (A x - B x) ^ 2) + 4 * ∫ x, A x * B x := by
    calc
      _ = ∫ x, (A x - B x) ^ 2 + 4 * (A x * B x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        cas
      _ = _ := by
        have hdifference : Integrable (fun x ↦ (A x - B x) ^ 2) volume :=
          (hA.sub hB).integrable_sq
        rw [integral_add hdifference (hAB.const_mul 4), integral_const_mul]
  rw [hcross, hsplit]
  linarith

/-- In L² norm, the derivatives mixing the last coordinate with the transverse
coordinates are bounded by half the Laplacian norm. -/
theorem sqrt_sum_integral_axial_mixed_sq_le {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 3 u)
    (h1 : ∀ i : Fin (n + 1), MemLp (∂[i] u) 2 volume)
    (h2 : ∀ i j : Fin (n + 1),
      MemLp (∂[i] (∂[j] u)) 2 volume)
    (h3 : ∀ i j k : Fin (n + 1),
      MemLp (∂[i] (∂[j] (∂[k] u))) 2 volume) :
    √(∑ i : Fin n,
      ∫ x, ((∂[i.castSucc] (∂[(Fin.last n)] u)) x) ^ 2) ≤
      (1 / 2 : ℝ) * √
        (∫ x, (∑ i : Fin (n + 1), (∂[i] (∂[i] u)) x) ^ 2) := by
  have hquarter : √(1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
    norm_num
  calc
    _ ≤ √((1 / 4 : ℝ) *
        ∫ x, (∑ i : Fin (n + 1), (∂[i] (∂[i] u)) x) ^ 2) :=
      Real.sqrt_le_sqrt (sum_integral_axial_mixed_sq_le hu h1 h2 h3)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4), hquarter]

end PDE.Analysis
