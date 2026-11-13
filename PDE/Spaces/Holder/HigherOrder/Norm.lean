/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import PDE.Spaces.Holder.HigherOrder.Derivatives

import PDE.Analysis.Calculus.Jet.NormalTaylor
import CAS.ExactTactic

/-!
# The derivative sum norm and completeness

The sum of the uniform norms of all derivatives through order `k`, plus the Hölder
seminorms at order `k`, is equivalent to the complete norm inherited from the closed
derivative graph. The comparison constant depends only on the dimension and order.
On an open convex domain, a supplied Hessian envelope gives Taylor estimates directly
from the graph fields, including at the boundary.
For graphs constructed from ordinary formulas, per-field budgets bound the graph
norm by a maximum and Evans's norm by a sum.

Jet evaluation at any point of the closure has norm at most one in the graph norm
(`norm_jetEvalCLM_le`). The Hessian has exactly the Euclidean operator norm of its coordinate
matrix (`norm_hessian_eq_matrix_norm`), so a matrix norm bound applies to the derivative field
with no dimension-dependent constant.

## Main definitions

* `HolderSpace.CKGammaOn.evansNorm`: the norm (3) of Evans §5.1, the sum of the uniform norms of
  all derivatives of order at most `k` and of the Hölder seminorms of the derivatives of order
  `k`.

## Main results

* `HolderSpace.CKGammaOn.norm_le_evansNorm` and `HolderSpace.CKGammaOn.evansNorm_le`: the graph
  norm is at most `evansNorm`, and `evansNorm` is at most
  `Fintype.card (MultiIndex n k) + Fintype.card (MultiIndex.Top n k)` times the graph norm.
* `HolderSpace.CKGammaOn.exists_limit_evansNorm`: on an open domain, every sequence that is Cauchy
  for `evansNorm` converges for `evansNorm`.
* `HolderSpace.CKGammaOn.normal_segment_taylor_bounds` and
  `HolderSpace.CKGammaOn.norm_div_cube_le_of_hessian_bound`: on an open convex domain, if a
  derivative field and its first derivatives vanish at `base` and the Hessian is at most
  `K * ‖y - base‖` on the segment, then the field is at most `K / 6 * ‖x - base‖ ^ 3`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, (3) and Theorem 1, p. 255.
  <https://doi.org/10.1090/gsm/019>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.8.4, for the bound of a
  function with cubic vanishing at a point by its third derivatives.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Filter
open Set
open scoped Topology BoundedContinuousFunction

namespace HolderSpace.CKGammaOn

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}

/-- The top-order derivative, with its Hölder bound. -/
def topDerivative (f : CKGammaOn n k Ω γ) (a : MultiIndex.Top n k) :
    C0GammaOn (closure Ω) γ :=
  f.1.2 a

/-- Top-order Hölder derivatives respect addition. -/
@[simp]
theorem topDerivative_add (f g : CKGammaOn n k Ω γ) (a : MultiIndex.Top n k) :
    (f + g).topDerivative a = f.topDerivative a + g.topDerivative a :=
  rfl

/-- Top-order Hölder derivatives respect constant scalar multiplication. -/
@[simp]
theorem topDerivative_smul (c : ℝ) (f : CKGammaOn n k Ω γ) (a : MultiIndex.Top n k) :
    (c • f).topDerivative a = c • f.topDerivative a :=
  rfl

/-- The top-order Hölder field is the corresponding continuous derivative. -/
@[simp]
theorem topDerivative_toBoundedContinuousFunction (f : CKGammaOn n k Ω γ)
    (a : MultiIndex.Top n k) :
    (f.topDerivative a).toBoundedContinuousFunction = f.derivative a.1 :=
  f.2.1 a

/-- Evans's norm (3) of §5.1: the sum of `‖f.derivative a‖` over the multiindices `a` of order at
most `k`, plus the sum of the Hölder seminorms of the derivatives of order `k`. Each coordinate
multiindex is counted once. -/
def evansNorm (f : CKGammaOn n k Ω γ) : ℝ :=
  (∑ a : MultiIndex n k, ‖f.derivative a‖) +
    ∑ a : MultiIndex.Top n k, ((f.topDerivative a).holderSeminorm : ℝ)

/-- The derivative sum norm is nonnegative. -/
theorem evansNorm_nonneg (f : CKGammaOn n k Ω γ) : 0 ≤ f.evansNorm :=
  add_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _)

/-- Every derivative supremum norm is bounded by the complete graph norm. -/
theorem norm_derivative_le (f : CKGammaOn n k Ω γ) (a : MultiIndex n k) :
    ‖f.derivative a‖ ≤ ‖f‖ :=
  (norm_le_pi_norm f.1.1 a).trans (norm_fst_le f.1)

/-- Jet extraction has norm at most one in the Hölder graph norm, including
at the spatial boundary. The coefficient space uses the maximum coordinate norm. -/
theorem norm_jetEvalCLM_le (x : closure Ω) :
    ‖jetEvalCLM (γ := γ) (k := k) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
  intro a
  exact ((f.derivative a).norm_coe_le_norm x).trans (f.norm_derivative_le a)

/-- Every top-order Hölder norm is bounded by the complete graph norm. -/
theorem norm_topDerivative_le (f : CKGammaOn n k Ω γ) (a : MultiIndex.Top n k) :
    ‖f.topDerivative a‖ ≤ ‖f‖ :=
  (norm_le_pi_norm f.1.2 a).trans (norm_snd_le f.1)

open scoped Matrix.Norms.L2Operator in
/-- The curried Hessian has exactly the Euclidean operator norm of its coordinate
matrix. Matrix norm certificates therefore bound the actual derivative field,
without a dimension-dependent conversion constant. -/
theorem norm_hessian_eq_matrix_norm (f : CKGammaOn n k Ω γ)
    (a : MultiIndex n k) (ha : a.order + 1 < k) (x : ℝ^n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = f.interiorDerivative
      ((a.succ (by omega) i).succ (by simp only [MultiIndex.order_succ]; omega) j) x) :
    ‖f.hessian a ha x‖ = ‖A‖ := by
  have hmap : f.hessian a ha x =
      (InnerProductSpace.toDualMap ℝ (ℝ^n)).toContinuousLinearMap.comp
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) A) := by
    ext u v
    change f.hessian a ha x u v =
      inner ℝ (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) A) u) v
    rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
    simp [hessian, gradient, hA, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_assoc]
  rw [hmap, (InnerProductSpace.toDualMap ℝ (ℝ^n)).norm_toContinuousLinearMap_comp,
    ← Matrix.cstar_norm_def]

/-- Taylor estimates for any coordinate derivative field whose value and first
derivative traces vanish at the base. The Hessian envelope is an input, so tighter
numerical bounds can be used without changing the analytic proof. Both endpoints
may lie on the boundary, and no derivative of the Hessian is required. -/
theorem normal_segment_taylor_bounds (f : CKGammaOn n k Ω γ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (a : MultiIndex n k)
    (ha : a.order + 1 < k) {base x : ℝ^n} (hbase : base ∈ closure Ω)
    (hx : x ∈ closure Ω) {M K : ℝ}
    (hH : ∀ y ∈ segment ℝ base x, ‖f.hessian a ha y‖ ≤ M + K * ‖y - base‖)
    (hzero : f.derivative a ⟨base, hbase⟩ = 0)
    (hfirst : ∀ i : Fin n, f.derivative (a.succ (by omega) i) ⟨base, hbase⟩ = 0) :
    ‖f.gradient a (by omega) x‖ ≤ M * ‖x - base‖ + K * ‖x - base‖ ^ 2 / 2 ∧
      ‖f.derivative a ⟨x, hx⟩‖ ≤ M * ‖x - base‖ ^ 2 / 2 + K * ‖x - base‖ ^ 3 / 6 := by
  have hseg : segment ℝ base x ⊆ closure Ω := hconv.closure.segment_subset hbase hx
  have hQ (y : ℝ^n) (hy : y ∈ segment ℝ base x) :
      HasFDerivWithinAt (f.interiorDerivative a) (f.gradient a (by omega) y)
        (segment ℝ base x) y := by
    simpa only [gradient, interiorDerivative_apply _ _ (hseg hy)] using
      (f.hasFDerivWithinAt_derivative_closure hΩ hconv a (by omega) (hseg hy)).mono hseg
  have hD (y : ℝ^n) (hy : y ∈ segment ℝ base x) :
      HasFDerivWithinAt (f.gradient a (by omega)) (f.hessian a ha y)
        (segment ℝ base x) y :=
    (f.hasFDerivWithinAt_gradient_closure hΩ hconv a ha (hseg hy)).mono hseg
  have hgrad : f.gradient a (by omega) base = 0 := by
    simp only [gradient, interiorDerivative_apply _ _ hbase, hfirst, zero_smul,
      Finset.sum_const_zero]
  have hbound := PDE.Analysis.normal_segment_taylor_bounds_of_derivative_fields
    hQ hD hH (by simpa only [interiorDerivative_apply _ _ hbase] using hzero) hgrad
  simpa only [interiorDerivative_apply _ _ hx] using hbound

/-- Exact low-order trace cancellation and a linear Hessian envelope remove a cubic
singular weight. This applies to the same Hölder fields used by the trace map. -/
theorem norm_div_cube_le_of_hessian_bound (f : CKGammaOn n k Ω γ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (a : MultiIndex n k)
    (ha : a.order + 1 < k) {base x : ℝ^n} (hbase : base ∈ closure Ω)
    (hx : x ∈ closure Ω) {K : ℝ}
    (hH : ∀ y ∈ segment ℝ base x, ‖f.hessian a ha y‖ ≤ K * ‖y - base‖)
    (hzero : f.derivative a ⟨base, hbase⟩ = 0)
    (hfirst : ∀ i : Fin n, f.derivative (a.succ (by omega) i) ⟨base, hbase⟩ = 0)
    (hne : x ≠ base) : ‖f.derivative a ⟨x, hx⟩‖ / ‖x - base‖ ^ 3 ≤ K / 6 := by
  have hbound := f.normal_segment_taylor_bounds hΩ hconv a ha hbase hx
    (M := 0) (K := K) (fun y hy ↦ by simpa using hH y hy) hzero hfirst
  have hnorm : 0 < ‖x - base‖ ^ 3 :=
    pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 3
  apply (div_le_iff₀ hnorm).mpr
  calc
    ‖f.derivative a ⟨x, hx⟩‖ ≤ K * ‖x - base‖ ^ 3 / 6 := by simpa using hbound.2
    _ = K / 6 * ‖x - base‖ ^ 3 := by cas

/-- The complete graph norm is bounded by Evans's derivative sum norm. -/
theorem norm_le_evansNorm (f : CKGammaOn n k Ω γ) : ‖f‖ ≤ f.evansNorm := by
  classical
  change ‖f.1‖ ≤ f.evansNorm
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg f.evansNorm_nonneg).mpr
    intro a
    exact (Finset.single_le_sum (fun b _ ↦ norm_nonneg (f.derivative b))
      (Finset.mem_univ a)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _))
  · apply (pi_norm_le_iff_of_nonneg f.evansNorm_nonneg).mpr
    intro a
    change ‖f.topDerivative a‖ ≤ _
    rw [C0GammaOn.norm_def, topDerivative_toBoundedContinuousFunction]
    exact add_le_add
      (Finset.single_le_sum (fun b _ ↦ norm_nonneg (f.derivative b)) (Finset.mem_univ a.1))
      (Finset.single_le_sum (fun b _ ↦ NNReal.coe_nonneg (f.topDerivative b).holderSeminorm)
        (Finset.mem_univ a))

section OfDerivativeFields

open scoped NNReal

variable (hΩ : IsOpen Ω) (v : MultiIndex n k → ℝ^n → ℝ)
  (hcont : ∀ a, ContinuousOn (v a) (closure Ω))
  (C : MultiIndex n k → ℝ≥0)
  (hbound : ∀ a x, x ∈ closure Ω → ‖v a x‖ ≤ C a)
  (H : MultiIndex.Top n k → ℝ≥0)
  (hholder : ∀ a, HolderOnWith (H a) (γ : ℝ≥0) (v a.1) (closure Ω))
  (hderiv : ∀ a (ha : a.order < k) x, x ∈ Ω →
    HasFDerivAt (v a)
      (∑ i : Fin n, v (a.succ ha i) x • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x)

private theorem bounds_ofDerivativeFields :
    let f := ofDerivativeFields hΩ v hcont C hbound H hholder hderiv
    (∀ a, ‖f.derivative a‖ ≤ C a) ∧
      ∀ a, ((f.topDerivative a).holderSeminorm : ℝ) ≤ H a := by
  constructor
  · intro a
    apply (BoundedContinuousFunction.norm_le (C a).coe_nonneg).mpr
    intro x
    rw [derivative_ofDerivativeFields]
    exact hbound a x x.2
  · intro a
    change (nnHolderNorm (γ : ℝ≥0) ((closure Ω).domRestrict (v a.1)) : ℝ) ≤ H a
    have hnn : nnHolderNorm (γ : ℝ≥0) ((closure Ω).domRestrict (v a.1)) ≤ H a :=
      ENNReal.coe_le_coe.mp (coe_nnHolderNorm_le_eHolderNorm.trans
        (HolderWith.restrict_iff.mpr (hholder a)).eHolderNorm_le)
    exact_mod_cast hnn

/-- Per-field uniform and Hölder bounds control the complete graph norm by a
maximum budget. No number-of-coordinates factor is introduced. -/
theorem norm_ofDerivativeFields_le {B : ℝ}
    (hC : ∀ a, (C a : ℝ) ≤ B)
    (hCH : ∀ a : MultiIndex.Top n k, (C a.1 : ℝ) + H a ≤ B) :
    ‖ofDerivativeFields hΩ v hcont C hbound H hholder hderiv‖ ≤ B := by
  obtain ⟨hc, hh⟩ := bounds_ofDerivativeFields hΩ v hcont C hbound H hholder hderiv
  let f := ofDerivativeFields hΩ v hcont C hbound H hholder hderiv
  have hB : 0 ≤ B := (C 0).coe_nonneg.trans (hC 0)
  change ‖f.1‖ ≤ B
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro a
    change ‖f.derivative a‖ ≤ B
    exact (hc a).trans (hC a)
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro a
    change ‖f.topDerivative a‖ ≤ B
    rw [C0GammaOn.norm_def, topDerivative_toBoundedContinuousFunction]
    exact (add_le_add (hc a.1) (hh a)).trans (hCH a)

/-- The supplied budgets bound Evans's norm by their finite sum, counting each
coordinate multiindex once and each top-order Hölder seminorm once. -/
theorem evansNorm_ofDerivativeFields_le :
    (ofDerivativeFields hΩ v hcont C hbound H hholder hderiv).evansNorm ≤
      (∑ a : MultiIndex n k, (C a : ℝ)) + ∑ a : MultiIndex.Top n k, (H a : ℝ) := by
  obtain ⟨hc, hh⟩ := bounds_ofDerivativeFields hΩ v hcont C hbound H hholder hderiv
  exact add_le_add (Finset.sum_le_sum fun a _ ↦ hc a) (Finset.sum_le_sum fun a _ ↦ hh a)

end OfDerivativeFields

/-- The sum norm is bounded by a dimension- and order-dependent multiple of the graph norm. -/
theorem evansNorm_le (f : CKGammaOn n k Ω γ) :
    f.evansNorm ≤
      (Fintype.card (MultiIndex n k) + Fintype.card (MultiIndex.Top n k) : ℝ) * ‖f‖ := by
  calc
    f.evansNorm ≤
        (∑ _ : MultiIndex n k, ‖f‖) + ∑ _ : MultiIndex.Top n k, ‖f‖ :=
      add_le_add (Finset.sum_le_sum fun a _ ↦ f.norm_derivative_le a)
        (Finset.sum_le_sum fun a _ ↦
          (f.topDerivative a).holderSeminorm_le_norm.trans (f.norm_topDerivative_le a))
    _ = _ := by simp [add_mul]

/-- Vanishing of the derivative sum norm means that the function is zero. -/
theorem evansNorm_eq_zero_iff (f : CKGammaOn n k Ω γ) : f.evansNorm = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm (h ▸ f.norm_le_evansNorm) (norm_nonneg _))
  · rintro rfl
    exact le_antisymm (by simpa using (0 : CKGammaOn n k Ω γ).evansNorm_le)
      (0 : CKGammaOn n k Ω γ).evansNorm_nonneg

/-- The derivative sum norm satisfies the triangle inequality. -/
theorem evansNorm_add_le (f g : CKGammaOn n k Ω γ) :
    (f + g).evansNorm ≤ f.evansNorm + g.evansNorm := by
  have hs (a : MultiIndex.Top n k) :
      ((f.topDerivative a + g.topDerivative a).holderSeminorm : ℝ) ≤
        (f.topDerivative a).holderSeminorm + (g.topDerivative a).holderSeminorm := by
    exact_mod_cast (f.topDerivative a).memHolder.nnHolderNorm_add_le
      (g.topDerivative a).memHolder
  simp only [evansNorm, derivative_add, topDerivative_add]
  calc
    _ ≤ (∑ a : MultiIndex n k, (‖f.derivative a‖ + ‖g.derivative a‖)) +
        ∑ a : MultiIndex.Top n k,
          ((f.topDerivative a).holderSeminorm + (g.topDerivative a).holderSeminorm : ℝ) :=
      add_le_add (Finset.sum_le_sum fun _ _ ↦ norm_add_le _ _)
        (Finset.sum_le_sum fun a _ ↦ hs a)
    _ = _ := by simp only [Finset.sum_add_distrib]; ring

/-- The derivative sum norm is absolutely homogeneous. -/
theorem evansNorm_smul (c : ℝ) (f : CKGammaOn n k Ω γ) :
    (c • f).evansNorm = ‖c‖ * f.evansNorm := by
  have hs (a : MultiIndex.Top n k) :
      ((c • f.topDerivative a).holderSeminorm : ℝ) =
        ‖c‖ * (f.topDerivative a).holderSeminorm := by
    simpa only [C0GammaOn.holderSeminorm, C0GammaOn.toBoundedContinuousFunction_smul,
      BoundedContinuousFunction.coe_smul, Pi.smul_def, NNReal.coe_mul, coe_nnnorm] using
      congrArg (fun r : NNReal ↦ (r : ℝ)) ((f.topDerivative a).memHolder.nnHolderNorm_smul c)
  simp only [evansNorm, derivative_smul, topDerivative_smul, norm_smul, hs,
    Finset.mul_sum, mul_add]

/-- Convergence in the graph norm implies convergence in Evans's sum norm. -/
theorem tendsto_evansNorm_sub {u : ℕ → CKGammaOn n k Ω γ} {f : CKGammaOn n k Ω γ}
    (h : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun j ↦ (u j - f).evansNorm) atTop (𝓝 0) := by
  have hn : Tendsto (fun j ↦ ‖u j - f‖) atTop (𝓝 0) := by
    simpa using (h.sub (tendsto_const_nhds (x := f))).norm
  exact squeeze_zero (fun j ↦ (u j - f).evansNorm_nonneg)
    (fun j ↦ (u j - f).evansNorm_le) (by
      simpa using hn.const_mul
        (Fintype.card (MultiIndex n k) + Fintype.card (MultiIndex.Top n k) : ℝ))

/-- Every sequence Cauchy in Evans's derivative sum norm has a limit in that norm.
The domain need only be open; neither boundedness nor boundary regularity is required. -/
theorem exists_limit_evansNorm (hΩ : IsOpen Ω) (u : ℕ → CKGammaOn n k Ω γ)
    (hu : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, (u i - u j).evansNorm < ε) :
    ∃ f : CKGammaOn n k Ω γ,
      Tendsto (fun j ↦ (u j - f).evansNorm) atTop (𝓝 0) := by
  have hc : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun i hi j hj ↦ ?_⟩
    rw [dist_eq_norm]
    exact (u i - u j).norm_le_evansNorm.trans_lt (hN i hi j hj)
  have := completeSpace (n := n) (k := k) (γ := γ) hΩ
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨f, tendsto_evansNorm_sub hf⟩

end HolderSpace.CKGammaOn
