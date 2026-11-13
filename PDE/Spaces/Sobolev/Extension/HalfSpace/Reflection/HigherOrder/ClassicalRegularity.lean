/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedJets

/-!
# Classical regularity of one-sided weighted reflection

The zeroth and first moment identities make weighted reflection continuously
differentiable across the reflecting plane. Only the derivative within the closed
upper half-space is needed; the original function need not be differentiable below it.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set
open scoped Topology

variable {n : ℕ}

/-- The first two moments make the weighted sum of the normal dilations the identity. -/
theorem sum_reflectionCoeff_smul_normalDilation (i : Fin n) {k : ℕ} (hk : 1 ≤ k) :
    ∑ j, reflectionCoeff k j • normalDilation i (reflectionNode k j) =
      ContinuousLinearMap.id ℝ (ℝ^n) := by
  ext x l
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.id_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, normalDilation_apply]
  by_cases hl : l = i
  · simp only [hl, ↓reduceIte, ← mul_assoc, ← Finset.sum_mul]
    simpa only [pow_one, one_mul] using congrArg (· * x i)
      (sum_reflectionCoeff_mul_pow k 1 hk)
  · simp [hl, ← Finset.sum_mul]

/-- A continuous derivative on the closed upper half-space extends to a global `C¹`
function by the weighted reflection. No lower-side derivative is assumed. -/
theorem contDiff_one_weightedReflectionFun (i : Fin n) {k : ℕ} (hk : 1 ≤ k)
    {f : ℝ^n → ℝ} {f' : ℝ^n → (ℝ^n →L[ℝ] ℝ)}
    (hf' : Continuous f')
    (hderiv : ∀ x, 0 ≤ x i →
      HasFDerivWithinAt f (f' x) {y | 0 ≤ y i} x) :
    ContDiff ℝ 1 (weightedReflectionFun i k f) := by
  classical
  let d : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦
    ∑ j, reflectionCoeff k j •
      ((f' (normalDilation i (reflectionNode k j) x)).comp
        (normalDilation i (reflectionNode k j)))
  have hd : Continuous d :=
    continuous_finsetSum _ fun j _ ↦
      ((hf'.comp (normalDilation i (reflectionNode k j)).continuous).clm_comp
        (continuous_const (y := normalDilation i (reflectionNode k j)))).const_smul
          (reflectionCoeff k j)
  have hd0 (x : ℝ^n) (hx : x i = 0) : d x = f' x := by
    dsimp [d]
    simp only [normalDilation_eq_self i _ x hx]
    simp only [← ContinuousLinearMap.comp_smul]
    rw [← ContinuousLinearMap.comp_finsetSum, sum_reflectionCoeff_smul_normalDilation i hk,
      ContinuousLinearMap.comp_id]
  let D : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦ if x i < 0 then d x else f' x
  have hD : Continuous D := Continuous.piecewise (s := {x : ℝ^n | x i < 0})
    (fun x hx ↦ hd0 x (frontier_lt_subset_eq (EuclideanSpace.proj i).continuous
      continuous_const hx)) hd hf'
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨D, hD, fun x ↦ ?_⟩
  have hu : HasFDerivWithinAt (weightedReflectionFun i k f) (D x)
      {y | 0 ≤ y i} x := by
    by_cases hx : 0 ≤ x i
    · rw [show D x = f' x from ite_eq_right (not_lt.mpr hx)]
      exact (hderiv x hx).congr' (fun y hy ↦ weightedReflectionFun_eq_of_nonneg i k f y hy) hx
    · apply HasFDerivWithinAt.of_notMem_closure
      have hs : IsClosed {y : ℝ^n | 0 ≤ y i} :=
        isClosed_le continuous_const (EuclideanSpace.proj i).continuous
      simpa only [hs.closure_eq, mem_ofPred_eq] using hx
  have hl : HasFDerivWithinAt (weightedReflectionFun i k f) (D x)
      {y | y i ≤ 0} x := by
    by_cases hx : x i ≤ 0
    · have hDx : D x = d x := by
        by_cases hx' : x i < 0
        · exact ite_eq_left hx'
        · simp only [D, ite_eq_right hx']
          exact (hd0 x (le_antisymm hx (not_lt.mp hx'))).symm
      rw [hDx]
      have hsum : HasFDerivWithinAt (reflectedJet i k 0 f) (d x)
          {y | y i ≤ 0} x := by
        have hterm (j : Fin (k + 1)) :
            HasFDerivWithinAt
              (fun y ↦ reflectionCoeff k j • f (normalDilation i (reflectionNode k j) y))
              (reflectionCoeff k j •
                ((f' (normalDilation i (reflectionNode k j) x)).comp
                  (normalDilation i (reflectionNode k j)))) {y | y i ≤ 0} x := by
          have hm : MapsTo (normalDilation i (reflectionNode k j))
              {y : ℝ^n | y i ≤ 0} {y | 0 ≤ y i} := by
            intro y hy
            simpa only [mem_ofPred_eq, normalDilation_apply, ↓reduceIte] using
              mul_nonneg_of_nonpos_of_nonpos (reflectionNode_neg k j).le hy
          exact ((hderiv _ (hm hx)).comp x
            (normalDilation i (reflectionNode k j)).hasFDerivAt.hasFDerivWithinAt hm).const_smul
              (reflectionCoeff k j)
        have heq : reflectedJet i k 0 f = fun y ↦
            ∑ j, reflectionCoeff k j • f (normalDilation i (reflectionNode k j) y) :=
          funext fun y ↦ by simp only [reflectedJet, pow_zero, mul_one, smul_eq_mul]
        exact heq ▸ HasFDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ ↦ hterm j)
      refine hsum.congr' (fun y hy ↦ ?_) hx
      by_cases hy' : y i < 0
      · exact ite_eq_left hy'
      · rw [weightedReflectionFun, ite_eq_right hy']
        exact (reflectedJet_eq_on_boundary i k 0 (Nat.zero_le k) f y
          (le_antisymm hy (not_lt.mp hy'))).symm
    · apply HasFDerivWithinAt.of_notMem_closure
      have hs : IsClosed {y : ℝ^n | y i ≤ 0} :=
        isClosed_le (EuclideanSpace.proj i).continuous continuous_const
      simpa only [hs.closure_eq, mem_ofPred_eq] using hx
  have hcover : {y : ℝ^n | 0 ≤ y i} ∪ {y | y i ≤ 0} = univ :=
    eq_univ_of_forall fun y ↦ le_total 0 (y i)
  rw [← hasFDerivWithinAt_univ, ← hcover]
  exact hu.union hl

end SobolevSpace.GraphSpace.HigherOrderReflection
