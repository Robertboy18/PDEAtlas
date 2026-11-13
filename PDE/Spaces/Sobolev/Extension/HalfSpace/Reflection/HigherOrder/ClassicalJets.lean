/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HalfSpaceGluing
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalRegularity

/-!
# Finite classical regularity of weighted reflection

The reflection moments match all coordinate jets of the derivative field. Consequently
a `C^k` derivative on the closed upper half-space gives a global `C^{k+1}` extension,
without any regularity assumption on the source below that half-space.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set
open scoped Topology

variable {n : ℕ}

/-- Weighted jets glue through every order allowed by the reflection moments. -/
theorem contDiff_piecewise_reflectedJet (i : Fin n) (K r : ℕ) {k : ℕ}
    (hr : r + k ≤ K) {f : ℝ^n → ℝ} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun x ↦ if x i < 0 then reflectedJet i K r f x else f x) := by
  refine PDE.Analysis.contDiff_piecewise_halfSpace i ?_ hf ?_
  · exact ContDiff.sum fun j _ ↦
      contDiff_const.mul (hf.comp (normalDilation i (reflectionNode K j)).contDiff)
  · intro α hα x hx
    rw [iteratedPartialDeriv_reflectedJet i K r hf α hα]
    exact reflectedJet_eq_on_boundary i K (r + α.count i)
      (le_trans (Nat.add_le_add_left (List.count_le_length.trans hα) r) hr) _ x hx

/-- The derivative of one-sided reflection is the reflected derivative composed with
the normal dilations. This formula uses only derivatives within the upper half-space. -/
theorem hasFDerivAt_weightedReflectionFun (i : Fin n) {K : ℕ} (hK : 1 ≤ K)
    {f : ℝ^n → ℝ} {f' : ℝ^n → (ℝ^n →L[ℝ] ℝ)}
    (hderiv : ∀ x, 0 ≤ x i →
      HasFDerivWithinAt f (f' x) {y | 0 ≤ y i} x) (x : ℝ^n) :
    HasFDerivAt (weightedReflectionFun i K f)
      (if x i < 0 then
        ∑ j, reflectionCoeff K j •
          ((f' (normalDilation i (reflectionNode K j) x)).comp
            (normalDilation i (reflectionNode K j)))
      else f' x) x := by
  refine PDE.Analysis.hasFDerivAt_piecewise_halfSpace i
    (f' := fun y ↦ ∑ j, reflectionCoeff K j •
      ((f' (normalDilation i (reflectionNode K j) y)).comp
        (normalDilation i (reflectionNode K j)))) ?_ hderiv
    (fun y hy ↦ reflectedJet_eq_on_boundary i K 0 (Nat.zero_le K) f y hy) ?_ x
  · intro y hy
    have hterm (j : Fin (K + 1)) :
        HasFDerivWithinAt
          (fun z ↦ reflectionCoeff K j • f (normalDilation i (reflectionNode K j) z))
          (reflectionCoeff K j •
            ((f' (normalDilation i (reflectionNode K j) y)).comp
              (normalDilation i (reflectionNode K j)))) {z | z i ≤ 0} y := by
      have hm : MapsTo (normalDilation i (reflectionNode K j))
          {z : ℝ^n | z i ≤ 0} {z | 0 ≤ z i} := by
        intro z hz
        simpa only [mem_ofPred_eq, normalDilation_apply, ↓reduceIte] using
          mul_nonneg_of_nonpos_of_nonpos (reflectionNode_neg K j).le hz
      exact ((hderiv _ (hm hy)).comp y
        (normalDilation i (reflectionNode K j)).hasFDerivAt.hasFDerivWithinAt hm).const_smul
          (reflectionCoeff K j)
    have heq : reflectedJet i K 0 f = fun z ↦
        ∑ j, reflectionCoeff K j • f (normalDilation i (reflectionNode K j) z) := by
      funext z
      simp only [reflectedJet, pow_zero, mul_one, smul_eq_mul]
    rw [heq]
    exact HasFDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ ↦ hterm j)
  · intro y hy
    simp only [normalDilation_eq_self i _ y hy, ← ContinuousLinearMap.comp_smul]
    rw [← ContinuousLinearMap.comp_finsetSum, sum_reflectionCoeff_smul_normalDilation i hK,
      ContinuousLinearMap.comp_id]

/-- A `C^k` derivative on the closed upper half-space yields a global `C^{k+1}`
weighted reflection. Its source is unrestricted on the lower half-space. -/
theorem contDiff_succ_weightedReflectionFun (i : Fin n) (k : ℕ)
    {f : ℝ^n → ℝ} {f' : ℝ^n → (ℝ^n →L[ℝ] ℝ)}
    (hf' : ContDiff ℝ k f')
    (hderiv : ∀ x, 0 ≤ x i →
      HasFDerivWithinAt f (f' x) {y | 0 ≤ y i} x) :
    ContDiff ℝ (k + 1) (weightedReflectionFun i (k + 1) f) := by
  classical
  let D : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦
    if x i < 0 then
      ∑ j, reflectionCoeff (k + 1) j •
        ((f' (normalDilation i (reflectionNode (k + 1) j) x)).comp
          (normalDilation i (reflectionNode (k + 1) j)))
    else f' x
  have hcoord (l : Fin n) : ContDiff ℝ k
      (fun x ↦ D x (EuclideanSpace.single l 1)) := by
    have heq : (fun x ↦ D x (EuclideanSpace.single l 1)) =
        fun x ↦ if x i < 0 then
          reflectedJet i (k + 1) (if l = i then 1 else 0)
            (fun y ↦ f' y (EuclideanSpace.single l 1)) x
        else f' x (EuclideanSpace.single l 1) := by
      funext x
      by_cases hx : x i < 0
      · simp only [D, hx, ↓reduceIte, sum_apply, smul_apply,
          ContinuousLinearMap.comp_apply, normalDilation_single,
          map_smul, smul_eq_mul, reflectedJet]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp [mul_assoc]
      · simp only [D, hx, ↓reduceIte]
    rw [heq]
    apply contDiff_piecewise_reflectedJet i (k + 1)
      (if l = i then 1 else 0) (by split_ifs <;> omega)
    exact hf'.clm_apply contDiff_const
  have hD : ContDiff ℝ k D := by
    have heq : D = fun x ↦
        ∑ l, D x (EuclideanSpace.single l 1) • EuclideanSpace.proj l := by
      funext x
      ext v
      have hv : v = ∑ l, v l • EuclideanSpace.single l 1 := by
        ext l
        simp [Pi.single_apply]
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
        EuclideanSpace.coe_proj]
      exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _
    rw [heq]
    exact ContDiff.sum fun l _ ↦ (hcoord l).smul_const _
  exact contDiff_succ_iff_hasFDerivAt.mpr
    ⟨D, hD, hasFDerivAt_weightedReflectionFun i (by omega) hderiv⟩

end SobolevSpace.GraphSpace.HigherOrderReflection
