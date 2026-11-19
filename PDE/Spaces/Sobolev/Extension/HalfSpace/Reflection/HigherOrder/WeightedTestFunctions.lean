/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.IntegralIdentities
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeakDilation
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedLp

/-!
# Transformed tests for weighted reflection

Changing variables in the lower half-space transfers a whole-space pairing to an
upper-half-space pairing. The resulting test has coefficients `cⱼ aⱼ^r |aⱼ⁻¹|`.
Its normal derivative lowers the row index, and its boundary value at row `r + 1`
vanishes by the moment equation at index `r`.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory TopologicalSpace
open SobolevSpace.Extension.GraphSpace.HalfSpace
open scoped ENNReal Distributions

variable (n k : ℕ) [Fact (0 < n)]

/-- Pull a test back by the inverse of a reflected normal dilation. -/
def inverseDilationTestFunction (j : Fin (k + 1)) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  let e := normalDilationEquiv (PDE.Common.lastIndex (n := n))
    (reflectionNode k j) (reflectionNode_neg k j).ne
  TestFunction.precompProper (e.symm : ℝ^n → ℝ^n)
    e.symm.contDiff e.symm.toHomeomorph.isProperMap φ

/-- The inverse dilation acts on the normal coordinate alone. -/
@[simp] theorem inverseDilationTestFunction_apply (j : Fin (k + 1))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    inverseDilationTestFunction n k j φ x =
      φ (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j)⁻¹ x) :=
  rfl

/-- The test obtained by transferring row `r` of weighted reflection upstairs. -/
def weightedTest (r : ℕ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  φ + ∑ j, (reflectionCoeff k j * reflectionNode k j ^ r *
    |(reflectionNode k j)⁻¹|) • inverseDilationTestFunction n k j φ

/-- Pointwise change-of-variables formula for the transformed test. -/
theorem weightedTest_apply (r : ℕ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    weightedTest n k r φ x = φ x +
      ∑ j, (reflectionCoeff k j * reflectionNode k j ^ r *
        |(reflectionNode k j)⁻¹|) *
          φ (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j)⁻¹ x) := by
  simp [weightedTest]

/-- Inverse dilation multiplies the normal derivative by the inverse node. -/
theorem lineDerivCLM_inverseDilationTestFunction (i : Fin n) (j : Fin (k + 1))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ))
        (inverseDilationTestFunction n k j φ) =
      (if i = PDE.Common.lastIndex (n := n) then (reflectionNode k j)⁻¹ else 1) •
        inverseDilationTestFunction n k j
          (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ) := by
  ext x
  rw [testFunction_lineDerivCLM_apply]
  change (∂[i]
      (fun y ↦ φ (normalDilation (PDE.Common.lastIndex (n := n))
        (reflectionNode k j)⁻¹ y))) x = _
  rw [partialDeriv_comp_normalDilation _ _ _ _ _
    (φ.contDiff.differentiable (by simp)).differentiableAt]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, inverseDilationTestFunction_apply,
    testFunction_lineDerivCLM_apply, partialDeriv]
  rfl

/-- Differentiating the transformed next row recovers the current transformed derivative. -/
theorem lineDerivCLM_weightedTest (i : Fin n) (r : ℕ)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ))
        (weightedTest n k (r + if i = PDE.Common.lastIndex (n := n) then 1 else 0) φ) =
      weightedTest n k r
        (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ) := by
  simp only [weightedTest, map_add, map_sum, map_smul, lineDerivCLM_inverseDilationTestFunction,
    smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · simp only [hi, ↓reduceIte, pow_succ]
    have ha := (reflectionNode_neg k j).ne
    field_simp
  · simp [hi]

/-- Row `r + 1` vanishes on the boundary when moment `r` is matched.
The hypothesis is `r ≤ k`; no moment at `r + 1` is used. -/
theorem weightedTest_succ_zero_on_boundary (r : ℕ) (hr : r ≤ k)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n)
    (hx : x (PDE.Common.lastIndex (n := n)) = 0) :
    weightedTest n k (r + 1) φ x = 0 := by
  rw [weightedTest_apply]
  have hcoef (j : Fin (k + 1)) :
      reflectionCoeff k j * reflectionNode k j ^ (r + 1) *
        |(reflectionNode k j)⁻¹| = -(reflectionCoeff k j * reflectionNode k j ^ r) := by
    rw [pow_succ, abs_of_neg (inv_neg''.mpr (reflectionNode_neg k j))]
    have ha := (reflectionNode_neg k j).ne
    field_simp
  simp_rw [normalDilation_eq_self _ _ x hx, hcoef, neg_mul, Finset.sum_neg_distrib]
  rw [← Finset.sum_mul, sum_reflectionCoeff_mul_pow k r hr, one_mul, add_neg_cancel]

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The lower weighted branch pairs with the finite sum of inverse-dilated tests. -/
theorem integral_weightedPullbackLp_mul (r : ℕ) (u : DerivLp n p ℝ^n₊)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x, weightedPullbackLp n k p r u x * φ x ∂domainMeasure n ℝ^n₋) =
      ∑ j, (reflectionCoeff k j * reflectionNode k j ^ r * |(reflectionNode k j)⁻¹|) *
        ∫ x, u x * inverseDilationTestFunction n k j φ x ∂domainMeasure n ℝ^n₊ := by
  let c (j : Fin (k + 1)) := reflectionCoeff k j * reflectionNode k j ^ r
  let v (j : Fin (k + 1)) :=
    dilationPullbackLp n p (reflectionNode k j) (reflectionNode_neg k j) u
  have hInt (j : Fin (k + 1)) :
      Integrable (fun x ↦ (c j • v j : DerivLp n p ℝ^n₋) x * φ x)
        (domainMeasure n ℝ^n₋) :=
    integrable_mul_of_memLp_measure n p (Lp.memLp _)
      φ.contDiff.continuous φ.hasCompactSupport
  calc
    _ = ∫ x, ∑ j, (c j • v j : DerivLp n p ℝ^n₋) x * φ x
        ∂domainMeasure n ℝ^n₋ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j ↦ c j • v j)] with x hx
      simp only [weightedPullbackLp, sum_apply, smul_apply]
      change (∑ j, c j • v j : DerivLp n p ℝ^n₋) x * φ x = _
      rw [hx]
      simp only [Finset.sum_apply, Finset.sum_mul]
    _ = ∑ j, ∫ x, (c j • v j : DerivLp n p ℝ^n₋) x * φ x
        ∂domainMeasure n ℝ^n₋ :=
      integral_finsetSum _ (fun j _ ↦ hInt j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hs :
          (∫ x, (c j • v j : DerivLp n p ℝ^n₋) x * φ x ∂domainMeasure n ℝ^n₋) =
            c j * ∫ x, v j x * φ x ∂domainMeasure n ℝ^n₋ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul (c j) (v j)] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [hs, integral_dilationPullbackLp_mul]
      simp only [c, inverseDilationTestFunction_apply, mul_assoc]

/-- A whole-space weighted pairing equals the upper-half-space pairing with
the transformed test, including its exact Jacobian factors. -/
theorem integral_weightedExtendLp_mul (r : ℕ) (u : DerivLp n p ℝ^n₊)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x, weightedExtendLp n k p r u x * φ x ∂domainMeasure n univ) =
      ∫ x, u x * weightedTest n k r φ x ∂domainMeasure n ℝ^n₊ := by
  have hInt (v : DerivLp n p univ) :
      Integrable (fun x ↦ v x * φ x) (domainMeasure n univ) :=
    integrable_mul_of_memLp_measure n p (Lp.memLp v)
      φ.contDiff.continuous φ.hasCompactSupport
  have hsplit :
      (∫ x, weightedExtendLp n k p r u x * φ x ∂domainMeasure n univ) =
        (∫ x, u x * φ x ∂domainMeasure n ℝ^n₊) +
        ∫ x, weightedPullbackLp n k p r u x * φ x ∂domainMeasure n ℝ^n₋ := by
    have hupper :
        (∫ x, HalfSpace.embedUpper (n := n) (p := p) u x * φ x
          ∂domainMeasure n univ) = ∫ x, u x * φ x ∂domainMeasure n ℝ^n₊ :=
      integral_embedUpper_mul n p u φ
    have hlower :
        (∫ x, HalfSpace.embedLower (n := n) (p := p) (weightedPullbackLp n k p r u) x *
          φ x ∂domainMeasure n univ) =
        ∫ x, weightedPullbackLp n k p r u x * φ x ∂domainMeasure n ℝ^n₋ :=
      integral_embedLower_mul n p (weightedPullbackLp n k p r u) φ
    rw [← hupper, ← hlower, ← integral_add (hInt _) (hInt _)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (HalfSpace.embedUpper (n := n) (p := p) u)
      (HalfSpace.embedLower (n := n) (p := p) (weightedPullbackLp n k p r u))]
      with x hx
    change ((HalfSpace.embedUpper (n := n) (p := p) u +
      HalfSpace.embedLower (n := n) (p := p) (weightedPullbackLp n k p r u) :
      DerivLp n p univ) : ℝ^n → ℝ) x * φ x = _
    rw [hx, Pi.add_apply, add_mul]
  rw [hsplit, integral_weightedPullbackLp_mul]
  let c (j : Fin (k + 1)) :=
    reflectionCoeff k j * reflectionNode k j ^ r * |(reflectionNode k j)⁻¹|
  have hIntUpper (θ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
      Integrable (fun x ↦ u x * θ x) (domainMeasure n ℝ^n₊) :=
    integrable_mul_of_memLp n p (Lp.memLp u) θ.contDiff.continuous θ.hasCompactSupport
  have hterm (j : Fin (k + 1)) :
      Integrable (fun x ↦ c j * (u x * inverseDilationTestFunction n k j φ x))
        (domainMeasure n ℝ^n₊) :=
    (hIntUpper (inverseDilationTestFunction n k j φ)).const_mul (c j)
  calc
    _ = (∫ x, u x * φ x ∂domainMeasure n ℝ^n₊) +
        ∑ j, ∫ x, c j * (u x * inverseDilationTestFunction n k j φ x)
          ∂domainMeasure n ℝ^n₊ := by simp only [integral_const_mul, c]
    _ = ∫ x, u x * φ x + ∑ j, c j * (u x * inverseDilationTestFunction n k j φ x)
        ∂domainMeasure n ℝ^n₊ := by
      rw [integral_add (hIntUpper φ) (integrable_finsetSum _ (fun j _ ↦ hterm j)),
        integral_finsetSum _ (fun j _ ↦ hterm j)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [weightedTest_apply, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [inverseDilationTestFunction_apply, c]
      ring

end SobolevSpace.GraphSpace.HigherOrderReflection
