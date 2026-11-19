/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.CoordinateReflection
public import PDE.FDeriv.PartialDeriv

/-!
# Normal dilations and mixed derivatives

Dilating a single coordinate by `a` multiplies an iterated partial derivative by
`a` to the multiplicity of that coordinate. Negative dilations are the reflected
arguments used in higher-order half-space extension.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open PDE.Common

variable {n : ℕ}

/-- Dilate coordinate `i` by `a`, leaving all tangential coordinates fixed. -/
def normalDilation (i : Fin n) (a : ℝ) : ℝ^n →L[ℝ] ℝ^n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦ (if j = i then a else 1) • EuclideanSpace.proj j)

/-- Coordinate formula for a normal dilation. -/
@[simp] theorem normalDilation_apply (i : Fin n) (a : ℝ) (x : ℝ^n) (j : Fin n) :
    normalDilation i a x j = (if j = i then a else 1) * x j := by
  by_cases hji : j = i <;> simp [normalDilation, hji]

/-- Every dilation fixes its boundary hyperplane pointwise. -/
theorem normalDilation_eq_self (i : Fin n) (a : ℝ) (x : ℝ^n) (hx : x i = 0) :
    normalDilation i a x = x := by
  ext j
  by_cases hji : j = i <;> simp [hji, hx]

/-- Composition multiplies the two normal dilation factors. -/
theorem normalDilation_comp_apply (i : Fin n) (a b : ℝ) (x : ℝ^n) :
    normalDilation i a (normalDilation i b x) = normalDilation i (a * b) x := by
  ext j
  by_cases hji : j = i <;> simp [hji, mul_assoc]

/-- Unit normal dilation is the identity. -/
@[simp] theorem normalDilation_one (i : Fin n) (x : ℝ^n) :
    normalDilation i 1 x = x := by
  ext j
  simp

/-- A nonzero normal dilation is a continuous linear equivalence. -/
def normalDilationEquiv (i : Fin n) (a : ℝ) (ha : a ≠ 0) : ℝ^n ≃L[ℝ] ℝ^n :=
  ContinuousLinearEquiv.equivOfInverse (normalDilation i a) (normalDilation i a⁻¹)
    (fun x ↦ by rw [normalDilation_comp_apply, inv_mul_cancel₀ ha, normalDilation_one])
    (fun x ↦ by rw [normalDilation_comp_apply, mul_inv_cancel₀ ha, normalDilation_one])

/-- The equivalence uses the same coordinate dilation as its underlying function. -/
@[simp] theorem normalDilationEquiv_apply (i : Fin n) (a : ℝ) (ha : a ≠ 0) (x : ℝ^n) :
    normalDilationEquiv i a ha x = normalDilation i a x :=
  rfl

/-- Coordinate vectors acquire exactly their normal dilation factor. -/
theorem normalDilation_single (i j : Fin n) (a : ℝ) :
    normalDilation i a (EuclideanSpace.single j 1) =
      (if j = i then a else 1) • EuclideanSpace.single j 1 := by
  ext l
  by_cases hlj : l = j
  · subst l
    by_cases hji : j = i <;> simp [hji]
  · by_cases hji : j = i
    · subst j
      simp [hlj]
    · simp [hlj, hji]

/-- The chain rule for one normal dilation and one coordinate derivative. -/
theorem partialDeriv_comp_normalDilation (i j : Fin n) (a : ℝ)
    (f : ℝ^n → ℝ) (x : ℝ^n) (hf : DifferentiableAt ℝ f (normalDilation i a x)) :
    (∂[j] (fun y ↦ f (normalDilation i a y))) x =
      (if j = i then a else 1) * (∂[j] f) (normalDilation i a x) := by
  have h := hf.hasFDerivAt.comp x ((normalDilation i a).hasFDerivAt (x := x))
  change fderiv ℝ (f ∘ normalDilation i a) x (EuclideanSpace.single j 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, normalDilation_single, map_smul]
  rfl

/-- A mixed derivative acquires one dilation factor for each normal direction in its word. -/
theorem iteratedPartialDeriv_comp_normalDilation (i : Fin n) (a : ℝ)
    {k : ℕ} {f : ℝ^n → ℝ} (hf : ContDiff ℝ k f)
    (α : List (Fin n)) (hα : α.length ≤ k) :
    iteratedPartialDeriv α (fun y ↦ f (normalDilation i a y)) =
      fun x ↦ a ^ α.count i * iteratedPartialDeriv α f (normalDilation i a x) := by
  induction α with
  | nil => simp [iteratedPartialDeriv]
  | cons j α ih =>
    have hα' : α.length ≤ k := by simpa using (Nat.le_of_succ_le hα)
    have hdiff : Differentiable ℝ (iteratedPartialDeriv α f) :=
      (PDE.contDiff_iteratedPartialDeriv_of_le hf α hα').differentiable (by
        have : 0 < k - α.length := by simpa using Nat.sub_pos_of_lt hα
        exact_mod_cast this.ne')
    funext x
    change (∂[j] (iteratedPartialDeriv α
      (fun y ↦ f (normalDilation i a y)))) x = _
    rw [ih hα']
    rw [show (fun y ↦ a ^ α.count i * iteratedPartialDeriv α f
        (normalDilation i a y)) =
      (fun y ↦ a ^ α.count i • iteratedPartialDeriv α f
        (normalDilation i a y)) from rfl, PDE.partialDeriv_const_smul]
    rw [partialDeriv_comp_normalDilation i j a _ x hdiff.differentiableAt]
    by_cases hji : j = i
    · subst j
      simp [iteratedPartialDeriv, pow_succ, mul_assoc]
    · simp [iteratedPartialDeriv, hji]

end SobolevSpace.GraphSpace.HigherOrderReflection
