/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.Coefficients
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.NormalDilation
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Boundary jets of weighted normal reflections

The lower branch is a finite linear combination of reflected, normally dilated copies
of the source. Differentiating a word with `r` normal directions multiplies the `j`th
coefficient by `reflectionNode k j ^ r`. The Vandermonde identities then show that
every mixed jet through order `k` agrees with the source on the boundary.

These are classical derivative identities for `C^k` data. For Sobolev data, the passage
from matching boundary traces to global weak derivatives is a separate gluing argument.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

variable {n : ℕ}

/-- The lower branch associated to a coordinate with `r` normal derivatives. -/
def reflectedJet (i : Fin n) (k r : ℕ) (f : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  ∑ j, (reflectionCoeff k j * reflectionNode k j ^ r) *
    f (normalDilation i (reflectionNode k j) x)

/-- On the boundary, the weighted branch reproduces every jet through order `k`. -/
theorem reflectedJet_eq_on_boundary (i : Fin n) (k r : ℕ) (hr : r ≤ k)
    (f : ℝ^n → ℝ) (x : ℝ^n) (hx : x i = 0) :
    reflectedJet i k r f x = f x := by
  simp only [reflectedJet, normalDilation_eq_self i _ x hx]
  rw [← Finset.sum_mul, sum_reflectionCoeff_mul_pow k r hr, one_mul]

/-- Weighted reflection as a literal piecewise function; boundary values use the source. -/
def weightedReflectionFun (i : Fin n) (k : ℕ) (f : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  if x i < 0 then reflectedJet i k 0 f x else f x

/-- Weighted reflection agrees pointwise with the source on the closed upper half-space. -/
theorem weightedReflectionFun_eq_of_nonneg (i : Fin n) (k : ℕ)
    (f : ℝ^n → ℝ) (x : ℝ^n) (hx : 0 ≤ x i) :
    weightedReflectionFun i k f x = f x := by
  simp [weightedReflectionFun, not_lt.mpr hx]

private theorem iteratedPartialDeriv_sum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ^n → ℝ) (α : List (Fin n))
    (hF : ∀ j ∈ s, ContDiff ℝ α.length (F j)) :
    iteratedPartialDeriv α (fun x ↦ ∑ j ∈ s, F j x) =
      fun x ↦ ∑ j ∈ s, iteratedPartialDeriv α (F j) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    funext x
    exact PDE.iteratedPartialDeriv_zero α x
  | @insert j s hjs ih =>
    have hj := hF j (Finset.mem_insert_self j s)
    have hs : ∀ l ∈ s, ContDiff ℝ α.length (F l) :=
      fun l hl ↦ hF l (Finset.mem_insert_of_mem hl)
    have hsum : ContDiff ℝ α.length (fun x ↦ ∑ l ∈ s, F l x) :=
      ContDiff.sum hs
    simp only [Finset.sum_insert hjs]
    have hadd : iteratedPartialDeriv α (F j + (fun x ↦ ∑ l ∈ s, F l x)) =
        fun x ↦ iteratedPartialDeriv α (F j) x +
          iteratedPartialDeriv α (fun x ↦ ∑ l ∈ s, F l x) x :=
      PDE.iteratedPartialDeriv_add_of_contDiff α hj hsum
    rw [show (fun x ↦ F j x + ∑ l ∈ s, F l x) =
      F j + (fun x ↦ ∑ l ∈ s, F l x) from rfl, hadd, ih hs]

/-- The mixed derivative of a weighted branch is the branch with the corresponding
additional normal multiplicity, applied to the source mixed derivative. -/
theorem iteratedPartialDeriv_reflectedJet (i : Fin n) (k r : ℕ)
    {m : ℕ} {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f)
    (α : List (Fin n)) (hα : α.length ≤ m) :
    iteratedPartialDeriv α (reflectedJet i k r f) =
      reflectedJet i k (r + α.count i) (iteratedPartialDeriv α f) := by
  have hterm : ∀ j : Fin (k + 1),
      ContDiff ℝ α.length (fun x ↦
        (reflectionCoeff k j * reflectionNode k j ^ r) *
          f (normalDilation i (reflectionNode k j) x)) := by
    intro j
    exact (contDiff_const.mul (hf.comp (normalDilation i (reflectionNode k j)).contDiff)).of_le
      (by exact_mod_cast hα)
  change iteratedPartialDeriv α (fun x ↦ ∑ j, _) = _
  rw [iteratedPartialDeriv_sum Finset.univ _ α (fun j _ ↦ hterm j)]
  funext x
  unfold reflectedJet
  apply Finset.sum_congr rfl
  intro j _
  have hsmul : iteratedPartialDeriv α
      ((reflectionCoeff k j * reflectionNode k j ^ r) •
        (fun y ↦ f (normalDilation i (reflectionNode k j) y))) =
      fun y ↦ (reflectionCoeff k j * reflectionNode k j ^ r) •
        iteratedPartialDeriv α (fun y ↦ f (normalDilation i (reflectionNode k j) y)) y :=
    PDE.iteratedPartialDeriv_const_smul _ α _
  change iteratedPartialDeriv α
    ((reflectionCoeff k j * reflectionNode k j ^ r) •
      (fun y ↦ f (normalDilation i (reflectionNode k j) y))) x = _
  rw [hsmul, iteratedPartialDeriv_comp_normalDilation i _ hf α hα]
  simp [pow_add, mul_assoc]

/-- All mixed classical derivatives through order `k` match across the boundary.
No vanishing or parity condition is imposed on the source jet. -/
theorem iteratedPartialDeriv_reflectedJet_boundary (i : Fin n) (k : ℕ)
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ k f)
    (α : List (Fin n)) (hα : α.length ≤ k) (x : ℝ^n) (hx : x i = 0) :
    iteratedPartialDeriv α (reflectedJet i k 0 f) x = iteratedPartialDeriv α f x := by
  rw [iteratedPartialDeriv_reflectedJet i k 0 hf α hα, zero_add]
  exact reflectedJet_eq_on_boundary i k (α.count i)
    ((List.count_le_length).trans hα) _ x hx

end SobolevSpace.GraphSpace.HigherOrderReflection
