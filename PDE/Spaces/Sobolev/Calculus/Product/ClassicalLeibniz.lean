/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.DerivativeSplits
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Higher-order product rules

The Leibniz rule for an iterated partial derivative of a product of smooth functions on `ℝ^n`.
Iterated derivatives are indexed here by words `α : List (Fin n)` rather than by multi-indices,
so the classical formula `∂^α(fg) = ∑_{β ≤ α} (α choose β) ∂^β f ∂^{α-β} g` is stated without
binomial coefficients: the sum runs over `derivativeSplits α`, the list of all `2^{|α|}` ordered
assignments of the letters of `α` to the two factors, each contributing
`∂^{β} f · ∂^{γ} g` with `β` and `γ` the letters sent to `f` and to `g`. Collecting equal
terms recovers the binomial coefficients, but the Sobolev product
estimates use the unfolded form, since it lets each summand be bounded separately.

We also record the scaling rule `∂ᵢ(h(c·)) = c (∂ᵢh)(c·)` for a single coordinate
derivative, which is what dilations of test functions need.

## Main results

* `iteratedPartialDeriv_mul_eq_sum_split`: for `C^∞` functions `f, g`,
  `∂^α(fg) = ∑_{(β,γ) ∈ derivativeSplits α} ∂^β f · ∂^γ g` pointwise.
* `partialDeriv_comp_const_smul`: the chain rule for the dilation `z ↦ c • z` in one coordinate.

## Implementation notes

The proof is an induction on the word `α`, peeling off the outermost derivative with the
first-order product rule and pushing it through the list sum; the private lemmas
`differentiableAt_list_sum` and `partialDeriv_list_sum` supply differentiability and linearity
of `partialDeriv` over finite list sums. The `C^∞` hypothesis is more than needed (order `|α|`
would do) but avoids tracking orders through the induction.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open Function

variable {n : ℕ}



/-- Chain rule for a dilation in one coordinate direction: if `h` is differentiable at `c • x`,
then `∂ᵢ (h (c • ·)) x = c · (∂ᵢ h) (c • x)`. -/
theorem partialDeriv_comp_const_smul (c : ℝ) {i : Fin n} {h : ℝ^n → ℝ} {x : ℝ^n}
    (hh : DifferentiableAt ℝ h (c • x)) :
    (∂[i] (fun z ↦ h (c • z))) x = c * (∂[i] h) (c • x) := by
  have hsmul :
      HasFDerivAt (fun z : ℝ^n ↦ c • z) (c • (1 : ℝ^n →L[ℝ] ℝ^n)) x := by
    rw [show (fun z : ℝ^n ↦ c • z) = c • (fun z : ℝ^n ↦ z) by rfl]
    exact (hasFDerivAt_id x).const_smul c
  have hcomp := hh.hasFDerivAt.comp x hsmul
  have hfderiv_eq := hcomp.fderiv
  have happly :=
    congrArg (fun (T : ℝ^n →L[ℝ] ℝ) ↦ T (EuclideanSpace.single i (1 : ℝ))) hfderiv_eq
  have hdir :
      (c • (1 : ℝ^n →L[ℝ] ℝ^n)) (EuclideanSpace.single i (1 : ℝ)) =
        c • EuclideanSpace.single i (1 : ℝ) := by
    simp
  -- rewrite `T (c • v)` as `c * T v`
  rw [show (fun z : ℝ^n ↦ h (c • z)) = h ∘ fun z : ℝ^n ↦ c • z by rfl]
  simpa [partialDeriv, hdir, smul_eq_mul, mul_assoc] using happly

private theorem differentiableAt_list_sum {ι : Type*} {F : ι → ℝ^n → ℝ} {x : ℝ^n}
    (L : List ι) (hF : ∀ p ∈ L, DifferentiableAt ℝ (F p) x) :
    DifferentiableAt ℝ (fun y ↦ (L.map fun p ↦ F p y).sum) x := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF p (by simp)).fun_add (ih fun q hq ↦ hF q (by simp [hq]))

private theorem partialDeriv_list_sum {ι : Type*} {i : Fin n} {F : ι → ℝ^n → ℝ} {x : ℝ^n}
    (L : List ι) (hF : ∀ p ∈ L, DifferentiableAt ℝ (F p) x) :
    (∂[i] (fun y ↦ (L.map fun p ↦ F p y).sum)) x = (L.map fun p ↦ (∂[i] (F p)) x).sum := by
  induction L with
  | nil => simp [partialDeriv]
  | cons p L ih =>
    have hL : ∀ q ∈ L, DifferentiableAt ℝ (F q) x := fun q hq ↦ hF q (by simp [hq])
    simp only [List.map_cons, List.sum_cons]
    rw [PDE.partialDeriv_add (hF p (by simp)) (differentiableAt_list_sum L hL), ih hL]

/-- Leibniz rule for iterated partial derivatives of a product of `C^∞` functions, in unfolded
form: `∂^α(fg)` is the sum over all ordered splits `(β, γ)` of the word `α` (see
`derivativeSplits`) of `∂^β f · ∂^γ g`. Equal splits are not merged, so no binomial
coefficients appear. -/
theorem iteratedPartialDeriv_mul_eq_sum_split :
    ∀ (α : List (Fin n)) (f g : ℝ^n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ x,
        iteratedPartialDeriv (n := n) α (fun y ↦ f y * g y) x =
          ((derivativeSplits (n := n) α).map (fun p ↦
            iteratedPartialDeriv (n := n) p.1 f x *
              iteratedPartialDeriv (n := n) p.2 g x)).sum := by
  intro α f g hf hg
  have hd {h : ℝ^n → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (β : List (Fin n)) (x : ℝ^n) :
      DifferentiableAt ℝ (iteratedPartialDeriv (n := n) β h) x :=
    ((PDE.contDiff_top_iteratedPartialDeriv (n := n) hh β).differentiable
      (by simp)).differentiableAt
  induction α with
  | nil => intro x; simp [derivativeSplits, iteratedPartialDeriv]
  | cons i rest ih =>
    intro x
    -- differentiate the sum for `rest` termwise, by the product rule
    change (∂[i] (fun y ↦ iteratedPartialDeriv (n := n) rest (fun z ↦ f z * g z) y)) x = _
    rw [funext ih, partialDeriv_list_sum _ fun p _ ↦ (hd hf p.1 x).mul (hd hg p.2 x)]
    simp only [derivativeSplits, List.map_append, List.map_map, Function.comp_def]
    rw [List.sum_append, add_comm, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun p _ ↦ ?_)
    rw [PDE.partialDeriv_mul (hd hf p.1 x) (hd hg p.2 x)]
    rfl

end SobolevSpace
