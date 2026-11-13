/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import PDE.Common.Euclidean
public import PDE.Notation.PartialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Coordinate Partial Derivatives

Partial derivatives are defined by applying Mathlib's total `fderiv` expression to the standard
coordinate direction. This keeps the PDE layer aligned with Mathlib's calculus API while giving
later files coordinate notation for `∂ᵢ u` and iterated partial derivatives.

Because `fderiv` is a total function, `partialDeriv i f x` is also a total expression. It should be
read as the classical partial derivative only under an accompanying differentiability hypothesis.
It is then the derivative `∂u/∂xᵢ(x)` of Evans, Appendix A, notation for derivatives (i), and the
iterated partial derivatives are the `u_{xᵢxⱼ}`, `u_{xᵢxⱼxₖ}`, ... of (iii) there.

The final section relates derivative words made of one repeated coordinate to iterates of that
coordinate derivative (`iteratedPartialDeriv_replicate`,
`iteratedPartialDeriv_replicate_append_single`, `iteratedPartialDeriv_two_after_replicate`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix A, notation for derivatives (i)-(iii), p. 701.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

variable {n : ℕ}

open PDE

noncomputable section

/-- Partial derivative expression `∂ᵢ f(x)` for a Euclidean-domain map.

This is total because it is defined using Mathlib's `fderiv`; it does not itself assert that `f` is
differentiable at `x`. -/
def PDE.partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (f : ℝ^n → E) (x : ℝ^n) : E :=
  fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))

namespace PDE.FDeriv

/-- Classical coordinate derivatives for the shared `∂[i] f` notation.

Write `∂[i] f x` or `∂[i] ∂[j] f x`.
The index belongs to `Fin n`, and the codomain can be any real normed space.
This means `fderiv ℝ f x (EuclideanSpace.single i 1)`, not the derivative of a coordinate
restriction when only that restriction is differentiable. Classical use requires
differentiability of the map being differentiated. -/
instance instPartialDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PDE.PartialDerivative n (ℝ^n → E) (ℝ^n → E) where
  partialDeriv := PDE.partialDeriv

/-- On ordinary functions, the dispatch projection is the classical coordinate derivative. -/
@[simp] theorem partialDerivative_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (f : ℝ^n → E) :
    PDE.PartialDerivative.partialDeriv i f = PDE.partialDeriv i f :=
  rfl

end PDE.FDeriv

namespace PDE

/-- A coordinate direction has unit norm, so evaluating the total Fréchet
derivative in that direction is bounded by its operator norm.
No differentiability or completeness assumption is needed. -/
theorem norm_partialDeriv_le_norm_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (f : ℝ^n → E) (x : ℝ^n) :
    ‖(∂[i] f) x‖ ≤ ‖fderiv ℝ f x‖ := by
  simpa only [partialDeriv, PiLp.norm_single, norm_one, mul_one] using
    (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i (1 : ℝ))

/-- The derivative of coordinate `j` in coordinate direction `i` is the Kronecker delta. -/
@[simp]
theorem partialDeriv_coord (i j : Fin n)
    (x : ℝ^n) :
    (∂[i] (fun y : ℝ^n ↦ y j)) x = if i = j then 1 else 0 := by
  unfold partialDeriv
  have hfd :
      fderiv ℝ (fun y : ℝ^n ↦ y j) x =
        (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ) := by
    simpa [EuclideanSpace.proj] using
      (ContinuousLinearMap.hasFDerivAt
        (f := (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ))
        (x := x)).fderiv
  rw [hfd]
  simp [EuclideanSpace.proj, eq_comm]

/-- Expand a Fréchet derivative in the Euclidean coordinate basis.

The codomain is an arbitrary real normed space, so the same formula covers scalar
advection and vector-valued transport. -/
theorem fderiv_apply_eq_sum_smul_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ^n → E) (x v : ℝ^n) :
    (fderiv ℝ f x) v =
      ∑ j : Fin n, v j • (∂[j] f) x := by
  have hv :
      v = ∑ j : Fin n, v j • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  calc
    (fderiv ℝ f x) v =
        (fderiv ℝ f x)
          (∑ j : Fin n, v j • EuclideanSpace.single j (1 : ℝ)) :=
      congrArg (fderiv ℝ f x) hv
    _ = ∑ j : Fin n,
        (fderiv ℝ f x) (v j • EuclideanSpace.single j (1 : ℝ)) := by simp
    _ = ∑ j : Fin n,
        v j • (∂[j] f) x := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp [partialDeriv]

/-- Scalar specialization of `fderiv_apply_eq_sum_smul_partialDeriv`. -/
theorem fderiv_apply_eq_sum_partialDeriv_mul
    (f : ℝ^n → ℝ) (x v : ℝ^n) :
    (fderiv ℝ f x) v =
      ∑ j : Fin n, (∂[j] f) x * v j := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [smul_eq_mul, mul_comm]

/-- The Fréchet derivative of a scalar function as a continuous linear map, reconstructed
from its coordinate derivatives and the coordinate projections. -/
theorem fderiv_eq_sum_partialDeriv_smul_proj
    (f : ℝ^n → ℝ) (x : ℝ^n) :
    fderiv ℝ f x =
      ∑ i : Fin n, (∂[i] f) x • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) := by
  ext v
  simpa using fderiv_apply_eq_sum_partialDeriv_mul f x v

/-- Taking a coordinate partial derivative of a Euclidean-valued map and then projecting to one
component agrees with differentiating that scalar component. -/
theorem partialDeriv_apply
    {m : ℕ} {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (i : Fin n) (j : Fin m) (hu : DifferentiableAt ℝ u x) :
    (∂[i] u) x j = (∂[i] (fun y ↦ u y j)) x := by
  let projection : ℝ^m →L[ℝ] ℝ :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j
  have hcomp :
      HasFDerivAt (projection ∘ u)
        (projection.comp (fderiv ℝ u x)) x :=
    projection.hasFDerivAt.comp x hu.hasFDerivAt
  have happ := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i (1 : ℝ))) hcomp.fderiv
  simpa [partialDeriv, projection, Function.comp_def,
    ContinuousLinearMap.comp_apply] using happ.symm

/-- Iterated partial derivative expression along a list of coordinate directions.

The list head is the outermost, last-applied derivative:
`iteratedPartialDeriv (i :: rest) f = partialDeriv i (iteratedPartialDeriv rest f)`.

As with `partialDeriv`, this is a total expression. Use explicit `ContDiffAt` or stronger
regularity hypotheses when the analytic existence of every displayed derivative matters. -/
def iteratedPartialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : List (Fin n)) (f : ℝ^n → E) (x : ℝ^n) : E :=
  match indices with
  | [] => f x
  | i :: rest => partialDeriv (n := n) i (fun y ↦ iteratedPartialDeriv rest f y) x

open scoped Topology in
/-- Equality of germs is preserved by any finite word of coordinate derivatives.
This concerns the total derivative expressions and needs no regularity assumption. -/
theorem _root_.Filter.EventuallyEq.iteratedPartialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E} {x : ℝ^n} (h : f =ᶠ[𝓝 x] g) (indices : List (Fin n)) :
    iteratedPartialDeriv indices f =ᶠ[𝓝 x] iteratedPartialDeriv indices g := by
  induction indices with
  | nil => exact h
  | cons i rest ih =>
      exact (ih.fderiv (𝕜 := ℝ)).mono fun y hy ↦
        congrArg (fun L : ℝ^n →L[ℝ] E ↦ L (EuclideanSpace.single i 1)) hy

/-- Concatenating derivative words is composition of the corresponding
iterated coordinate derivatives. -/
theorem iteratedPartialDeriv_append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (left right : List (Fin n)) (f : ℝ^n → E) (x : ℝ^n) :
    iteratedPartialDeriv (n := n) (left ++ right) f x =
      iteratedPartialDeriv (n := n) left
        (fun y ↦ iteratedPartialDeriv (n := n) right f y) x := by
  induction left generalizing x with
  | nil => simp [iteratedPartialDeriv]
  | cons i rest ih => simp [iteratedPartialDeriv, ih]

/-- Appending one coordinate direction differentiates the base function first
and then applies the preceding derivative word. -/
theorem iteratedPartialDeriv_append_single
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : List (Fin n)) (i : Fin n) (f : ℝ^n → E) (x : ℝ^n) :
    iteratedPartialDeriv (n := n) (indices ++ [i]) f x =
      iteratedPartialDeriv (n := n) indices (fun y ↦ (∂[i] f) y) x := by
  simpa [iteratedPartialDeriv] using
    iteratedPartialDeriv_append (n := n) indices [i] f x

/-- Repeating one coordinate direction `m` times is the `m`-fold iterate of that
coordinate derivative. -/
theorem iteratedPartialDeriv_replicate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (i : Fin n) (f : ℝ^n → E) :
    iteratedPartialDeriv (n := n) (List.replicate m i) f =
      (partialDeriv (n := n) i)^[m] f := by
  induction m with
  | zero => funext x; simp [iteratedPartialDeriv]
  | succ m ih =>
      funext x
      simp only [List.replicate_succ, iteratedPartialDeriv, Function.iterate_succ_apply']
      rw [ih]

/-- Every iterated coordinate derivative of the zero function vanishes. -/
@[simp]
theorem iteratedPartialDeriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : List (Fin n)) (x : ℝ^n) :
    iteratedPartialDeriv indices (0 : ℝ^n → E) x = 0 := by
  induction indices generalizing x with
  | nil =>
      simp [iteratedPartialDeriv]
  | cons i rest ih =>
      simp [iteratedPartialDeriv, ih, partialDeriv]

/-!
## One-dimensional coordinate bridge
-/

/-- At a point of differentiability, pulling a function on `ℝ^1` back along the canonical
identification with `ℝ` turns its sole partial derivative into the ordinary derivative. -/
theorem deriv_comp_equivOfUnique_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ^1 → E) (t : ℝ)
    (hu : DifferentiableAt ℝ u
      ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)) :
    deriv (u ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t =
      (∂[0] u)
        ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t) := by
  have he :=
    (PiLp.equivOfUnique 2 ℝ
      (fun _ : Fin 1 ↦ ℝ)).symm.toContinuousLinearMap.hasFDerivAt (x := t)
  have hcomp := hu.hasFDerivAt.comp t he
  have hone :
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm (1 : ℝ) =
        EuclideanSpace.single 0 (1 : ℝ) := by
    ext i
    fin_cases i
    simp
  rw [hcomp.hasDerivAt.deriv]
  simp [partialDeriv, hone]

/-- Partial derivative of a sum is the sum of partial derivatives. -/
theorem partialDeriv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f g : ℝ^n → E}
    {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    (∂[i] (fun y ↦ f y + g y)) x = (∂[i] f) x + (∂[i] g) x := by
  change fderiv ℝ (f + g) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_add hf hg]
  rfl

/-- Coordinate differentiation distributes over addition as an equality of functions. -/
theorem _root_.Differentiable.partialDeriv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) :
    ∂[i] (f + g) = ∂[i] f + ∂[i] g := by
  funext x
  exact PDE.partialDeriv_add (hf x) (hg x)

/-- Coordinate differentiation distributes over a finite sum of maps differentiable
at the point. The values may lie in any real normed space. -/
theorem partialDeriv_sum
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) {f : ι → ℝ^n → E} {x : ℝ^n}
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) x) (i : Fin n) :
    (∂[i] (fun y ↦ ∑ j ∈ s, f j y)) x = ∑ j ∈ s, (∂[i] (f j)) x := by
  simp only [partialDeriv, fderiv_fun_sum hf, sum_apply]

/-- A constant scalar can be pulled through a partial derivative.

Unlike the sum rule, this identity needs no differentiability hypothesis: Mathlib's total
Fréchet derivative commutes with scalar multiplication even at points where the derivative is
defined to be zero. -/
@[simp]
theorem partialDeriv_const_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) {i : Fin n} {f : ℝ^n → E} {x : ℝ^n} :
    (∂[i] (fun y ↦ c • f y)) x = c • (∂[i] f) x := by
  change fderiv ℝ (c • f) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [congrFun (fderiv_const_smul_field c) x]
  rfl

/-- The product rule for a real scalar function times a vector-valued function. -/
theorem partialDeriv_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {c : ℝ^n → ℝ} {f : ℝ^n → E} {x : ℝ^n}
    (hc : DifferentiableAt ℝ c x) (hf : DifferentiableAt ℝ f x) :
    (∂[i] (fun y ↦ c y • f y)) x =
      c x • (∂[i] f) x + (∂[i] c) x • f x := by
  change fderiv ℝ (fun y ↦ c y • f y) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_fun_smul hc hf]
  rfl

/-- The scalar–vector product rule as an equality of functions. -/
theorem _root_.Differentiable.partialDeriv_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ^n → ℝ} {f : ℝ^n → E}
    (hc : Differentiable ℝ c) (hf : Differentiable ℝ f) (i : Fin n) :
    ∂[i] (c • f) = c • ∂[i] f + ∂[i] c • f := by
  funext x
  exact PDE.partialDeriv_smul (hc x) (hf x)

/-- Partial derivative of a product under pointwise differentiability. -/
theorem partialDeriv_mul {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A]
    {i : Fin n} {f g : ℝ^n → A}
    {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    (∂[i] (fun y ↦ f y * g y)) x =
      (∂[i] f) x * g x + f x * (∂[i] g) x := by
  rw [show (fun y ↦ f y * g y) = f * g by rfl]
  have happ := congrArg (fun L ↦ L (EuclideanSpace.single i (1 : ℝ))) (fderiv_mul hf hg)
  simpa [partialDeriv, add_apply, smul_apply, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm, add_assoc, add_left_comm, add_comm] using happ

/-- Partial derivative of a negation is the negation of the partial derivative. -/
@[simp]
theorem partialDeriv_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f : ℝ^n → E}
    {x : ℝ^n} :
    (∂[i] (-f)) x = -(∂[i] f) x := by
  simpa [partialDeriv] using
    congrArg (fun L ↦ L (EuclideanSpace.single i (1 : ℝ)))
      (fderiv_neg (𝕜 := ℝ) (f := f) (x := x))

/-- `partialDeriv_neg` for a function written as `fun y ↦ -f y`. -/
theorem partialDeriv_fun_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f : ℝ^n → E}
    {x : ℝ^n} :
    (∂[i] (fun y ↦ -f y)) x = -(∂[i] f) x :=
  partialDeriv_neg

/-- Partial derivative of a difference is the difference of partial derivatives. -/
theorem partialDeriv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f g : ℝ^n → E}
    {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    (∂[i] (fun y ↦ f y - g y)) x = (∂[i] f) x - (∂[i] g) x := by
  change fderiv ℝ (f - g) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_sub hf hg]
  rfl

/-- Coordinate differentiation distributes over subtraction as an equality of functions. -/
theorem _root_.Differentiable.partialDeriv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) :
    ∂[i] (f - g) = ∂[i] f - ∂[i] g := by
  funext x
  exact PDE.partialDeriv_sub (hf x) (hg x)

/-- Partial derivative of a constant function. -/
@[simp]
theorem partialDeriv_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {x : ℝ^n} (c : E) :
    (∂[i] (fun _ : ℝ^n ↦ c)) x = 0 := by
  simp [partialDeriv]

/-- Equal Fréchet derivatives have equal values in every coordinate direction. -/
theorem partialDeriv_eq_of_fderiv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E} {x : ℝ^n}
    (h : fderiv ℝ f x = fderiv ℝ g x) (i : Fin n) :
    (∂[i] f) x = (∂[i] g) x := by
  simpa only [partialDeriv] using
    congrArg (fun D : ℝ^n →L[ℝ] E ↦ D (EuclideanSpace.single i (1 : ℝ))) h

/-! ## Second coordinate derivatives -/

/-- Differentiating the Fréchet derivative and then evaluating on two coordinate
directions gives the corresponding mixed coordinate derivative. -/
theorem secondPartialDeriv_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n) {x : ℝ^n}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    (∂[i] (∂[j] f)) x =
      fderiv ℝ (fderiv ℝ f) x
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  unfold partialDeriv
  rw [fderiv_clm_apply hf (differentiableAt_const _)]
  simp

/-- A mixed second coordinate derivative is the second Fréchet derivative evaluated on the
corresponding coordinate directions. -/
theorem secondPartialDeriv_eq_iteratedFDeriv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    (∂[i] (fun y ↦ (∂[j] f) y)) x =
      iteratedFDeriv ℝ 2 f x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)] := by
  rw [secondPartialDeriv_eq_fderiv i j
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one),
    iteratedFDeriv_two_apply]
  rfl

/-- Mixed second coordinate derivatives distribute over addition under local `C²` hypotheses. -/
theorem secondPartialDeriv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {f g : ℝ^n → E} {x : ℝ^n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (∂[i] (fun y ↦ (∂[j] (fun z ↦ f z + g z)) y)) x =
      (∂[i] (fun y ↦ (∂[j] f) y)) x +
        (∂[i] (fun y ↦ (∂[j] g) y)) x := by
  rw [secondPartialDeriv_eq_iteratedFDeriv_apply i j (hf.add hg),
    secondPartialDeriv_eq_iteratedFDeriv_apply i j hf,
    secondPartialDeriv_eq_iteratedFDeriv_apply i j hg]
  change (iteratedFDeriv ℝ 2 (f + g) x) _ = _
  rw [iteratedFDeriv_add_apply hf hg]
  rfl

/-- Mixed second coordinate derivatives distribute over subtraction under local `C²` hypotheses. -/
theorem secondPartialDeriv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {f g : ℝ^n → E} {x : ℝ^n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (∂[i] (fun y ↦ (∂[j] (fun z ↦ f z - g z)) y)) x =
      (∂[i] (fun y ↦ (∂[j] f) y)) x -
        (∂[i] (fun y ↦ (∂[j] g) y)) x := by
  rw [secondPartialDeriv_eq_iteratedFDeriv_apply i j (hf.sub hg),
    secondPartialDeriv_eq_iteratedFDeriv_apply i j hf,
    secondPartialDeriv_eq_iteratedFDeriv_apply i j hg]
  change (iteratedFDeriv ℝ 2 (f - g) x) _ = _
  rw [iteratedFDeriv_sub_apply hf hg]
  rfl

/-! ## Commutation of smooth coordinate derivatives -/

/-- Pointwise Clairaut theorem for Euclidean coordinate partials. A `C²` germ at `x` is enough;
the proof uses Mathlib's symmetry theorem for the second Fréchet derivative. -/
theorem partialDeriv_partialDeriv_comm_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    (∂[i] (fun y ↦ (∂[j] f) y)) x =
      (∂[j] (fun y ↦ (∂[i] f) y)) x := by
  rw [secondPartialDeriv_eq_iteratedFDeriv_apply i j hf,
    secondPartialDeriv_eq_iteratedFDeriv_apply j i hf]
  exact
    (hf.isSymmSndFDerivAt (by norm_num)).iteratedFDeriv_cons
      (v := EuclideanSpace.single i (1 : ℝ))
      (w := EuclideanSpace.single j (1 : ℝ))

/-- Global `C²` functions have commuting Euclidean coordinate partials. -/
theorem partialDeriv_partialDeriv_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    (hf : ContDiff ℝ 2 f) (x : ℝ^n) :
    (∂[i] (fun y ↦ (∂[j] f) y)) x =
      (∂[j] (fun y ↦ (∂[i] f) y)) x :=
  partialDeriv_partialDeriv_comm_at i j hf.contDiffAt

/-- Function-valued form of coordinate commutation for a `C²` function. -/
theorem partialDeriv_partialDeriv_comm_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    (hf : ContDiff ℝ 2 f) :
    (fun x ↦ (∂[i] (fun y ↦ (∂[j] f) y)) x) =
      fun x ↦ (∂[j] (fun y ↦ (∂[i] f) y)) x := by
  funext x
  exact partialDeriv_partialDeriv_comm i j hf x

/-- The affine line through `x` obtained by varying only coordinate `i`. -/
def coordinateLine (i : Fin n) (x : ℝ^n)
    (s : ℝ) : ℝ^n :=
  x + (s - x i) • EuclideanSpace.single i (1 : ℝ)

/-- The coordinate line through `x` returns to `x` at the parameter value `x i`. -/
@[simp]
theorem coordinateLine_self (i : Fin n) (x : ℝ^n) :
    coordinateLine i x (x i) = x := by
  simp [coordinateLine]

/-- Along the coordinate line in direction `i`, the `i`-th coordinate is the parameter itself. -/
@[simp]
theorem coordinateLine_apply_same (i : Fin n)
    (x : ℝ^n) (s : ℝ) :
    coordinateLine i x s i = s := by
  simp [coordinateLine]

/-- Varying coordinate `i` twice keeps only the second value. -/
theorem coordinateLine_coordinateLine (i : Fin n)
    (x : ℝ^n) (s u : ℝ) :
    coordinateLine i (coordinateLine i x s) u = coordinateLine i x u := by
  ext j
  by_cases h : j = i
  · subst j
    simp [coordinateLine]
  · simp [coordinateLine, h]

/-- The coordinate line has the corresponding standard basis vector as its
derivative. -/
theorem hasDerivAt_coordinateLine (i : Fin n)
    (x : ℝ^n) (s : ℝ) :
    HasDerivAt (coordinateLine i x) (EuclideanSpace.single i (1 : ℝ)) s := by
  let e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  let L : ℝ →L[ℝ] ℝ^n :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight e
  have hscalar : HasDerivAt (fun u : ℝ ↦ u - x i) 1 s :=
    (hasDerivAt_id s).sub_const (x i)
  have hlinear : HasDerivAt (fun u : ℝ ↦ L (u - x i)) (L 1) s :=
    L.hasFDerivAt.comp_hasDerivAt s hscalar
  have h := hlinear.const_add x
  have hLone : L 1 = e := by
    simp [L]
  rw [hLone] at h
  have hc : HasDerivAt (coordinateLine i x) e s := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ ?_)
    simp [coordinateLine, L, e]
  simpa only [e] using hc

/-- A coordinate line is smooth of every finite or infinite order. -/
theorem contDiff_coordinateLine (i : Fin n) (x : ℝ^n) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateLine i x) := by
  unfold coordinateLine
  fun_prop

/-- At a point of differentiability, a coordinate partial derivative is the
ordinary derivative of the restriction to the corresponding coordinate line. -/
theorem partialDeriv_eq_deriv_coordinateLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i : Fin n)
    (x : ℝ^n) (hf : DifferentiableAt ℝ f x) :
    (∂[i] f) x = deriv (f ∘ coordinateLine i x) (x i) := by
  have hfline : DifferentiableAt ℝ f (coordinateLine i x (x i)) := by
    simpa using hf
  have hcomp := hfline.hasFDerivAt.comp_hasDerivAt (x i)
    (hasDerivAt_coordinateLine i x (x i))
  rw [coordinateLine_self] at hcomp
  simpa [partialDeriv] using hcomp.deriv.symm

/-- Repeating one coordinate partial `m` times is the `m`-th Fréchet
derivative evaluated on `m` copies of the corresponding coordinate unit vector.
Unlike the block-commutation results below, this pointwise theorem needs only
local `C^m` regularity at the evaluation point. -/
theorem iterate_partialDeriv_eq_iteratedFDeriv_single
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f : ℝ^n → E}
    {x : ℝ^n} (hf : ContDiffAt ℝ m f x) :
    ((fun g y ↦ (∂[i] g) y)^[m] f) x =
      iteratedFDeriv ℝ m f x
        (fun _ : Fin m ↦ EuclideanSpace.single i (1 : ℝ)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
      let ei := EuclideanSpace.single i (1 : ℝ)
      let ev : (ℝ^n →L[ℝ] E) →L[ℝ] E :=
        (ContinuousLinearMap.apply ℝ E) ei
      have hfd : ContDiffAt ℝ m (fderiv ℝ f) x :=
        hf.fderiv_right (by norm_num)
      have hpi : ContDiffAt ℝ m
          (fun y ↦ (∂[i] f) y) x := by
        simpa [partialDeriv, ei] using hfd.clm_apply (by fun_prop)
      rw [Function.iterate_succ_apply]
      rw [ih hpi]
      have hcomp :
          iteratedFDeriv ℝ m
              (fun y ↦ (fderiv ℝ f y) ei) x =
            ev.compContinuousMultilinearMap
              (iteratedFDeriv ℝ m (fderiv ℝ f) x) := by
        simpa [ev, Function.comp_def] using
          ev.iteratedFDeriv_comp_left hfd (i := m) (by norm_num)
      have happ := congrArg (fun L ↦ L (fun _ : Fin m ↦ ei)) hcomp
      rw [iteratedFDeriv_succ_apply_right]
      change
        iteratedFDeriv ℝ m
            (fun y ↦ (fderiv ℝ f y) ei) x (fun _ : Fin m ↦ ei) =
          (iteratedFDeriv ℝ m (fderiv ℝ f) x
            (fun _ : Fin m ↦ ei)) ei
      simpa [ev, ei, partialDeriv, Function.comp_def] using happ

/-- The ordinary `m`-th derivative along a coordinate line is the `m`-th
Fréchet derivative evaluated on repeated copies of that coordinate direction.
The proof is local: it passes through an open neighborhood supplied by
`ContDiffAt`, so it remains applicable to coefficients such as `1 / r` away
from their singular set. -/
theorem iteratedDeriv_coordinateLine_eq_iteratedFDeriv_single
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f : ℝ^n → E}
    {x : ℝ^n} (hf : ContDiffAt ℝ m f x) :
    iteratedDeriv m (f ∘ coordinateLine i x) (x i) =
      iteratedFDeriv ℝ m f x
        (fun _ : Fin m ↦ EuclideanSpace.single i (1 : ℝ)) := by
  let ei := EuclideanSpace.single i (1 : ℝ)
  let L : ℝ →L[ℝ] ℝ^n :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin n ↦ ℝ) i)
  have hLval (u : ℝ) : L u = u • ei := by
    ext j
    simp [L, ei]
  let c : ℝ^n := x - L (x i)
  obtain ⟨U, hU, hfU⟩ :=
    hf.contDiffOn (le_refl (m : WithTop ℕ∞)) (by intro h; cases h)
  rcases mem_nhds_iff.1 hU with ⟨V, hVU, hVopen, hxV⟩
  let S : Set (ℝ^n) := {y | c + y ∈ V}
  have hSopen : IsOpen S :=
    hVopen.preimage (continuous_const.add continuous_id)
  have hshift : ContDiffOn ℝ m (fun y ↦ f (c + y)) S := by
    have hmap : ContDiffOn ℝ m
        (fun y : ℝ^n ↦ c + y) S := by
      fun_prop
    exact hfU.comp hmap (by intro y hy; exact hVU hy)
  have hxsplit : c + L (x i) = x := by simp [c]
  have hxS : L (x i) ∈ S := by simpa [S, hxsplit] using hxV
  have hpreopen : IsOpen (L ⁻¹' S) := hSopen.preimage L.continuous
  have hw := L.iteratedFDerivWithin_comp_right hshift hSopen.uniqueDiffOn
    hpreopen.uniqueDiffOn hxS (i := m) (by norm_num)
  rw [(iteratedFDerivWithin_of_isOpen m hpreopen) (by exact hxS),
      (iteratedFDerivWithin_of_isOpen m hSopen) hxS] at hw
  have hwapp := congrArg (fun T ↦ T (fun _ : Fin m ↦ (1 : ℝ))) hw
  have hshiftDeriv :=
    iteratedFDeriv_comp_add_left (𝕜 := ℝ) m c (L (x i)) (f := f)
  rw [hshiftDeriv, hxsplit] at hwapp
  unfold iteratedDeriv
  have hcompfun :
      (fun y ↦ f (c + y)) ∘ (L : ℝ → ℝ^n) =
        f ∘ coordinateLine i x := by
    funext s
    apply congrArg f
    dsimp [c]
    rw [hLval, hLval]
    unfold coordinateLine
    module
  rw [hcompfun] at hwapp
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hLval, ei]
    using hwapp

/-- Local bridge between repeated coordinate partials and repeated
one-variable derivatives along the associated coordinate line. -/
theorem iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f : ℝ^n → E}
    {x : ℝ^n} (hf : ContDiffAt ℝ m f x) :
    ((fun g y ↦ (∂[i] g) y)^[m] f) x =
      iteratedDeriv m (f ∘ coordinateLine i x) (x i) := by
  exact (iterate_partialDeriv_eq_iteratedFDeriv_single i m hf).trans
    (iteratedDeriv_coordinateLine_eq_iteratedFDeriv_single i m hf).symm

/-- Germ equality propagates to a repeated coordinate derivative. No regularity is
needed, since the coordinate derivatives are those of the total derivative. -/
theorem iterate_partialDeriv_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f g : ℝ^n → E}
    {x : ℝ^n} (h : f =ᶠ[nhds x] g) :
    ((fun q y ↦ (∂[i] q) y)^[m] f) =ᶠ[nhds x]
      ((fun q y ↦ (∂[i] q) y)^[m] g) := by
  have h' := h.iteratedPartialDeriv (List.replicate m i)
  rw [iteratedPartialDeriv_replicate, iteratedPartialDeriv_replicate] at h'
  exact h'

/-- Repeated coordinate partials at a point depend only on the germ of the function
there. -/
theorem iterate_partialDeriv_congr_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f g : ℝ^n → E}
    {x : ℝ^n} (h : f =ᶠ[nhds x] g) :
    ((fun q y ↦ (∂[i] q) y)^[m] f) x =
      ((fun q y ↦ (∂[i] q) y)^[m] g) x :=
  (iterate_partialDeriv_eventuallyEq i m h).eq_of_nhds

/-- Nested blocks of two coordinate derivatives at a point depend only on the germ of
the function there. -/
theorem mixed_iterate_partialDeriv_congr_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) (a b : ℕ) {f g : ℝ^n → E}
    {x : ℝ^n} (h : f =ᶠ[nhds x] g) :
    ((fun q y ↦ (∂[i] q) y)^[a]
      ((fun q y ↦ (∂[j] q) y)^[b] f)) x =
    ((fun q y ↦ (∂[i] q) y)^[a]
      ((fun q y ↦ (∂[j] q) y)^[b] g)) x :=
  iterate_partialDeriv_congr_nhds i a (iterate_partialDeriv_eventuallyEq j b h)

/-- A repeated coordinate derivative distributes over a sum under the sharp
local regularity hypotheses. -/
theorem iterate_partialDeriv_add_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f g : ℝ^n → E}
    {x : ℝ^n} (hf : ContDiffAt ℝ m f x)
    (hg : ContDiffAt ℝ m g x) :
    ((fun q y ↦ (∂[i] q) y)^[m] (fun y ↦ f y + g y)) x =
      ((fun q y ↦ (∂[i] q) y)^[m] f) x +
        ((fun q y ↦ (∂[i] q) y)^[m] g) x := by
  change ((fun q y ↦ (∂[i] q) y)^[m] (f + g)) x = _
  have hfg : ContDiffAt ℝ m (f + g) x := hf.add hg
  rw [iterate_partialDeriv_eq_iteratedFDeriv_single i m (f := f + g) hfg,
      iterate_partialDeriv_eq_iteratedFDeriv_single i m hf,
      iterate_partialDeriv_eq_iteratedFDeriv_single i m hg]
  rw [iteratedFDeriv_add_apply hf hg]
  rfl

/-- Taking `k` coordinate derivatives lowers local differentiability order by
`k`. -/
theorem contDiffAt_iterate_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (k m : ℕ) {f : ℝ^n → E}
    {x : ℝ^n} (hf : ContDiffAt ℝ (m + k) f x) :
    ContDiffAt ℝ m
      ((fun g y ↦ (∂[i] g) y)^[k] f) x := by
  induction k generalizing f with
  | zero => simpa using hf
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have hf' : ContDiffAt ℝ (m + k + 1) f x := by
        simpa [Nat.cast_add, add_assoc] using hf
      have hfd : ContDiffAt ℝ (m + k) (fderiv ℝ f) x :=
        hf'.fderiv_right (by norm_num)
      have hpi : ContDiffAt ℝ (m + k)
          (fun y ↦ (∂[i] f) y) x := by
        simpa [partialDeriv] using hfd.clm_apply (by fun_prop)
      exact ih hpi

/-- Taking `k` coordinate derivatives lowers global differentiability order by
`k`. -/
theorem contDiff_iterate_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (k m : ℕ) {f : ℝ^n → E}
    (hf : ContDiff ℝ (m + k) f) :
    ContDiff ℝ m
      ((fun g y ↦ (∂[i] g) y)^[k] f) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦
    contDiffAt_iterate_partialDeriv i k m hf.contDiffAt

/-! ## Regularity of coordinate derivatives -/

/-- A coordinate partial inherits local regularity one order below the
regularity of the original function. -/
theorem _root_.ContDiffAt.partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} {x : ℝ^n} {k r : WithTop ℕ∞}
    (hf : ContDiffAt ℝ r f x) (i : Fin n)
    (hkr : k + 1 ≤ r) : ContDiffAt ℝ k (∂[i] f) x := by
  change ContDiffAt ℝ k (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x
  exact (hf.fderiv_right hkr).clm_apply contDiffAt_const

open scoped ContDiff in
/-- Global regularity of a coordinate partial, with an explicit index and
arbitrary finite, smooth, or analytic order comparison.

The comparison proof can be omitted. An expected result type determines the
order; otherwise smooth and analytic orders are preserved, and finite orders
default to one less. In particular, `(hf.partialDeriv i).differentiable (by simp)`
infers the order when `hf` is smooth or analytic. -/
theorem _root_.ContDiff.partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} {k r : WithTop ℕ∞}
    (hf : ContDiff ℝ r f) (i : Fin n)
    (hkr : k + 1 ≤ r := by
      first
      | exact le_rfl
      | exact (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
      | exact (show (ω : WithTop ℕ∞) + 1 ≤ ω by simp)
      | exact le_of_eq (tsub_add_cancel_of_le (by simp))
      | norm_num) : ContDiff ℝ k (∂[i] f) := by
  change ContDiff ℝ k (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)))
  exact (hf.fderiv_right hkr).clm_apply contDiff_const

/-- A smooth function remains smooth after taking one coordinate partial
derivative. -/
theorem contDiff_top_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f : ℝ^n → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (∂[i] f) x) :=
  hf.partialDeriv i

/-- Taking one coordinate derivative lowers a finite differentiability order by one. -/
theorem contDiff_partialDeriv_of_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {i : Fin n} {f : ℝ^n → E}
    (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m (fun x ↦ (∂[i] f) x) :=
  hf.partialDeriv i

/-! ## Exact repeated-coordinate Leibniz rule -/

/-- A derivative word of length `j ≤ k` lowers `C^k` regularity to
`C^(k-j)`. -/
theorem contDiff_iteratedPartialDeriv_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {f : ℝ^n → E}
    (hf : ContDiff ℝ k f) (indices : List (Fin n))
    (hindices : indices.length ≤ k) :
    ContDiff ℝ ((k - indices.length : ℕ) : ℕ∞)
      (fun x ↦ iteratedPartialDeriv (n := n) indices f x) := by
  induction indices with
  | nil => simpa [iteratedPartialDeriv] using hf
  | cons i rest ih =>
      simp only [List.length_cons] at hindices ⊢
      have hrest : rest.length ≤ k := by omega
      have hr := ih hrest
      have hsub : k - rest.length = (k - (rest.length + 1)) + 1 := by omega
      have hr' : ContDiff ℝ (((k - (rest.length + 1)) + 1 : ℕ) : ℕ∞)
          (fun x ↦ iteratedPartialDeriv (n := n) rest f x) := by
        simpa [hsub] using hr
      change ContDiff ℝ ((k - (rest.length + 1) : ℕ) : ℕ∞)
        (fun x ↦ (∂[i] (fun y ↦ iteratedPartialDeriv (n := n) rest f y)) x)
      exact contDiff_partialDeriv_of_succ (i := i) hr'

/-- A smooth function remains smooth after any finite word of coordinate
partial derivatives. -/
theorem contDiff_top_iteratedPartialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (indices : List (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ iteratedPartialDeriv (n := n) indices f x) := by
  induction indices with
  | nil => simpa [iteratedPartialDeriv] using hf
  | cons i rest ih =>
      simpa [iteratedPartialDeriv] using contDiff_top_partialDeriv ih

/-- Iterated coordinate derivatives distribute over addition under the
minimal finite regularity hypothesis. -/
theorem iteratedPartialDeriv_add_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E} (indices : List (Fin n))
    (hf : ContDiff ℝ indices.length f)
    (hg : ContDiff ℝ indices.length g) :
    (fun x ↦ iteratedPartialDeriv (n := n) indices (f + g) x) =
      fun x ↦ iteratedPartialDeriv (n := n) indices f x +
        iteratedPartialDeriv (n := n) indices g x := by
  induction indices generalizing f g with
  | nil =>
      funext x
      simp [iteratedPartialDeriv]
  | cons i rest ih =>
      have hfrest : ContDiff ℝ 1
          (fun x ↦ iteratedPartialDeriv (n := n) rest f x) := by
        simpa using contDiff_iteratedPartialDeriv_of_le
          (n := n) hf rest (by simp)
      have hgrest : ContDiff ℝ 1
          (fun x ↦ iteratedPartialDeriv (n := n) rest g x) := by
        simpa using contDiff_iteratedPartialDeriv_of_le
          (n := n) hg rest (by simp)
      have hftail : ContDiff ℝ rest.length f := hf.of_le (by simp)
      have hgtail : ContDiff ℝ rest.length g := hg.of_le (by simp)
      funext x
      simp only [iteratedPartialDeriv]
      rw [ih hftail hgtail]
      exact partialDeriv_add
        (hfrest.differentiable one_ne_zero).differentiableAt
        (hgrest.differentiable one_ne_zero).differentiableAt

/-- Iterated coordinate derivatives distribute over subtraction under the
minimal finite regularity hypothesis. -/
theorem iteratedPartialDeriv_sub_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E} (indices : List (Fin n))
    (hf : ContDiff ℝ indices.length f)
    (hg : ContDiff ℝ indices.length g) :
    (fun x ↦ iteratedPartialDeriv (n := n) indices (f - g) x) =
      fun x ↦ iteratedPartialDeriv (n := n) indices f x -
        iteratedPartialDeriv (n := n) indices g x := by
  induction indices generalizing f g with
  | nil =>
      funext x
      simp [iteratedPartialDeriv]
  | cons i rest ih =>
      have hfrest : ContDiff ℝ 1
          (fun x ↦ iteratedPartialDeriv (n := n) rest f x) := by
        simpa using contDiff_iteratedPartialDeriv_of_le
          (n := n) hf rest (by simp)
      have hgrest : ContDiff ℝ 1
          (fun x ↦ iteratedPartialDeriv (n := n) rest g x) := by
        simpa using contDiff_iteratedPartialDeriv_of_le
          (n := n) hg rest (by simp)
      have hftail : ContDiff ℝ rest.length f := hf.of_le (by simp)
      have hgtail : ContDiff ℝ rest.length g := hg.of_le (by simp)
      funext x
      simp only [iteratedPartialDeriv]
      rw [ih hftail hgtail]
      exact partialDeriv_sub
        (hfrest.differentiable one_ne_zero).differentiableAt
        (hgrest.differentiable one_ne_zero).differentiableAt

/-- A constant scalar can be pulled through every iterated coordinate
derivative. This identity needs no regularity hypothesis because Mathlib's
total Fréchet derivative commutes with scalar multiplication. -/
theorem iteratedPartialDeriv_const_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (indices : List (Fin n)) (f : ℝ^n → E) :
    (fun x ↦ iteratedPartialDeriv (n := n) indices (c • f) x) =
      fun x ↦ c • iteratedPartialDeriv (n := n) indices f x := by
  induction indices with
  | nil =>
      funext x
      simp [iteratedPartialDeriv]
  | cons i rest ih =>
      funext x
      simp only [iteratedPartialDeriv]
      rw [ih]
      exact partialDeriv_const_smul c

/-- A constant scalar can be pulled through repeated differentiation in one
coordinate. This is the `Function.iterate` form of
`iteratedPartialDeriv_const_smul`. -/
theorem iterate_partialDeriv_const_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) (c : ℝ) (f : ℝ^n → E) :
    ((fun h x ↦ (∂[i] h) x)^[m] (fun x ↦ c • f x)) =
      fun x ↦ c • ((fun h x ↦ (∂[i] h) x)^[m] f) x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext x
      exact partialDeriv_const_smul c

/-- Pullback along the canonical equivalence from `ℝ` to `ℝ^1` identifies every
ordinary iterated derivative with repetition of the sole coordinate derivative. -/
theorem iteratedDeriv_comp_equivOfUnique_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (u : ℝ^1 → E) (hu : ContDiff ℝ j u) (t : ℝ) :
    iteratedDeriv j (u ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t =
      iteratedPartialDeriv (n := 1) (List.replicate j (0 : Fin 1)) u
        ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t) := by
  induction j generalizing t with
  | zero => simp [iteratedPartialDeriv]
  | succ j ih =>
      rw [show j + 1 = Nat.succ j by omega, iteratedDeriv_succ]
      have hfun :
          iteratedDeriv j
              (u ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) =
          fun s ↦ iteratedPartialDeriv (n := 1)
            (List.replicate j (0 : Fin 1)) u
              ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm s) := by
        funext s
        exact ih (hu.of_le (by norm_num)) s
      rw [hfun]
      have hg : ContDiff ℝ 1
          (fun x ↦ iteratedPartialDeriv (n := 1)
            (List.replicate j (0 : Fin 1)) u x) :=
        by
          simpa using contDiff_iteratedPartialDeriv_of_le hu
            (List.replicate j (0 : Fin 1)) (by simp)
      simpa [List.replicate_succ, iteratedPartialDeriv, Function.comp_def] using
        deriv_comp_equivOfUnique_symm
          (fun x ↦ iteratedPartialDeriv (n := 1)
            (List.replicate j (0 : Fin 1)) u x) t (hg.differentiable_one _)

/-- Smoothness is preserved after any finite number of partial derivatives in
one fixed coordinate. -/
theorem contDiff_top_iterate_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f : ℝ^n → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞)
      ((fun g x ↦ (∂[i] g) x)^[m] f) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_top_partialDeriv ih

/-- Repeated coordinate partials agree with repeated one-variable derivatives
along the affine coordinate line.  The equality is stated at every point of
the line so induction does not hide a change of base point. -/
theorem iterate_partialDeriv_coordinateLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (m : ℕ) {f : ℝ^n → E}
    (hf : ContDiff ℝ m f) (x : ℝ^n) :
    (fun s ↦ ((fun g y ↦ (∂[i] g) y)^[m] f)
        (coordinateLine i x s)) =
      (deriv^[m]) (f ∘ coordinateLine i x) := by
  funext s
  have h :=
    iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at
      i m (x := coordinateLine i x s) hf.contDiffAt
  simp only [coordinateLine_apply_same] at h
  rw [show f ∘ coordinateLine i (coordinateLine i x s) =
      f ∘ coordinateLine i x by
    funext u
    simp [coordinateLine_coordinateLine]] at h
  simpa only [iteratedDeriv_eq_iterate] using h

/-- One coordinate derivative commutes with a block of `m` derivatives in
another coordinate for a `C^(m+1)` function. -/
theorem partialDeriv_iterate_partialDeriv_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n) (m : ℕ)
    (hf : ContDiff ℝ (m + 1) f) :
    (fun g x ↦ (∂[i] g) x)
        ((fun g x ↦ (∂[j] g) x)^[m] f) =
      (fun g x ↦ (∂[j] g) x)^[m]
        ((fun x ↦ (∂[i] f) x)) := by
  let Di : (ℝ^n → E) → ℝ^n → E :=
    fun g x ↦ (∂[i] g) x
  let Dj : (ℝ^n → E) → ℝ^n → E :=
    fun g x ↦ (∂[j] g) x
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      change Di (Dj (Dj^[m] f)) = Dj^[m + 1] (Di f)
      have hswap := partialDeriv_partialDeriv_comm_of_contDiff i j
        (contDiff_iterate_partialDeriv j m 2
          (hf.of_le (by
            apply le_of_eq
            exact_mod_cast
              (show 2 + m = (m + 1) + 1 by omega))))
      change Di (Dj (Dj^[m] f)) = Dj (Di (Dj^[m] f)) at hswap
      rw [hswap]
      have hf_m : ContDiff ℝ (m + 1) f := hf.of_le (by norm_num)
      have hih := ih hf_m
      change Di (Dj^[m] f) = Dj^[m] (Di f) at hih
      rw [hih]
      exact (Function.iterate_succ_apply' Dj m (Di f)).symm

/-- Coordinate blocks of lengths `a` and `b` commute for a `C^(a+b)` function.
This is the block form needed when a PDE operator is differentiated by a mixed
multi-index. -/
theorem iterate_partialDeriv_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n) (a b : ℕ)
    (hf : ContDiff ℝ (a + b) f) :
    (fun g x ↦ (∂[i] g) x)^[a]
        ((fun g x ↦ (∂[j] g) x)^[b] f) =
      (fun g x ↦ (∂[j] g) x)^[b]
        ((fun g x ↦ (∂[i] g) x)^[a] f) := by
  let Di : (ℝ^n → E) → ℝ^n → E :=
    fun g x ↦ (∂[i] g) x
  let Dj : (ℝ^n → E) → ℝ^n → E :=
    fun g x ↦ (∂[j] g) x
  induction a generalizing f with
  | zero => rfl
  | succ a ih =>
      rw [Function.iterate_succ_apply']
      change Di (Di^[a] (Dj^[b] f)) = Dj^[b] (Di^[a + 1] f)
      have hf_ab : ContDiff ℝ (a + b) f := hf.of_le (by
        gcongr
        exact Nat.le_succ a)
      have hih := ih hf_ab
      change Di^[a] (Dj^[b] f) = Dj^[b] (Di^[a] f) at hih
      rw [hih]
      have hcomm := partialDeriv_iterate_partialDeriv_comm i j b
        (contDiff_iterate_partialDeriv i a (b + 1) (by
          simpa [add_comm, add_left_comm, add_assoc] using hf))
      change Di (Dj^[b] (Di^[a] f)) = Dj^[b] (Di (Di^[a] f)) at hcomm
      rw [hcomm]
      exact congrArg (Dj^[b]) (Function.iterate_succ_apply' Di a f).symm

/-- Coordinate product rule as an equality of functions. -/
theorem partialDeriv_mul_of_contDiff
    (i : Fin n) {f g : ℝ^n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (fun x ↦ (∂[i] (fun y ↦ f y * g y)) x) =
      fun x ↦ (∂[i] f) x * g x +
        f x * (∂[i] g) x := by
  funext x
  unfold partialDeriv
  have h := fderiv_fun_mul (c := f) (d := g) (x := x)
    ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt)
  rw [h]
  simp
  ring

/-- A coordinate derivative distributes over a finite sum of `C¹` scalar
functions. -/
theorem partialDeriv_finset_sum_of_contDiff
    (i : Fin n) {m : ℕ} (F : ℕ → ℝ^n → ℝ)
    (hF : ∀ j < m, ContDiff ℝ 1 (F j)) :
    (fun x ↦ (∂[i] (fun y ↦ Finset.sum (Finset.range m) (fun j ↦ F j y))) x) =
      fun x ↦ Finset.sum (Finset.range m)
        (fun j ↦ (∂[i] (F j)) x) := by
  funext x
  have hdiff : ∀ j ∈ Finset.range m, DifferentiableAt ℝ (F j) x := by
    intro j hj
    exact ((hF j (Finset.mem_range.1 hj)).differentiable (by simp)).differentiableAt
  simp only [partialDeriv]
  rw [fderiv_fun_sum]
  · simp
  · exact hdiff

/-- Repeated differentiation in one coordinate distributes over a fixed finite
sum of `C^m` functions. -/
theorem iterate_partialDeriv_finset_sum
    (i : Fin n) (m count : ℕ)
    (F : ℕ → ℝ^n → ℝ)
    (hF : ∀ j < count, ContDiff ℝ m (F j)) :
    ((fun h x ↦ (∂[i] h) x)^[m]
      (fun x ↦ Finset.sum (Finset.range count) (fun j ↦ F j x))) =
      fun x ↦ Finset.sum (Finset.range count) (fun j ↦
        ((fun h x ↦ (∂[i] h) x)^[m] (F j)) x) := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
      have hF_m : ∀ j < count, ContDiff ℝ m (F j) := by
        intro j hj
        exact (hF j hj).of_le (by norm_num)
      rw [Function.iterate_succ_apply', ih F hF_m]
      rw [partialDeriv_finset_sum_of_contDiff]
      · simp only [Function.iterate_succ_apply']
      · intro j hj
        exact contDiff_iterate_partialDeriv i m 1 (by
          simpa [add_comm] using hF j hj)

/-- Exact binomial Leibniz formula for repeatedly differentiating a product in
one coordinate.  The proof differentiates the finite rank-`m` sum, applies the
ordinary product rule to every row, and uses Pascal's identity to recover the
rank-`m+1` binomial coefficients. -/
theorem iterate_partialDeriv_mul
    (i : Fin n) (m : ℕ) (f g : ℝ^n → ℝ)
    (hf : ContDiff ℝ m f) (hg : ContDiff ℝ m g) :
    ((fun h x ↦ (∂[i] h) x)^[m] (fun x ↦ f x * g x)) =
      fun x ↦ Finset.sum (Finset.range (m + 1)) (fun j ↦ (m.choose j : ℝ) *
        ((fun h x ↦ (∂[i] h) x)^[j] f) x *
        ((fun h x ↦ (∂[i] h) x)^[m - j] g) x) := by
  have const_mul (c : ℝ) (h : ℝ^n → ℝ) (x : ℝ^n) :
      (∂[i] (fun y ↦ c * h y)) x =
        c * (∂[i] h) x := by
    simpa only [PDE.FDeriv.partialDerivative_eq, smul_eq_mul] using
      (partialDeriv_const_smul (n := n) (E := ℝ) c (i := i) (f := h) (x := x))
  induction m generalizing f g with
  | zero => simp
  | succ m ih =>
      have hf_m : ContDiff ℝ m f := hf.of_le (by norm_num)
      have hg_m : ContDiff ℝ m g := hg.of_le (by norm_num)
      rw [Function.iterate_succ_apply', ih f g hf_m hg_m]
      rw [partialDeriv_finset_sum_of_contDiff i]
      · funext x
        calc
          Finset.sum (Finset.range (m + 1)) (fun j ↦
              (∂[i] (fun x ↦ (m.choose j : ℝ) *
                  ((fun h x ↦ (∂[i] h) x)^[j] f) x *
                  ((fun h x ↦ (∂[i] h) x)^[m - j] g) x)) x) =
              Finset.sum (Finset.range (m + 1)) (fun j ↦
                (m.choose j : ℝ) *
                  (((fun h x ↦ (∂[i] h) x)^[j + 1] f) x *
                    ((fun h x ↦ (∂[i] h) x)^[m - j] g) x +
                   ((fun h x ↦ (∂[i] h) x)^[j] f) x *
                    ((fun h x ↦ (∂[i] h) x)^[(m - j) + 1] g) x)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjle : j ≤ m :=
              Nat.le_of_lt_succ (Finset.mem_range.1 hj)
            rw [show (fun x ↦ (m.choose j : ℝ) *
                ((fun h x ↦ (∂[i] h) x)^[j] f) x *
                ((fun h x ↦ (∂[i] h) x)^[m - j] g) x) =
              fun x ↦ (m.choose j : ℝ) *
                (((fun h x ↦ (∂[i] h) x)^[j] f) x *
                 ((fun h x ↦ (∂[i] h) x)^[m - j] g) x) by
                  funext y; ring]
            rw [const_mul]
            rw [congrFun (partialDeriv_mul_of_contDiff i
              (contDiff_iterate_partialDeriv i j 1
                (hf.of_le (by
                  exact_mod_cast
                    (show 1 + j ≤ m + 1 by omega))))
              (contDiff_iterate_partialDeriv i (m - j) 1
                (hg.of_le (by
                  exact_mod_cast
                    (show 1 + (m - j) ≤ m + 1 by omega))))) x]
            simp only [Function.iterate_succ_apply']
          _ =
              Finset.sum (Finset.range (m + 1)) (fun j ↦
                (m.choose j : ℝ) *
                  ((fun h x ↦ (∂[i] h) x)^[j] f) x *
                  ((fun h x ↦ (∂[i] h) x)^[(m + 1) - j] g) x) +
              Finset.sum (Finset.range (m + 1)) (fun j ↦
                (m.choose j : ℝ) *
                  ((fun h x ↦ (∂[i] h) x)^[j + 1] f) x *
                  ((fun h x ↦ (∂[i] h) x)^[m - j] g) x) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
            have hsub : m + 1 - j = (m - j) + 1 := by omega
            rw [hsub]
            ring
          _ = Finset.sum (Finset.range (m + 1 + 1)) (fun j ↦
              ((m + 1).choose j : ℝ) *
                ((fun h x ↦ (∂[i] h) x)^[j] f) x *
                ((fun h x ↦ (∂[i] h) x)^[(m + 1) - j] g) x) := by
            symm
            simpa [mul_assoc] using
              (Finset.sum_choose_succ_mul (R := ℝ)
                (fun p q ↦
                  ((fun h x ↦ (∂[i] h) x)^[p] f) x *
                  ((fun h x ↦ (∂[i] h) x)^[q] g) x) m)
      · intro j hj
        have hjle : j ≤ m := Nat.le_of_lt_succ hj
        simpa [smul_eq_mul, mul_assoc] using
          ContDiff.const_smul (m.choose j : ℝ)
            ((contDiff_iterate_partialDeriv i j 1
                (hf.of_le (by
                  exact_mod_cast
                    (show 1 + j ≤ m + 1 by omega)))).mul
              (contDiff_iterate_partialDeriv i (m - j) 1
                (hg.of_le (by
                  exact_mod_cast
                    (show 1 + (m - j) ≤ m + 1 by omega)))))

/-- Two successive binomial expansions give the product rule for two blocks of
coordinate derivatives. Only `C^(q+p)` regularity is required; the coordinates
need not be distinct. -/
theorem iterate_partialDeriv_iterate_partialDeriv_mul
    (r z : Fin n) (q p : ℕ) (a g : ℝ^n → ℝ)
    (ha : ContDiff ℝ ((q + p : ℕ) : WithTop ℕ∞) a)
    (hg : ContDiff ℝ ((q + p : ℕ) : WithTop ℕ∞) g) (x : ℝ^n) :
    ((fun h x ↦ (∂[r] h) x)^[q]
      ((fun h x ↦ (∂[z] h) x)^[p] (fun y ↦ a y * g y))) x =
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
        ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
          (((fun h x ↦ (∂[r] h) x)^[i]
              ((fun h x ↦ (∂[z] h) x)^[j] a)) x *
            ((fun h x ↦ (∂[r] h) x)^[q - i]
              ((fun h x ↦ (∂[z] h) x)^[p - j] g)) x) := by
  let Dr : (ℝ^n → ℝ) → ℝ^n → ℝ := fun h x ↦ (∂[r] h) x
  let Dz : (ℝ^n → ℝ) → ℝ^n → ℝ := fun h x ↦ (∂[z] h) x
  change Dr^[q] (Dz^[p] (fun y ↦ a y * g y)) x =
    ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
        (Dr^[i] (Dz^[j] a) x * Dr^[q - i] (Dz^[p - j] g) x)
  have hreg (f : ℝ^n → ℝ) (hf : ContDiff ℝ ((q + p : ℕ) : WithTop ℕ∞) f)
      (j : ℕ) (hj : j ≤ p) : ContDiff ℝ q (Dz^[j] f) := by
    apply contDiff_iterate_partialDeriv z j q
    exact hf.of_le (by exact_mod_cast (show q + j ≤ q + p by omega))
  have hterm (j : ℕ) (hj : j < p + 1) : ContDiff ℝ q
      (fun y ↦ (p.choose j : ℝ) * Dz^[j] a y * Dz^[p - j] g y) := by
    exact (contDiff_const.mul (hreg a ha j (by omega))).mul
      (hreg g hg (p - j) (by omega))
  have hap : ContDiff ℝ p a := ha.of_le (by exact_mod_cast (show p ≤ q + p by omega))
  have hgp : ContDiff ℝ p g := hg.of_le (by exact_mod_cast (show p ≤ q + p by omega))
  rw [iterate_partialDeriv_mul z p a g hap hgp]
  change Dr^[q] (fun y ↦ ∑ j ∈ Finset.range (p + 1),
    (p.choose j : ℝ) * Dz^[j] a y * Dz^[p - j] g y) x = _
  rw [iterate_partialDeriv_finset_sum r q (p + 1) _ hterm]
  change (∑ j ∈ Finset.range (p + 1),
    Dr^[q] (fun y ↦ (p.choose j : ℝ) * Dz^[j] a y * Dz^[p - j] g y) x) = _
  calc
    _ = ∑ j ∈ Finset.range (p + 1), ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) * (p.choose j : ℝ) *
          (Dr^[i] (Dz^[j] a) x * Dr^[q - i] (Dz^[p - j] g) x) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjp : j ≤ p := by have := Finset.mem_range.mp hj; omega
      have he : (fun y ↦ (p.choose j : ℝ) * Dz^[j] a y * Dz^[p - j] g y) =
          (fun y ↦ (p.choose j : ℝ) * (Dz^[j] a y * Dz^[p - j] g y)) := by
        funext y
        ring
      rw [he]
      have hs := iterate_partialDeriv_const_smul (n := n) (E := ℝ) r q
        (p.choose j : ℝ) (fun y ↦ Dz^[j] a y * Dz^[p - j] g y)
      simp only [smul_eq_mul] at hs
      rw [hs, iterate_partialDeriv_mul r q _ _
        (hreg a ha j hjp) (hreg g hg (p - j) (by omega))]
      change (p.choose j : ℝ) * (∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) * Dr^[i] (Dz^[j] a) x *
          Dr^[q - i] (Dz^[p - j] g) x) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/--
Coordinate product rule for three differentiable factors, obtained by applying
`partialDeriv_mul` twice. The corresponding first-order
distributional cutoff rule is `PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz`.
-/
theorem partialDeriv_triple_product
    {n : ℕ} (i : Fin n) {χ f g : ℝ^n → ℝ} {x : ℝ^n}
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    (∂[i] (fun y ↦ χ y * f y * g y)) x =
      (∂[i] χ) x * f x * g x +
        χ x * (∂[i] f) x * g x +
          χ x * f x * (∂[i] g) x := by
  rw [partialDeriv_mul (hχ.fun_mul hf) hg, partialDeriv_mul hχ hf]
  ring

/-- Coordinate derivative of the square of a real-valued function. -/
theorem partialDeriv_sq
    {n : ℕ} (i : Fin n) {f : ℝ^n → ℝ} {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) :
    (∂[i] (fun y ↦ f y ^ 2)) x = 2 * f x * (∂[i] f) x := by
  rw [show (fun y ↦ f y ^ 2) = (fun y ↦ f y * f y) by funext y; ring,
    partialDeriv_mul hf hf]
  ring

/-!
## Repeated coordinate blocks
-/

/-- A repeated block followed by one final coordinate derivative is the
corresponding iterate applied to that final derivative.
-/
theorem iteratedPartialDeriv_replicate_append_single
    (m : ℕ) (i j : Fin n)
    (F : ℝ^n → ℝ) :
    iteratedPartialDeriv (n := n) (List.replicate m i ++ [j]) F =
      ((fun G x ↦ (∂[i] G) x)^[m])
        (∂[j] F) := by
  funext x
  rw [iteratedPartialDeriv_append_single]
  exact congrFun (iteratedPartialDeriv_replicate m i _) x

/-- For a `C^(m+1)` function, the mixed two-derivative row applied after `m`
derivatives in coordinate `i` equals `m+1` derivatives in `i` followed by the
coordinate-`j` derivative.
-/
theorem iteratedPartialDeriv_two_after_replicate
    (m : ℕ) (i j : Fin n)
    (F : ℝ^n → ℝ)
    (hF : ContDiff ℝ (m + 1) F) :
    iteratedPartialDeriv (n := n) [i, j]
        (iteratedPartialDeriv (n := n) (List.replicate m i) F) =
      iteratedPartialDeriv (n := n) (List.replicate (m + 1) i ++ [j]) F := by
  rw [iteratedPartialDeriv_replicate m i F]
  simp only [iteratedPartialDeriv]
  change (∂[i] (∂[j] (((fun G x ↦ (∂[i] G) x)^[m]) F))) = _
  have hcomm := partialDeriv_iterate_partialDeriv_comm j i m hF
  rw [congrArg (partialDeriv (n := n) i) hcomm]
  rw [iteratedPartialDeriv_replicate_append_single (m + 1) i j F]
  simp only [Function.iterate_succ_apply']

end PDE

namespace PDE.FDeriv

public meta section

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display classical coordinate derivatives, retaining the target type of ordinary coercions.
The notation infers its operator from the input, so `↑` needs this type even when
the classical derivative would have supplied it. Function coercions `⇑` infer their own type. -/
@[delab app.PDE.partialDeriv]
def delabPartialDeriv : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  withOverApp 6 do
    let i ← withAppFn <| withAppArg delab
    let f ← withAppArg do
      let e := (← getExpr).consumeMData
      let needsType ← match e.getAppFn with
        | .const name _ => do
          let info ← Meta.getCoeFnInfo? name
          pure (info.any (fun info ↦ info.type matches .coe))
        | _ => pure false
      withTypeAscription delab (cond := needsType)
    `(∂[$i] $f)

end

end PDE.FDeriv
