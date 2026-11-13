/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak

/-!
# Classical derivative lemmas for Sobolev density

A `C^k` function is its own weak derivative of every order up to `k`: for a derivative word
`α` of length at most `k` and every test function `φ` supported in `Ω`,

`∫ f ∂^α φ = (-1)^|α| ∫ (∂^α f) φ`,

so `∂^α f` is the weak derivative `D^α f` on `Ω` in the sense of Evans, PDE, §5.2.1. We
prove that identity by iterating one-variable integration by parts on `ℝ^n`, with the test
function supplying the compact support. It is the analytic input for the graph-space
constructors in `PDE.Spaces.Sobolev.Approximation.Density.Constructors`, which turn a smooth
function into a Sobolev element whose derivative rows are its classical derivatives.

## Main results

* `hasCompactSupport_iteratedPartialDeriv`: derivatives of a compactly supported function have
  compact support.
* `integral_by_parts_iteratedPartialDeriv_rev`: iterated integration by parts against a
  smooth compactly supported test function, for a `C^∞` function `f`. The derivative word on
  the right is reversed, since each step moves the outermost derivative across.
* `hasWeakDerivativeOn_iteratedPartialDeriv`: for `C^∞` functions, the classical derivative
  indexed by `α` is the weak derivative on every set `Ω`.
* `hasWeakDerivativeOn_iteratedPartialDeriv_finite`: the same for a `C^{|α|}` function, using
  only as many classical derivatives as the word requires.

## Implementation notes

Derivative words are lists of coordinate indices rather than multi-indices. Integration by
parts naturally produces the reversed word, and the symmetric statements are recovered from
`iteratedPartialDeriv_congr_perm_smooth` (or its finite-regularity variant), which says that
permuting a derivative word does not change the classical derivative of a sufficiently smooth
function. Integrals over `Ω` are integrals against `domainMeasure n Ω`, the restriction of
Lebesgue measure; since both integrands vanish off `Ω` when the test function does, they agree
with the integrals over all of `ℝ^n`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, (1)-(3), p. 256, for the definition of weak
  derivatives by integration by parts against test functions.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal


namespace GraphSpace

section SmoothLemmas

variable {n : ℕ}

/-- Finite-regularity iterated integration by parts. A derivative word of length `j` requires
only `C^j` regularity of the function; compact support is supplied by the test function. -/
private theorem integral_by_parts_iteratedPartialDeriv_rev_finite
    {f : ℝ^n → ℝ} (α : List (Fin n))
    (hf : ContDiff ℝ (α.length : ℕ∞) f)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ volume) =
      (-1) ^ α.length *
        (∫ x, iteratedPartialDeriv (n := n) α.reverse f x * φ.toFun x ∂ volume) := by
  induction α generalizing f with
  | nil => simp [iteratedPartialDeriv]
  | cons i rest ih =>
    simp only [List.length_cons] at hf ⊢
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ iteratedPartialDeriv (n := n) rest φ.toFun x) :=
      PDE.contDiff_top_iteratedPartialDeriv (n := n) (f := φ.toFun) φ.contDiff rest
    have hcsψ : HasCompactSupport (fun x ↦ iteratedPartialDeriv (n := n) rest φ.toFun x) :=
      hasCompactSupport_iteratedPartialDeriv (n := n) (f := φ.toFun) φ.hasCompactSupport rest
    have hdf : ContDiff ℝ rest.length (fun x ↦ (∂[i] f) x) :=
      PDE.contDiff_partialDeriv_of_succ (i := i) hf
    -- One integration by parts in the direction `eᵢ` moves `∂ᵢ` from the test function to `f`.
    have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f)
      (g := fun y ↦ iteratedPartialDeriv (n := n) rest φ.toFun y)
      (v := EuclideanSpace.single i (1 : ℝ))
      (((by simpa [partialDeriv] using hdf.continuous :
        Continuous fun x ↦ fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))).mul
          hψ.continuous).integrable_of_hasCompactSupport hcsψ.mul_left)
      ((hf.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport
          (hcsψ.fderiv_apply (𝕜 := ℝ) (v := EuclideanSpace.single i (1 : ℝ))).mul_left)
      ((hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcsψ.mul_left)
      (fun _ _ ↦ (hf.differentiable (by simp)).differentiableAt)
      (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
    have hrev (x : ℝ^n) : iteratedPartialDeriv (n := n) rest.reverse (fun y ↦ (∂[i] f) y) x =
        iteratedPartialDeriv (n := n) (i :: rest).reverse f x := by
      simp [List.reverse_cons, PDE.iteratedPartialDeriv_append_single (n := n)
        (indices := rest.reverse) (i := i) (f := f) x]
    calc (∫ x, f x * iteratedPartialDeriv (n := n) (i :: rest) φ.toFun x ∂volume)
        = -∫ x, (∂[i] f) x * iteratedPartialDeriv (n := n) rest φ.toFun x ∂volume := by
          simpa [iteratedPartialDeriv, partialDeriv, mul_comm] using hIBP
      _ = _ := by
          rw [ih (f := fun y ↦ (∂[i] f) y) hdf]
          simp [pow_succ, hrev, mul_comm]

/-- Iterated global integration by parts against a smooth compactly supported
test function.  Derivative order reverses because each new derivative is
moved from the test function onto the smooth factor. -/
theorem integral_by_parts_iteratedPartialDeriv_rev {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ α : List (Fin n), ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      (∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ volume)
        =
      (-1) ^ α.length *
        (∫ x, iteratedPartialDeriv (n := n) (α.reverse) f x * φ.toFun x ∂ volume) :=
  fun α ↦
    integral_by_parts_iteratedPartialDeriv_rev_finite α (hf.of_le (WithTop.coe_le_coe.2 le_top))

/-- A finite-order classical derivative is the corresponding weak derivative.
Only as many classical derivatives as occur in the derivative word are
required. -/
theorem hasWeakDerivativeOn_iteratedPartialDeriv_finite
    {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ} (α : List (Fin n))
    (hf : ContDiff ℝ (α.length : ℕ∞) f) :
    HasWeakDerivativeOn (n := n) Ω α f
      (fun x ↦ iteratedPartialDeriv (n := n) α f x) := by
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn Ω,
    (PDE.contDiff_iteratedPartialDeriv_of_le (n := n) hf α le_rfl).continuous
      |>.locallyIntegrable.locallyIntegrableOn Ω, fun φ hφ ↦ ?_⟩
  -- Integration by parts produces the reversed word, which has the same derivative.
  have hswap (x : ℝ^n) :
      iteratedPartialDeriv (n := n) α.reverse f x = iteratedPartialDeriv (n := n) α f x :=
    congrFun (iteratedPartialDeriv_congr_perm_of_contDiff (by simpa using hf) (by simp)) x
  rw [integral_mul_eq_global_of_tsupport_subset _ _
      ((tsupport_iteratedPartialDeriv_subset_tsupport (n := n) α φ.toFun).trans hφ),
    integral_mul_eq_global_of_tsupport_subset _ _ hφ,
    integral_by_parts_iteratedPartialDeriv_rev_finite α hf]
  simp only [hswap]

/-- For a smooth function, the classical derivative indexed by a derivative word is its weak
derivative on every domain. -/
theorem hasWeakDerivativeOn_iteratedPartialDeriv
    {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin n)) :
    HasWeakDerivativeOn (n := n) Ω α f (fun x ↦ iteratedPartialDeriv (n := n) α f x) :=
  hasWeakDerivativeOn_iteratedPartialDeriv_finite α (hf.of_le (WithTop.coe_le_coe.2 le_top))

end SmoothLemmas

end GraphSpace

end SobolevSpace
