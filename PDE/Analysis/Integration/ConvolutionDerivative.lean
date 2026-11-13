/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Coordinate derivatives of convolutions

For a locally integrable kernel `f` and a compactly supported right factor `g` on `ℝ^n`,
coordinate derivatives of the convolution `f ⋆ g` fall on `g`: `∂ᵢ (f ⋆ g) = f ⋆ ∂ᵢ g`. We
prove this for one coordinate derivative, for two, and for every finite word of coordinate
derivatives. The fundamental-solution convolution of the Poisson equation and the heat
evolution of a source term both differentiate through it. For the Poisson equation these are
the formula for `u_{x_i}` and the formula (10) for `u_{x_i x_j}` in step 1 of the proof of
Evans, §2.2.1, Theorem 1, where the kernel is the fundamental solution `Φ` and the right
factor lies in `C²_c(ℝ^n)`. The first derivative comes from Mathlib's
`HasCompactSupport.hasFDerivAt_convolution_right`.

## Main results

* `convolution_partialDeriv_right`: one coordinate derivative of `f ⋆ g` for `g ∈ C¹`.
* `convolution_iteratedPartialDeriv_two_right`: two coordinate derivatives for `g ∈ C²`.
* `convolution_iteratedPartialDeriv_right`: any word of coordinate derivatives for smooth `g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(b), Theorem 1 (Solving Poisson's equation) and
  step 1 of its proof, (9) and (10), p. 23. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory

variable {n : ℕ}

/-- A coordinate derivative of a convolution with a compactly supported
`C¹` right factor can be transferred onto that factor. -/
theorem convolution_partialDeriv_right
    (f g : ℝ^n → ℝ)
    (hf : LocallyIntegrable f volume) (hgc : HasCompactSupport g)
    (hg1 : ContDiff ℝ 1 g) (i : Fin n)
    (x : ℝ^n) :
    (∂[i] (fun y ↦ convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume y)) x =
      convolution f (fun y ↦ (∂[i] g) y)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hderiv : HasFDerivAt
      (fun q ↦ convolution f g L volume q)
      ((convolution f (fderiv ℝ g) (L.precompR (ℝ^n)) volume) x) x := by
    simpa [L] using hgc.hasFDerivAt_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℝ) hf hg1 x
  have heval :
      (∂[i] (fun q ↦ convolution f g L volume q)) x =
        (convolution f (fderiv ℝ g) (L.precompR (ℝ^n)) volume x)
          (EuclideanSpace.single i 1) := by
    unfold partialDeriv
    simpa using congrArg
      (fun A ↦ A (EuclideanSpace.single i (1 : ℝ))) hderiv.fderiv
  have hprecomp :
      (convolution f (fderiv ℝ g) (L.precompR (ℝ^n)) volume x)
          (EuclideanSpace.single i 1) =
        convolution f
          (fun z ↦ fderiv ℝ g z (EuclideanSpace.single i 1))
          L volume x := by
    simpa [L] using MeasureTheory.convolution_precompR_apply
      (L := ContinuousLinearMap.mul ℝ ℝ) hf (hgc.fderiv ℝ)
      (hg1.continuous_fderiv one_ne_zero) x
      (EuclideanSpace.single i (1 : ℝ))
  simpa [partialDeriv] using heval.trans hprecomp

/-- Every mixed second coordinate derivative of a convolution with a compactly
supported `C²` right factor can be transferred onto that factor. -/
theorem convolution_iteratedPartialDeriv_two_right
    (f g : ℝ^n → ℝ)
    (hf : LocallyIntegrable f volume) (hgc : HasCompactSupport g)
    (hg2 : ContDiff ℝ 2 g) (i j : Fin n)
    (x : ℝ^n) :
    iteratedPartialDeriv (n := n) [i, j]
        (fun y ↦ convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume y) x =
      convolution f
        (fun y ↦ iteratedPartialDeriv (n := n) [i, j] g y)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  let dg : ℝ^n → ℝ := fun y ↦ (∂[j] g) y
  have hfirst :
      (fun y ↦ (∂[j] (fun z ↦ convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume z)) y) =
        fun y ↦ convolution f dg (ContinuousLinearMap.mul ℝ ℝ) volume y := by
    funext y
    exact convolution_partialDeriv_right f g hf hgc
      (hg2.of_le (by norm_num)) j y
  have hdg_supp : HasCompactSupport dg := by
    simpa [dg, partialDeriv] using
      hgc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j (1 : ℝ))
  have hdg_diff : ContDiff ℝ 1 dg := by
    simpa [dg, partialDeriv] using
      (hg2.fderiv_right (m := 1) (n := 2) (by norm_num)).clm_apply
        (contDiff_const : ContDiff ℝ 1 fun _ : ℝ^n ↦
          EuclideanSpace.single j (1 : ℝ))
  simp only [iteratedPartialDeriv]
  rw [hfirst]
  exact convolution_partialDeriv_right f dg hf hdg_supp hdg_diff i x

/-- Every finite iterated coordinate derivative of a convolution with a
smooth compactly supported right factor can be transferred onto that factor. -/
theorem convolution_iteratedPartialDeriv_right
    (f g : ℝ^n → ℝ)
    (hf : LocallyIntegrable f volume) (hgc : HasCompactSupport g)
    (hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g) (alpha : List (Fin n))
    (x : ℝ^n) :
    iteratedPartialDeriv (n := n) alpha
        (fun y ↦ convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume y) x =
      convolution f
        (fun y ↦ iteratedPartialDeriv (n := n) alpha g y)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  have hsmooth : ∀ beta : List (Fin n),
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y ↦ iteratedPartialDeriv (n := n) beta g y) := by
    intro beta
    induction beta with
    | nil => simpa [iteratedPartialDeriv] using hgsmooth
    | cons i rest ih =>
        have hfd : ContDiff ℝ (⊤ : ℕ∞)
            (fderiv ℝ (fun y ↦ iteratedPartialDeriv (n := n) rest g y)) := by
          simpa using ih.fderiv_right
            (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
        simpa [iteratedPartialDeriv, partialDeriv] using
          hfd.clm_apply
            (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
              (fun _ : ℝ^n ↦
                EuclideanSpace.single i (1 : ℝ)))
  have hsupp : ∀ beta : List (Fin n),
      HasCompactSupport
        (fun y ↦ iteratedPartialDeriv (n := n) beta g y) := by
    intro beta
    induction beta with
    | nil => simpa [iteratedPartialDeriv] using hgc
    | cons i rest ih =>
        simpa [iteratedPartialDeriv, partialDeriv] using
          ih.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
  induction alpha generalizing x with
  | nil => simp [iteratedPartialDeriv]
  | cons i rest ih =>
      have ihfun :
          (fun y ↦ iteratedPartialDeriv (n := n) rest
            (fun z ↦ convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume z) y) =
          fun y ↦ convolution f
            (fun z ↦ iteratedPartialDeriv (n := n) rest g z)
            (ContinuousLinearMap.mul ℝ ℝ) volume y := by
        funext y
        exact ih y
      simp only [iteratedPartialDeriv]
      rw [ihfun]
      exact convolution_partialDeriv_right f
        (fun z ↦ iteratedPartialDeriv (n := n) rest g z)
        hf (hsupp rest) ((hsmooth rest).of_le (by norm_num)) i x

end PDE.Analysis
