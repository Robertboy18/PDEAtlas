/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.SpatialJets
import PDE.Analysis.Calculus.Support.Parametric

/-!
# Uniform source bounds for Duhamel's formula

A compactly supported `C²` spacetime source has uniformly bounded spatial second derivatives. The
same constants work for every source time, including the moving endpoint of the Duhamel integral.
Evans uses such a bound on `‖D²f‖_{L^∞}` in (15) of his proof of §2.3.1(c), Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(c), proof of Theorem 2 (Solution of nonhomogeneous
  problem), (15), p. 51.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open PDE.Common

variable {n : ℕ}

/-- Compact support and `C²` regularity provide one bound for every pure second spatial
derivative, uniformly in source time. -/
theorem exists_uniform_sourceSecond_bound
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ C : Fin n → ℝ,
      ∀ (i : Fin n) (s : ℝ) (y : ℝ^n),
        |(∂[i]
          (fun z ↦
            (∂[i]
              (fun w ↦ f (timeSpaceCons (n := n) s w))) z))
          y| ≤ C i := by
  have hglobal : HasCompactSupport
      (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons p.1 p.2)) :=
    hfc.comp_homeomorph (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph
  have hsecond (i : Fin n) : HasCompactSupport
      (fun p : ℝ × ℝ^n ↦ (∂[i]
        (∂[i] (fun x ↦ f (timeSpaceCons p.1 x)))) p.2) :=
    (hglobal.fderiv_snd_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).fderiv_snd_apply
      (𝕜 := ℝ) (EuclideanSpace.single i 1)
  choose C hC using fun i ↦
    PDE.continuous_secondPartialDeriv_timeSpaceCons_spatial f hf2 i i
      |>.bounded_above_of_compact_support (hsecond i)
  exact ⟨C, fun i s y ↦ by simpa only [Real.norm_eq_abs] using hC i (s, y)⟩

end HeatEquation
