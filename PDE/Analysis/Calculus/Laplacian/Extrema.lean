/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import PDE.Analysis.Calculus.SecondDirectionalDerivative

/-!
# The Laplacian at a local extremum

At a `C²` local maximum, every directional second derivative is nonpositive.
Taking an orthonormal trace gives the sign of Mathlib's Laplacian; negation gives
the corresponding statement at a local minimum.
-/

@[expose] public noncomputable section

open scoped Laplacian

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → ℝ} {x : E}

/-- At a `C²` local maximum, Mathlib's Laplacian is nonpositive. -/
theorem IsLocalMax.laplacian_nonpos
    (hmax : IsLocalMax f x) (hf : ContDiffAt ℝ 2 f x) : Δ f x ≤ 0 := by
  classical
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_nonpos
  intro i _
  have h := PDE.Analysis.secondDirectionalDerivative_nonpos_at_localMax
    hmax hf.continuousAt ((stdOrthonormalBasis ℝ E) i)
  rw [PDE.Analysis.secondDirectionalDerivative_eq_fderiv hf] at h
  simpa [iteratedFDeriv_two_apply] using h

/-- At a `C²` local minimum, Mathlib's Laplacian is nonnegative. -/
theorem IsLocalMin.laplacian_nonneg
    (hmin : IsLocalMin f x) (hf : ContDiffAt ℝ 2 f x) : 0 ≤ Δ f x := by
  have h : Δ (-f) x ≤ 0 := hmin.neg.laplacian_nonpos hf.neg
  simpa only [InnerProductSpace.laplacian_neg, Pi.neg_apply, neg_nonpos] using h
