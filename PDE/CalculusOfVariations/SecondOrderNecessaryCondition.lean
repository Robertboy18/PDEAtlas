/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import PDE.Analysis.Calculus.LocalExtrema
import PDE.Analysis.Calculus.SecondDirectionalDerivative

/-!
# Second-order necessary conditions

At a local minimum of a twice continuously Fréchet differentiable real-valued functional,
the second variation is nonnegative in every direction: restrict to each affine line.
Symmetry of the second Fréchet derivative then makes the Hessian a positive-semidefinite
bilinear form.

The affine-line argument is the abstract form of the derivation of the
second-variation inequality (11) in Evans, §8.1.3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.3, inequality (11).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local minimum of a `C²` real function has nonnegative second derivative. -/
theorem IsLocalMin.deriv_deriv_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hf : ContDiffAt ℝ 2 f x) :
    0 ≤ deriv (deriv f) x := by
  have h := hmin.neg.deriv_deriv_nonpos hf.continuousAt.neg
  change deriv (deriv (-f)) x ≤ 0 at h
  rw [deriv.neg'] at h
  change deriv (-(deriv f)) x ≤ 0 at h
  rw [deriv.neg] at h
  exact neg_nonpos.mp h

/-- At a local minimum of a `C²` real-valued functional, the Hessian is nonnegative on
every diagonal direction. -/
theorem IsLocalMin.fderiv_fderiv_apply_self_nonneg
    {f : E → ℝ} {u : E} (hmin : IsLocalMin f u)
    (hf : ContDiffAt ℝ 2 f u) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) u v v := by
  have h := PDE.Analysis.secondDirectionalDerivative_nonpos_at_localMax
    hmin.neg hf.continuousAt.neg v
  rw [PDE.Analysis.secondDirectionalDerivative_neg,
    PDE.Analysis.secondDirectionalDerivative_eq_fderiv hf] at h
  exact neg_nonpos.mp h

/-- At a local minimum, the Hessian of a `C²` real-valued functional defines a
positive-semidefinite bilinear form. -/
theorem IsLocalMin.isPosSemidef_fderiv_fderiv
    {f : E → ℝ} {u : E} (hmin : IsLocalMin f u)
    (hf : ContDiffAt ℝ 2 f u) :
    (fderiv ℝ (fderiv ℝ f) u).toBilinForm.IsPosSemidef := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    intro v w
    simpa using hf.isSymmSndFDerivAt (by norm_num) v w
  · exact ⟨hmin.fderiv_fderiv_apply_self_nonneg hf⟩

end
