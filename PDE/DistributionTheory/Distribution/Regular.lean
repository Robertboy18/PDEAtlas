/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Regular.Directional
public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Regular distributions

Classical coordinate differentiation commutes with the regular distribution associated to
a scalar function. Densities use Mathlib's `Distribution.ofFun` directly;
local integrability identifies its action with the Bochner integral. Integration by parts
then identifies its distributional derivative. For `C¹` functions this is formula (1) of Evans,
§5.2.1, which motivates the definition (3) of weak derivatives; here `f` is only assumed
differentiable, with `f` and `∂[i] f` locally integrable.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, (1) and (3), p. 256.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped Distributions

namespace Distribution

variable {n : ℕ}

/-- Classical coordinate differentiation commutes with passage to the associated
regular distribution. -/
theorem lineDerivCLM_ofFun
    (f df : ℝ^n → ℝ)
    (hf : LocallyIntegrableOn f (⊤ : Opens (ℝ^n)) volume)
    (hdf : LocallyIntegrableOn df (⊤ : Opens (ℝ^n)) volume)
    (i : Fin n)
    (hfDiff : Differentiable ℝ f)
    (hdf_eq : ∀ x, df x = (∂[i] f) x) :
    lineDerivCLM
        (EuclideanSpace.single i (1 : ℝ)) (ofFun ⊤ f volume ⊤) =
      ofFun ⊤ df volume ⊤ := by
  have heq : df = fun x ↦ fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) := by
    funext x
    exact hdf_eq x
  subst df
  exact lineDerivCLM_ofFun_fderiv _ hfDiff hf hdf

end Distribution
