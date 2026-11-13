/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback

/-!
# Weak derivatives under scalar dilation

The Sobolev change of variables theorem applies on the whole space, with no support
or boundary assumption. For scalar dilation its matrix chain rule reduces to one
factor of the scalar in each first derivative. This is the derivative identity used
to rescale a zero-extended function.
-/

@[expose] public noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Scalar dilation preserves the first weak derivative identities of a global
finite-exponent Sobolev function. Negative factors and dimension zero are allowed. -/
theorem hasWeakDerivativeOn_comp_smul (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    {u : ℝ^n → ℝ} {du : Fin n → ℝ^n → ℝ}
    (hu : MemLp u p (domainMeasure n univ))
    (hdu : ∀ j, MemLp (du j) p (domainMeasure n univ))
    (hweak : ∀ j, HasWeakDerivativeOn univ [j] u (du j)) (i : Fin n) :
    HasWeakDerivativeOn univ [i] (fun x ↦ u (a • x))
      (fun x ↦ a * du i (a • x)) := by
  let e : ℝ^n ≃L[ℝ] ℝ^n :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  let E := e.toHomeomorph.toOpenPartialHomeomorph
  have hchain := hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
    (Approximation.standardMollifier n) hp (E := E) e.contDiff e.symm.contDiff
    hu hdu hweak i
  have hder (x : ℝ^n) : fderiv ℝ (fun y ↦ E y) x =
      a • ContinuousLinearMap.id ℝ (ℝ^n) :=
    ((hasFDerivAt_id x).const_smul a).fderiv
  simp only [hder, smul_apply, ContinuousLinearMap.id_apply,
    PiLp.smul_apply, PiLp.single_apply, smul_eq_mul] at hchain
  simpa [E, e, Finset.mul_sum, mul_comm] using hchain

end SobolevSpace.WeakChangeOfVariables
