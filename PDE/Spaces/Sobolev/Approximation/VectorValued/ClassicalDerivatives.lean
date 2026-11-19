/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder
public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
import PDE.FDeriv.Calculus

/-!
# Classical Banach-valued derivatives as weak derivatives

Continuous linear maps commute with finite words of coordinate derivatives under the
corresponding finite regularity hypothesis. Applying this identity to scalar functionals
transfers the scalar integration-by-parts theorem to arbitrary real Banach codomains.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace

/-- Continuous linear maps commute with every coordinate derivative through the available
finite classical order. -/
theorem ContinuousLinearMap.iteratedPartialDeriv_comp
    {n k : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {f : ℝ^n → E} (hf : ContDiff ℝ k f) (α : List (Fin n)) (hα : α.length ≤ k) :
    iteratedPartialDeriv α (L ∘ f) = L ∘ iteratedPartialDeriv α f := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    change ∂[i] (iteratedPartialDeriv α (L ∘ f)) =
      L ∘ (∂[i] (iteratedPartialDeriv α f))
    rw [ih (by simpa using (Nat.le_of_succ_le hα))]
    funext x
    have hlt : α.length < k := by simpa using hα
    exact L.partialDeriv_comp i
      ((PDE.contDiff_iteratedPartialDeriv_of_le hf α hlt.le).differentiable
        (by exact_mod_cast (show k - α.length ≠ 0 by omega)) x)

namespace SobolevSpace.VectorValued

variable {n k : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens ℝ^n} {f : ℝ^n → F}

/-- A globally `C^k` Banach-valued function has its classical coordinate derivatives as
weak derivatives on every open domain, through order `k`. -/
theorem hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiff
    (hf : ContDiff ℝ k f) (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn Ω α f (iteratedPartialDeriv α f) := by
  have hd : LocallyIntegrable (iteratedPartialDeriv α f) volume :=
    (PDE.contDiff_iteratedPartialDeriv_of_le hf α hα).continuous.locallyIntegrable
  apply (hasWeakDerivativeOn_iff_forall_dual
    (hf.continuous.locallyIntegrable.locallyIntegrableOn Ω)
    (hd.locallyIntegrableOn Ω)).mpr
  intro L
  have h := SobolevSpace.hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn
    Ω.isOpen (L.contDiff.comp hf).contDiffOn α hα
  rw [L.iteratedPartialDeriv_comp hf α hα] at h
  exact h

/-- Smooth Banach-valued maps have their classical derivatives as weak derivatives of
all finite orders. -/
theorem hasWeakDerivativeOn_iteratedPartialDeriv
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin n)) :
    HasWeakDerivativeOn Ω α f (iteratedPartialDeriv α f) :=
  hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiff (hf.of_le (by simp)) α le_rfl

end SobolevSpace.VectorValued
