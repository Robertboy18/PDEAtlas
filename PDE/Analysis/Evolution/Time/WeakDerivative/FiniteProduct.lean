/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Bochner
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weak time derivatives in finite Hilbert products

Coordinate weak derivatives determine the weak derivative in the finite
Hilbert product. Separation is applied to the Bochner
integrals, so no dual-indexed intersection of exceptional sets is needed.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

open MeasureTheory Set
open scoped ContDiff

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)] {I : Set ℝ} {u g : ℝ → PiLp 2 E}

/-- Local integrability and the coordinate weak derivatives give the weak
derivative of a finite Hilbert-valued trajectory, including the empty product. -/
theorem of_piLp_coordinates
    (hu : LocallyIntegrableOn u I volume) (hg : LocallyIntegrableOn g I volume)
    (h : ∀ i, HasWeakTimeDerivativeOn I (fun t ↦ u t i) (fun t ↦ g t i)) :
    HasWeakTimeDerivativeOn I u g := by
  apply of_integral_smul_eq hu hg
  intro φ hφ hcs hsupp
  have hdφ := (contDiff_infty_iff_deriv.mp hφ).2
  have hgtest := integrable_smul_test hg hφ.continuous hcs hsupp
  have hutest := integrable_smul_test hu hdφ.continuous hcs.deriv
    (tsupport_deriv_subset.trans hsupp)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ by
      rw [image_eq_zero_of_notMem_tsupport
        (fun hm ↦ ht (hsupp (tsupport_deriv_subset hm))), zero_smul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun hm ↦ ht (hsupp hm)), zero_smul])]
  apply PiLp.ext
  intro i
  let P : PiLp 2 E →L[ℝ] E i := PiLp.proj 2 E i
  change P (∫ t, deriv φ t • u t) = P (-(∫ t, φ t • g t))
  rw [map_neg, ← P.integral_comp_comm hutest, ← P.integral_comp_comm hgtest]
  simpa only [map_smul, P, PiLp.proj_apply, neg_neg] using
    congrArg Neg.neg ((h i).integral_smul_eq hφ hcs hsupp).symm

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
