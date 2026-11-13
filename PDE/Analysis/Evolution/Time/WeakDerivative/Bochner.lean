/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Bochner integral tests for weak time derivatives

For Banach-valued functions, testing through the continuous dual is equivalent
to the vector-valued integration-by-parts identity. Dual separation is applied
to the integrals, without intersecting exceptional sets indexed by the dual.
The fundamental lemma then gives uniqueness of the weak derivative on an open
time domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {U : Set ℝ} {u g : ℝ → X}

/-- A weak derivative tested through the dual satisfies vector-valued
integration by parts against every compactly supported smooth scalar test. -/
theorem integral_smul_eq (hweak : HasWeakTimeDerivativeOn U u g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ U) :
    (∫ t, φ t • g t) = -(∫ t, deriv φ t • u t) := by
  have hdφ := (contDiff_infty_iff_deriv.mp hφ).2
  have hg := integrable_smul_test hweak.locallyIntegrable_g hφ.continuous hcs hsupp
  have hu := integrable_smul_test hweak.locallyIntegrable_f hdφ.continuous hcs.deriv
    (tsupport_deriv_subset.trans hsupp)
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ell
  rw [map_neg, ← ell.integral_comp_comm hg, ← ell.integral_comp_comm hu]
  simpa only [map_smul, smul_eq_mul, mul_comm] using
    hweak.integral_eq ell φ hφ hcs hsupp

/-- Two Banach-valued weak derivatives of the same trajectory agree almost
everywhere on an open time domain. -/
theorem ae_eq (hU : IsOpen U) {g₁ g₂ : ℝ → X}
    (h₁ : HasWeakTimeDerivativeOn U u g₁)
    (h₂ : HasWeakTimeDerivativeOn U u g₂) :
    g₁ =ᵐ[volume.restrict U] g₂ := by
  have hzero : HasWeakTimeDerivativeOn U (fun _ ↦ (0 : X))
      (fun t ↦ g₁ t - g₂ t) := by
    simpa only [sub_self] using h₁.sub h₂
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hzero.locallyIntegrable_g (fun φ hφ hcs hsupp ↦ by
      simpa only [smul_zero, integral_zero, neg_zero] using
        hzero.integral_smul_eq hφ hcs hsupp)
  apply (ae_restrict_iff' hU.measurableSet).2
  filter_upwards [hae] with t ht hmem
  exact sub_eq_zero.mp (ht hmem)

/-- The Bochner integration-by-parts identity on the time domain gives the
weak derivative predicate. This is the scalar-test formulation used
for Banach-valued Sobolev curves. -/
theorem of_integral_smul_eq
    (hu : LocallyIntegrableOn u U volume) (hg : LocallyIntegrableOn g U volume)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ t in U, deriv φ t • u t) = -(∫ t in U, φ t • g t)) :
    HasWeakTimeDerivativeOn U u g where
  locallyIntegrable_f := hu
  locallyIntegrable_g := hg
  integral_eq := by
    intro ell φ hφ hcs hsupp
    have hdφ := (contDiff_infty_iff_deriv.mp hφ).2
    have hgtest := integrable_smul_test hg hφ.continuous hcs hsupp
    have hutest := integrable_smul_test hu hdφ.continuous hcs.deriv
      (tsupport_deriv_subset.trans hsupp)
    have hφzero (t : ℝ) (ht : t ∉ U) : φ t = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem ↦ ht (hsupp hmem))
    have hdφzero (t : ℝ) (ht : t ∉ U) : deriv φ t = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hmem ↦ ht (hsupp (tsupport_deriv_subset hmem)))
    have hglobal := h φ hφ hcs hsupp
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht ↦ by rw [hdφzero t ht, zero_smul]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht ↦ by rw [hφzero t ht, zero_smul])]
      at hglobal
    have hdual := congrArg ell hglobal
    rw [map_neg, ← ell.integral_comp_comm hutest, ← ell.integral_comp_comm hgtest] at hdual
    have hneg := congrArg Neg.neg hdual
    simpa only [neg_neg, map_smul, smul_eq_mul, mul_comm] using hneg.symm

/-- An injective continuous linear map detects weak derivatives when both
unmapped fields are locally integrable. No bounded inverse is required. -/
theorem of_map {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (hA : Function.Injective A)
    (hu : LocallyIntegrableOn u U volume) (hg : LocallyIntegrableOn g U volume)
    (hweak : HasWeakTimeDerivativeOn U (fun t ↦ A (u t)) (fun t ↦ A (g t))) :
    HasWeakTimeDerivativeOn U u g := by
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
  apply hA
  rw [map_neg, ← A.integral_comp_comm hutest, ← A.integral_comp_comm hgtest]
  simp only [map_smul]
  simpa only [neg_neg] using congrArg Neg.neg (hweak.integral_smul_eq hφ hcs hsupp).symm

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
