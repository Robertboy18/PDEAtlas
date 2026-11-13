/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness of weak derivatives

A weak derivative on an open Euclidean domain is unique almost everywhere. The statement
uses only the local integrability built into
`SobolevSpace.HasWeakDerivativeOn`; no global `Lᵖ` assumption is needed.

The result is the Lemma (uniqueness of weak derivatives) of Evans §5.2.1. As in Evans's proof, we
subtract the two identities and apply Mathlib's fundamental lemma for locally integrable functions,
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, Lemma (uniqueness of weak derivatives), p. 257.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function

variable {n : ℕ}

/-- Uniqueness of weak derivatives (Evans §5.2.1, Lemma): on an open `Ω`, two weak `α`-derivatives
`g₁` and `g₂` of `f` on `Ω` agree almost everywhere on `Ω`. Local integrability is part of
`HasWeakDerivativeOn`, so no global `Lᵖ` hypothesis is needed. -/
theorem HasWeakDerivativeOn.unique_ae
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω)
    {α : List (Fin n)} {f g₁ g₂ : ℝ^n → ℝ}
    (hg₁ : HasWeakDerivativeOn (n := n) Ω α f g₁)
    (hg₂ : HasWeakDerivativeOn (n := n) Ω α f g₂) :
    g₁ =ᵐ[domainMeasure n Ω] g₂ := by
  have haez : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ Ω → g₁ x - g₂ x = 0 := by
    apply hΩopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hg₁.locallyIntegrable_g.sub hg₂.locallyIntegrable_g)
    intro ψ hψSmooth hψCs hψSupp
    let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      { toFun := ψ
        contDiff' := hψSmooth
        hasCompactSupport' := hψCs
        tsupport_subset' := Set.subset_univ _ }
    have hpairing :
        (∫ x, g₁ x * ψ x ∂domainMeasure n Ω) =
          ∫ x, g₂ x * ψ x ∂domainMeasure n Ω :=
      mul_left_cancel₀ (pow_ne_zero α.length (neg_ne_zero.mpr one_ne_zero))
        ((hg₁ φ hψSupp).symm.trans (hg₂ φ hψSupp))
    have hsupp : Function.support (fun x ↦ ψ x • (g₁ x - g₂ x)) ⊆ Ω :=
      (Function.support_smul_subset_left _ _).trans ((subset_tsupport ψ).trans hψSupp)
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by
        by_contra hne
        exact hx (hsupp hne))]
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [MeasureTheory.integral_sub
      (by simpa only [mul_comm] using hg₁.integrable_mul_testFunction φ hψSupp)
      (by simpa only [mul_comm] using hg₂.integrable_mul_testFunction φ hψSupp)]
    simpa only [sub_eq_zero, mul_comm] using hpairing
  change ∀ᵐ x ∂(volume : Measure (ℝ^n)).restrict Ω, g₁ x = g₂ x
  rw [MeasureTheory.ae_restrict_iff' hΩopen.measurableSet]
  filter_upwards [haez] with x hx hxo
  exact sub_eq_zero.mp (hx hxo)

/-- A zeroth-order weak derivative agrees almost everywhere with the original
function on an open domain. -/
theorem HasWeakDerivativeOn.nil_ae_eq
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω) {f g : ℝ^n → ℝ}
    (h : HasWeakDerivativeOn (n := n) Ω [] f g) :
    f =ᵐ[domainMeasure n Ω] g :=
  (hasWeakDerivativeOn_nil (n := n) h.locallyIntegrable_f).unique_ae hΩopen h

end SobolevSpace
