/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Inverse.Monotone
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.AffineFan
public import PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.Profile
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.DistributionTheory.TestFunction
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# The inverse-characteristic rarefaction

For an increasing characteristic speed `e`, the middle wave is
`e.symm (x / t)`. The inverse identities give its quasilinear equation.
When `e = F′`, the flux and all compatible entropy pairs are conservative
across the continuous fan. For a uniformly convex flux, the derivative lower bound supplies
`e` and its C¹ inverse.

This is the rarefaction calculation in Evans, §3.4.4, Theorem 4(ii).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.4, Theorem 4(ii), equation (56).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Riemann

/-- The inverse-characteristic middle state is C¹ at positive time. -/
theorem contDiffAt_inverse_ratio (e : ℝ ≃o ℝ) (he : ContDiff ℝ 1 e.symm) {p : ℝ^2} (ht : p 0 ≠ 0) :
    ContDiffAt ℝ 1 (fun x : ℝ^2 ↦ e.symm (x 1 / x 0)) p := by
  have hx : ContDiffAt ℝ 1 (fun x : ℝ^2 ↦ x 1) p := by cas
  have ht' : ContDiffAt ℝ 1 (fun x : ℝ^2 ↦ x 0) p := by cas
  exact he.contDiffAt.comp p (hx.div ht' ht)

/-- The inverse identity gives the classical equation of the middle wave. -/
theorem inverse_ratio_quasilinear (e : ℝ ≃o ℝ) (he : ContDiff ℝ 1 e.symm) {p : ℝ^2} (ht : p 0 ≠ 0) :
    (∂[0] (fun x : ℝ^2 ↦ e.symm (x 1 / x 0))) p + e (e.symm (p 1 / p 0)) *
      (∂[1] (fun x : ℝ^2 ↦ e.symm (x 1 / x 0))) p = 0 := by
  have hr : DifferentiableAt ℝ (fun x : ℝ^2 ↦ x 1 / x 0) p := by
    have hx : ContDiffAt ℝ 1 (fun x : ℝ^2 ↦ x 1) p := by cas
    have ht' : ContDiffAt ℝ 1 (fun x : ℝ^2 ↦ x 0) p := by cas
    exact (hx.div ht' ht).differentiableAt_one
  have htime : (∂[0] (fun x : ℝ^2 ↦ x 1 / x 0)) p =
      -(p 1) * (p 0)⁻¹ * (p 0)⁻¹ := by cas
  have hspace : (∂[1] (fun x : ℝ^2 ↦ x 1 / x 0)) p =
      (p 0)⁻¹ := by cas
  rw [partialDeriv_comp_real 0 he.differentiable_one.differentiableAt hr,
    partialDeriv_comp_real 1 he.differentiable_one.differentiableAt hr,
    htime, hspace, e.apply_symm_apply]
  have halgebra (t x d : ℝ) :
      (-x * t⁻¹ * t⁻¹) * d + (x / t) * (t⁻¹ * d) = 0 := by cas
  exact halgebra (p 0) (p 1) (deriv e.symm (p 1 / p 0))

/-- The flux of an inverse-characteristic wave satisfies the
conservation equation wherever time is nonzero. -/
theorem inverse_ratio_conservation {F : ℝ → ℝ} (hF : Differentiable ℝ F) (e : ℝ ≃o ℝ)
    (he : ContDiff ℝ 1 e.symm) (hSpeed : ∀ r, e r = deriv F r) {p : ℝ^2} (ht : p 0 ≠ 0) :
    (∂[0] (fun x : ℝ^2 ↦ e.symm (x 1 / x 0))) p +
      (∂[1] (fun x : ℝ^2 ↦ F (e.symm (x 1 / x 0)))) p = 0 := by
  rw [partialDeriv_comp_real 1 hF.differentiableAt
    ((contDiffAt_inverse_ratio e he ht).differentiableAt_one), ← hSpeed]
  simpa only [mul_comm] using inverse_ratio_quasilinear e he ht

/-- Both endpoint identities follow from the global inverse identities. -/
theorem inverse_ratio_interface (e : ℝ ≃o ℝ) (r : ℝ) {t : ℝ} (ht : t ≠ 0) :
    e.symm ((AffineInterface.interface (e r) t) 1 / (AffineInterface.interface (e r) t) 0) = r := by
  simp [AffineInterface.interface, ht]

/-- The increasing inverse-characteristic fan is a weak conservative pair
for the flux. -/
theorem integral_inverse_ratio_affineFan_eq_zero {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (e : ℝ ≃o ℝ)
    (he : ContDiff ℝ 1 e.symm) (hSpeed : ∀ r, e r = deriv F r) (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    {uL uR : ℝ} (hLR : uL ≤ uR) :
    (∫ p : ℝ^2, AffineFan.profile (e uL) (e uR) uL (fun x ↦ e.symm (x 1 / x 0)) uR p *
      (∂[0] (φ : ℝ^2 → ℝ)) p + AffineFan.profile (e uL) (e uR) (F uL)
      (fun x ↦ F (e.symm (x 1 / x 0))) (F uR) p * (∂[1] (φ : ℝ^2 → ℝ)) p) = 0 := by
  apply AffineFan.integral_conservative_pair_profile_eq_zero φ (e uL) (e uR) (e.monotone hLR)
    (fun x ↦ e.symm (x 1 / x 0)) (fun x ↦ F (e.symm (x 1 / x 0))) uL (F uL) uR (F uR)
    (fun _ hp ↦ contDiffAt_inverse_ratio e he (ne_of_gt hp))
    (fun p hp ↦ hF.contDiffAt.comp p (contDiffAt_inverse_ratio e he (ne_of_gt hp)))
    (fun _ hp ↦ inverse_ratio_conservation hF.differentiable_one e he hSpeed (ne_of_gt hp.1))
  · exact fun t ht ↦ inverse_ratio_interface e uL (ne_of_gt ht)
  · intro t ht
    rw [inverse_ratio_interface e uL (ne_of_gt ht)]
  · exact fun t ht ↦ inverse_ratio_interface e uR (ne_of_gt ht)
  · intro t ht
    rw [inverse_ratio_interface e uR (ne_of_gt ht)]

/-- Every compatible entropy pair has zero entropy production across the
increasing inverse-characteristic fan. -/
theorem integral_entropy_inverse_ratio_affineFan_eq_zero (e : ℝ ≃o ℝ) (he : ContDiff ℝ 1 e.symm)
    {a : ℝ → ℝ} (hSpeed : ∀ r, e r = a r) (E : EntropyPair a) (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    {uL uR : ℝ} (hLR : uL ≤ uR) :
    (∫ p : ℝ^2,
      AffineFan.profile (e uL) (e uR) (E.η uL)
          (fun x ↦ E.η (e.symm (x 1 / x 0))) (E.η uR) p * (∂[0] (φ : ℝ^2 → ℝ)) p +
        AffineFan.profile (e uL) (e uR) (E.q uL)
          (fun x ↦ E.q (e.symm (x 1 / x 0))) (E.q uR) p * (∂[1] (φ : ℝ^2 → ℝ)) p) = 0 := by
  apply E.integral_affineFan_eq_zero φ (e.monotone hLR)
    (fun _ hp ↦ contDiffAt_inverse_ratio e he (ne_of_gt hp))
  · intro p hp
    rw [← hSpeed]
    exact inverse_ratio_quasilinear e he (ne_of_gt hp.1)
  · exact fun t ht ↦ inverse_ratio_interface e uL (ne_of_gt ht)
  · exact fun t ht ↦ inverse_ratio_interface e uR (ne_of_gt ht)

/-- The bounded clamped rarefaction is a weak solution at
positive time. Its flux is locally integrable without a global growth bound
on the flux. -/
theorem rarefactionProfile_isWeakSolution {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (e : ℝ ≃o ℝ)
    (he : ContDiff ℝ 1 e.symm) (hSpeed : ∀ r, e r = deriv F r) {uL uR : ℝ} (hLR : uL ≤ uR) :
    IsWeakSolution F forwardHalfSpace (rarefactionProfile e uL uR) := by
  have hu := memLp_top_rarefactionProfile e hLR volume
  refine
    { u_locallyIntegrable := (hu.locallyIntegrable le_top).locallyIntegrableOn _
      flux_locallyIntegrable :=
        ((hF.continuous.comp_memLp_top hu).locallyIntegrable le_top).locallyIntegrableOn _
      weak_eq := ?_ }
  intro φ
  calc
    (∫ p : ℝ^2, weakIntegrand F (rarefactionProfile e uL uR) φ p) = ∫ p : ℝ^2,
          AffineFan.profile (e uL) (e uR) uL (fun x ↦ e.symm (x 1 / x 0)) uR p *
              (∂[0] (φ : ℝ^2 → ℝ)) p + AffineFan.profile (e uL) (e uR) (F uL)
              (fun x ↦ F (e.symm (x 1 / x 0))) (F uR) p * (∂[1] (φ : ℝ^2 → ℝ)) p := by
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ forwardHalfSpace
      · simp only [weakIntegrand, rarefactionProfile_eq_affineFan e hLR hp, AffineFan.comp_profile]
      · simp only [weakIntegrand, φ.partialDeriv_eq_zero_of_notMem hp 0,
          φ.partialDeriv_eq_zero_of_notMem hp 1, mul_zero, add_zero]
    _ = 0 := integral_inverse_ratio_affineFan_eq_zero hF e he hSpeed φ hLR

/-- Every compatible convex C¹ entropy inequality holds for the bounded
rarefaction representative. Each tested entropy integral is in fact zero. -/
theorem rarefactionProfile_isEntropyWeakSolution {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (e : ℝ ≃o ℝ)
    (he : ContDiff ℝ 1 e.symm) (hSpeed : ∀ r, e r = deriv F r) {uL uR : ℝ} (hLR : uL ≤ uR) :
    IsEntropyWeakSolution F forwardHalfSpace (rarefactionProfile e uL uR) := by
  refine ⟨rarefactionProfile_isWeakSolution hF e he hSpeed hLR, fun E _hconv ↦ ?_⟩
  have hu := memLp_top_rarefactionProfile e hLR volume
  refine
    ⟨((E.eta_contDiff.continuous.comp_memLp_top hu).locallyIntegrable le_top).locallyIntegrableOn _,
      ((E.entropyFlux_contDiff.continuous.comp_memLp_top hu).locallyIntegrable
        le_top).locallyIntegrableOn _, ?_⟩
  intro φ _hφ
  have hzero : (∫ p : ℝ^2, entropyWeakIntegrand (rarefactionProfile e uL uR) E φ p) = 0 := by
    calc
      (∫ p : ℝ^2, entropyWeakIntegrand (rarefactionProfile e uL uR) E φ p) = ∫ p : ℝ^2,
            AffineFan.profile (e uL) (e uR) (E.η uL)
                (fun x ↦ E.η (e.symm (x 1 / x 0))) (E.η uR) p * (∂[0] (φ : ℝ^2 → ℝ)) p +
              AffineFan.profile (e uL) (e uR) (E.q uL)
                (fun x ↦ E.q (e.symm (x 1 / x 0))) (E.q uR) p * (∂[1] (φ : ℝ^2 → ℝ)) p := by
        apply integral_congr_ae
        filter_upwards [] with p
        by_cases hp : p ∈ forwardHalfSpace
        · simp only [entropyWeakIntegrand, rarefactionProfile_eq_affineFan e hLR hp,
            AffineFan.comp_profile]
        · simp only [entropyWeakIntegrand, φ.partialDeriv_eq_zero_of_notMem hp 0,
            φ.partialDeriv_eq_zero_of_notMem hp 1, mul_zero, add_zero]
      _ = 0 := integral_entropy_inverse_ratio_affineFan_eq_zero e he hSpeed E φ hLR
  exact hzero.ge

end PDE.Hyperbolic.ConservationLaw.Scalar.Riemann
