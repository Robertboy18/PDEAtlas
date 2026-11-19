/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.Rarefaction
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.ConvexShock
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Uniqueness
public import PDE.Hyperbolic.ConservationLaw.Riemann.Trace
import PDE.Hyperbolic.ConservationLaw.Scalar.InitialBoundaryCutoff
import Mathlib.Analysis.Convex.Deriv
import CAS.ExactTactic

/-!
# The scalar Riemann initial-value problem

The compressive shock and increasing inverse-characteristic fan give an
entropy solution for every pair of states. Convexity bounds the shock speed
between the endpoint characteristics. Together with the fan edges,
this gives finite propagation and hence the strong initial trace.
The initial-boundary identity follows from the time-cutoff theorem.

For a uniformly convex flux we construct the characteristic inverse, with a
slope constant fixed before the two states. Uniqueness is in the Oleinik class.
Together these give Evans, §3.4.4, Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.4, Theorem 4, equations (54)-(56); §3.4.3(b), Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Riemann

/-- The arbitrary-jump representative satisfies the interior equation and
every compatible convex C¹ entropy inequality. -/
theorem riemannSolution_isEntropyWeakSolution {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hconv : ConvexOn ℝ univ F) (e : ℝ ≃o ℝ) (he : ContDiff ℝ 1 e.symm)
    (hSpeed : ∀ r, e r = deriv F r) (uL uR : ℝ) :
    IsEntropyWeakSolution F forwardHalfSpace (riemannSolution F e uL uR) := by
  by_cases hLR : uR < uL
  · have hRH := rankineHugoniotSpeed_satisfies (flux := F) hLR.ne
    have hs := hRH.isEntropyWeakSolution_planarShock_of_convex hLR.le
      (hconv.subset (subset_univ _) (convex_Icc uR uL)) hF
    apply (hs.mono_domain le_top).congr_ae_restrict
    filter_upwards [ae_restrict_mem forwardHalfSpace.isOpen.measurableSet] with p hp
    exact (riemannSolution_of_right_lt_left F e hLR hp).symm
  · apply (rarefactionProfile_isEntropyWeakSolution hF e he hSpeed
      (le_of_not_gt hLR)).congr_ae_restrict
    filter_upwards [ae_restrict_mem forwardHalfSpace.isOpen.measurableSet] with p hp
    exact (riemannSolution_of_left_le_right F e (le_of_not_gt hLR) hp).symm

/-- To the left of the endpoint characteristic cone the state is exactly
the left datum. The shock-speed bound comes from convexity. -/
theorem riemannSolution_eq_left_outside_cone {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    (hconv : ConvexOn ℝ univ F) (e : ℝ ≃o ℝ) (hSpeed : ∀ r, e r = deriv F r) (uL uR : ℝ) {p : ℝ^2}
    (ht : 0 < p 0) (hx : p 1 < -max |e uL| |e uR| * p 0) :
    riemannSolution F e uL uR p = uL := by
  have hL : -max |e uL| |e uR| ≤ e uL := (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
  have hR : -max |e uL| |e uR| ≤ e uR := (neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)
  by_cases hLR : uR < uL
  · rw [riemannSolution_of_right_lt_left F e hLR ht]
    apply planarShock_apply_of_mem
    have hs := deriv_right_le_rankineHugoniotSpeed hconv hLR (hF uR)
    rw [← hSpeed] at hs
    exact hx.trans_le (mul_le_mul_of_nonneg_right (hR.trans hs) ht.le)
  · rw [riemannSolution_of_left_le_right F e (le_of_not_gt hLR) ht]
    exact rarefactionProfile_eq_left e ht (hx.le.trans (mul_le_mul_of_nonneg_right hL ht.le))

/-- To the right of the endpoint characteristic cone the state is exactly
the right datum, including its boundary. -/
theorem riemannSolution_eq_right_outside_cone {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    (hconv : ConvexOn ℝ univ F) (e : ℝ ≃o ℝ) (hSpeed : ∀ r, e r = deriv F r) (uL uR : ℝ) {p : ℝ^2}
    (ht : 0 < p 0) (hx : max |e uL| |e uR| * p 0 ≤ p 1) :
    riemannSolution F e uL uR p = uR := by
  have hL : e uL ≤ max |e uL| |e uR| := (le_abs_self _).trans (le_max_left _ _)
  have hR : e uR ≤ max |e uL| |e uR| := (le_abs_self _).trans (le_max_right _ _)
  by_cases hLR : uR < uL
  · rw [riemannSolution_of_right_lt_left F e hLR ht]
    apply planarShock_apply_of_not_mem
    have hs := rankineHugoniotSpeed_le_deriv_left hconv hLR (hF uL)
    rw [← hSpeed] at hs
    exact not_lt_of_ge ((mul_le_mul_of_nonneg_right (hs.trans hL) ht.le).trans hx)
  · rw [riemannSolution_of_left_le_right F e (le_of_not_gt hLR) ht]
    exact rarefactionProfile_eq_right e (le_of_not_gt hLR) ht
      ((mul_le_mul_of_nonneg_right hR ht.le).trans hx)

/-- Finite propagation proves the strong local `L¹` trace of the
bounded representative. -/
theorem riemannSolution_hasInitialTraceLocallyL1 {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    (hconv : ConvexOn ℝ univ F) (e : ℝ ≃o ℝ) (hSpeed : ∀ r, e r = deriv F r) (uL uR : ℝ) :
    HasInitialTraceLocallyL1 (riemannSolution F e uL uR) (riemannData uL uR) :=
  hasInitialTraceLocallyL1_riemannData_of_finitePropagation (measurable_riemannSolution F e uL uR)
    (fun p _ ↦ norm_riemannSolution_le F e uL uR p)
    (fun _ ht hx ↦ riemannSolution_eq_left_outside_cone hF hconv e hSpeed uL uR ht hx)
    (fun _ ht hx ↦ riemannSolution_eq_right_outside_cone hF hconv e hSpeed uL uR ht hx)

/-- The constructed solution satisfies the initial weak identity
with its initial face. -/
theorem riemannSolution_isWeakInitialValueSolution {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hconv : ConvexOn ℝ univ F) (e : ℝ ≃o ℝ) (he : ContDiff ℝ 1 e.symm)
    (hSpeed : ∀ r, e r = deriv F r) (uL uR : ℝ) :
    IsWeakInitialValueSolution F (riemannData uL uR) (riemannSolution F e uL uR) := by
  have hi : IsWeakSolutionWithInitialTrace F (riemannData uL uR) (riemannSolution F e uL uR) :=
    ⟨(riemannSolution_isEntropyWeakSolution hF hconv e he hSpeed uL uR).weak,
      riemannSolution_hasInitialTraceLocallyL1 hF.differentiable_one hconv e hSpeed uL uR⟩
  exact hi.isWeakInitialValueSolution_of_locallyBounded hF.continuous
    (fun _ _ ↦ ⟨max ‖uL‖ ‖uR‖, fun p _ _ ↦ norm_riemannSolution_le F e uL uR p⟩)

/-- The sharp pointwise estimate implies Evans's three-variable AE
Oleinik condition with the same constant. -/
theorem hasOleinikBound_riemannSolution (F : ℝ → ℝ) (e : ℝ ≃o ℝ) {K : ℝ≥0}
    (he : LipschitzWith K e.symm) (uL uR : ℝ) :
    HasOleinikBound (riemannSolution F e uL uR) (K : ℝ) := by
  refine ⟨K.coe_nonneg, Filter.Eventually.of_forall fun p ht hz ↦ ?_⟩
  apply (riemannSolution_slope_le F e he uL uR ht p.2.1 hz.le).trans
  have halgebra (C t z : ℝ) :
      C * (1 + t⁻¹) * z = C * z / t + C * z := by cas
  rw [halgebra]
  exact le_add_of_nonneg_right (mul_nonneg K.coe_nonneg hz.le)

/-- The scalar Riemann theorem from uniform convexity, for arbitrary
left and right states. The global inverse and positive slope constant are
constructed before the states are chosen. The displayed `riemannSolution`
is the shock/fan/constant formula, with its prescribed initial value.

The final clause gives uniqueness against any bounded weak initial
solution satisfying its own AE Oleinik bound. It assumes neither a
trace nor all convex entropy inequalities of that competitor. -/
theorem exists_riemann_initial_value_solution {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hcurv : ∀ r, θ ≤ deriv (deriv F) r) :
    ∃ (e : ℝ ≃o ℝ) (C : ℝ),
      (∀ r, e r = deriv F r) ∧ C = θ⁻¹ ∧ 0 < C ∧
      ∀ uL uR : ℝ,
        IsWeakInitialValueSolution F (riemannData uL uR) (riemannSolution F e uL uR) ∧
        IsEntropyWeakSolution F forwardHalfSpace (riemannSolution F e uL uR) ∧
        HasInitialTraceLocallyL1 (riemannSolution F e uL uR) (riemannData uL uR) ∧
        Measurable (riemannSolution F e uL uR) ∧
        MemLp (riemannSolution F e uL uR) ∞ (volume.restrict forwardHalfSpace) ∧
        (∀ p, ‖riemannSolution F e uL uR p‖ ≤ max ‖uL‖ ‖uR‖) ∧
        (∀ p : ℝ^2, p 0 ≤ 0 →
          riemannSolution F e uL uR p = riemannData uL uR (p 1)) ∧
        (∀ a : ℝ, 0 < a → ∀ p,
          riemannSolution F e uL uR (a • p) = riemannSolution F e uL uR p) ∧
        (∀ t : ℝ, 0 < t → ∀ x z : ℝ, 0 ≤ z →
          riemannSolution F e uL uR !₂[t, x + z] -
            riemannSolution F e uL uR !₂[t, x] ≤ C * z / t) ∧
        HasOleinikBound (riemannSolution F e uL uR) C ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -max |deriv F uL| |deriv F uR| * p 0 →
          riemannSolution F e uL uR p = uL) ∧
        (∀ p : ℝ^2, 0 < p 0 → max |deriv F uL| |deriv F uR| * p 0 ≤ p 1 →
          riemannSolution F e uL uR p = uR) ∧
        (uR < uL → LaxShock (deriv F) uL uR (rankineHugoniotSpeed F uL uR)) ∧
        (∀ v : ℝ^2 → ℝ,
          IsWeakInitialValueSolution F (riemannData uL uR) v →
          MemLp v ∞ (volume.restrict forwardHalfSpace) →
          (∃ Cv, HasOleinikBound v Cv) →
          v =ᵐ[volume.restrict forwardHalfSpace] riemannSolution F e uL uR) := by
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  let e := PDE.Analysis.orderIsoOfDerivLowerBound hF'.differentiable_one hθ hcurv
  have he : ContDiff ℝ 1 e.symm := PDE.Analysis.contDiff_orderIsoOfDerivLowerBound_symm hF' hθ hcurv
  have hSpeed : ∀ r, e r = deriv F r := fun _ ↦ rfl
  let K : ℝ≥0 := (⟨θ, hθ.le⟩ : ℝ≥0)⁻¹
  have hLip : LipschitzWith K e.symm := PDE.Analysis.lipschitzWith_orderIsoOfDerivLowerBound_symm
      hF'.differentiable_one hθ hcurv
  have hK : (K : ℝ) = θ⁻¹ := rfl
  have hFone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hstrict : StrictConvexOn ℝ univ F := StrictMono.strictConvexOn_univ_of_deriv hF.continuous
      (fun x y hxy ↦ by simpa only [hSpeed] using e.strictMono hxy)
  have hconv : ConvexOn ℝ univ F := hstrict.convexOn
  refine ⟨e, K, hSpeed, hK, ?_, ?_⟩
  · rw [hK]
    exact inv_pos.mpr hθ
  intro uL uR
  have hi := riemannSolution_isWeakInitialValueSolution hFone hconv e he hSpeed uL uR
  have hb := memLp_top_riemannSolution F e uL uR (volume.restrict forwardHalfSpace)
  have hs := hasOleinikBound_riemannSolution F e hLip uL uR
  refine ⟨hi, riemannSolution_isEntropyWeakSolution hFone hconv e he hSpeed uL uR,
    riemannSolution_hasInitialTraceLocallyL1 hFone.differentiable_one hconv e hSpeed uL uR,
    measurable_riemannSolution F e uL uR, hb, norm_riemannSolution_le F e uL uR,
    fun _ ht ↦ riemannSolution_of_nonpos F e uL uR ht,
    fun _ ha p ↦ riemannSolution_smul_of_pos F e uL uR ha p,
    fun _ ht x _ hz ↦ riemannSolution_slope_le F e hLip uL uR ht x hz, hs, ?_, ?_, ?_, ?_⟩
  · intro p ht hx
    apply riemannSolution_eq_left_outside_cone hFone.differentiable_one hconv e hSpeed uL uR ht
    simpa only [hSpeed] using hx
  · intro p ht hx
    apply riemannSolution_eq_right_outside_cone hFone.differentiable_one hconv e hSpeed uL uR ht
    simpa only [hSpeed] using hx
  · exact fun hLR ↦ laxShock_rankineHugoniotSpeed hstrict hLR
      (hFone.differentiable_one uR) (hFone.differentiable_one uL)
  · exact fun v hv hvBdd hvSlope ↦ hv.ae_eq_of_oleinik hF hconv hi hvBdd hb hvSlope ⟨K, hs⟩

end PDE.Hyperbolic.ConservationLaw.Scalar.Riemann
