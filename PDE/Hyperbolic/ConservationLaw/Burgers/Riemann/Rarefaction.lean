/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Rarefaction.BoundaryIntegrals
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import PDE.DistributionTheory.TestFunction
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.EntropyShock

/-!
# Burgers rarefaction profiles

For `uL ≤ uR` the Burgers Riemann problem is solved by the rarefaction fan
`u(t, x) = uL` for `x < uL t`, `x / t` for `uL t ≤ x ≤ uR t`, and `uR` for `x > uR t`. We
prove that the profile is a weak solution, and an entropy weak solution, of
`u_t + (u²/2)_x = 0` on the open half-space `t > 0`.

The profile is continuous on `t > 0` and `C¹` away from the two rays `x = uL t` and `x = uR t`,
where only its derivative jumps. There is no discontinuity, so the argument is not a
Rankine–Hugoniot computation: the profile is exhibited as the affine fan of
`ConservationLaw.AffineFan` with middle state `x / t`, and the fan integration theorem shows
that the boundary terms along the two rays cancel because the traces match. Every entropy
integral vanishes, so the entropy inequalities hold with equality and convexity of the entropy
is not used.

The final theorems transfer the conclusion to the unified `riemannSolution`, which differs from
the rarefaction profile only on the null hyperplane `t = 0`.

## Main results

* `rarefactionProfile_eq_affine_fan_profile`: on `t > 0` the clamped self-similar formula is
  the three-region affine fan.
* `rarefactionProfile_isWeakSolution_on_forwardHalfSpace`,
  `rarefactionProfile_isEntropyWeakSolution_on_forwardHalfSpace`: the weak and entropy
  statements for `uL ≤ uR`.
* `riemannSolution_isEntropyWeakSolution_on_forwardHalfSpace`: combined with the shock branch,
  the Burgers Riemann solution is an entropy weak solution on `t > 0` for all states.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, Example 2; §3.4.4, Theorem 4(ii), equation (56).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace BurgersEquation.Riemann

noncomputable section

open TopologicalSpace

open scoped Distributions Topology

open PDE.Hyperbolic.ConservationLaw.Scalar
open MeasureTheory
open PDE.Common
open PDE.Hyperbolic.ConservationLaw

open scoped Interval

/-- The self-similar ratio `x / t` is measurable. -/
theorem measurable_ratio : Measurable ratio := by
  change Measurable (fun x : ℝ^2 ↦ x 1 * (x 0)⁻¹)
  fun_prop

/-- A rarefaction profile is measurable: it is a clamped self-similar ratio. -/
theorem measurable_rarefactionProfile (uL uR : ℝ) :
    Measurable (rarefactionProfile uL uR) := by
  change Measurable
    (fun x : ℝ^2 ↦ if ratio x < uL then uL else if uR < ratio x then uR else ratio x)
  exact Measurable.ite (measurableSet_lt measurable_ratio measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_ratio) measurable_const
      measurable_ratio)

/-! ### Rarefaction profile is a weak solution on `{t>0}` -/

private theorem rarefactionProfile_eq_uL_of_mem_left {uL uR : ℝ} {x : ℝ^2} (hx0 : 0 < x 0)
    (hx : x 1 < uL * x 0) :
    rarefactionProfile uL uR x = uL := by
  -- `x 1 < uL * x 0` means `ratio x < uL` when `t > 0`
  have hx0' : x 0 ≠ 0 := ne_of_gt hx0
  have hratio : ratio x < uL := by
    -- divide by `x 0 > 0`
    have : x 1 * (x 0)⁻¹ < uL * x 0 * (x 0)⁻¹ := by
      simpa [ratio, mul_assoc] using (mul_lt_mul_of_pos_right hx (inv_pos.2 hx0))
    change x 1 * (x 0)⁻¹ < uL
    simpa [mul_assoc, hx0', mul_inv_cancel] using this
  simp [rarefactionProfile, hratio]

private theorem rarefactionProfile_eq_uR_of_not_mem_left {uL uR : ℝ} (h : uL ≤ uR) {x : ℝ^2}
    (hx0 : 0 < x 0) (hx : ¬ x 1 < uR * x 0) :
    rarefactionProfile uL uR x = uR := by
  have hx0' : x 0 ≠ 0 := ne_of_gt hx0
  have hratio_ge : uR ≤ ratio x := by
    -- `¬ x < uR*t` means `uR ≤ x/t` for `t>0`
    have hx' : uR * x 0 ≤ x 1 := le_of_not_gt hx
    have : uR * x 0 * (x 0)⁻¹ ≤ x 1 * (x 0)⁻¹ :=
      mul_le_mul_of_nonneg_right hx' (inv_nonneg.2 (le_of_lt hx0))
    simpa [ratio, mul_assoc, hx0', mul_inv_cancel, mul_left_comm, mul_comm] using this
  have hratio_not_lt_uL : ¬ ratio x < uL := not_lt_of_ge (le_trans h hratio_ge)
  change (if ratio x < uL then uL else if uR < ratio x then uR else ratio x) = uR
  rw [ite_eq_right hratio_not_lt_uL]
  by_cases hr : uR < ratio x
  · rw [ite_eq_left hr]
  · have hr' : ratio x = uR := le_antisymm (le_of_not_gt hr) hratio_ge
    rw [ite_eq_right hr, hr']

private theorem rarefactionProfile_eq_ratio_of_mem_fan {uL uR : ℝ} {x : ℝ^2} (hx0 : 0 < x 0)
    (hL : ¬ x 1 < uL * x 0) (hR : x 1 < uR * x 0) :
    rarefactionProfile uL uR x = ratio x := by
  have hx0' : x 0 ≠ 0 := ne_of_gt hx0
  have hratio_ge : uL ≤ ratio x := by
    have hx' : uL * x 0 ≤ x 1 := le_of_not_gt hL
    have : uL * x 0 * (x 0)⁻¹ ≤ x 1 * (x 0)⁻¹ :=
      mul_le_mul_of_nonneg_right hx' (inv_nonneg.2 (le_of_lt hx0))
    simpa [ratio, mul_assoc, hx0', mul_inv_cancel, mul_left_comm, mul_comm] using this
  have hratio_lt : ratio x < uR := by
    have : x 1 * (x 0)⁻¹ < uR * x 0 * (x 0)⁻¹ :=
      by simpa [ratio, mul_assoc] using (mul_lt_mul_of_pos_right hR (inv_pos.2 hx0))
    change x 1 * (x 0)⁻¹ < uR
    simpa [mul_assoc, hx0', mul_inv_cancel] using this
  have hratio_not_lt_uL : ¬ ratio x < uL := not_lt_of_ge hratio_ge
  have hratio_not_uR_lt : ¬ uR < ratio x := not_lt_of_ge (le_of_lt hratio_lt)
  simp [rarefactionProfile, hratio_not_lt_uL, hratio_not_uR_lt]

/-- An ordered rarefaction profile takes values in the closed interval between its end states. -/
private theorem rarefactionProfile_mem_Icc {uL uR : ℝ} (h : uL ≤ uR) (x : ℝ^2) :
    rarefactionProfile uL uR x ∈ Set.Icc uL uR := by
  by_cases hL : ratio x < uL
  · simp [rarefactionProfile, hL, h]
  · by_cases hR : uR < ratio x
    · simp [rarefactionProfile, hL, hR, h]
    · simpa [rarefactionProfile, hL, hR] using
        (show uL ≤ ratio x ∧ ratio x ≤ uR from ⟨le_of_not_gt hL, le_of_not_gt hR⟩)

private theorem rarefactionProfile_locallyIntegrable (uL uR : ℝ) :
    LocallyIntegrable (rarefactionProfile uL uR) volume := by
  let C : ℝ := max ‖uL‖ ‖uR‖
  exact locallyIntegrable_of_measurable_norm_le_const (measurable_rarefactionProfile uL uR)
    ((norm_nonneg uL).trans (le_max_left ‖uL‖ ‖uR‖)) norm_rarefactionProfile_le

/-- A continuous scalar function of an ordered rarefaction profile is locally integrable.
Compactness of the interval `[uL, uR]` supplies the required uniform bound. -/
private theorem rarefactionComposition_locallyIntegrable
    {uL uR : ℝ} (h : uL ≤ uR) (g : ℝ → ℝ) (hg : Continuous g) :
    LocallyIntegrable (fun x : ℝ^2 ↦ g (rarefactionProfile uL uR x)) volume := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc uL uR) hg.continuousOn
  have hC_nonneg : 0 ≤ C := (norm_nonneg (g uL)).trans (hC uL ⟨le_rfl, h⟩)
  apply locallyIntegrable_of_measurable_norm_le_const
      (hg.measurable.comp (measurable_rarefactionProfile uL uR)) hC_nonneg
  exact fun x ↦ hC (rarefactionProfile uL uR x) (rarefactionProfile_mem_Icc h x)

private theorem rarefactionFlux_locallyIntegrable (uL uR : ℝ) :
    LocallyIntegrable (fun x : ℝ^2 ↦ flux (rarefactionProfile uL uR x)) volume := by
  let M : ℝ := max ‖uL‖ ‖uR‖
  let C : ℝ := M ^ 2 / 2
  have hM : 0 ≤ M := (norm_nonneg uL).trans (le_max_left ‖uL‖ ‖uR‖)
  have hC : 0 ≤ C := div_nonneg (sq_nonneg M) (by norm_num)
  have hmeas : Measurable (fun x : ℝ^2 ↦ flux (rarefactionProfile uL uR x)) := by
    have hflux : Measurable flux := by
      unfold flux
      fun_prop
    exact hflux.comp (measurable_rarefactionProfile uL uR)
  refine locallyIntegrable_of_measurable_norm_le_const hmeas hC fun x ↦ ?_
  have hu : |rarefactionProfile uL uR x| ≤ M := by
    simpa [M, Real.norm_eq_abs] using norm_rarefactionProfile_le (uL := uL) (uR := uR) x
  have hpow : |rarefactionProfile uL uR x| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
  have hpow' : rarefactionProfile uL uR x ^ 2 ≤ M ^ 2 := by
    simpa using hpow
  rw [Real.norm_eq_abs]
  unfold flux
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
  simpa [C] using div_le_div_of_nonneg_right hpow' (by norm_num : (0 : ℝ) ≤ 2)

/-- On positive time, the clamped self-similar formula is the corresponding
three-region affine fan. -/
theorem rarefactionProfile_eq_affine_fan_profile {uL uR : ℝ} (h : uL ≤ uR) {x : ℝ^2}
    (hx : x ∈ forwardHalfSpace) :
    rarefactionProfile uL uR x = AffineFan.profile uL uR uL ratio uR x := by
  by_cases hleft : x ∈ AffineInterface.leftHalfSpace uL
  · rw [AffineFan.profile_eq_left hleft]
    exact rarefactionProfile_eq_uL_of_mem_left hx hleft
  · by_cases hright : x ∈ AffineInterface.leftHalfSpace uR
    · rw [AffineFan.profile_eq_middle hleft hright]
      exact rarefactionProfile_eq_ratio_of_mem_fan hx hleft hright
    · rw [AffineFan.profile_eq_right hleft hright]
      exact rarefactionProfile_eq_uR_of_not_mem_left h hx hright

/-- The increasing Burgers rarefaction profile is a weak solution on positive
time. -/
theorem rarefactionProfile_isWeakSolution_on_forwardHalfSpace {uL uR : ℝ} (h : uL ≤ uR) :
    PDE.Hyperbolic.ConservationLaw.Scalar.IsWeakSolution flux forwardHalfSpace
      (rarefactionProfile uL uR) := by
  refine
    { u_locallyIntegrable := (rarefactionProfile_locallyIntegrable uL uR).locallyIntegrableOn
          forwardHalfSpace
      flux_locallyIntegrable := (rarefactionFlux_locallyIntegrable uL uR).locallyIntegrableOn
          forwardHalfSpace
      weak_eq := ?_ }
  intro φ
  calc
    (∫ x : ℝ^2, PDE.Hyperbolic.ConservationLaw.Scalar.weakIntegrand flux
          (rarefactionProfile uL uR) φ x ∂volume) = ∫ x : ℝ^2,
          (AffineFan.profile uL uR uL ratio uR x * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x +
            AffineFan.profile uL uR (flux uL) (fun p : ℝ^2 ↦ flux (ratio p)) (flux uR) x *
              (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x) ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ forwardHalfSpace
        · have hprofile := rarefactionProfile_eq_affine_fan_profile h hx
          simp only [PDE.Hyperbolic.ConservationLaw.Scalar.weakIntegrand, hprofile,
            AffineFan.comp_profile]
        · have htime : (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x = 0 :=
            φ.partialDeriv_eq_zero_of_notMem hx (0 : Fin 2)
          have hspace : (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x = 0 :=
            φ.partialDeriv_eq_zero_of_notMem hx (1 : Fin 2)
          simp [PDE.Hyperbolic.ConservationLaw.Scalar.weakIntegrand, htime, hspace]
    _ = 0 := integral_ratio_affine_fan_eq_zero φ h

/-- The increasing Burgers rarefaction profile satisfies every convex entropy
inequality on positive time; in fact, each entropy integral vanishes. -/
theorem rarefactionProfile_isEntropyWeakSolution_on_forwardHalfSpace {uL uR : ℝ} (h : uL ≤ uR) :
    _root_.PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropyWeakSolution flux forwardHalfSpace
      (rarefactionProfile uL uR) := by
  refine ⟨rarefactionProfile_isWeakSolution_on_forwardHalfSpace h, ?_⟩
  intro E _hconv
  refine ⟨(rarefactionComposition_locallyIntegrable h E.η
        E.eta_contDiff.continuous).locallyIntegrableOn forwardHalfSpace,
      (rarefactionComposition_locallyIntegrable h E.q
        E.entropyFlux_contDiff.continuous).locallyIntegrableOn forwardHalfSpace, ?_⟩
  intro φ _hφ_nonneg
  have hzero : (∫ x : ℝ^2, PDE.Hyperbolic.ConservationLaw.Scalar.entropyWeakIntegrand
            (rarefactionProfile uL uR) E φ x ∂volume) = 0 := by
    calc
      (∫ x : ℝ^2, PDE.Hyperbolic.ConservationLaw.Scalar.entropyWeakIntegrand
            (rarefactionProfile uL uR) E φ x ∂volume) = ∫ x : ℝ^2, (AffineFan.profile uL uR (E.η uL)
                (fun p : ℝ^2 ↦ E.η (ratio p)) (E.η uR) x * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x +
              AffineFan.profile uL uR (E.q uL) (fun p : ℝ^2 ↦ E.q (ratio p)) (E.q uR) x *
                (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x)
              ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          by_cases hx : x ∈ forwardHalfSpace
          · have hprofile := rarefactionProfile_eq_affine_fan_profile h hx
            simp only [PDE.Hyperbolic.ConservationLaw.Scalar.entropyWeakIntegrand, hprofile,
              AffineFan.comp_profile]
          · have htime : (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x = 0 :=
              φ.partialDeriv_eq_zero_of_notMem hx (0 : Fin 2)
            have hspace : (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x = 0 :=
              φ.partialDeriv_eq_zero_of_notMem hx (1 : Fin 2)
            simp [PDE.Hyperbolic.ConservationLaw.Scalar.entropyWeakIntegrand, htime, hspace]
      _ = 0 := integral_entropy_ratio_affine_fan_eq_zero φ E h
  simp [hzero]

/-- On the nondecreasing branch, the assigned time-zero datum changes the
rarefaction profile only on the null hyperplane `t = 0`. -/
theorem riemannSolution_ae_eq_rarefactionProfile_of_not_lt {uL uR : ℝ} (h : ¬ uR < uL) :
    riemannSolution uL uR =ᵐ[volume] rarefactionProfile uL uR := by
  have htime : ∀ᵐ x : ℝ^2 ∂volume, x 0 ≠ 0 := by
    let timeLinear : ℝ^2 →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 2)).toLinearMap
    have hker : LinearMap.ker timeLinear ≠ ⊤ := by
      intro htop
      have hmem : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈
            LinearMap.ker timeLinear := by
        rw [htop]
        exact Submodule.mem_top
      simp [timeLinear, EuclideanSpace.proj] at hmem
    have hset :
        {x : ℝ^2 | x 0 = 0} = (LinearMap.ker timeLinear : Set ℝ^2) := by
      ext x
      simp [timeLinear, EuclideanSpace.proj]
    have hzero : volume {x : ℝ^2 | x 0 = 0} = 0 := by
      rw [hset]
      exact Measure.addHaar_submodule volume (LinearMap.ker timeLinear) hker
    have hcompl : {x : ℝ^2 | x 0 = 0}ᶜ ∈ ae volume := compl_mem_ae_iff.2 hzero
    filter_upwards [hcompl] with x hx
    simpa using hx
  filter_upwards [htime] with x hx using riemannSolution_apply_of_not_lt_of_time_ne_zero h hx

/-- The unified Riemann solution is a weak Burgers solution on `t > 0` for all states. On the
nondecreasing branch `uL ≤ uR` it agrees with the rarefaction profile almost everywhere, and the
weak formulation is insensitive to such changes; the shock branch is
`riemannSolution_isWeakSolution_of_lt`. -/
theorem riemannSolution_isWeakSolution_of_not_lt {uL uR : ℝ} :
    PDE.Hyperbolic.ConservationLaw.Scalar.IsWeakSolution
      flux forwardHalfSpace (riemannSolution uL uR) := by
  by_cases h : uR < uL
  · exact (riemannSolution_isWeakSolution_of_lt h).mono_domain
      (show forwardHalfSpace ≤ (⊤ : Opens ℝ^2) from le_top)
  have hle : uL ≤ uR := le_of_not_gt h
  exact (rarefactionProfile_isWeakSolution_on_forwardHalfSpace (uL := uL) (uR := uR) hle).congr_ae
      (riemannSolution_ae_eq_rarefactionProfile_of_not_lt h).symm

/-- On the nondecreasing branch the unified Riemann solution is an entropy weak solution on
`t > 0`, again by almost-everywhere agreement with the rarefaction profile. -/
theorem riemannSolution_isEntropyWeakSolution_of_not_lt {uL uR : ℝ} (h : ¬ uR < uL) :
    _root_.PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropyWeakSolution flux forwardHalfSpace
      (riemannSolution uL uR) := by
  have hle : uL ≤ uR := le_of_not_gt h
  exact (rarefactionProfile_isEntropyWeakSolution_on_forwardHalfSpace
      (uL := uL) (uR := uR) hle).congr_ae
        (riemannSolution_ae_eq_rarefactionProfile_of_not_lt h).symm

/-- The Burgers Riemann solution is an entropy weak solution on positive time for all states. -/
theorem riemannSolution_isEntropyWeakSolution_on_forwardHalfSpace (uL uR : ℝ) :
    _root_.PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropyWeakSolution flux forwardHalfSpace
      (riemannSolution uL uR) := by
  by_cases h : uR < uL
  · exact (riemannSolution_isEntropyWeakSolution_of_lt h).mono_domain
      (show forwardHalfSpace ≤ (⊤ : Opens ℝ^2) from le_top)
  · exact riemannSolution_isEntropyWeakSolution_of_not_lt h

end

end BurgersEquation.Riemann
