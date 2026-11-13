/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineFan
public import PDE.Hyperbolic.ConservationLaw.Riemann.Data
public import PDE.Hyperbolic.ConservationLaw.Scalar.PlanarShock
import CAS.ExactTactic

/-!
# Scalar Riemann profile geometry

The increasing characteristic-speed map parametrizes the fan. Clamping its
inverse between the two states gives a measurable bounded representative,
including the equal-state case. The inverse Lipschitz estimate controls the
spatial slope with a constant independent of the states.
The full profile selects the compressive planar shock or the increasing
fan, and extends the prescribed datum to nonpositive times.

With `e` in the role of `F'`, so that `e.symm` is Evans's `G = (F')⁻¹`, `rarefactionProfile` is
the rarefaction wave (56) of Evans, §3.4.4, Theorem 4(ii). At positive times `riemannSolution` is
the shock (54) with the speed (55) when `uR < uL`, and the wave (56) otherwise, as in Theorem 4
for Riemann's problem (53).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.4, equation (53) and Theorem 4, equations (54)-(56).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Riemann

/-- The inverse-characteristic wave clamped between its two end states. -/
def rarefactionProfile (e : ℝ ≃o ℝ) (uL uR : ℝ) (p : ℝ^2) : ℝ :=
  max uL (min uR (e.symm (p 1 / p 0)))

/-- Clamping may equivalently be performed on characteristic speeds. -/
theorem rarefactionProfile_eq_inverse_clamp (e : ℝ ≃o ℝ) (uL uR : ℝ) (p : ℝ^2) :
    rarefactionProfile e uL uR p = e.symm (max (e uL) (min (e uR) (p 1 / p 0))) := by
  rw [e.symm.map_sup, e.symm.map_inf, e.symm_apply_apply, e.symm_apply_apply]
  rfl

/-- Equal states give a constant profile at every spacetime point. -/
@[simp] theorem rarefactionProfile_same (e : ℝ ≃o ℝ) (u : ℝ) (p : ℝ^2) :
    rarefactionProfile e u u p = u :=
  max_eq_left (min_le_left _ _)

/-- The profile stays in the interval between ordered states. -/
theorem rarefactionProfile_mem_Icc (e : ℝ ≃o ℝ) {uL uR : ℝ} (hLR : uL ≤ uR)
    (p : ℝ^2) : rarefactionProfile e uL uR p ∈ Icc uL uR :=
  ⟨le_max_left _ _, max_le hLR (min_le_left _ _)⟩

/-- The global norm bound depends only on the two end states. -/
theorem norm_rarefactionProfile_le (e : ℝ ≃o ℝ) {uL uR : ℝ} (hLR : uL ≤ uR)
    (p : ℝ^2) : ‖rarefactionProfile e uL uR p‖ ≤ max ‖uL‖ ‖uR‖ := by
  obtain ⟨hL, hR⟩ := rarefactionProfile_mem_Icc e hLR p
  rw [Real.norm_eq_abs]
  apply abs_le.2
  constructor
  · calc
      -(max ‖uL‖ ‖uR‖) ≤ -‖uL‖ := neg_le_neg (le_max_left _ _)
      _ ≤ uL := neg_abs_le uL
      _ ≤ rarefactionProfile e uL uR p := hL
  · exact hR.trans ((le_abs_self uR).trans (le_max_right _ _))

/-- The totalized quotient and continuous ordered clamp make the profile
jointly measurable, including the zero-time hyperplane. -/
theorem measurable_rarefactionProfile (e : ℝ ≃o ℝ) (uL uR : ℝ) :
    Measurable (rarefactionProfile e uL uR) := by
  have hr : Measurable (fun p : ℝ^2 ↦ p 1 / p 0) := by fun_prop
  exact measurable_const.max (measurable_const.min (e.symm.continuous.measurable.comp hr))

/-- The profile is essentially bounded for any measure on spacetime. -/
theorem memLp_top_rarefactionProfile (e : ℝ ≃o ℝ) {uL uR : ℝ} (hLR : uL ≤ uR)
    (μ : Measure ℝ^2) : MemLp (rarefactionProfile e uL uR) ∞ μ :=
  memLp_top_of_bound (measurable_rarefactionProfile e uL uR).aestronglyMeasurable
    (max ‖uL‖ ‖uR‖) (Filter.Eventually.of_forall (norm_rarefactionProfile_le e hLR))

/-- To the left of the first characteristic, the clamp is the left state. -/
theorem rarefactionProfile_eq_left (e : ℝ ≃o ℝ) {uL uR : ℝ} {p : ℝ^2}
    (ht : 0 < p 0) (hL : p 1 ≤ e uL * p 0) :
    rarefactionProfile e uL uR p = uL := by
  have hr : p 1 / p 0 ≤ e uL := (div_le_iff₀ ht).2 hL
  have hinv : e.symm (p 1 / p 0) ≤ uL := by
    simpa only [OrderIso.symm_apply_apply] using e.symm.monotone hr
  exact max_eq_left ((min_le_right _ _).trans hinv)

/-- To the right of the last characteristic, the clamp is the right state. -/
theorem rarefactionProfile_eq_right (e : ℝ ≃o ℝ) {uL uR : ℝ} (hLR : uL ≤ uR)
    {p : ℝ^2} (ht : 0 < p 0) (hR : e uR * p 0 ≤ p 1) :
    rarefactionProfile e uL uR p = uR := by
  have hr : e uR ≤ p 1 / p 0 := (le_div_iff₀ ht).2 hR
  have hinv : uR ≤ e.symm (p 1 / p 0) := by
    simpa only [OrderIso.symm_apply_apply] using e.symm.monotone hr
  simp only [rarefactionProfile, min_eq_left hinv, max_eq_right hLR]

/-- Between the two characteristics, the clamp is the inverse wave. -/
theorem rarefactionProfile_eq_middle (e : ℝ ≃o ℝ) {uL uR : ℝ} {p : ℝ^2}
    (ht : 0 < p 0) (hL : e uL * p 0 ≤ p 1) (hR : p 1 ≤ e uR * p 0) :
    rarefactionProfile e uL uR p = e.symm (p 1 / p 0) := by
  have hleft : uL ≤ e.symm (p 1 / p 0) := by
    simpa only [OrderIso.symm_apply_apply] using e.symm.monotone ((le_div_iff₀ ht).2 hL)
  have hright : e.symm (p 1 / p 0) ≤ uR := by
    simpa only [OrderIso.symm_apply_apply] using e.symm.monotone ((div_le_iff₀ ht).2 hR)
  simp only [rarefactionProfile, min_eq_right hright, max_eq_right hleft]

/-- At positive time the clamped formula agrees with the affine fan. -/
theorem rarefactionProfile_eq_affineFan (e : ℝ ≃o ℝ) {uL uR : ℝ} (hLR : uL ≤ uR)
    {p : ℝ^2} (ht : p ∈ forwardHalfSpace) :
    rarefactionProfile e uL uR p =
      AffineFan.profile (e uL) (e uR) uL (fun x ↦ e.symm (x 1 / x 0)) uR p := by
  by_cases hL : p ∈ AffineInterface.leftHalfSpace (e uL)
  · rw [AffineFan.profile_eq_left hL]
    exact rarefactionProfile_eq_left e ht (le_of_lt hL)
  · by_cases hR : p ∈ AffineInterface.leftHalfSpace (e uR)
    · rw [AffineFan.profile_eq_middle hL hR]
      exact rarefactionProfile_eq_middle e ht (le_of_not_gt hL) (le_of_lt hR)
    · rw [AffineFan.profile_eq_right hL hR]
      exact rarefactionProfile_eq_right e hLR ht (le_of_not_gt hR)

/-- Clamping preserves the inverse Lipschitz constant. This yields the sharp
one-sided spatial estimate without a state-dependent constant. -/
theorem rarefactionProfile_slope_le (e : ℝ ≃o ℝ) {K : ℝ≥0} (he : LipschitzWith K e.symm) (uL uR : ℝ)
    {t : ℝ} (ht : 0 < t) (x : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    rarefactionProfile e uL uR !₂[t, x + z] -
      rarefactionProfile e uL uR !₂[t, x] ≤ (K : ℝ) * z / t := by
  have hclamp := (he.const_min uR).const_max uL
  have hb := hclamp.dist_le_mul ((x + z) / t) (x / t)
  have hratio : (x + z) / t - x / t = z / t := by cas
  simp only [Real.dist_eq] at hb
  rw [hratio, abs_of_nonneg (div_nonneg hz ht.le)] at hb
  have hout := (le_abs_self (max uL (min uR (e.symm ((x + z) / t))) -
      max uL (min uR (e.symm (x / t))))).trans hb
  change max uL (min uR (e.symm ((x + z) / t))) - max uL (min uR (e.symm (x / t))) ≤ (K : ℝ) * z / t
  simpa only [mul_div_assoc] using hout

/-- The clamped fan depends only on the spacetime ratio. -/
theorem rarefactionProfile_smul_of_pos (e : ℝ ≃o ℝ) (uL uR : ℝ) {a : ℝ} (ha : 0 < a) (p : ℝ^2) :
    rarefactionProfile e uL uR (a • p) = rarefactionProfile e uL uR p := by
  have hr : (a * p 1) / (a * p 0) = p 1 / p 0 := by cas using ha
  change max uL (min uR (e.symm ((a * p 1) / (a * p 0)))) = max uL (min uR (e.symm (p 1 / p 0)))
  rw [hr]

/-- At each fixed time a downward planar shock is antitone in space. -/
theorem antitone_planarShock_slice {uL uR : ℝ} (hLR : uR ≤ uL) (s t : ℝ) :
    Antitone (fun x : ℝ ↦ planarShock uL uR s !₂[t, x]) := by
  intro x y hxy
  change planarShock uL uR s !₂[t, y] ≤ planarShock uL uR s !₂[t, x]
  by_cases hx : x < s * t
  · have hx' : !₂[t, x] ∈ AffineInterface.leftHalfSpace s := hx
    rw [planarShock_apply_of_mem hx']
    by_cases hy : y < s * t
    · have hy' : !₂[t, y] ∈ AffineInterface.leftHalfSpace s := hy
      rw [planarShock_apply_of_mem hy']
    · have hy' : !₂[t, y] ∉ AffineInterface.leftHalfSpace s := hy
      rw [planarShock_apply_of_not_mem hy']
      exact hLR
  · have hx' : !₂[t, x] ∉ AffineInterface.leftHalfSpace s := hx
    have hy' : !₂[t, y] ∉ AffineInterface.leftHalfSpace s :=
      not_lt_of_ge ((le_of_not_gt hx).trans hxy)
    rw [planarShock_apply_of_not_mem hx', planarShock_apply_of_not_mem hy']

/-- The scalar Riemann representative: a compressive shock for decreasing
states, the inverse-characteristic fan otherwise, and the prescribed step
datum at nonpositive times. -/
def riemannSolution (F : ℝ → ℝ) (e : ℝ ≃o ℝ) (uL uR : ℝ) (p : ℝ^2) : ℝ :=
  if 0 < p 0 then
    if uR < uL then planarShock uL uR (rankineHugoniotSpeed F uL uR) p
    else rarefactionProfile e uL uR p
  else riemannData uL uR (p 1)

/-- The constructed representative agrees exactly with the datum at
every nonpositive time. -/
theorem riemannSolution_of_nonpos (F : ℝ → ℝ) (e : ℝ ≃o ℝ) (uL uR : ℝ) {p : ℝ^2} (ht : p 0 ≤ 0) :
    riemannSolution F e uL uR p = riemannData uL uR (p 1) :=
  ite_eq_right (not_lt_of_ge ht)

/-- Positive-time compressive states select the planar shock. -/
theorem riemannSolution_of_right_lt_left (F : ℝ → ℝ) (e : ℝ ≃o ℝ)
    {uL uR : ℝ} (hLR : uR < uL) {p : ℝ^2} (ht : 0 < p 0) :
    riemannSolution F e uL uR p = planarShock uL uR (rankineHugoniotSpeed F uL uR) p := by
  simp only [riemannSolution, ite_eq_left ht, ite_eq_left hLR]

/-- Positive-time ordered states select the clamped fan, including equal
states. -/
theorem riemannSolution_of_left_le_right (F : ℝ → ℝ) (e : ℝ ≃o ℝ)
    {uL uR : ℝ} (hLR : uL ≤ uR) {p : ℝ^2} (ht : 0 < p 0) :
    riemannSolution F e uL uR p = rarefactionProfile e uL uR p := by
  simp only [riemannSolution, ite_eq_left ht, ite_eq_right (not_lt_of_ge hLR)]

/-- Equal states give the same constant at every spacetime point. -/
@[simp] theorem riemannSolution_same (F : ℝ → ℝ) (e : ℝ ≃o ℝ) (u : ℝ)
    (p : ℝ^2) : riemannSolution F e u u p = u := by
  by_cases ht : 0 < p 0
  · rw [riemannSolution_of_left_le_right F e le_rfl ht, rarefactionProfile_same]
  · rw [riemannSolution_of_nonpos F e u u (le_of_not_gt ht), riemannData_self]

/-- The solution stays between its two endpoint values globally. -/
theorem norm_riemannSolution_le (F : ℝ → ℝ) (e : ℝ ≃o ℝ) (uL uR : ℝ)
    (p : ℝ^2) : ‖riemannSolution F e uL uR p‖ ≤ max ‖uL‖ ‖uR‖ := by
  by_cases ht : 0 < p 0
  · by_cases hLR : uR < uL
    · rw [riemannSolution_of_right_lt_left F e hLR ht]
      by_cases hp : p ∈ AffineInterface.leftHalfSpace (rankineHugoniotSpeed F uL uR)
      · rw [planarShock_apply_of_mem hp]
        exact le_max_left _ _
      · rw [planarShock_apply_of_not_mem hp]
        exact le_max_right _ _
    · rw [riemannSolution_of_left_le_right F e (le_of_not_gt hLR) ht]
      exact norm_rarefactionProfile_le e (le_of_not_gt hLR) p
  · rw [riemannSolution_of_nonpos F e uL uR (le_of_not_gt ht)]
    exact norm_riemannData_le_max uL uR (p 1)

/-- Measurability includes the prescribed values on the initial slice. -/
theorem measurable_riemannSolution (F : ℝ → ℝ) (e : ℝ ≃o ℝ) (uL uR : ℝ) :
    Measurable (riemannSolution F e uL uR) := by
  have htime : MeasurableSet {p : ℝ^2 | 0 < p 0} := forwardHalfSpace.isOpen.measurableSet
  apply Measurable.ite htime
  · by_cases hLR : uR < uL
    · simpa only [ite_eq_left hLR] using measurable_planarShock uL uR (rankineHugoniotSpeed F uL uR)
    · simpa only [ite_eq_right hLR] using measurable_rarefactionProfile e uL uR
  · exact (measurable_riemannData uL uR).comp (by fun_prop)

/-- The global range bound gives essential boundedness for every measure. -/
theorem memLp_top_riemannSolution (F : ℝ → ℝ) (e : ℝ ≃o ℝ) (uL uR : ℝ)
    (μ : Measure ℝ^2) : MemLp (riemannSolution F e uL uR) ∞ μ :=
  memLp_top_of_bound (measurable_riemannSolution F e uL uR).aestronglyMeasurable
    (max ‖uL‖ ‖uR‖) (Filter.Eventually.of_forall (norm_riemannSolution_le F e uL uR))

/-- The inverse Lipschitz constant controls every state pair. Downward
shocks have nonpositive increments, and upward fans satisfy the sharp
`K z / t` estimate. -/
theorem riemannSolution_slope_le (F : ℝ → ℝ) (e : ℝ ≃o ℝ) {K : ℝ≥0} (he : LipschitzWith K e.symm)
    (uL uR : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    riemannSolution F e uL uR !₂[t, x + z] -
      riemannSolution F e uL uR !₂[t, x] ≤ (K : ℝ) * z / t := by
  by_cases hLR : uR < uL
  · rw [riemannSolution_of_right_lt_left F e hLR ht, riemannSolution_of_right_lt_left F e hLR ht]
    exact (sub_nonpos.mpr (antitone_planarShock_slice hLR.le (rankineHugoniotSpeed F uL uR) t
        (le_add_of_nonneg_right hz))).trans (div_nonneg (mul_nonneg K.coe_nonneg hz) ht.le)
  · rw [riemannSolution_of_left_le_right F e (le_of_not_gt hLR) ht,
      riemannSolution_of_left_le_right F e (le_of_not_gt hLR) ht]
    exact rarefactionProfile_slope_le e he uL uR ht x hz

/-- The prescribed representative is invariant under every positive
spacetime dilation, including on its nonpositive-time extension. -/
theorem riemannSolution_smul_of_pos (F : ℝ → ℝ) (e : ℝ ≃o ℝ) (uL uR : ℝ)
    {a : ℝ} (ha : 0 < a) (p : ℝ^2) :
    riemannSolution F e uL uR (a • p) = riemannSolution F e uL uR p := by
  by_cases ht : 0 < p 0
  · have hat : 0 < (a • p) 0 := mul_pos ha ht
    by_cases hLR : uR < uL
    · rw [riemannSolution_of_right_lt_left F e hLR hat, riemannSolution_of_right_lt_left F e hLR ht]
      exact planarShock_smul_of_pos ha uL uR (rankineHugoniotSpeed F uL uR) p
    · rw [riemannSolution_of_left_le_right F e (le_of_not_gt hLR) hat,
        riemannSolution_of_left_le_right F e (le_of_not_gt hLR) ht]
      exact rarefactionProfile_smul_of_pos e uL uR ha p
  · have hat : (a • p) 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt ht)
    rw [riemannSolution_of_nonpos F e uL uR hat,
      riemannSolution_of_nonpos F e uL uR (le_of_not_gt ht)]
    change (if a * p 1 < 0 then uL else uR) = (if p 1 < 0 then uL else uR)
    have hx : a * p 1 < 0 ↔ p 1 < 0 := by
      simpa only [mul_zero] using (mul_lt_mul_iff_right₀ (b := p 1) (c := 0) ha)
    simp only [hx]

end PDE.Hyperbolic.ConservationLaw.Scalar.Riemann
