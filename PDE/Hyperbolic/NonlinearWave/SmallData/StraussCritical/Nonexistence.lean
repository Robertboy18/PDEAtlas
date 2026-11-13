/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.Kato
public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.MassGrowth
public import PDE.Hyperbolic.NonlinearWave.SmallData.Inequality
import CAS.ExactTactic

/-!
# Critical Strauss nonexistence for the three-dimensional wave

For `p>2` and `p(p-2)=1`, a jointly C² wave with zero displacement and
nonnegative compact C² velocity of positive integral cannot exist for all
future times. The characteristic formula derives the logarithmic gain;
the mass identity and ball-volume inequality then contradict critical Kato.

The classical-duration module removes the support-cone hypothesis by finite
propagation.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Common

namespace WaveEquation.SmallData

/-- Global classical power-source waves are impossible at the Strauss polynomial
equality. Every growth estimate is derived from the displayed PDE and data. -/
theorem not_global_cauchy_solution_three_of_strauss_equality {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hh : ContDiff ℝ 2 h) (hhn : ∀ x, 0 ≤ h x)
    (hR : 0 < R) (hp : 2 < p) (hcritical : p * (p - 2) = 1)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^3, h x) :
    False := by
  let F := spatialMass u
  let P := spatialMass (∂[0] u)
  let C := massCoefficient 3 p
  let q := 3 * (p - 1)
  have hp1 : 1 < p := by linarith only [hp]
  have hp3 : p < 3 := by nlinarith only [hcritical]
  have hC : 0 < C := massCoefficient_pos 3 p
  have hq : 0 ≤ q := by dsimp [q]; linarith only [hp]
  have hhs (y : ℝ^3) (hy : R < ‖y‖) : h y = 0 := by
    have he := hs.partialDeriv_time 0 le_rfl y
      (by simpa only [add_zero] using hy)
    rwa [hinitial] at he
  have hF (t : ℝ) (ht : R ≤ t) : HasDerivAt F (P t) t :=
    hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs (hR.trans_le ht)
  have hP (t : ℝ) (ht : R ≤ t) : DifferentiableAt ℝ P t :=
    (hasDerivAt_spatialMass_time hu hs (hR.trans_le ht)).differentiableAt
  obtain ⟨hest, hlinear⟩ := cauchy_spatialMass_estimates hu hs hR hp1 hwave hinitial hpositive
  have hFzero : F 0 = 0 := by simp only [F, spatialMass, hzero, integral_zero]
  have hFpos (t : ℝ) (ht : R ≤ t) : 0 < F t := by
    have he := hlinear t (hR.trans_le ht).le
    change F 0 + (∫ x : ℝ^3, h x) * t ≤ F t at he
    rw [hFzero, zero_add] at he
    exact (mul_pos hpositive (hR.trans_le ht)).trans_le he
  apply Kato.not_critical_polynomial_second_order_on_Ici
    (F := F) (P := P) (C := C * (2 : ℝ) ^ (-q)) (R := 0) (p := p) (q := q) (α := 4 - p) (a := R)
    (mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)) hp1 hq
    (by linarith only [hp3])
    (by dsimp [q]; nlinarith only [hcritical]) (by simpa only [zero_add] using hR) hF hP hFpos
  · intro t ht
    rw [← (hF t ht).deriv]
    exact (hest t (hR.trans_le ht)).2.2.le
  · simpa only [zero_add] using tendsto_critical_spatialMass_div_rpow_atTop
      hu hs hh hhs hhn hR hp hcritical hpositive hwave hzero hinitial
  · intro t ht
    have htpos : 0 < t := hR.trans_le ht
    have hi := (hest t htpos).2.1
    rw [(hest t htpos).1] at hi
    have hv := Real.rpow_le_rpow_of_nonpos (add_pos hR htpos)
      (show R + t ≤ 2 * t by linarith only [ht]) (neg_nonpos.mpr hq)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htpos.le] at hv
    rw [show deriv P t = ∫ x : ℝ^3, |u (timeSpaceCons t x)| ^ p from
      (hasDerivAt_spatialMass_time_eq_source hu hs htpos (hwave t htpos)).deriv]
    simp only [zero_add]
    calc
      C * (2 : ℝ) ^ (-q) * t ^ (-q) * F t ^ p =
          C * ((2 : ℝ) ^ (-q) * t ^ (-q)) * F t ^ p := by ring
      _ ≤ C * (R + t) ^ (-q) * F t ^ p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC.le)
          (Real.rpow_nonneg (hFpos t ht).le _)
      _ ≤ _ := by
        change massCoefficient 3 p * (R + t) ^ (-(3 : ℝ) * (p - 1)) *
          |F t| ^ p ≤ _ at hi
        simpa only [C, q, neg_mul, abs_of_pos (hFpos t ht)] using hi

/-- The positive three-dimensional Strauss root is strictly greater than two. -/
theorem two_lt_one_add_sqrt_two : (2 : ℝ) < 1 + Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  nlinarith only [hs, hn]

/-- The positive Strauss root satisfies the precise reciprocal-density identity. -/
theorem one_add_sqrt_two_strauss_equality :
    (1 + Real.sqrt 2) * ((1 + Real.sqrt 2) - 2) = 1 := by
  cas

/-- The three-dimensional wave cannot persist globally at `p=1+√2`. -/
theorem not_global_cauchy_solution_three_at_strauss {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hh : ContDiff ℝ 2 h) (hhn : ∀ x, 0 ≤ h x)
    (hR : 0 < R)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ (1 + Real.sqrt 2))
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^3, h x) :
    False :=
  not_global_cauchy_solution_three_of_strauss_equality hu hs hh hhn hR
    two_lt_one_add_sqrt_two one_add_sqrt_two_strauss_equality hwave hzero hinitial hpositive

end WaveEquation.SmallData
