/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.CriticalNonexistence
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.SourceGrowth
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.PolynomialGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Subcritical three-dimensional power-source wave nonexistence

Positive Kirchhoff comparison and the outgoing Huygens shell derive the
stronger mass growth from the PDE. The polynomial Kato obstruction
then excludes a global wave when `p²-2p-1<0`, with `p>1`, nonnegative
displacement mass and positive velocity mass. Both initial fields may change sign.

The equality case of the Strauss polynomial and a maximal-lifespan
construction are not established here.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Common

namespace WaveEquation.SmallData

/-- The three-dimensional PDE is impossible in the strict Strauss polynomial
range. -/
theorem not_global_cauchy_solution_three_of_strauss_polynomial {u : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    {R p : ℝ} (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) (hR : 0 < R) (hp : 1 < p) (hcrit : p ^ 2 - 2 * p - 1 < 0)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hG : 0 ≤ ∫ x : ℝ^3, g x)
    (hpositive : 0 < ∫ x : ℝ^3, h x) :
    False := by
  by_cases hp2 : p ≤ 2
  · exact not_global_cauchy_solution_three_of_le hu hs hR hp hp2 hwave hinitial hpositive
  have hp2 : 2 < p := lt_of_not_ge hp2
  have hp3 : p < 3 := by nlinarith
  let F := spatialMass u
  let P := spatialMass (∂[0] u)
  let C := massCoefficient 3 p
  let q := 3 * (p - 1)
  have hC : 0 < C := massCoefficient_pos 3 p
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hgs (y : ℝ^3) (hy : R < ‖y‖) : g y = 0 := by
    rw [← hposition]
    exact hs 0 le_rfl y (by simpa only [add_zero] using hy)
  have hhs (y : ℝ^3) (hy : R < ‖y‖) : h y = 0 := by
    have he := hs.partialDeriv_time 0 le_rfl y
      (by simpa only [add_zero] using hy)
    rwa [hinitial] at he
  have hF (t : ℝ) (ht : R ≤ t) : HasDerivAt F (P t) t :=
    hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs (hR.trans_le ht)
  obtain ⟨δ, hδ, hgrowth⟩ := Kato.eventually_power_lower_bound_of_acceleration
    (F := F) (P := P) hR (shellSourceCoefficient_pos hR hpositive) hp3 hF
    (fun t ht ↦ by
      rw [(hasDerivAt_spatialMass_time_eq_source hu hs (hR.trans_le ht)
        (hwave t (hR.trans_le ht))).deriv]
      exact semilinear_source_lower_bound hu hs hg hh hgs hhs hR hp2 hG hpositive
        hwave hposition hinitial ht)
  obtain ⟨b, hb⟩ := eventually_atTop.mp hgrowth
  let a := max R b
  have ha : 0 < a := hR.trans_le (le_max_left R b)
  obtain ⟨hest, _⟩ := cauchy_spatialMass_estimates hu hs hR hp hwave hinitial hpositive
  apply Kato.not_polynomial_second_order_on_Ici (F := F) (P := P) (C := C * (2 : ℝ) ^ (-q)) (R := 0)
    (p := p) (q := q) (α := 4 - p) (δ := δ) (a := a)
    (mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)) hp (by linarith)
    (by dsimp [q]; nlinarith) hδ
  · exact fun t ht ↦ hF t ((le_max_left R b).trans ht)
  · intro t ht
    simpa only [zero_add] using hb t ((le_max_right R b).trans ht)
  · intro t ht
    have htR : R ≤ t := (le_max_left R b).trans ht
    have htpos : 0 < t := ha.trans_le ht
    have hg := hb t ((le_max_right R b).trans ht)
    have hFpos : 0 < F t := (mul_pos hδ (Real.rpow_pos_of_pos htpos _)).trans_le hg
    have hi := (hest t htpos).2.1
    rw [(hest t htpos).1] at hi
    have hv := Real.rpow_le_rpow_of_nonpos (add_pos hR htpos)
      (show R + t ≤ 2 * t by linarith) (neg_nonpos.mpr hq)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htpos.le] at hv
    rw [show deriv P t = ∫ x : ℝ^3, |u (timeSpaceCons t x)| ^ p from
      (hasDerivAt_spatialMass_time_eq_source hu hs htpos (hwave t htpos)).deriv]
    simp only [zero_add]
    calc
      C * (2 : ℝ) ^ (-q) * t ^ (-q) * F t ^ p =
          C * ((2 : ℝ) ^ (-q) * t ^ (-q)) * F t ^ p := by ring
      _ ≤ C * (R + t) ^ (-q) * F t ^ p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC.le)
          (Real.rpow_nonneg hFpos.le _)
      _ ≤ _ := by
        change massCoefficient 3 p * (R + t) ^ (-(3 : ℝ) * (p - 1)) *
          |F t| ^ p ≤ _ at hi
        simpa only [C, q, neg_mul, abs_of_pos hFpos] using hi
/-- Signed compact data with nonnegative displacement mass and positive velocity
mass cannot give a global forward-supported wave when `1<p<1+√2`. -/
theorem not_global_cauchy_solution_three_of_lt_strauss {u : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ} {R p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hR : 0 < R) (hp : 1 < p) (hcrit : p < 1 + Real.sqrt 2)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hG : 0 ≤ ∫ x : ℝ^3, g x)
    (hpositive : 0 < ∫ x : ℝ^3, h x) :
    False := by
  apply not_global_cauchy_solution_three_of_strauss_polynomial hu hs hg hh hR hp _
    hwave hposition hinitial hG hpositive
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hprod := mul_pos (by linarith : 0 < Real.sqrt 2 - (p - 1))
    (by linarith [Real.sqrt_nonneg 2] : 0 < Real.sqrt 2 + (p - 1))
  nlinarith

end WaveEquation.SmallData
