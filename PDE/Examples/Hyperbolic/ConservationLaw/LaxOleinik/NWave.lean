/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.LaxOleinik.Asymptotics
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.L1
import CAS.ExactTactic

/-!
# A nonquadratic drifting N-wave example

The flux `r⁴ / 4 + r² / 2 + 2r` is uniformly convex with unbounded second derivative.
The step datum `twoLobeDatum` has lobe parameters `p = 2`, `q = 4`. Its N-wave is
`x/t - 2` on `(2t - √(2t), 2t + √(4t))` and zero elsewhere
(`driftingQuarticFlux_twoLobe_nWave`), with `L¹` norm `3`. The Lax–Oleinik solution is
within `C/√t` of it in `L¹` for every `t > 0`
(`driftingQuarticFlux_twoLobe_nWave_convergence`, from `exists_integral_abs_sub_nWave_le`).
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common PDE.Hyperbolic.ConservationLaw
open PDE.Hyperbolic.ConservationLaw.LaxOleinik
open scoped ENNReal NNReal

namespace PDE.Examples.ConservationLaw.LaxOleinik

/-- A negative lobe of height one on `[-1, 0]` and a positive lobe of height two on
`[0, 1]`. -/
def twoLobeDatum (x : ℝ) : ℝ :=
  (Icc (0 : ℝ) 1).indicator (fun _ ↦ (2 : ℝ)) x -
    (Icc (-1 : ℝ) 0).indicator (fun _ ↦ (1 : ℝ)) x

/-- The two-lobe datum is essentially bounded by two. -/
theorem twoLobeDatum_memLp : MemLp twoLobeDatum ∞ volume := by
  apply memLp_top_of_bound
    (((measurable_const.indicator measurableSet_Icc).sub
      (measurable_const.indicator measurableSet_Icc)).aestronglyMeasurable) 2
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx₁ : x ∈ Icc (0 : ℝ) 1 <;>
    by_cases hx₂ : x ∈ Icc (-1 : ℝ) 0 <;> norm_num [twoLobeDatum, hx₁, hx₂]

/-- The bounded two-lobe datum is integrable. -/
theorem twoLobeDatum_integrable : Integrable twoLobeDatum volume :=
  (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).sub
    (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)

/-- The datum vanishes outside the interval `[-1, 1]`. -/
theorem twoLobeDatum_support :
    ∀ᵐ x ∂volume, x ∉ Icc (-1 : ℝ) 1 → twoLobeDatum x = 0 := by
  apply Filter.Eventually.of_forall
  intro x hx
  have h₁ : x ∉ Icc (0 : ℝ) 1 := fun h ↦ hx ⟨by linarith [h.1], h.2⟩
  have h₂ : x ∉ Icc (-1 : ℝ) 0 := fun h ↦ hx ⟨h.1, by linarith [h.2]⟩
  simp only [twoLobeDatum, indicator_of_notMem h₁, indicator_of_notMem h₂, sub_self]

/-- The signed mass of the datum is one. -/
theorem integral_twoLobeDatum : (∫ x, twoLobeDatum x) = 1 := by
  have hpos : Integrable ((Icc (0 : ℝ) 1).indicator (fun _ ↦ (2 : ℝ))) volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hneg : Integrable ((Icc (-1 : ℝ) 0).indicator (fun _ ↦ (1 : ℝ))) volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  unfold twoLobeDatum
  rw [integral_sub hpos hneg,
    integral_indicator_const _ measurableSet_Icc, integral_indicator_const _ measurableSet_Icc,
    smul_eq_mul, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
  norm_num

/-- The cumulative integral has minimum minus one, so the negative lobe
parameter is two. -/
theorem negativeLobeMass_twoLobeDatum : negativeLobeMass twoLobeDatum = 2 := by
  let fPos : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ ↦ (2 : ℝ))
  let fNeg : ℝ → ℝ := (Icc (-1 : ℝ) 0).indicator (fun _ ↦ (1 : ℝ))
  have hp : Integrable fPos volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hn : Integrable fNeg volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hnt : (∫ x, fNeg x) = 1 := by
    dsimp only [fNeg]
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
      Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
    norm_num
  have hp0 : (∫ x in Iio (0 : ℝ), fPos x) = 0 :=
    integral_Iio_eq_zero_of_ae_support_Icc
      (Filter.Eventually.of_forall fun _ hx ↦ indicator_of_notMem hx _) le_rfl
  have hn0 : (∫ x in Iio (0 : ℝ), fNeg x) = 1 := by
    rw [integral_Iio_eq_integral_of_ae_support_Icc hn
      (Filter.Eventually.of_forall fun _ hx ↦ indicator_of_notMem hx _) le_rfl, hnt]
  have hsplit (x : ℝ) : (∫ y in Iio x, twoLobeDatum y) =
      (∫ y in Iio x, fPos y) - ∫ y in Iio x, fNeg y :=
    integral_sub hp.integrableOn hn.integrableOn
  have hmin (x : ℝ) : -1 ≤ ∫ y in Iio x, twoLobeDatum y := by
    have hpos : 0 ≤ ∫ y in Iio x, fPos y := integral_nonneg
      (indicator_nonneg fun _ _ ↦ by norm_num)
    have hneg := setIntegral_le_integral hn
      (Filter.Eventually.of_forall (indicator_nonneg fun _ _ ↦ by norm_num))
      (s := Iio x)
    rw [hnt] at hneg
    rw [hsplit]
    linarith
  have h0 : (∫ y in Iio (0 : ℝ), twoLobeDatum y) = -1 := by
    rw [hsplit, hp0, hn0]
    norm_num
  have hleast : IsLeast (range fun x : ℝ ↦ ∫ y in Iio x, twoLobeDatum y) (-1) := by
    refine ⟨⟨0, h0⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hmin x
  rw [negativeLobeMass, hleast.csInf_eq]
  norm_num

/-- The positive lobe parameter is four. -/
theorem positiveLobeMass_twoLobeDatum : positiveLobeMass twoLobeDatum = 4 := by
  have h := positiveLobeMass_sub_negativeLobeMass twoLobeDatum_integrable
    (by norm_num : (-1 : ℝ) ≤ 1) twoLobeDatum_support
  rw [negativeLobeMass_twoLobeDatum, integral_twoLobeDatum] at h
  linarith

/-- The drifting quartic flux is `C³`. -/
theorem driftingQuarticFlux_contDiff_three : ContDiff ℝ 3 driftingQuarticFlux := by
  unfold driftingQuarticFlux
  fun_prop

/-- The N-wave for the two-lobe datum is `x/t - 2` on `(2t - √(2t), 2t + √(4t))` and zero
elsewhere. -/
theorem driftingQuarticFlux_twoLobe_nWave (t : ℝ) :
    nWave driftingQuarticFlux twoLobeDatum t =
      (Ioo (t * 2 - √(2 * t)) (t * 2 + √(4 * t))).indicator
        (fun x ↦ x / t - 2) := by
  funext x
  simp [nWave, negativeLobeMass_twoLobeDatum, positiveLobeMass_twoLobeDatum,
    driftingQuarticFlux_deriv, driftingQuarticFlux_deriv2]

/-- The concrete drifting N-wave has `L¹` norm three at every positive time. -/
theorem driftingQuarticFlux_twoLobe_nWave_mass {t : ℝ} (ht : 0 < t) :
    (∫ x, |nWave driftingQuarticFlux twoLobeDatum t x|) = 3 := by
  have hp : 0 ≤ negativeLobeMass twoLobeDatum := by
    rw [negativeLobeMass_twoLobeDatum]; norm_num
  have hq : 0 ≤ positiveLobeMass twoLobeDatum := by
    rw [positiveLobeMass_twoLobeDatum]; norm_num
  have hd : 0 < deriv (deriv driftingQuarticFlux) 0 := by
    rw [driftingQuarticFlux_deriv2]; norm_num
  simpa only [negativeLobeMass_twoLobeDatum, positiveLobeMass_twoLobeDatum,
    show ((2 : ℝ) + 4) / 2 = 3 by norm_num] using integral_abs_nWave hp hq hd ht

/-- There is `C ≥ 0` with `‖u(t) - N(t)‖_{L¹} ≤ C/√t` for every `t > 0`, where `N` is the
N-wave. -/
theorem driftingQuarticFlux_twoLobe_nWave_convergence :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x ↦ |solution driftingQuarticFlux twoLobeDatum !₂[t, x] -
        nWave driftingQuarticFlux twoLobeDatum t x|) volume ∧
      (∫ x, |solution driftingQuarticFlux twoLobeDatum !₂[t, x] -
        nWave driftingQuarticFlux twoLobeDatum t x|) ≤ C / √t :=
  exists_integral_abs_sub_nWave_le driftingQuarticFlux_contDiff_three (by norm_num)
    driftingQuarticFlux_deriv2_lower (by norm_num [driftingQuarticFlux])
    twoLobeDatum_memLp twoLobeDatum_support
    (by rw [negativeLobeMass_twoLobeDatum]; norm_num)
    (by rw [positiveLobeMass_twoLobeDatum]; norm_num)

end PDE.Examples.ConservationLaw.LaxOleinik
