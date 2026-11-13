/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.Comparison
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.Shell
import CAS.ExactTactic

/-!
# The outgoing-shell source lower bound

The full free wave has mass `∫g + t ∫h` in a shell of volume at most
`8 R |B₁| t²`. Its positive part lies below the absolute value of the
nonlinear wave. Jensen then bounds the source integral from below
by a positive multiple of `t^(2-p)`, without pointwise sign assumptions on the data.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set
open PDE.Analysis (unitBallVolume)

namespace WaveEquation.SmallData

/-- The exact positive constant in the three-dimensional shell source estimate. -/
def shellSourceCoefficient (R H p : ℝ) : ℝ :=
  (8 * R * unitBallVolume 3) ^ (1 - p) * H ^ p

/-- Positive radius and positive initial mass give a positive source coefficient. -/
theorem shellSourceCoefficient_pos {R H p : ℝ} (hR : 0 < R) (hH : 0 < H) :
    0 < shellSourceCoefficient R H p :=
  mul_pos (Real.rpow_pos_of_pos (by unfold unitBallVolume; positivity) _)
    (Real.rpow_pos_of_pos hH p)

/-- Positive mass in an outgoing shell forces a power-integral lower bound,
even when the comparison field changes sign. -/
private theorem shell_power_integral_lower_bound {v w : ℝ^3 → ℝ} {R H p t : ℝ} (hv : Continuous v)
    (hs : ∀ x, x ∉ outgoingShell R t → v x = 0) (hR : 0 < R) (hp : 1 ≤ p) (hH : 0 < H) (ht : R ≤ t)
    (hm : t * H ≤ ∫ x, v x) (hw : Integrable (fun x ↦ |w x| ^ p)) (hle : ∀ x, v x ≤ w x) :
    shellSourceCoefficient R H p * t ^ (2 - p) ≤ ∫ x, |w x| ^ p := by
  have htpos : 0 < t := hR.trans_le ht
  have hvol := volume_outgoingShell_bounds hR ht
  have hmass : 0 < t * H := mul_pos htpos hH
  have hj := compact_volume_mass_bound_of_le hv (isCompact_outgoingShell R t)
    hvol.1 hp hs (hmass.le.trans hm) hw hle
  have hvpow := Real.rpow_le_rpow_of_nonpos hvol.1 hvol.2 (by linarith : 1 - p ≤ 0)
  have hB : 0 < 8 * R * unitBallVolume 3 := by
    have : 0 < unitBallVolume 3 := by unfold unitBallVolume; positivity
    positivity
  have heq : (8 * R * unitBallVolume 3 * t ^ 2) ^ (1 - p) * (t * H) ^ p =
      shellSourceCoefficient R H p * t ^ (2 - p) := by
    rw [Real.mul_rpow hB.le (sq_nonneg t), Real.mul_rpow htpos.le hH.le,
      ← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    calc
      _ = shellSourceCoefficient R H p * (t ^ ((2 : ℝ) * (1 - p)) * t ^ p) := by
        dsimp [shellSourceCoefficient]
        ring
      _ = _ := by
        rw [← Real.rpow_add htpos, show (2 : ℝ) * (1 - p) + p = 2 - p by cas]
  rw [← heq]
  calc
    _ ≤ volume.real (outgoingShell R t) ^ (1 - p) * (t * H) ^ p :=
      mul_le_mul_of_nonneg_right hvpow (Real.rpow_nonneg hmass.le p)
    _ ≤ volume.real (outgoingShell R t) ^ (1 - p) * (∫ x, v x) ^ p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hmass.le hm (by linarith))
        (Real.rpow_nonneg hvol.1.le _)
    _ ≤ _ := hj

/-- The full free wave satisfies the same shell estimate against every pointwise
upper field whose power is integrable. -/
private theorem kirchhoffFormula_shell_lower_bound {g h w : ℝ^3 → ℝ} {R p t : ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : ∀ y : ℝ^3, R < ‖y‖ → g y = 0)
    (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) (hR : 0 < R) (hp : 1 ≤ p) (hG : 0 ≤ ∫ y : ℝ^3, g y)
    (hH : 0 < ∫ y : ℝ^3, h y) (ht : R ≤ t) (hw : Integrable (fun x ↦ |w x| ^ p))
    (hle : ∀ x, spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) ≤ w x) :
    shellSourceCoefficient R (∫ y : ℝ^3, h y) p * t ^ (2 - p) ≤ ∫ x : ℝ^3, |w x| ^ p := by
  have htpos : 0 < t := hR.trans_le ht
  have hslice : Continuous (fun x : ℝ^3 ↦
      spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)) :=
    (contDiff_two_kirchhoffFormula hg hh).continuous.comp
      (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  apply shell_power_integral_lower_bound hslice ?_ hR hp hH ht ?_ hw hle
  · intro x hx
    apply kirchhoffFormula_eq_zero_of_shell (hg.of_le (by norm_num)) hh.continuous
      hgs hhs hR.le htpos.le x
    simp only [outgoingShell, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_and_or, not_le, not_not] at hx
    rcases hx with hx | hx
    · exact Or.inr (by linarith)
    · exact Or.inl hx
  · change t * (∫ y : ℝ^3, h y) ≤ spatialMass (spaceTimeUncurry (kirchhoffFormula g h)) t
    rw [spatialMass_kirchhoffFormula (hg.of_le (by norm_num)) hh.continuous hgs hhs htpos]
    exact le_add_of_nonneg_left hG

/-- Jensen on the Huygens shell bounds the free velocity wave, including signed data. -/
theorem kirchhoff_power_integral_lower_bound {h : ℝ^3 → ℝ} {R p t : ℝ}
    (hh : ContDiff ℝ 2 h) (hs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0)
    (hR : 0 < R) (hp : 1 ≤ p) (hH : 0 < ∫ y : ℝ^3, h y) (ht : R ≤ t) :
    shellSourceCoefficient R (∫ y : ℝ^3, h y) p * t ^ (2 - p) ≤
      ∫ x : ℝ^3, |kirchhoffPotential h (timeSpaceCons t x)| ^ p := by
  have htpos : 0 < t := hR.trans_le ht
  have hc : Continuous (fun x : ℝ^3 ↦ kirchhoffPotential h (timeSpaceCons t x)) :=
    (contDiff_kirchhoffPotential hh).continuous.comp
      (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  have hr : Continuous (fun a : ℝ ↦ |a| ^ p) :=
    continuous_abs.rpow_const (fun _ ↦ Or.inr (zero_le_one.trans hp))
  have hk : HasCompactSupport (fun x : ℝ^3 ↦ |kirchhoffPotential h (timeSpaceCons t x)| ^ p) :=
    ((kirchhoffPotential_hasForwardSupport hs).hasCompactSupport_slice htpos.le).comp_left
      (g := fun a : ℝ ↦ |a| ^ p) (by simp [Real.zero_rpow (zero_lt_one.trans_le hp).ne'])
  exact kirchhoffFormula_shell_lower_bound (g := fun _ ↦ 0)
    (w := fun x : ℝ^3 ↦ kirchhoffPotential h (timeSpaceCons t x))
    contDiff_const hh (fun _ _ ↦ rfl) hs hR hp (by simp) hH ht
    ((hr.comp hc).integrable_of_hasCompactSupport hk)
    (fun x ↦ by rw [kirchhoffFormula_zero_displacement hh.continuous])

/-- Signed compact data with nonnegative displacement mass and positive velocity
mass give the shell growth estimate for the nonlinear source. -/
theorem semilinear_source_lower_bound {u : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ} {R p t : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : ∀ y : ℝ^3, R < ‖y‖ → g y = 0) (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) (hR : 0 < R)
    (hp : 2 < p) (hG : 0 ≤ ∫ y : ℝ^3, g y) (hH : 0 < ∫ y : ℝ^3, h y)
    (hwave : ∀ s, 0 < s → ∀ x : ℝ^3, waveOperator u (timeSpaceCons s x) =
      |u (timeSpaceCons s x)| ^ p)
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (ht : R ≤ t) :
    shellSourceCoefficient R (∫ y : ℝ^3, h y) p * t ^ (2 - p) ≤
      ∫ x : ℝ^3, |u (timeSpaceCons t x)| ^ p := by
  have htpos : 0 < t := hR.trans_le ht
  have hreg : Continuous (fun z : ℝ ↦ |z| ^ p) := (contDiff_two_abs_rpow hp).continuous
  have hslice : Continuous (fun x : ℝ^3 ↦ u (timeSpaceCons t x)) :=
    hu.continuous.comp (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  have hsupp : HasCompactSupport (fun x : ℝ^3 ↦ |u (timeSpaceCons t x)| ^ p) :=
    (hs.hasCompactSupport_slice htpos.le).comp_left (g := fun a : ℝ ↦ |a| ^ p)
      (by simp [Real.zero_rpow (by linarith : p ≠ 0)])
  have hint : Integrable (fun x : ℝ^3 ↦ |u (timeSpaceCons t x)| ^ p) :=
    (hreg.comp hslice).integrable_of_hasCompactSupport hsupp
  exact kirchhoffFormula_shell_lower_bound (w := fun x : ℝ^3 ↦ u (timeSpaceCons t x))
    (R := R) (p := p) (t := t) hg hh hgs hhs hR (by linarith) hG hH ht hint
    (fun x ↦ kirchhoffFormula_le_of_nonneg_source (f := fun z : ℝ^4 ↦ |u z| ^ p)
      hu ((contDiff_two_abs_rpow hp).comp hu)
      hg hh hwave hposition hinitial (fun _ _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) htpos.le x)

end WaveEquation.SmallData
