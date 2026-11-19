/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.SecondDirectionalDerivative
public import PDE.Analysis.Calculus.SignedPower.Deriv
public import PDE.FDeriv.Euclidean.Laplacian
public import PDE.Hyperbolic.Classical.ForwardLocalization
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Sign
import CAS.ExactTactic

/-!
# Radial lifting of a characteristic wave

Characteristic derivatives determine the radial wave operator. The signed-quadratic branch and
exact traces transfer to physical backward cones.
-/

@[expose] public noncomputable section

section

open Set Filter
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

private theorem second_deriv_affine {W : Parameter → ℝ} (hW : ContDiff ℝ 2 W) (p v : Parameter)
    (t : ℝ) :
    deriv (deriv (fun s : ℝ ↦ W (p + s • v))) t = fderiv ℝ (fderiv ℝ W) (p + t • v) v v := by
  have hline : (fun s : ℝ ↦ W (p + t • v + s • v)) =
      (fun s : ℝ ↦ W (p + (t + s) • v)) := by
    simp only [add_smul, add_assoc]
  have hd := PDE.Analysis.secondDirectionalDerivative_eq_fderiv (hW.contDiffAt (x := p + t • v)) v
  unfold PDE.Analysis.secondDirectionalDerivative at hd
  rw [hline] at hd
  have hfirst : deriv (fun s : ℝ ↦ W (p + (t + s) • v)) =
      fun s : ℝ ↦ deriv (fun q : ℝ ↦ W (p + q • v)) (t + s) :=
    funext (deriv_comp_const_add (fun q : ℝ ↦ W (p + q • v)) t)
  rw [hfirst, deriv_comp_const_add, add_zero] at hd
  exact hd

/-- Mixed characteristic differentiation equals the Hessian in the two
coordinate directions. -/
theorem mixed_characteristic_deriv_eq_fderiv {W : Parameter → ℝ} (hW : ContDiff ℝ 2 W) (a b ε : ℝ) :
    deriv (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) a) b =
      fderiv ℝ (fderiv ℝ W) (a, b, ε) (0, 1, 0) (1, 0, 0) := by
  have hfirst : (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) a) =
      (fun t : ℝ ↦ fderiv ℝ W (a, t, ε) (1, 0, 0)) := by
    funext t
    exact deriv_polynomial_goursat_first_eq_fderiv (hW.of_le (by norm_num)) a t ε
  rw [hfirst]
  have hpath : HasDerivAt (fun t : ℝ ↦ (a, t, ε)) (0, 1, 0) b :=
    (hasDerivAt_const b a).prodMk ((hasDerivAt_id b).prodMk (hasDerivAt_const b ε))
  have hD := ((hW.fderiv_right (m := 1) (by norm_num)).differentiable_one
    (a, b, ε)).hasFDerivAt.comp_hasDerivAt b hpath
  simpa only [Function.comp_def, add_zero, map_zero] using
    (hD.clm_apply (hasDerivAt_const b (1, 0, 0))).deriv

/-- The characteristic variables `a=t+r-1`, `b=t-r+1` turn the radial
one-dimensional wave operator into four times the mixed derivative. -/
theorem time_radius_difference_eq_mixed {W : Parameter → ℝ} (hW : ContDiff ℝ 2 W) (t r ε : ℝ) :
    deriv (deriv (fun s : ℝ ↦ W (s + r - 1, s - r + 1, ε))) t -
      deriv (deriv (fun s : ℝ ↦ W (t + s - 1, t - s + 1, ε))) r =
      4 * deriv (fun b : ℝ ↦ deriv (fun a : ℝ ↦ W (a, b, ε)) (t + r - 1)) (t - r + 1) := by
  have htline : (fun s : ℝ ↦ W (s + r - 1, s - r + 1, ε)) =
      (fun s : ℝ ↦ W ((r - 1, 1 - r, ε) + s • (1, 1, 0))) := by
    funext s
    congr 1
    ext <;> dsimp <;> cas
  have hrline : (fun s : ℝ ↦ W (t + s - 1, t - s + 1, ε)) =
      (fun s : ℝ ↦ W ((t - 1, t + 1, ε) + s • (1, -1, 0))) := by
    funext s
    congr 1
    ext <;> dsimp <;> cas
  have htp : (r - 1, 1 - r, ε) + t • (1, 1, 0) = (t + r - 1, t - r + 1, ε) := by
    ext <;> dsimp <;> cas
  have hrp : (t - 1, t + 1, ε) + r • (1, -1, 0) = (t + r - 1, t - r + 1, ε) := by
    ext <;> dsimp <;> cas
  rw [htline, hrline, second_deriv_affine hW, second_deriv_affine hW, htp, hrp,
    mixed_characteristic_deriv_eq_fderiv hW]
  have hplus : ((1, 1, 0) : Parameter) = (1, 0, 0) + (0, 1, 0) := by norm_num
  have hminus : ((1, -1, 0) : Parameter) = (1, 0, 0) - (0, 1, 0) := by norm_num
  rw [hplus, hminus]
  simp only [map_add, map_sub, add_apply, sub_apply]
  have hsymm := (hW.contDiffAt (x := (t + r - 1, t - r + 1, ε))).isSymmSndFDerivAt
    (by norm_num) (1, 0, 0) (0, 1, 0)
  rw [hsymm]
  ring

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter PDE.Common
open scoped Topology ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- Radial lifting in the characteristic coordinates centered on radius one. -/
def radialGoursatField (W : Parameter → ℝ) (ε : ℝ) (z : SpaceTime 3) : ℝ :=
  W (time z + ‖spatialPart z‖ - 1, time z - ‖spatialPart z‖ + 1, ε) /
    ‖spatialPart z‖

/-- The radial lift preserves finite differentiability away from the spatial origin. -/
theorem contDiffAt_radialGoursatField {W : Parameter → ℝ} {k : ℕ∞ω} (hW : ContDiff ℝ k W) (ε : ℝ)
    {z : SpaceTime 3} (hz : spatialPart z ≠ 0) :
    ContDiffAt ℝ k (radialGoursatField W ε) z := by
  have ht : ContDiff ℝ k (time : SpaceTime 3 → ℝ) := (timeCLM 3).contDiff
  have hx : ContDiff ℝ k (spatialPart : SpaceTime 3 → ℝ^3) := by
    have heq : (spatialPartCLM 3 : SpaceTime 3 → ℝ^3) = spatialPart :=
      funext (spatialPartCLM_eq_spatialPart 3)
    rw [← heq]
    exact (spatialPartCLM 3).contDiff
  have hn : ContDiffAt ℝ k (fun q : SpaceTime 3 ↦ ‖spatialPart q‖) z :=
    (contDiffAt_norm ℝ hz).comp z hx.contDiffAt
  have hp : ContDiffAt ℝ k (fun q : SpaceTime 3 ↦
      (time q + ‖spatialPart q‖ - 1, time q - ‖spatialPart q‖ + 1, ε)) z :=
    ((ht.contDiffAt.add hn).sub contDiffAt_const).prodMk
      (((ht.contDiffAt.sub hn).add contDiffAt_const).prodMk contDiffAt_const)
  exact (hW.contDiffAt.comp z hp).div hn (norm_ne_zero_iff.mpr hz)

/-- The physical wave operator of the radial lift is four times the mixed
characteristic derivative divided by the radius. -/
theorem waveOperator_radialGoursatField {W : Parameter → ℝ} (hW : ContDiff ℝ 2 W) (ε t : ℝ)
    {x : ℝ^3} (hx : x ≠ 0) :
    WaveEquation.waveOperator (radialGoursatField W ε) (timeSpaceCons t x) =
      4 / ‖x‖ * deriv (fun b : ℝ ↦ deriv (fun a : ℝ ↦ W (a, b, ε)) (t + ‖x‖ - 1))
      (t - ‖x‖ + 1) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu := contDiffAt_radialGoursatField hW ε
    (z := timeSpaceCons t x) (by simpa using hx)
  rw [WaveEquation.waveOperator_timeSpaceCons_of_contDiffAt hu]
  simp only [radialGoursatField, time, timeSpaceCons_zero, spatialPart_timeSpaceCons]
  have hprofile : ContDiff ℝ 2 (fun r : ℝ ↦ W (t + r - 1, t - r + 1, ε)) :=
    hW.comp (((contDiff_const.add contDiff_id).sub contDiff_const).prodMk
      (((contDiff_const.sub contDiff_id).add contDiff_const).prodMk contDiff_const))
  have hquot : ContDiffAt ℝ 2 (fun r : ℝ ↦ W (t + r - 1, t - r + 1, ε) / r) ‖x‖ :=
    hprofile.contDiffAt.div contDiffAt_id hr
  have hlap := EuclideanLaplacian.laplacian_radial
    (fun r : ℝ ↦ W (t + r - 1, t - r + 1, ε) / r) x hx hquot
  simp only [Function.comp_def] at hlap
  rw [hlap, PDE.CoordinateSystems.radialLaplacian_three_div hprofile.contDiffAt hr]
  simp only [div_eq_mul_inv, deriv_mul_const_field']
  have heq := time_radius_difference_eq_mixed hW t ‖x‖ ε
  generalize deriv (deriv (fun s : ℝ ↦ W (s + ‖x‖ - 1, s - ‖x‖ + 1, ε))) t = A at *
  generalize deriv (deriv (fun s : ℝ ↦ W (t + s - 1, t - s + 1, ε))) ‖x‖ = B at *
  generalize deriv (fun b : ℝ ↦ deriv (fun a : ℝ ↦ W (a, b, ε))
    (t + ‖x‖ - 1)) (t - ‖x‖ + 1) = C at *
  rw [← sub_mul, heq]
  ring

/-- A signed quadratic mixed equation becomes the signed quadratic physical
wave equation for the same lifted field. -/
theorem radialGoursatField_signed_quadratic {W : Parameter → ℝ} (hW : ContDiff ℝ 2 W) (ε t : ℝ)
    {x : ℝ^3} (hx : x ≠ 0)
    (hmixed : HasDerivAt (fun b : ℝ ↦ deriv (fun a : ℝ ↦ W (a, b, ε)) (t + ‖x‖ - 1))
      (-Real.signedPower 2 (W (t + ‖x‖ - 1, t - ‖x‖ + 1, ε)) /
      (4 * (1 + ((t + ‖x‖ - 1) - (t - ‖x‖ + 1)) / 2))) (t - ‖x‖ + 1)) :
    WaveEquation.waveOperator (radialGoursatField W ε) (timeSpaceCons t x) +
      Real.signedPower 2 (radialGoursatField W ε (timeSpaceCons t x)) = 0 := by
  rw [waveOperator_radialGoursatField hW ε t hx, hmixed.deriv]
  simp only [radialGoursatField, time, timeSpaceCons_zero, spatialPart_timeSpaceCons,
    Real.signedPower, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    abs_div, abs_of_nonneg (norm_nonneg x)]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  generalize W (t + ‖x‖ - 1, t - ‖x‖ + 1, ε) = z
  generalize |z| = q
  generalize ‖x‖ = r at *
  cas using hr

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter PDE.Common
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- A closed backward cone with vertex on `t+|x|=1` lies between the two
characteristic levels `-2T≤a≤0` and `0≤b≤2T`. -/
theorem backwardCone_characteristic_bounds {T s : ℝ} {x y : ℝ^3} (hx : T + ‖x‖ = 1)
    (hs : s ∈ Icc 0 T) (hy : y ∈ Metric.closedBall x (T - s)) :
    -2 * T ≤ s + ‖y‖ - 1 ∧ s + ‖y‖ - 1 ≤ 0 ∧ 0 ≤ s - ‖y‖ + 1 ∧ s - ‖y‖ + 1 ≤ 2 * T ∧
      1 - 2 * T ≤ ‖y‖ ∧ ‖y‖ ≤ 1 := by
  have hdist : dist y x ≤ T - s := hy
  have hup : ‖y‖ ≤ dist y x + ‖x‖ := by
    simpa only [dist_zero_right] using dist_triangle y x 0
  have hlo : ‖x‖ ≤ dist y x + ‖y‖ := by
    simpa only [dist_zero_right, dist_comm] using dist_triangle x y 0
  constructor
  · linarith [hs.1]
  constructor
  · linarith
  constructor
  · linarith [hs.1]
  constructor
  · linarith
  constructor <;> linarith [hs.1]

/-- The zero characteristic supplies the mixed equation on the edge where
the one-sided negative branch meets zero. -/
theorem mixed_signed_quadratic_on_zero_characteristic {W : Parameter → ℝ} {ε η b : ℝ}
    (hzero : ∀ b ∈ Ioo (-η) η, W (0, b, ε) = 0 ∧ HasDerivAt (fun a : ℝ ↦ W (a, b, ε)) ε 0)
    (hb : b ∈ Ioo (-η) η) :
    HasDerivAt (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) 0)
      (-Real.signedPower 2 (W (0, b, ε)) / (4 * (1 + (0 - b) / 2))) b := by
  have he : (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) 0) =ᶠ[𝓝 b]
      fun _ : ℝ ↦ ε := by
    filter_upwards [isOpen_Ioo.mem_nhds hb] with t ht
    exact (hzero t ht).2.deriv
  rw [(hzero b hb).1, Real.signedPower_zero, neg_zero, zero_div]
  exact (hasDerivAt_const b ε).congr_of_eventuallyEq he

/-- On a sufficiently short closed backward cone, the radial lift
satisfies the signed quadratic wave equation, including the zero edge. -/
theorem radialGoursatField_signed_quadratic_on_cone {W : Parameter → ℝ} (hW : ContDiff ℝ 2 W)
    {ε η T : ℝ}
    (hzero : ∀ b ∈ Ioo (-η) η, W (0, b, ε) = 0 ∧ HasDerivAt (fun a : ℝ ↦ W (a, b, ε)) ε 0)
    (hmixed : ∀ a ∈ Ioo (-η) 0, ∀ b ∈ Ioo (-η) η, HasDerivAt
      (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) a) (-Real.signedPower 2 (W (a, b, ε)) /
      (4 * (1 + (a - b) / 2))) b)
    (hTη : 2 * T < η) (hTsmall : T < 1 / 4) {x : ℝ^3} (hx : T + ‖x‖ = 1) {s : ℝ}
    (hs : s ∈ Icc 0 T) {y : ℝ^3} (hy : y ∈ Metric.closedBall x (T - s)) :
    WaveEquation.waveOperator (radialGoursatField W ε) (timeSpaceCons s y) +
      Real.signedPower 2 (radialGoursatField W ε (timeSpaceCons s y)) = 0 := by
  have hT : 0 ≤ T := hs.1.trans hs.2
  obtain ⟨halow, haup, hblow, hbup, hradlow, _⟩ := backwardCone_characteristic_bounds hx hs hy
  have hb : s - ‖y‖ + 1 ∈ Ioo (-η) η := ⟨by linarith, hbup.trans_lt hTη⟩
  have hyrad : 0 < ‖y‖ := by linarith
  apply radialGoursatField_signed_quadratic hW ε s (norm_pos_iff.mp hyrad)
  rcases haup.eq_or_lt with ha | ha
  · rw [ha]
    exact mixed_signed_quadratic_on_zero_characteristic hzero hb
  · exact hmixed _ ⟨by linarith, ha⟩ _ hb

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
