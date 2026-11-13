/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalClassicalMatching
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Localization
import CAS.ExactTactic

/-!
# Exact local matching on an incoming cone

Local uniqueness matches the integral wave with the annular Goursat field. An exact
characteristic zero identifies the full cone derivative with the time derivative.
-/

@[expose] public noncomputable section

section

open Set Filter Metric PDE PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The constructed branch gives an exact incoming nodal segment and exact
transverse velocity for every integral trajectory with its annular data. -/
theorem exists_pos_local_goursat_nodal_trace {W : Parameter → ℝ} (hW : ContDiff ℝ 3 W) {ε η σ L : ℝ}
    (hη : 0 < η) (hσ : 0 < σ) (hL : 0 < L)
    (hzero : ∀ t ∈ Ioo (-η) η, W (0, t, ε) = 0 ∧ HasDerivAt (fun a : ℝ ↦ W (a, t, ε)) ε 0)
    (hmixed : ∀ a ∈ Ioo (-η) 0, ∀ t ∈ Ioo (-η) η, HasDerivAt
      (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) a) (-Real.signedPower 2 (W (a, t, ε)) /
      (4 * (1 + (a - t) / 2))) t)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hdata : ∀ x : ℝ^3, |‖x‖ - 1| < σ → g x = W (‖x‖ - 1, 1 - ‖x‖, ε) / ‖x‖ ∧
      HasDerivAt (fun t : ℝ ↦ W (t + ‖x‖ - 1, t - ‖x‖ + 1, ε) / ‖x‖) (h x) 0)
    {u : ℝ × ℝ^3 → ℝ} (hu : ContDiffOn ℝ 1 u {p | |p.1| < L})
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = cauchyFreeField g h p +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ -Real.signedPower 2
      (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ δ < L ∧ ∀ T ∈ Ioo 0 δ, ∀ x : ℝ^3, T + ‖x‖ = 1 → u (T, x) = 0 ∧
      HasDerivAt (fun t : ℝ ↦ u (t, x)) (ε / ‖x‖) T := by
  obtain ⟨V, hV, hVeq⟩ := exists_contDiff_radialGoursat_extension hW ε
  obtain ⟨d, hd, hdL, hmatch⟩ := exists_pos_eq_on_cone_of_local_classical_signedPower
    (R := 1) (by norm_num : (1 : ℝ) ≤ 2) hL hu.continuousOn hV hg hh hue
  let η₀ := min η σ
  have hη₀ : 0 < η₀ := lt_min hη hσ
  let δ := min d (min (η₀ / 2) (1 / 4)) / 2
  have hδ : 0 < δ := half_pos (lt_min hd (lt_min (half_pos hη₀) (by norm_num)))
  have hδd : δ < d := (half_lt_self (lt_min hd
    (lt_min (half_pos hη₀) (by norm_num)))).trans_le (min_le_left _ _)
  have hδη : δ < η₀ / 2 := (half_lt_self (lt_min hd
    (lt_min (half_pos hη₀) (by norm_num)))).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδquarter : δ < 1 / 4 := (half_lt_self (lt_min hd
    (lt_min (half_pos hη₀) (by norm_num)))).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδL : δ < L := hδd.trans hdL
  refine ⟨δ, hδ, hδquarter, hδL, ?_⟩
  intro T hT x hx
  have hTquarter : T < 1 / 4 := hT.2.trans hδquarter
  have hTη : 2 * T < η := by
    linarith [hT.2.trans hδη, min_le_left η σ]
  have hTσ : 2 * T < σ := by
    linarith [hT.2.trans hδη, min_le_right η σ]
  have hrlo : 1 / 2 < ‖x‖ := by linarith
  have hrhi : ‖x‖ < 3 / 2 := by linarith [hT.1]
  have hbase (y : ℝ^3) (hy : y ∈ closedBall x T) : 1 / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 3 / 2 := by
    obtain ⟨_, _, _, _, hlo, hhi⟩ := backwardCone_characteristic_bounds hx
      (s := 0) ⟨le_rfl, hT.1.le⟩ (by simpa using hy)
    constructor <;> linarith
  have hbaseσ (y : ℝ^3) (hy : y ∈ closedBall x T) : |‖y‖ - 1| < σ := by
    obtain ⟨_, _, _, _, hlo, hhi⟩ := backwardCone_characteristic_bounds hx
      (s := 0) ⟨le_rfl, hT.1.le⟩ (by simpa using hy)
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hpos (y : ℝ^3) (hy : y ∈ closedBall x T) : g y = V (timeSpaceCons 0 y) := by
    have hy' := hbase y hy
    rw [hVeq _ (by simpa using hy'.1) (by simpa using hy'.2)]
    simpa only [radialGoursatField, time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons, zero_add, zero_sub, neg_add_eq_sub] using (hdata y (hbaseσ y hy)).1
  have hvel (y : ℝ^3) (hy : y ∈ closedBall x T) : h y = (∂[0] V) (timeSpaceCons 0 y) := by
    have hy' := hbase y hy
    exact (annular_extension_initial_velocity (hV.of_le (by norm_num)) hVeq
      hy'.1 hy'.2 (hdata y (hbaseσ y hy)).2).symm
  have heq := hmatch (T, x) ⟨hT.1, hT.2.trans hδd⟩ (by dsimp; linarith [hT.1])
    hpos hvel (fun s hs y hy ↦ annular_extension_signed_quadratic_on_cone
      (hW.of_le (by norm_num)) hzero hmixed hVeq hTη hTquarter hx hs hy)
  have haxis : ∀ s ∈ Icc 0 T, u (s, x) = radialGoursatField W ε (timeSpaceCons s x) := by
    intro s hs
    have hs0 : 0 ≤ s / T := div_nonneg hs.1 hT.1.le
    have hs1 : s / T ≤ 1 := (div_le_one hT.1).mpr hs.2
    let q : Cone := ⟨(s / T, 0), ⟨⟨hs0, hs1⟩, by simpa using sub_nonneg.mpr hs1⟩⟩
    have hphysical : physicalPoint (T, x) q = (s, x) := by
      dsimp only [physicalPoint, coneTime, coneSpace, q]
      simp only [smul_zero, add_zero]
      congr 1
      cas using hT.1.ne'
    have he := heq q
    rw [hphysical] at he
    exact he.trans (hVeq _ (by simpa using hrlo.le) (by simpa using hrhi.le))
  have htrace := radialGoursatField_zero_characteristic_trace
    (hW.of_le (by norm_num)) hzero (x := x) (t := T) (by linarith)
    (by constructor <;> linarith [hT.1])
  refine ⟨(haxis T ⟨hT.1.le, le_rfl⟩).trans htrace.1, ?_⟩
  have huat : ContDiffAt ℝ 1 u (T, x) := hu.contDiffAt
    ((isOpen_lt (continuous_fst.abs) continuous_const).mem_nhds
      (by change |T| < L; rw [abs_of_pos hT.1]; exact hT.2.trans hδL))
  have hd : DifferentiableAt ℝ (fun t : ℝ ↦ u (t, x)) T :=
    (huat.differentiableAt one_ne_zero).comp T
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hdwithin : HasDerivWithinAt (fun t : ℝ ↦ u (t, x)) (ε / ‖x‖) (Icc 0 T) T :=
    htrace.2.hasDerivWithinAt.congr_of_mem haxis ⟨hT.1.le, le_rfl⟩
  have hderiv := (uniqueDiffOn_Icc hT.1 T ⟨hT.1.le, le_rfl⟩).eq_deriv _
    hd.hasDerivAt.hasDerivWithinAt hdwithin
  exact hderiv ▸ hd.hasDerivAt

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- Exact vanishing on an incoming cone identifies its full apex-scaling
derivative with the ordinary time derivative, assuming only differentiability. -/
theorem fderiv_cone_direction_eq_time_of_zero_characteristic {u : ℝ × ℝ^3 → ℝ} {δ T : ℝ} {x : ℝ^3}
    (hδ : δ ≤ 1) (hT : T ∈ Ioo 0 δ) (hx : T + ‖x‖ = 1) (hu : DifferentiableAt ℝ u (T, x))
    (hzero : ∀ s ∈ Ioo 0 δ, ∀ y : ℝ^3, s + ‖y‖ = 1 → u (s, y) = 0) :
    fderiv ℝ u (T, x) (T, x) = deriv (fun s : ℝ ↦ u (s, x)) T := by
  have hr : 0 < ‖x‖ := by linarith [hT.2]
  let q : ℝ → ℝ × ℝ^3 := fun s ↦ (s, ((1 - s) / ‖x‖) • x)
  let v : ℝ × ℝ^3 := (1, (-1 / ‖x‖) • x)
  have hqT : q T = (T, x) := by
    dsimp only [q]
    congr 1
    rw [show 1 - T = ‖x‖ by linarith, div_self hr.ne', one_smul]
  have hscalar : HasDerivAt (fun s : ℝ ↦ (1 - s) / ‖x‖) (-1 / ‖x‖) T := by
    generalize ‖x‖ = r at hr ⊢
    cas using hr.ne'
  have hq : HasDerivAt q v T := (hasDerivAt_id T).prodMk (hscalar.smul_const x)
  have hcomp : HasDerivAt (fun s : ℝ ↦ u (q s)) (fderiv ℝ u (T, x) v) T := by
    have hd : HasFDerivAt u (fderiv ℝ u (T, x)) (q T) := hqT.symm ▸ hu.hasFDerivAt
    exact hd.comp_hasDerivAt T hq
  have hnear : (fun s : ℝ ↦ u (q s)) =ᶠ[𝓝 T] fun _ ↦ (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hT] with s hs
    apply hzero s hs
    have hs1 : s < 1 := hs.2.trans_le hδ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hr),
      div_mul_cancel₀ _ hr.ne']
    cas
  have hvzero : fderiv ℝ u (T, x) v = 0 :=
    hcomp.unique ((hasDerivAt_const T (0 : ℝ)).congr_of_eventuallyEq hnear)
  have hvec : (T, x) + ‖x‖ • v = ((1 : ℝ), (0 : ℝ^3)) := by
    apply Prod.ext
    · change T + ‖x‖ * 1 = 1
      simpa only [mul_one] using hx
    · change x + ‖x‖ • ((-1 / ‖x‖) • x) = 0
      rw [smul_smul]
      have hs : ‖x‖ * (-1 / ‖x‖) = -1 := by
        generalize ‖x‖ = r at hr ⊢
        cas using hr.ne'
      rw [hs, neg_one_smul, add_neg_cancel]
  have hfull := congrArg (fderiv ℝ u (T, x)) hvec
  simp only [map_add, map_smul, hvzero, smul_zero, add_zero] at hfull
  have htime := hu.hasFDerivAt.comp_hasDerivAt T ((hasDerivAt_id T).prodMk (hasDerivAt_const T x))
  exact hfull.trans htime.deriv.symm

/-- A known ordinary velocity on the exact incoming zero characteristic is
also the full derivative appearing in the nodal moment. -/
theorem fderiv_cone_direction_of_zero_characteristic {u : ℝ × ℝ^3 → ℝ} {δ T a : ℝ} {x : ℝ^3}
    (hδ : δ ≤ 1) (hT : T ∈ Ioo 0 δ) (hx : T + ‖x‖ = 1) (hu : DifferentiableAt ℝ u (T, x))
    (hzero : ∀ s ∈ Ioo 0 δ, ∀ y : ℝ^3, s + ‖y‖ = 1 → u (s, y) = 0)
    (htime : HasDerivAt (fun s : ℝ ↦ u (s, x)) a T) :
    fderiv ℝ u (T, x) (T, x) = a := by
  rw [fderiv_cone_direction_eq_time_of_zero_characteristic hδ hT hx hu hzero, htime.deriv]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
