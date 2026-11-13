/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespanData
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.WeakCoupling.Power
import CAS.ExactTactic

/-!
# Small-amplitude waves from varying Cauchy profiles

The initial profiles may vary with the coupling parameter. A uniformly bounded,
jointly C¹ family of free waves gives coefficient-one signed-power waves
after amplitude rescaling. Their normalized fields and first derivatives approach
the limiting free wave. Fixed compact profiles are a direct special case.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

private theorem cauchyFreeField_const_mul {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : Continuous h)
    (c : ℝ) (p : ℝ × ℝ^3) :
    cauchyFreeField (fun x ↦ c * g x) (fun x ↦ c * h x) p = c * cauchyFreeField g h p := by
  have hpot (f : ℝ^3 → ℝ) : kirchhoffPotential (fun x ↦ c * f x) =
      fun z ↦ c * kirchhoffPotential f z := by
    funext z
    simp only [kirchhoffPotential, spaceTimeUncurry, unitSphereAverage, integral_const_mul]
    cas
  unfold cauchyFreeField
  rw [kirchhoffFormula_eq_potentials (g := fun x ↦ c * g x) (h := fun x ↦ c * h x)
      (contDiff_const.mul hg) (continuous_const.mul hh),
    kirchhoffFormula_eq_potentials hg hh, hpot, hpot]
  simp only [← smul_eq_mul, partialDeriv_const_smul]
  simp only [smul_eq_mul, mul_add]

private theorem signedPower_mul_amplitude {r κ : ℝ} (hr : 1 < r) (z : ℝ) :
    Real.signedPower r ((κ ^ 2) ^ (r - 1)⁻¹ * z) = (κ ^ 2) ^ (r - 1)⁻¹ * κ ^ 2 *
      Real.signedPower r z := by
  have ha : 0 ≤ (κ ^ 2) ^ (r - 1)⁻¹ := Real.rpow_nonneg (sq_nonneg κ) _
  unfold Real.signedPower
  rw [abs_mul, abs_of_nonneg ha, Real.mul_rpow ha (abs_nonneg z),
    Real.rpow_inv_rpow (sq_nonneg κ) (sub_pos.mpr hr).ne']
  cas

/-- A jointly regular, uniformly bounded family of free Cauchy waves generates
small-amplitude coefficient-one nonlinear waves on the same finite interval.
Both initial traces and the tested PDE use the varying profiles; the
normalized fields and their first derivatives approach the limiting free wave. -/
theorem exists_smallAmplitude_tested_trajectory_of_bounded_free_family {r S : ℝ} (hr : 1 < r)
    (hS : 0 < S) {g h : ℝ → ℝ^3 → ℝ} (hg : ∀ κ, ContDiff ℝ 3 (g κ)) (hh : ∀ κ, ContDiff ℝ 2 (h κ))
    (hH : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ^3) ↦ cauchyFreeField (g z.1) (h z.1) z.2)) {B : ℝ}
    (hB : 0 ≤ B)
    (hbound : ∀ κ : ℝ, |κ| ≤ 1 → ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S →
      |cauchyFreeField (g κ) (h κ) p| ≤ B) :
    let ε : ℝ → ℝ := fun κ ↦ (κ ^ 2) ^ (r - 1)⁻¹
    ∃ δ : ℝ, 0 < δ ∧ ∃ v : ℝ → (ℝ × ℝ^3) → ℝ,
      ContDiffOn ℝ 1 (Function.uncurry v) {z | |z.1| < δ ∧ |z.2.1| < S + 1} ∧
      (∀ κ : ℝ, |κ| < δ →
        ContDiffOn ℝ 1 (fun p ↦ ε κ * v κ p) {p | |p.1| < S + 1} ∧
        (∀ x : ℝ^3, ε κ * v κ (0, x) = ε κ * g κ x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ ε κ * v κ (t, x)) (ε κ * h κ x) 0) ∧
        (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S →
          ε κ * v κ p = cauchyFreeField (fun x ↦ ε κ * g κ x) (fun x ↦ ε κ * h κ x) p +
            oddDuhamelSolution 0
              (fun z : ℝ^4 ↦ -Real.signedPower r
                (ε κ * v κ (timeSpaceContinuousLinearEquiv 3 z)))
              (timeSpaceCons p.1 p.2)) ∧
        ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 S,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, ε κ * v κ (s, x) * φ x))
            ((∫ x : ℝ^3, ε κ * v κ (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (ε κ * v κ (t, x)) * φ x) t) ∧
      TendstoLocallyUniformly v (cauchyFreeField (g 0) (h 0)) (𝓝 0) ∧
      TendstoLocallyUniformly (fun κ p ↦ fderiv ℝ (v κ) p)
        (fderiv ℝ (cauchyFreeField (g 0) (h 0))) (𝓝 0) := by
  intro ε
  have hg2 (κ : ℝ) : ContDiff ℝ 2 (g κ) := (hg κ).of_le (by norm_num)
  have hh1 (κ : ℝ) : ContDiff ℝ 1 (h κ) := (hh κ).of_le (by norm_num)
  have hg1 (κ : ℝ) : ContDiff ℝ 1 (g κ) := (hg κ).of_le (by norm_num)
  obtain ⟨δ, hδ, _, hfamily⟩ := exists_weakCoupling_signedPower_trajectory hr.le hS.le hB
  obtain ⟨v, a, hv, ha, heq, _, hrem, hvlim, hdlim⟩ :=
    hfamily (fun z ↦ cauchyFreeField (g z.1) (h z.1) z.2) hH hbound
  refine ⟨δ, hδ, v, hv, ?_, hvlim, hdlim⟩
  intro κ hκ
  have hL : 0 < S + 1 := by linarith
  have htL {t : ℝ} (ht : t ∈ Icc 0 S) : |t| < S + 1 := by
    rw [abs_of_nonneg ht.1]
    linarith [ht.2]
  have hvs : ContDiffOn ℝ 1 (v κ) {p : ℝ × ℝ^3 | |p.1| < S + 1} :=
    hv.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨hκ, hp⟩)
  have hus : ContDiffOn ℝ 1 (fun p ↦ ε κ * v κ p)
      {p : ℝ × ℝ^3 | |p.1| < S + 1} := contDiffOn_const.mul hvs
  have hu0 (x : ℝ^3) : ε κ * v κ (0, x) = ε κ * g κ x := by
    rw [heq κ (0, x) hκ (by simpa using hL)]
    simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero,
      cauchyFreeField_initial_position]
  have hut (x : ℝ^3) : HasDerivAt (fun t ↦ ε κ * v κ (t, x)) (ε κ * h κ x) 0 := by
    have hopen : IsOpen {z : ℝ × (ℝ × ℝ^3) | |z.1| < δ ∧ |z.2.1| < S + 1} :=
      (isOpen_lt continuous_fst.abs continuous_const).inter
        (isOpen_lt (continuous_fst.comp continuous_snd).abs continuous_const)
    have hnear := hopen.mem_nhds (x := (κ, (0, x)))
      (show |κ| < δ ∧ |(0 : ℝ)| < S + 1 by simpa using And.intro hκ hL)
    have haf : ContDiffAt ℝ 1 (Function.uncurry a) (κ, (0, x)) := ha.contDiffAt hnear
    have hpath : ContDiffAt ℝ 1 (fun t : ℝ ↦ (κ, (t, x))) 0 :=
      contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const)
    have hac : ContDiffAt ℝ 1 (fun t : ℝ ↦ a κ (t, x)) 0 := by
      simpa only [Function.comp_def, Function.uncurry] using haf.comp 0 hpath
    have hsq : HasDerivAt (fun t : ℝ ↦ (κ * t) ^ 2) 0 0 := by cas
    have hd := (hasDerivAt_cauchyFreeField_initial_velocity (hg2 κ) (hh1 κ) x).fun_add
      (hsq.fun_mul (hac.differentiableAt one_ne_zero).hasDerivAt)
    have hvd : HasDerivAt (fun t ↦ v κ (t, x)) (h κ x) 0 := by
      apply (show HasDerivAt
        (fun t ↦ cauchyFreeField (g κ) (h κ) (t, x) + (κ * t) ^ 2 * a κ (t, x)) (h κ x) 0
          from by simpa using hd).congr_of_eventuallyEq
      filter_upwards [(continuous_id.abs.continuousAt).eventually
        (gt_mem_nhds (by simpa using hL))] with t ht
      exact heq κ (t, x) hκ ht
    exact hvd.const_mul (ε κ)
  have hphysical (p : ℝ × ℝ^3) (hp : p.1 ∈ Icc 0 S) :
      ε κ * v κ p = cauchyFreeField (fun x ↦ ε κ * g κ x) (fun x ↦ ε κ * h κ x) p +
        oddDuhamelSolution 0 (fun z : ℝ^4 ↦ -Real.signedPower r
            (ε κ * v κ (timeSpaceContinuousLinearEquiv 3 z)))
          (timeSpaceCons p.1 p.2) := by
    rw [heq κ p hκ (htL hp), hrem κ p hκ hp, cauchyFreeField_const_mul (hg1 κ) (hh κ).continuous,
      oddDuhamelSolution_zero_eq_normalized _ _ hp.1]
    simp only [timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons]
    have hs (z : ℝ) : -Real.signedPower r (ε κ * z) =
        (ε κ * κ ^ 2) * -Real.signedPower r z := by
      rw [signedPower_mul_amplitude hr]
      cas
    simp_rw [hs, integral_const_mul]
    have hweights (s z : ℝ) : (1 - s) * ((ε κ * κ ^ 2 * z) / unitSphereArea 3) =
        (ε κ * κ ^ 2) * ((1 - s) * (z / unitSphereArea 3)) := by cas
    simp_rw [hweights, integral_const_mul]
    cas
  refine ⟨hus, hu0, hut, hphysical, ?_⟩
  intro φ hφ hφs t ht
  apply hasDerivAt_deriv_integral_of_signedPower_integral_eq hr.le hL
    (contDiff_const.mul (hg κ)) (contDiff_const.mul (hh κ))
    (hus.mono (fun p hp ↦ abs_lt.mpr ⟨hp.1, by linarith [hp.2]⟩))
    (fun p hp ↦ hphysical p ⟨hp.1, hp.2.le⟩) hφ hφs ht

/-- Arbitrary compact Cauchy profiles generate coefficient-one signed-power
waves on any prescribed finite interval at sufficiently small amplitude.
The normalized fields converge locally uniformly with their full first jet.
The spatially tested PDE and both Cauchy traces belong to the constructed waves. -/
theorem exists_smallAmplitude_tested_trajectory_of_compact_data {r S : ℝ} (hr : 1 < r) (hS : 0 < S)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    let ε : ℝ → ℝ := fun κ ↦ (κ ^ 2) ^ (r - 1)⁻¹
    ∃ δ : ℝ, 0 < δ ∧ ∃ v : ℝ → (ℝ × ℝ^3) → ℝ,
      ContDiffOn ℝ 1 (Function.uncurry v) {z | |z.1| < δ ∧ |z.2.1| < S + 1} ∧
      (∀ κ : ℝ, |κ| < δ →
        ContDiffOn ℝ 1 (fun p ↦ ε κ * v κ p) {p | |p.1| < S + 1} ∧
        (∀ x : ℝ^3, ε κ * v κ (0, x) = ε κ * g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ ε κ * v κ (t, x)) (ε κ * h x) 0) ∧
        (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S →
          ε κ * v κ p = cauchyFreeField (fun x ↦ ε κ * g x) (fun x ↦ ε κ * h x) p +
            oddDuhamelSolution 0
              (fun z : ℝ^4 ↦ -Real.signedPower r
                (ε κ * v κ (timeSpaceContinuousLinearEquiv 3 z)))
              (timeSpaceCons p.1 p.2)) ∧
        ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 S,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, ε κ * v κ (s, x) * φ x))
            ((∫ x : ℝ^3, ε κ * v κ (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (ε κ * v κ (t, x)) * φ x) t) ∧
      TendstoLocallyUniformly v (cauchyFreeField g h) (𝓝 0) ∧
      TendstoLocallyUniformly (fun κ p ↦ fderiv ℝ (v κ) p)
        (fderiv ℝ (cauchyFreeField g h)) (𝓝 0) := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  obtain ⟨B, hB, hbound⟩ := exists_bound_cauchyFreeField_of_compact_data hg2 hh1 hgs hhs S
  exact exists_smallAmplitude_tested_trajectory_of_bounded_free_family hr hS
    (fun _ ↦ hg) (fun _ ↦ hh) ((contDiff_one_cauchyFreeField hg2 hh1).comp contDiff_snd)
    hB (fun _ _ p hp ↦ hbound p hp)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
