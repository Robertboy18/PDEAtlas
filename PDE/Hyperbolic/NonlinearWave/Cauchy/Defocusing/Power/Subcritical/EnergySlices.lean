/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.SpatialSupport
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder.Continuous
import PDE.Analysis.Calculus.CompactLpCurry

/-!
# Energy representatives of finite-speed C¹ trajectories

A common compact spatial support makes each continuous first derivative an L²
function. Joint continuity gives continuity in L², and the finite C¹ Sobolev
constructor identifies the spatial derivatives with the weak derivatives.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open PDE SobolevSpace SobolevSpace.GraphSpace
open scoped Topology ENNReal Sobolev Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A finite-speed C¹ field with its ordinary compact initial velocity has
continuous H¹ and L² representatives on every shorter closed time interval. -/
theorem exists_continuous_energy_representatives_of_forward_support {b L S R : ℝ} (hb : 0 < b)
    (hSL : S < L) {u : ℝ × ℝ^3 → ℝ} (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) {h : ℝ^3 → ℝ}
    (hhs : HasCompactSupport h) (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) :
    ∃ q : Icc 0 S → W^{1,2}((univ : Set (ℝ^3))),
      ∃ v : Icc 0 S → Lp ℝ 2 (domainMeasure 3 univ),
        Continuous q ∧ Continuous v ∧ ∀ t : Icc 0 S,
          (wkpBaseCoordinateCLM (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
            (fun x ↦ u (t, x)) ∧
          (∀ i : Fin 3, (wkpCoordinateCLM (singleDerivIndex 3 i) (q t) : ℝ^3 → ℝ)
            =ᵐ[domainMeasure 3 univ] ∂[i] (fun x ↦ u (t, x))) ∧
          (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
            fun x ↦ fderiv ℝ u (t, x) (1, 0) := by
  let J := Icc 0 S
  let O : Set (ℝ × ℝ^3) := {p | -b < p.1 ∧ p.1 < L}
  have hO : IsOpen O := (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  have hm (t : J) (x : ℝ^3) : (t.val, x) ∈ O :=
    ⟨by linarith [t.property.1], t.property.2.trans_lt hSL⟩
  have hreg (t : J) : ContDiff ℝ 1 (fun x : ℝ^3 ↦ u (t, x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hu.contDiffAt (hO.mem_nhds (hm t x))).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hc : Continuous (fun z : J × ℝ^3 ↦ u (z.1, z.2)) := hu.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun z ↦ hm z.1 z.2)
  have hdc : Continuous (fun z : J × ℝ^3 ↦ fderiv ℝ u (z.1, z.2)) :=
    (hu.continuousOn_fderiv_of_isOpen hO le_rfl).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun z ↦ hm z.1 z.2)
  have hdspace (t : J) (x : ℝ^3) (i : Fin 3) : (∂[i] (fun y : ℝ^3 ↦ u (t, y))) x =
        fderiv ℝ u (t, x) (0, EuclideanSpace.single i 1) := by
    have hd := ((hu.contDiffAt (hO.mem_nhds (hm t x))).differentiableAt
      one_ne_zero).hasFDerivAt.comp x ((hasFDerivAt_const (t : ℝ) x).prodMk (hasFDerivAt_id x))
    change fderiv ℝ (fun y : ℝ^3 ↦ u (t, y)) x (EuclideanSpace.single i 1) = _
    change HasFDerivAt (fun y : ℝ^3 ↦ u (t, y)) _ x at hd
    rw [hd.fderiv]
    rfl
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  let K : Compacts (ℝ^3) := ⟨Metric.closedBall 0 (max (R + S) Rh), isCompact_closedBall _ _⟩
  have : IsFiniteMeasure ((domainMeasure 3 univ).restrict (K : Set (ℝ^3))) :=
    isFiniteMeasure_restrict.mpr K.isCompact.measure_ne_top
  have hK (x : ℝ^3) (hx : x ∉ K) : max (R + S) Rh < ‖x‖ := by
    change x ∉ Metric.closedBall 0 (max (R + S) Rh) at hx
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hzero (t : J) (x : ℝ^3) (hx : x ∉ K) : u (t, x) = 0 := by
    apply hsupp (t, x) ⟨t.property.1, t.property.2.trans_lt hSL⟩
    exact (add_le_add (le_refl R) t.property.2).trans_lt ((le_max_left _ _).trans_lt (hK x hx))
  have hvzero (t : J) (x : ℝ^3) (hx : x ∉ K) : fderiv ℝ u (t, x) (1, 0) = 0 := by
    by_cases ht : (t : ℝ) = 0
    · have hd := ((hu.contDiffAt (hO.mem_nhds (hm t x))).differentiableAt
        one_ne_zero).hasFDerivAt.comp_hasDerivAt (t : ℝ)
        ((hasDerivAt_id (t : ℝ)).prodMk (hasDerivAt_const (t : ℝ) x))
      have he : fderiv ℝ u (t, x) (1, 0) = h x := by
        apply hd.unique
        simpa only [ht, Function.comp_def, id_eq] using hvel x
      rw [he]
      exact hhR x ((le_max_right _ _).trans (hK x hx).le)
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have hxR : R + (t : ℝ) < ‖x‖ := (add_le_add (le_refl R) t.property.2).trans_lt
          ((le_max_left _ _).trans_lt (hK x hx))
      have he : u =ᶠ[𝓝 ((t : ℝ), x)] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds htpos,
          (isOpen_lt continuous_fst continuous_const).mem_nhds (t.property.2.trans_lt hSL),
          (isOpen_lt (continuous_const.add continuous_fst) continuous_snd.norm).mem_nhds hxR]
          with p hp0 hpL hpR
        exact hsupp p ⟨hp0.le, hpL⟩ hpR
      rw [he.fderiv_eq]
      simp
  have hpartial (i : Fin 3) : Continuous (fun z : J × ℝ^3 ↦
      (∂[i] (fun x : ℝ^3 ↦ u (z.1, x))) z.2) := by
    simpa only [hdspace] using
      hdc.clm_apply (continuous_const (y := (0, EuclideanSpace.single i (1 : ℝ))))
  obtain ⟨q, hq, hqae⟩ := exists_continuous_firstOrder_of_common_compact_support (p := 2)
      isOpen_univ K hc hreg hpartial hzero
  have hvc : Continuous (fun z : J × ℝ^3 ↦ fderiv ℝ u (z.1, z.2) (1, 0)) :=
    hdc.clm_apply continuous_const
  have hvMem (t : J) : MemLp (fun x : ℝ^3 ↦ fderiv ℝ u (t, x) (1, 0)) 2 (domainMeasure 3 univ) :=
    (hvc.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro K.isCompact (hvzero t))
  let v (t : J) := (hvMem t).toLp (fun x : ℝ^3 ↦ fderiv ℝ u (t, x) (1, 0))
  have hvae (t : J) : (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
      fun x ↦ fderiv ℝ u (t, x) (1, 0) := (hvMem t).coeFn_toLp
  exact ⟨q, v, hq, continuous_Lp_of_common_compact_support K hvc hvzero hvae,
    fun t ↦ ⟨(hqae t).1, (hqae t).2, hvae t⟩⟩


/-- Arbitrary compact C³ displacement and C² velocity construct a
signed-power integral trajectory whose displacement and ordinary velocity
are continuous energy-space curves on every shorter closed time interval. -/
theorem exists_signedPower_energy_trajectory_of_compact_data {r : ℝ} (hr : 1 ≤ r) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ T M R : ℝ, 0 < T ∧ 0 ≤ M ∧ ∃ u : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 u {p | |p.1| < T} ∧
      (∀ x : ℝ^3, u (0, x) = g x) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |u p| ≤ M) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → R + p.1 < ‖p.2‖ → u p = 0) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
        u p = cauchyFreeField g h p + WaveEquation.oddDuhamelSolution 0
          (fun z : ℝ^4 ↦ -Real.signedPower r (u (PDE.Common.timeSpaceContinuousLinearEquiv 3 z)))
          (PDE.Common.timeSpaceCons p.1 p.2)) ∧
      (∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        ∀ t ∈ Ioo 0 T,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t) ∧
      ∀ S : ℝ, S < T → ∃ q : Icc 0 S → W^{1,2}((univ : Set (ℝ^3))),
        ∃ v : Icc 0 S → Lp ℝ 2 (domainMeasure 3 univ),
          Continuous q ∧ Continuous v ∧ ∀ t : Icc 0 S,
            (wkpBaseCoordinateCLM (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
              (fun x ↦ u (t, x)) ∧
            (∀ i : Fin 3, (wkpCoordinateCLM (singleDerivIndex 3 i) (q t) : ℝ^3 → ℝ)
              =ᵐ[domainMeasure 3 univ] ∂[i] (fun x ↦ u (t, x))) ∧
            (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
              fun x ↦ fderiv ℝ u (t, x) (1, 0) := by
  obtain ⟨T, M, R, hT, hM, u, hu, hpos, hvel, hB, hsupp, heq, hw⟩ :=
    exists_supported_signedPower_weak_trajectory_of_compact_data hr hg hh hgs hhs
  refine ⟨T, M, R, hT, hM, u, hu, hpos, hvel, hB, hsupp, heq, hw, ?_⟩
  intro S hST
  exact exists_continuous_energy_representatives_of_forward_support hT hST
    (hu.mono (fun _ hp ↦ abs_lt.mpr hp)) hhs hvel hsupp

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
