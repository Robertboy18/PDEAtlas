/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.EnergyPrimitives
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.EnergySlices
public import PDE.Hyperbolic.NonlinearWave.Cauchy.LinearUniqueness
import PDE.Analysis.Calculus.CompactLpCurry

/-!
# Energy evolution of signed-power integral trajectories

Compact spatial support identifies the negative signed-power force as a continuous
L² curve. The tested PDE supplies the two vector primitives, and linear
wave uniqueness identifies the constructed energy variables with the Duhamel
curve. Constant extension is used only outside the closed comparison interval.

Arbitrary compact C³ displacement and C² velocity supply these hypotheses for
all real exponents at least one. This gives a C¹ energy wave.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open PDE SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational
open scoped Topology ENNReal Sobolev Laplacian InnerProductSpace
open scoped SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp 3 2 univ) (massForm 3) (massForm_coercive 3) massForm_symmetric

/-- The signed-power force of a continuous finite-speed field has
continuous spatial L² representatives on each shorter closed time interval. -/
theorem exists_continuous_signedPower_load_of_forward_support {r b L S R : ℝ} (hr : 0 < r)
    (hb : 0 < b) (hSL : S < L) {u : ℝ × ℝ^3 → ℝ} (hu : ContinuousOn u {p | -b < p.1 ∧ p.1 < L})
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) :
    ∃ F : Icc 0 S → DerivLp 3 2 univ, Continuous F ∧ ∀ t : Icc 0 S,
      (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun x ↦ -Real.signedPower r (u (t, x)) := by
  let J := Icc 0 S
  let K : Compacts (ℝ^3) := ⟨Metric.closedBall 0 (R + S), isCompact_closedBall _ _⟩
  have hc : Continuous (fun z : J × ℝ^3 ↦ u (z.1, z.2)) := hu.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ ⟨by linarith [z.1.property.1], z.1.property.2.trans_lt hSL⟩)
  have hFc : Continuous (fun z : J × ℝ^3 ↦ -Real.signedPower r (u (z.1, z.2))) :=
    ((Real.continuous_signedPower hr).comp hc).neg
  have hzero (t : J) (x : ℝ^3) (hx : x ∉ K) :
      -Real.signedPower r (u (t, x)) = 0 := by
    have hx' : R + S < ‖x‖ := by
      change x ∉ Metric.closedBall 0 (R + S) at hx
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    rw [hsupp (t, x) ⟨t.property.1, t.property.2.trans_lt hSL⟩
      ((add_le_add (le_refl R) t.property.2).trans_lt hx'), Real.signedPower_zero, neg_zero]
  have hmem (t : J) : MemLp (fun x : ℝ^3 ↦ -Real.signedPower r (u (t, x))) 2
      (domainMeasure 3 univ) :=
    (hFc.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro K.isCompact (hzero t))
  let F (t : J) := (hmem t).toLp (fun x : ℝ^3 ↦ -Real.signedPower r (u (t, x)))
  have hfae (t : J) : (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
      fun x ↦ -Real.signedPower r (u (t, x)) := (hmem t).coeFn_toLp
  have : IsFiniteMeasure ((domainMeasure 3 univ).restrict (K : Set (ℝ^3))) :=
    isFiniteMeasure_restrict.mpr K.isCompact.measure_ne_top
  exact ⟨F, continuous_Lp_of_common_compact_support K hFc hzero hfae, hfae⟩


/-- A finite-speed C¹ signed-power field satisfying the tested PDE has
continuous energy variables and force. Their vector primitives and massive
Duhamel representation are conclusions, including both time endpoints. -/
theorem exists_energy_representation_of_signedPower_tested_equation {r b L S R : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) (hS : 0 < S) (hSL : S < L) {u : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) {h : ℝ^3 → ℝ} (hhs : HasCompactSupport h)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0)
    (hwave : ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 L,
      HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
      ((∫ x : ℝ^3, u (t, x) * laplacian φ x) - ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t) :
    ∃ (q : ℝ → H¹(ℝ^3)) (v F : ℝ → DerivLp 3 2 univ),
      Continuous q ∧ Continuous v ∧ Continuous F ∧
      (∀ t ∈ Icc 0 S,
        ((energyTriple 3).inclusion (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
          (fun x ↦ u (t, x)) ∧
        (∀ i : Fin 3, (wkpCoordinateCLM (singleDerivIndex 3 i) (q t) : ℝ^3 → ℝ)
          =ᵐ[domainMeasure 3 univ] ∂[i] (fun x ↦ u (t, x))) ∧
        (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
          (fun x ↦ fderiv ℝ u (t, x) (1, 0)) ∧
        (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
          (fun x ↦ -Real.signedPower r (u (t, x)))) ∧
      (∀ t ∈ Icc 0 S,
        (∫ s in 0..t, v s) = (energyTriple 3).inclusion (q t) -
          (energyTriple 3).inclusion (q 0) ∧
        (∫ s in 0..t, (energyTriple 3).pivotToDual (F s) - gradientForm 3 (q s)) =
          (energyTriple 3).pivotToDual (v t) - (energyTriple 3).pivotToDual (v 0)) ∧
      ∀ t ∈ Icc 0 S, (q t, v t) = C
        ((linearSemigroup 3).realOrbit ((C).symm (q 0, v 0)) t +
          (linearSemigroup 3).duhamel
            (fun s ↦ (C).symm (0, F s + (energyTriple 3).inclusion (q s))) t) := by
  obtain ⟨q₀, v₀, hq₀, hv₀, hae⟩ :=
    exists_continuous_energy_representatives_of_forward_support hb hSL hu hhs hvel hsupp
  obtain ⟨F₀, hF₀, hFae₀⟩ := exists_continuous_signedPower_load_of_forward_support
    (zero_lt_one.trans_le hr) hb hSL hu.continuousOn hsupp
  let q := IccExtend hS.le q₀
  let v := IccExtend hS.le v₀
  let F := IccExtend hS.le F₀
  have hq : Continuous q := hq₀.Icc_extend'
  have hv : Continuous v := hv₀.Icc_extend'
  have hF : Continuous F := hF₀.Icc_extend'
  have hqae (t : ℝ) (ht : t ∈ Icc 0 S) :
      ((energyTriple 3).inclusion (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
        fun x ↦ u (t, x) := by
    rw [show q t = q₀ ⟨t, ht⟩ from IccExtend_of_mem hS.le q₀ ht]
    exact (hae ⟨t, ht⟩).1
  have hvae (t : ℝ) (ht : t ∈ Icc 0 S) : (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
        fun x ↦ fderiv ℝ u (t, x) (1, 0) := by
    rw [show v t = v₀ ⟨t, ht⟩ from IccExtend_of_mem hS.le v₀ ht]
    exact (hae ⟨t, ht⟩).2.2
  have hFae (t : ℝ) (ht : t ∈ Icc 0 S) : (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
        fun x ↦ -Real.signedPower r (u (t, x)) := by
    rw [show F t = F₀ ⟨t, ht⟩ from IccExtend_of_mem hS.le F₀ ht]
    exact hFae₀ ⟨t, ht⟩
  have hi := energy_integral_primitives_of_signedPower_tested_equation
    hr hb hS.le hSL hu hwave hq hv hF hqae hvae hFae
  refine ⟨q, v, F, hq, hv, hF, ?_, hi, ?_⟩
  · intro t ht
    refine ⟨hqae t ht, ?_, hvae t ht, hFae t ht⟩
    rw [show q t = q₀ ⟨t, ht⟩ from IccExtend_of_mem hS.le q₀ ht]
    exact (hae ⟨t, ht⟩).2.1
  · let f := fun s ↦ F s + (energyTriple 3).inclusion (q s)
    have hf : Continuous f := hF.add ((energyTriple 3).inclusion.continuous.comp hq)
    have hacc (s : ℝ) : (energyTriple 3).pivotToDual (f s) - massForm 3 (q s) =
        (energyTriple 3).pivotToDual (F s) - gradientForm 3 (q s) := by
      simp only [f, map_add, gradientForm, sub_apply, GelfandTriple.energyToDual,
        ContinuousLinearMap.comp_apply]
      abel
    exact linear_integral_identification hf (hq.prodMk hv) ((C).symm (q 0, v 0)) hS
      (fun t ht ↦ by
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using (hi t ht).1)
      (fun t ht ↦ by
        simpa only [ContinuousLinearEquiv.apply_symm_apply, hacc] using (hi t ht).2)


/-- Arbitrary compact C³ displacement and C² velocity produce a local
C¹ signed-power wave with both Cauchy traces, finite propagation, and its
energy-space Duhamel representation. This holds for every real exponent at least one. -/
theorem exists_signedPower_energy_representation_of_compact_data {r : ℝ} (hr : 1 ≤ r)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
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
      ∀ S : ℝ, 0 < S → S < T →
      ∃ (q : ℝ → H¹(ℝ^3)) (v F : ℝ → DerivLp 3 2 univ),
        Continuous q ∧ Continuous v ∧ Continuous F ∧
        (∀ t ∈ Icc 0 S,
          ((energyTriple 3).inclusion (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
            (fun x ↦ u (t, x)) ∧
          (∀ i : Fin 3, (wkpCoordinateCLM (singleDerivIndex 3 i) (q t) : ℝ^3 → ℝ)
            =ᵐ[domainMeasure 3 univ] ∂[i] (fun x ↦ u (t, x))) ∧
          (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
            (fun x ↦ fderiv ℝ u (t, x) (1, 0)) ∧
          (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
            (fun x ↦ -Real.signedPower r (u (t, x)))) ∧
        (∀ t ∈ Icc 0 S,
          (∫ s in 0..t, v s) = (energyTriple 3).inclusion (q t) -
            (energyTriple 3).inclusion (q 0) ∧
          (∫ s in 0..t, (energyTriple 3).pivotToDual (F s) - gradientForm 3 (q s)) =
            (energyTriple 3).pivotToDual (v t) - (energyTriple 3).pivotToDual (v 0)) ∧
        ∀ t ∈ Icc 0 S, (q t, v t) = C
          ((linearSemigroup 3).realOrbit ((C).symm (q 0, v 0)) t +
            (linearSemigroup 3).duhamel
              (fun s ↦ (C).symm (0, F s + (energyTriple 3).inclusion (q s))) t) := by
  obtain ⟨T, M, R, hT, hM, u, hu, hpos, hvel, hB, hsupp, heq, hw⟩ :=
    exists_supported_signedPower_weak_trajectory_of_compact_data hr hg hh hgs hhs
  refine ⟨T, M, R, hT, hM, u, hu, hpos, hvel, hB, hsupp, heq, hw, ?_⟩
  intro S hS hST
  exact exists_energy_representation_of_signedPower_tested_equation hr hT hS hST
    (hu.mono (fun _ hp ↦ abs_lt.mpr hp)) hhs hvel hsupp hw

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
