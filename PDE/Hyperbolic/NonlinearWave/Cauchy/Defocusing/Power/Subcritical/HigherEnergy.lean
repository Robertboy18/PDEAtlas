/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.EnergyRepresentation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FiniteInterval
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Regularity.IntegratedTime
import CAS.ExactTactic

/-!
# Higher Sobolev lifts of bounded signed-power energy waves

A cutoff agrees with the reaction along the bounded trajectory.
Finite-interval PDE uniqueness identifies that trajectory with the
first-jet solution, so generator-domain data provide H²/H¹/L² lifts.
Compact C³ displacement and C² velocity give the generator-domain hypothesis for the constructed
local wave. Strong time-integration identifies the higher lifts as the almost-everywhere energy
derivative and gives absolute continuity.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open PDE SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval Laplacian ENNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp 3 2 univ) (massForm 3) (massForm_coercive 3) massForm_symmetric

/-- Compact C² displacement and C¹ velocity give the generator-domain
condition for any energy representatives of these functions. -/
theorem exists_generator_of_compact_cauchy_data {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {q : H¹(ℝ^3)}
    {v : DerivLp 3 2 univ}
    (hq : ((energyTriple 3).inclusion q : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] g)
    (hv : (v : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] h) :
    ∃ Ax : EnergyState 3, (linearSemigroup 3).HasGeneratorAt ((C).symm (q, v)) Ax := by
  have hlift {k : ℕ} {f : ℝ^3 → ℝ} (hf : ContDiff ℝ k f) (hfs : HasCompactSupport f) :
      ∃ U : W^{k,2}(ℝ^3), baseRepresentative U =ᵐ[domainMeasure 3 univ] f := by
    have hmem (a : DerivIndex 3 k) :
        MemLp (iteratedPartialDeriv a.toList f) 2 (domainMeasure 3 univ) :=
      (contDiff_iteratedPartialDeriv_of_le hf a.toList
        a.toList_length_le).continuous.memLp_of_hasCompactSupport
          (hfs.iteratedPartialDeriv a.toList)
    refine ⟨mkWkpSpaceOnOfContDiffMemLpFinite f hf hmem, ?_⟩
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae f hf hmem (baseIndex 3 k)
  obtain ⟨G, hG⟩ := hlift hg hgs
  obtain ⟨H, hH⟩ := hlift hh hhs
  have hqeq : lowerOrderCLM (by decide : 1 ≤ 2) G = q := by
    apply wkpBaseCoordinateCLM_injective isOpen_univ
    apply Lp.ext
    change baseRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) G) =ᵐ[_] baseRepresentative q
    rw [baseRepresentative_lowerOrderCLM]
    exact hG.trans hq.symm
  have hveq : (energyTriple 3).inclusion H = v := Lp.ext (hH.trans hv.symm)
  refine ⟨(C).symm (H, Δ G - wkpBaseCoordinateCLM G), ?_⟩
  simpa only [hqeq, hveq] using hasGeneratorAt_h2 G H


/-- A bounded signed-power energy wave with generator-domain initial data
has bounded higher Sobolev lifts on its finite existence interval.
The acceleration is the Laplacian plus the identified physical L² force.
Both higher time primitives and the almost-everywhere energy derivative
are conclusions. -/
theorem exists_h2_lifts_of_bounded_signedPower_energy_primitives
    {r S M : ℝ} (hr : 1 ≤ r) (hS : 0 ≤ S) (hM : 0 ≤ M)
    {q : ℝ → H¹(ℝ^3)} {v F : ℝ → DerivLp 3 2 univ}
    (hq : Continuous q) (hv : Continuous v)
    {u : ℝ × ℝ^3 → ℝ}
    (hB : ∀ t ∈ Icc 0 S, ∀ x : ℝ^3, |u (t, x)| ≤ M)
    (hqae : ∀ t ∈ Icc 0 S,
      ((energyTriple 3).inclusion (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
        fun x ↦ u (t, x))
    (hFae : ∀ t ∈ Icc 0 S,
      (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
        fun x ↦ -Real.signedPower r (u (t, x)))
    (hi : ∀ t ∈ Icc 0 S,
      (∫ s in 0..t, v s) = (energyTriple 3).inclusion (q t) -
        (energyTriple 3).inclusion (q 0) ∧
      (∫ s in 0..t, (energyTriple 3).pivotToDual (F s) - gradientForm 3 (q s)) =
        (energyTriple 3).pivotToDual (v t) - (energyTriple 3).pivotToDual (v 0))
    {Ax : EnergyState 3}
    (hx : (linearSemigroup 3).HasGeneratorAt ((C).symm (q 0, v 0)) Ax) :
    ∃ (U : ℝ → W^{2,2}(ℝ^3)) (V : ℝ → H¹(ℝ^3)) (A : ℝ → DerivLp 3 2 univ),
      MemLp U ∞ (volume.restrict (Icc 0 S)) ∧
      MemLp V ∞ (volume.restrict (Icc 0 S)) ∧
      MemLp A ∞ (volume.restrict (Icc 0 S)) ∧
      (∀ t ∈ Icc 0 S,
        lowerOrderCLM (by decide : 1 ≤ 2) (U t) = q t ∧
        (energyTriple 3).inclusion (V t) = v t ∧
        (energyTriple 3).pivotToDual (A t) =
          (energyTriple 3).pivotToDual (F t) - gradientForm 3 (q t) ∧
        A t = Δ (U t) + F t) ∧
      (∀ t ∈ Icc 0 S,
        (∫ s in 0..t, V s) = q t - q 0 ∧
        (∫ s in 0..t, A s) = v t - v 0) ∧
      AbsolutelyContinuousOnInterval (fun t ↦ (q t, v t)) 0 S ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 S),
        HasDerivAt (fun s ↦ (q s, v s)) (V t, A t) t := by
  have hs (z : ℝ) : 0 ≤ z * Real.signedPower r z := by
    unfold Real.signedPower
    nlinarith [mul_nonneg (Real.rpow_nonneg (abs_nonneg z) (r - 1)) (sq_nonneg z)]
  obtain ⟨g, K, _, _, hgLip, hmatch, _⟩ := SignCondition.exists_sign_preserving_lipschitz_reaction
      (m := 1) (Real.contDiff_one_signedPower hr) one_ne_zero hs
      (show 0 < M + 1 by linarith)
  let f : (ℝ^3 × ℝ × ℝ) → ℝ := fun z ↦ g z.2.2
  have hf : LipschitzWith K f := by
    simpa only [mul_one, Function.comp_def, f] using hgLip.comp
      (LipschitzWith.prod_snd.comp (LipschitzWith.prod_snd (α := ℝ^3)))
  have hf0 : f 0 = 0 := by
    change g 0 = 0
    rw [hmatch (by simpa using (show 0 ≤ M + 1 by linarith)), Real.signedPower_zero]
  have hreact (t : ℝ) (ht : t ∈ Icc 0 S) :
      FirstJet.reaction hf hf0 (q t, v t) = -F t := by
    apply Lp.ext
    filter_upwards [FirstJet.reaction_apply_ae hf hf0 (q t, v t),
      hqae t ht, hFae t ht, Lp.coeFn_neg (F t)] with x hreactx hqx hFx hneg
    rw [hreactx, hneg]
    change g ((energyTriple 3).inclusion (q t) x) = -(F t x)
    rw [hqx, hFx, neg_neg]
    exact hmatch (by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      using (hB t ht x).trans (le_add_of_nonneg_right zero_le_one))
  have hacc (t : ℝ) (ht : t ∈ Icc 0 S) : FirstJet.acceleration hf hf0 (q t, v t) =
        (energyTriple 3).pivotToDual (F t) - gradientForm 3 (q t) := by
    simp only [FirstJet.acceleration, hreact t ht, map_neg, neg_neg]
  have huOn : FirstJet.IsEnergySolutionOn hf hf0 (q 0, v 0) ⟨S, hS⟩
      (fun t ↦ (q t, v t)) := by
    refine ⟨(hq.prodMk hv).continuousOn, rfl, fun t ht ↦ (hi t ht).1, fun t ht ↦
      (intervalIntegral.integral_congr fun s hs ↦ ?_).trans (hi t ht).2⟩
    rw [uIcc_of_le ht.1] at hs
    exact hacc s ⟨hs.1, hs.2.trans ht.2⟩
  obtain ⟨z, hz⟩ := FirstJet.exists_energySolution hf hf0 (q 0, v 0)
  have heq := huOn.eqOn (hz.on ⟨S, hS⟩)
  obtain ⟨U, V, A, hU, hV, hA, hrep⟩ := hz.exists_memLp_h2_lifts hx S
  have hrepV (t : ℝ) (ht : t ∈ Icc 0 S) := (hrep t ht).2.1
  have hrepA (t : ℝ) (ht : t ∈ Icc 0 S) := (hrep t ht).2.2.1
  have htime := hz.absolutelyContinuous_of_lifts hS hV hA hrepV hrepA
  refine ⟨U, V, A, hU, hV, hA, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hh := hrep t ht
    rw [← heq ht] at hh
    exact ⟨hh.1, hh.2.1, hh.2.2.1.trans (hacc t ht),
      hh.2.2.2.trans (by rw [hreact t ht, sub_neg_eq_add])⟩
  · intro t ht
    have hVint := hz.integral_velocity_lift hV hrepV ht
    have hAint := hz.integral_acceleration_lift hA hrepA ht
    rw [← heq ht] at hVint hAint
    exact ⟨hVint, hAint⟩
  · exact htime.1.congr fun t ht ↦
      (heq (show t ∈ Icc 0 S by simpa only [uIcc_of_le hS] using ht)).symm
  · filter_upwards [htime.2, ae_restrict_mem measurableSet_Ioo] with t hd ht
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact heq (Ioo_subset_Icc_self hs)


/-- Arbitrary compact C³ displacement and C² velocity produce a local
C¹ signed-power wave with both Cauchy traces, finite propagation, and its
energy-space Duhamel representation and bounded H²/H¹/L² lifts. This holds for every real exponent
at least one. -/
theorem exists_signedPower_h2_trajectory_of_compact_data
    {r : ℝ} (hr : 1 ≤ r) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
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
      ∃ (q : ℝ → H¹(ℝ^3)) (v F : ℝ → DerivLp 3 2 univ)
          (U : ℝ → W^{2,2}(ℝ^3)) (V : ℝ → H¹(ℝ^3)) (A : ℝ → DerivLp 3 2 univ),
        Continuous q ∧ Continuous v ∧ Continuous F ∧
        MemLp U ∞ (volume.restrict (Icc 0 S)) ∧
        MemLp V ∞ (volume.restrict (Icc 0 S)) ∧
        MemLp A ∞ (volume.restrict (Icc 0 S)) ∧
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
          lowerOrderCLM (by decide : 1 ≤ 2) (U t) = q t ∧
          (energyTriple 3).inclusion (V t) = v t ∧
          (energyTriple 3).pivotToDual (A t) =
            (energyTriple 3).pivotToDual (F t) - gradientForm 3 (q t) ∧
          A t = Δ (U t) + F t) ∧
        (∀ t ∈ Icc 0 S,
          (∫ s in 0..t, v s) = (energyTriple 3).inclusion (q t) -
            (energyTriple 3).inclusion (q 0) ∧
          (∫ s in 0..t, (energyTriple 3).pivotToDual (F s) - gradientForm 3 (q s)) =
            (energyTriple 3).pivotToDual (v t) - (energyTriple 3).pivotToDual (v 0)) ∧
        (∀ t ∈ Icc 0 S,
          (∫ s in 0..t, V s) = q t - q 0 ∧
          (∫ s in 0..t, A s) = v t - v 0) ∧
        AbsolutelyContinuousOnInterval (fun t ↦ (q t, v t)) 0 S ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 S),
          HasDerivAt (fun s ↦ (q s, v s)) (V t, A t) t) ∧
        ∀ t ∈ Icc 0 S, (q t, v t) = C
          ((linearSemigroup 3).realOrbit ((C).symm (q 0, v 0)) t +
            (linearSemigroup 3).duhamel
              (fun s ↦ (C).symm (0, F s + (energyTriple 3).inclusion (q s))) t) := by
  obtain ⟨T, M, R, hT, hM, u, hu, hpos, hvel, hB, hsupp, heq, hw, henergy⟩ :=
    exists_signedPower_energy_representation_of_compact_data hr hg hh hgs hhs
  refine ⟨T, M, R, hT, hM, u, hu, hpos, hvel, hB, hsupp, heq, hw, fun S hS hST ↦ ?_⟩
  obtain ⟨q, v, F, hq, hv, hF, hae, hi, hmild⟩ := henergy S hS hST
  have hzero : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have hq0 : ((energyTriple 3).inclusion (q 0) : ℝ^3 → ℝ)
      =ᵐ[domainMeasure 3 univ] g := by
    filter_upwards [(hae 0 hzero).1] with x hx
    exact hx.trans (hpos x)
  have hv0 : (v 0 : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] h := by
    filter_upwards [(hae 0 hzero).2.2.1] with x hx
    rw [hx]
    have hO : IsOpen {p : ℝ × ℝ^3 | |p.1| < T} := isOpen_lt continuous_fst.abs continuous_const
    have hm : (0, x) ∈ {p : ℝ × ℝ^3 | |p.1| < T} := by simpa using hT
    have hd := ((hu.contDiffAt (hO.mem_nhds hm)).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    exact hd.unique (hvel x)
  obtain ⟨Ax, hx⟩ := exists_generator_of_compact_cauchy_data
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs hq0 hv0
  obtain ⟨U, V, A, hU, hV, hA, hlift, hstrong, hac, hderiv⟩ :=
    exists_h2_lifts_of_bounded_signedPower_energy_primitives hr hS.le hM hq hv
      (fun t ht x ↦ hB (t, x) ⟨ht.1, ht.2.trans_lt hST⟩)
      (fun t ht ↦ (hae t ht).1) (fun t ht ↦ (hae t ht).2.2.2) hi hx
  exact ⟨q, v, F, U, V, A, hq, hv, hF, hU, hV, hA, hae, hlift, hi, hstrong, hac, hderiv, hmild⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
