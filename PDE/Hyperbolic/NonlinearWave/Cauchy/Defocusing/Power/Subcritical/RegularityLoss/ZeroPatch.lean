/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Topology.UniformConvergence.ZeroSet
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalIntegral.BoundedIdentification
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss.IncomingFamily
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss.IncomingMoment
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Incoming.Cone
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave

/-!
# A bounded incoming wave with positive nodal moment

Compact convergence preserves the full-cone nodal sign. The exact Goursat zero patch gives a
positive moment for the same bounded local wave.
-/

@[expose] public noncomputable section

section

open Set Filter Metric
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- Full first-jet convergence to the constructed compact free baseline gives
positive cone-direction derivatives at every zero on the complete incoming cone. -/
theorem eventually_pos_on_incoming_cone_zeros {v : ℝ → (ℝ × ℝ^3) → ℝ}
    (hlim : TendstoLocallyUniformly v (cauchyFreeField incomingDisplacement incomingVelocity) (𝓝 0))
    (hdlim : TendstoLocallyUniformly (fun κ p ↦ fderiv ℝ (v κ) p)
      (fderiv ℝ (cauchyFreeField incomingDisplacement incomingVelocity)) (𝓝 0)) :
    ∀ᶠ κ : ℝ in 𝓝 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ^3, t + ‖x‖ = 1 → v κ (t, x) = 0 → 0 <
      fderiv ℝ (v κ) (t, x) (t, x) := by
  let H := cauchyFreeField incomingDisplacement incomingVelocity
  let K : Set (ℝ × ℝ^3) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.1 + ‖p.2‖ = 1}
  have hKclosed : IsClosed K := (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_eq (continuous_fst.add continuous_snd.norm) continuous_const)
  have hKsub : K ⊆ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℝ^3) 1 := fun p hp ↦
    ⟨hp.1, by rw [mem_closedBall, dist_zero_right]; linarith [hp.1.1, hp.2]⟩
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).of_isClosed_subset hKclosed hKsub
  have hnorm (p : ℝ × ℝ^3) (hp : p ∈ K) : ‖p‖ ≤ 1 := by
    rw [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hp.1.1]
    exact max_le hp.1.2 (by linarith [hp.1.1, hp.2])
  have hH : ContDiff ℝ 1 H := contDiff_one_cauchyFreeField
    (contDiff_incomingDisplacement.of_le (by norm_num))
    (contDiff_incomingVelocity.of_le (by norm_num))
  have hF : TendstoUniformlyOn v H (𝓝 0) K :=
    tendstoLocallyUniformly_iff_forall_isCompact.mp hlim K hK
  have hDF : TendstoUniformlyOn (fun κ p ↦ fderiv ℝ (v κ) p) (fderiv ℝ H) (𝓝 0) K :=
    tendstoLocallyUniformly_iff_forall_isCompact.mp hdlim K hK
  have hG : TendstoUniformlyOn (fun κ p ↦ fderiv ℝ (v κ) p p)
      (fun p ↦ fderiv ℝ H p p) (𝓝 0) K := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hDF ε hε] with κ hκ p hp
    rw [dist_eq_norm, ← sub_apply]
    exact ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (hnorm p hp))).trans_lt (by simpa only [dist_eq_norm] using hκ p hp)
  have hsign := hK.eventually_pos_on_zeros_of_tendstoUniformlyOn hH.continuous.continuousOn
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_id).continuousOn
    (fun p hp hz ↦ fderiv_incoming_cauchyFreeField_pos_on_cone_zeros hp.1.1 hp.2 hz) hF hG
  filter_upwards [hsign] with κ hκ t ht x hx hz using hκ (t, x) ⟨ht, hx⟩ hz

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter Metric PDE.Analysis PDE.Common WaveEquation
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A jointly regular compact family with zero data at parameter zero has a
uniformly small free wave on every fixed finite strip for small parameters. -/
theorem eventually_abs_cauchyFreeField_lt_of_zero_compact_family {g h : ℝ → ℝ^3 → ℝ}
    (hg : ContDiff ℝ 2 (Function.uncurry g)) (hh : ContDiff ℝ 1 (Function.uncurry h))
    (hg0 : g 0 = 0) (hh0 : h 0 = 0) {K : Set (ℝ^3)} (hK : IsCompact K)
    (hs : ∀ κ : ℝ, ∀ x ∉ K, g κ x = 0 ∧ h κ x = 0) (S : ℝ) {B : ℝ} (hB : 0 < B) :
    ∀ᶠ κ : ℝ in 𝓝 0, ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S → |cauchyFreeField (g κ) (h κ) p| < B := by
  have hH := contDiff_cauchyFreeField_family (k := 1) hg hh
  have hzero (p : ℝ × ℝ^3) : cauchyFreeField (g 0) (h 0) p = 0 := by
    rw [hg0, hh0]
    change spaceTimeUncurry (kirchhoffFormula (fun _ ↦ 0) (fun _ ↦ 0)) _ = 0
    rw [kirchhoffFormula_zero_displacement continuous_const]
    simp [kirchhoffPotential, spaceTimeUncurry, unitSphereAverage]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ^3)
  let C : Set (ℝ × ℝ^3) := Icc 0 S ×ˢ closedBall 0 (R + S)
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hnear : ∀ᶠ κ : ℝ in 𝓝 0, ∀ p ∈ C,
      |cauchyFreeField (g κ) (h κ) p| < B := by
    refine hC.eventually_forall_of_forall_eventually fun p _ ↦ ?_
    apply hH.continuous.abs.continuousAt.eventually_lt_const
    change |cauchyFreeField (g 0) (h 0) p| < B
    simpa only [hzero p, abs_zero] using hB
  filter_upwards [hnear] with κ hκ p hp
  by_cases hx : p.2 ∈ closedBall (0 : ℝ^3) (R + S)
  · exact hκ p ⟨hp, hx⟩
  · have hz (x : ℝ^3) (hx : R < ‖x‖) : g κ x = 0 ∧ h κ x = 0 :=
      hs κ x fun hxK ↦ hx.not_ge (by simpa only [mem_closedBall, dist_zero_right] using hR hxK)
    have hout : R + S < ‖p.2‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    have he := WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport
      ((hg.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id))
      (hh.continuous.comp (continuous_const.prodMk continuous_id))
      (fun x hx ↦ (hz x hx).1) (fun x hx ↦ (hz x hx).2) p.1 hp.1 p.2
      (by linarith [hp.2])
    change kirchhoffFormula (g κ) (h κ) p.2 p.1 = 0 at he
    change |kirchhoffFormula (g κ) (h κ) p.2 p.1| < B
    rwa [he, abs_zero]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped ContDiff Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

/-- Smooth compact data generate a signed-quadratic C¹ tested wave whose
whole incoming nodal moment is positive. All traces and identities concern the
same field. -/
theorem exists_smooth_bounded_quadratic_wave_pos_nodalMoment_with_zero_patch :
    ∃ g h : ℝ^3 → ℝ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      HasCompactSupport g ∧ HasCompactSupport h ∧ ∃ u : (ℝ × ℝ^3) → ℝ,
        ContDiffOn ℝ 1 u {p | |p.1| < 3} ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
        (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 2 →
          u p = cauchyFreeField g h p + oddDuhamelSolution 0
            (fun z : ℝ^4 ↦ -Real.signedPower 2 (u (timeSpaceContinuousLinearEquiv 3 z)))
            (timeSpaceCons p.1 p.2)) ∧
        (∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 2,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower 2 (u (t, x)) * φ x) t) ∧
        (∃ M : ℝ, 0 < M ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 2 → |u p| ≤ M) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo (0 : ℝ) δ, ∀ x : ℝ^3,
          t + ‖x‖ = 1 → u (t, x) = 0) ∧
        0 < nodalMoment 2 (u ∘ timeSpaceContinuousLinearEquiv 3) 0 1 := by
  obtain ⟨_, _, _, _, g, h, hg, hh, _, _, ⟨K, hK, hs⟩, _, d, hd, _, v,
    hactual, hpatch, hlim, hdlim⟩ := exists_smooth_incoming_quadratic_goursat_wave_family
  obtain ⟨M, hM, hMC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 2)
    (4 * ‖WaveEquation.SmallData.Classical.LocalPower.duhamelOperator‖)
  have hbar : M / 2 + 4 * ‖WaveEquation.SmallData.Classical.LocalPower.duhamelOperator‖ *
      M ^ 2 < M := by
    have hmul := mul_lt_mul_of_pos_right hMC hM
    nlinarith
  let G : ℝ → ℝ^3 → ℝ := fun κ x ↦ κ ^ 2 * g κ x
  let J : ℝ → ℝ^3 → ℝ := fun κ x ↦ κ ^ 2 * h κ x
  have hG : ContDiff ℝ 2 (Function.uncurry G) :=
    (contDiff_fst.pow 2).mul (hg.of_le (by simp))
  have hJ : ContDiff ℝ 1 (Function.uncurry J) :=
    (contDiff_fst.pow 2).mul (hh.of_le (by simp))
  have hG0 : G 0 = 0 := by funext x; simp [G]
  have hJ0 : J 0 = 0 := by funext x; simp [J]
  have hsmall := eventually_abs_cauchyFreeField_lt_of_zero_compact_family hG hJ hG0 hJ0 hK
    (fun κ x hx ↦ by
      simp only [G, J, (hs κ x hx).1, (hs κ x hx).2, mul_zero, and_self]) 2 (half_pos hM)
  obtain ⟨a, b, hab, hsign⟩ :=
    ((eventually_pos_on_incoming_cone_zeros hlim hdlim).and hsmall).exists_Ioo_subset
  obtain ⟨κ, hκpos, hκsmall⟩ := exists_between (lt_min hab.2 hd)
  have hκd : κ < d := hκsmall.trans_le (min_le_right _ _)
  have hκboth := hsign ⟨hab.1.trans hκpos, hκsmall.trans_le (min_le_left _ _)⟩
  have hκsign := hκboth.1
  have hact := hactual κ (by rw [abs_of_pos hκpos]; exact hκd)
  let u : (ℝ × ℝ^3) → ℝ := fun p ↦ κ ^ 2 * v κ p
  have hκsq : 0 < κ ^ 2 := sq_pos_of_pos hκpos
  have hug : HasCompactSupport (fun x ↦ κ ^ 2 * g κ x) :=
    HasCompactSupport.intro hK fun x hx ↦ by simp only [(hs κ x hx).1, mul_zero]
  have huh : HasCompactSupport (fun x ↦ κ ^ 2 * h κ x) :=
    HasCompactSupport.intro hK fun x hx ↦ by simp only [(hs κ x hx).2, mul_zero]
  obtain ⟨δ, hδ, hδquarter, hzero⟩ := hpatch κ hκpos hκd
  refine ⟨_, _, contDiff_const.mul (hg.comp (contDiff_const.prodMk contDiff_id)),
    contDiff_const.mul (hh.comp (contDiff_const.prodMk contDiff_id)), hug, huh,
    u, hact.1, hact.2.1, hact.2.2.1, hact.2.2.2.1, hact.2.2.2.2, ?_,
    ⟨δ, hδ, fun t ht x hx ↦ (hzero t ht x hx).1⟩, ?_⟩
  · refine ⟨M, hM, ?_⟩
    have hfree : ContDiff ℝ 1 (cauchyFreeField (G κ) (J κ)) := contDiff_one_cauchyFreeField
        (hG.comp (contDiff_const.prodMk contDiff_id)) (hJ.comp (contDiff_const.prodMk contDiff_id))
    exact fun p hp ↦ (abs_lt_of_quadratic_integral_free_barrier (half_pos hM).le hM.le
      hact.1.continuousOn hfree.continuous (fun p hp ↦ (hκboth.2 p ⟨hp.1, hp.2.le⟩).le)
      (fun p hp ↦ hact.2.2.2.1 p ⟨hp.1, hp.2.le⟩) hbar p hp).le
  apply nodalMoment_pos_of_incoming_zero_patch (by norm_num : (1 : ℝ) < 2)
    hδ (hδquarter.trans (by norm_num)) hact.1
  · intro t ht x hx hz
    have humem : (t, x) ∈ {p : ℝ × ℝ^3 | |p.1| < 3} := by
      change |t| < 3
      rw [abs_of_nonneg ht.1]
      exact ht.2.trans_lt (by norm_num)
    have huDiff : DifferentiableAt ℝ u (t, x) :=
      (hact.1.contDiffAt ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds
        humem)).differentiableAt one_ne_zero
    have hrecover : (fun p ↦ (κ ^ 2)⁻¹ * u p) = v κ :=
      funext fun p ↦ inv_mul_cancel_left₀ hκsq.ne' _
    have hvDiff : DifferentiableAt ℝ (v κ) (t, x) := by
      rw [← hrecover]
      exact huDiff.const_mul _
    have hvzero : v κ (t, x) = 0 := (mul_eq_zero.mp hz).resolve_left hκsq.ne'
    change 0 ≤ fderiv ℝ (fun p ↦ κ ^ 2 * v κ p) (t, x) (t, x)
    rw [fderiv_const_mul hvDiff]
    exact (mul_pos hκsq (hκsign t ht x hx hvzero)).le
  · intro t ht x hx
    obtain ⟨hz, hD⟩ := hzero t ht x hx
    refine ⟨hz, ?_⟩
    rw [hD]
    apply div_pos hκsq
    have ht1 : t < 1 := ht.2.trans (hδquarter.trans (by norm_num))
    linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

end
