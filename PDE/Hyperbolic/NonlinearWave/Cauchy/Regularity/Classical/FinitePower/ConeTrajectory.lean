/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Integral
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Reaction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalTrajectory
import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.CompactData
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave
import CAS.ExactTactic

/-!
# C² integral trajectories above exponent two

The compact-cone construction is used at order two with the full
Kirchhoff field. A finite C² truncation is removed on the trajectory
by its short-time amplitude bound. This covers exponents above two only.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- A globally Lipschitz C² reaction and an arbitrary C² free field construct
one physical cone trajectory, with a C² remainder and a uniform remainder bound. -/
theorem exists_c2_cone_trajectory_of_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {C : NNReal}
    (hLip : LipschitzWith C f) :
    ∃ T : ℝ, 0 < T ∧
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 2 H → ∃ v a : ℝ × ℝ^3 → ℝ, ContDiffOn ℝ 2 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 2 a {p | |p.1| < T} ∧ (∀ p : ℝ × ℝ^3, |p.1| < T → v p = H p + p.1 ^ 2 * a p) ∧
      (∀ p : ℝ × ℝ^3, |p.1| < T → a p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        f (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) ∧
      ∀ B : ℝ, 0 ≤ B → (∀ z, |f z| ≤ B) → ∀ p : ℝ × ℝ^3, |p.1| < T → |a p| ≤ ‖duhamelOperator‖ *
        B := by
  let N := composeCompact (α := Cone) ⟨f, hf.continuous⟩
  have hNLip : LipschitzWith C N := by
    convert BoundedContinuousFunction.lipschitz_comp (α := Cone) hLip using 1
    ext w q
    rfl
  obtain ⟨T, hT, ψ, hψreg, hψeq, hψunique⟩ :=
    exists_c2_integral_solution_arbitrary_input duhamelOperator (contDiff_composeCompact hf) hNLip
  refine ⟨T, hT, fun H hH ↦ ?_⟩
  let A : ℝ × ℝ^3 → ℝ × (Cone →ᵇ ℝ) := fun p ↦ (p.1, coneField ⟨H, hH.continuous⟩ p)
  have hrestrict {p : ℝ × ℝ^3} (hp : |p.1| < T) (q : Cone) :
      ψ (A (physicalPoint p q)) = restrictCone q (ψ (A p)) := by
    apply hψunique _ ((abs_physicalPoint_time_le p q).trans_lt hp)
    have he := hψeq (A p) hp
    change ψ (A p) = coneField ⟨H, hH.continuous⟩ p + p.1 ^ 2 • duhamelOperator (N (ψ (A p))) at he
    calc
      restrictCone q (ψ (A p)) = restrictCone q (coneField ⟨H, hH.continuous⟩ p) +
            p.1 ^ 2 • restrictCone q (duhamelOperator (N (ψ (A p)))) := by
        conv_lhs => rw [he]
        rw [map_add, map_smul]
      _ = (A (physicalPoint p q)).2 + (A (physicalPoint p q)).1 ^ 2 •
          duhamelOperator (N (restrictCone q (ψ (A p)))) := by
        rw [restrictCone_coneField]
        apply congrArg (fun w ↦ coneField ⟨H, hH.continuous⟩ (physicalPoint p q) + w)
        have hN : restrictCone q (N (ψ (A p))) = N (restrictCone q (ψ (A p))) := by
          ext z
          rfl
        ext z
        simp only [BoundedContinuousFunction.smul_apply, restrictCone_apply,
          duhamelOperator_descend, hN, smul_eq_mul]
        change p.1 ^ 2 * (coneTime q ^ 2 * _) = (p.1 * coneTime q) ^ 2 * _
        cas
  let v : ℝ × ℝ^3 → ℝ := fun p ↦ ψ (A p) vertex
  have hv {p : ℝ × ℝ^3} (hp : |p.1| < T) (q : Cone) :
      v (physicalPoint p q) = ψ (A p) q := by
    dsimp only [v]
    rw [hrestrict hp q, restrictCone_apply, descend_vertex_right]
  let a : ℝ × ℝ^3 → ℝ := fun p ↦ duhamelOperator (N (ψ (A p))) vertex
  have hAc : ContDiff ℝ 2 A := contDiff_fst.prodMk (contDiff_coneField hH)
  have hw := hψreg.comp hAc.contDiffOn (fun _ hp ↦ hp)
  have ha := duhamelOperator.contDiff.comp_contDiffOn
    ((contDiff_composeCompact hf).comp_contDiffOn hw)
  refine ⟨v, a, ?_, ?_, ?_, ?_, ?_⟩
  · exact (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn hw
  · exact (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn ha
  · intro p hp
    have he := congrArg (fun w : Cone →ᵇ ℝ ↦ w vertex) (hψeq (A p) hp)
    change v p = coneField ⟨H, hH.continuous⟩ p vertex + p.1 ^ 2 * a p at he
    simpa only [coneField_apply, physicalPoint, vertex, coneTime, coneSpace,
      mul_one, smul_zero, add_zero, ContinuousMap.coe_mk] using he
  · intro p hp
    change duhamelOperator (N (ψ (A p))) vertex = _
    rw [duhamelOperator_apply]
    simp only [N, composeCompact_apply, descend_vertex_left]
    simp only [vertex, coneTime, one_pow, one_mul]
    congr 1 with s
    congr 3 with ω
    exact congrArg f (hv hp (rim s ω)).symm
  · intro B hB hbound p _
    have hn : ‖N (ψ (A p))‖ ≤ B :=
      (BoundedContinuousFunction.norm_le hB).mpr fun q ↦ hbound (ψ (A p) q)
    exact (duhamelOperator (N (ψ (A p)))).norm_coe_le_norm vertex |>.trans
      ((duhamelOperator.le_opNorm _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))


/-- Every signed real power above two admits a C² integral trajectory
from a bounded C² free field. The cutoff is absent from the conclusion. -/
theorem exists_c2_signedPower_cone_trajectory {r : ℝ} (hr : 2 < r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 2 H → (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 1 → |H p| ≤ B) →
        ∃ v a : ℝ × ℝ^3 → ℝ, ContDiffOn ℝ 2 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 2 a {p | |p.1| < T} ∧ (∀ p : ℝ × ℝ^3, |p.1| < T → v p = H p + p.1 ^ 2 * a p) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |v p| < B + 1) ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → a p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        -Real.signedPower r (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  have hs (z : ℝ) : 0 ≤ z * Real.signedPower r z := by
    unfold Real.signedPower
    nlinarith [mul_nonneg (Real.rpow_nonneg (abs_nonneg z) (r - 1)) (sq_nonneg z)]
  obtain ⟨f, C, hf, hfc, hLip, hmatch, _⟩ := exists_sign_preserving_lipschitz_reaction
      (m := 2) (contDiff_two_signedPower hr) (by norm_num) hs
      (show 0 < B + 2 by linarith)
  obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  obtain ⟨T₀, hT₀, htrajectory⟩ := exists_c2_cone_trajectory_of_lipschitz hf.neg hLip.neg
  have hc : Continuous (fun t : ℝ ↦ t ^ 2 * (‖duhamelOperator‖ * M)) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * (‖duhamelOperator‖ * M) < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hnear
  let T := min T₀ (min δ 1)
  have hT : 0 < T := lt_min hT₀ (lt_min hδ zero_lt_one)
  have hTT : T ≤ T₀ := min_le_left _ _
  have hTδ : T ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hT1 : T ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨T, hT, hT1, fun H hH hbound ↦ ?_⟩
  obtain ⟨v, a, hv, ha, heq, hrem, habound⟩ := htrajectory H hH
  have hva (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 T) : |v p| < B + 1 := by
    have hpt : |p.1| < T := by
      simpa only [abs_of_nonneg hp.1] using hp.2
    have hn : |a p| ≤ ‖duhamelOperator‖ * M := habound M hM0
      (fun z ↦ by simpa only [abs_neg, Real.norm_eq_abs] using hM z) p (hpt.trans_le hTT)
    have hsmall : p.1 ^ 2 * (‖duhamelOperator‖ * M) < 1 := hd (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hpt.trans_le hTδ)
    rw [heq p (hpt.trans_le hTT)]
    refine (abs_add_le _ _).trans_lt ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg p.1)]
    linarith [hbound p ⟨hp.1, hp.2.le.trans hT1⟩, mul_le_mul_of_nonneg_left hn (sq_nonneg p.1)]
  refine ⟨v, a, hv.mono (fun _ hp ↦ hp.trans_le hTT), ha.mono (fun _ hp ↦ hp.trans_le hTT),
    fun p hp ↦ heq p (hp.trans_le hTT), hva, ?_⟩
  intro p hp
  rw [hrem p (by simpa only [abs_of_nonneg hp.1] using hp.2.trans_le hTT)]
  congr 1 with s
  congr 3 with ω
  have hq : (physicalPoint p (rim s ω)).1 ∈ Ico 0 T := ⟨mul_nonneg hp.1 s.2.1,
      (mul_le_mul_of_nonneg_left s.2.2 hp.1).trans_lt (by simpa using hp.2)⟩
  have hbq := hva (physicalPoint p (rim s ω)) hq
  have hm := hmatch (show v (physicalPoint p (rim s ω)) ∈ Metric.closedBall 0 (B + 2) by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    linarith)
  exact congrArg Neg.neg hm

/-- Arbitrary compact C³ displacement and C² velocity produce a C²
signed-power integral trajectory for exponents above two, with both ordinary
Cauchy traces. Only the finite scalar C² regularity is used. -/
theorem exists_c2_signedPower_trajectory_of_compact_data {r : ℝ} (hr : 2 < r) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ v a : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 2 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 2 a {p | |p.1| < T} ∧
      (∀ x : ℝ^3, v (0, x) = g x) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ v (t, x)) (h x) 0) ∧
      (∀ p : ℝ × ℝ^3, |p.1| < T →
        v p = cauchyFreeField g h p + p.1 ^ 2 * a p) ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
        a p = ∫ s : I, (1 - (s : ℝ)) *
          ((∫ ω : Direction,
            -Real.signedPower r
              (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
              ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  have hH : ContDiff ℝ 2 (cauchyFreeField g h) :=
    (contDiff_two_kirchhoffFormula hg hh).comp (contDiff_timeSpaceCons_uncurry 3)
  obtain ⟨Rg, _, hgR⟩ := hgs.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  let R := max Rg Rh
  have hsupport (t : ℝ) (ht : t ∈ Icc 0 1) (x : ℝ^3) (hx : x ∉ Metric.closedBall 0 (R + 1)) :
      spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) = 0 := by
    apply WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport
      (hg.of_le (by norm_num)) hh.continuous (fun y hy ↦ hgR y ((le_max_left _ _).trans hy.le))
      (fun y hy ↦ hhR y ((le_max_right _ _).trans hy.le)) t ht.1 x
    have hx' : R + 1 < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    linarith [ht.2]
  have hHc : Continuous (spaceTimeUncurry (kirchhoffFormula g h)) := by
    have heq : spaceTimeUncurry (kirchhoffFormula g h) =
        cauchyFreeField g h ∘ timeSpaceContinuousLinearEquiv 3 := by
      funext z; simp [cauchyFreeField, timeSpaceContinuousLinearEquiv_apply]
    rw [heq]
    exact hH.continuous.comp (timeSpaceContinuousLinearEquiv 3).continuous
  obtain ⟨B, hB, hbound⟩ := exists_bound_of_compact_slab hHc
    (isCompact_closedBall (0 : ℝ^3) (R + 1)) hsupport
  obtain ⟨T, hT, _, htrajectory⟩ := exists_c2_signedPower_cone_trajectory hr hB
  obtain ⟨v, a, hv, ha, heq, _, hrem⟩ :=
    htrajectory (cauchyFreeField g h) hH (fun p hp ↦ hbound p.1 hp p.2)
  refine ⟨T, hT, v, a, hv, ha, ?_, ?_, heq, hrem⟩
  · intro x
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero,
      cauchyFreeField_initial_position] using heq (0, x) (by simpa using hT)
  · intro x
    have hnear : {p : ℝ × ℝ^3 | |p.1| < T} ∈ 𝓝 (0, x) :=
      (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simpa using hT)
    have hac : ContDiffAt ℝ 1 (fun t : ℝ ↦ a (t, x)) 0 :=
      ((ha.of_le (by norm_num)).contDiffAt hnear).comp 0 (contDiffAt_id.prodMk contDiffAt_const)
    have hd := (hasDerivAt_cauchyFreeField_initial_velocity (hg.of_le (by norm_num))
      (hh.of_le (by norm_num)) x).fun_add (((hasDerivAt_id (0 : ℝ)).fun_pow 2).fun_mul
        (hac.differentiableAt one_ne_zero).hasDerivAt)
    have htrace : HasDerivAt
        (fun t : ℝ ↦ cauchyFreeField g h (t, x) + t ^ 2 * a (t, x)) (h x) 0 := by
      simpa using hd
    apply htrace.congr_of_eventuallyEq
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear] with t ht
    exact heq (t, x) ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
