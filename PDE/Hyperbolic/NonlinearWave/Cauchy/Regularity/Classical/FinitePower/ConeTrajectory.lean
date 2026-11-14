/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Integral
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Reaction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalTrajectory
import PDE.Analysis.Calculus.LocalExtension.SmoothCutoff
import CAS.ExactTactic

/-!
# C² integral trajectories for a C² reaction

The compact-cone construction is used at order two with a bounded C² free field. A compactly
supported C² cutoff of the reaction is removed on the trajectory by its short-time amplitude
bound, so the trajectory solves the integral equation of the reaction itself
(`exists_c2_cone_trajectory`). No sign or growth condition on the reaction is used, and the
reaction need not vanish at zero. The signed powers above exponent two are the case
`exists_c2_signedPower_cone_trajectory`.

## How it works

`ContDiff.exists_lipschitzWith_compactSupport_eqOn_closedBall` cuts the reaction `f` off outside
`[-B - 1, B + 1]`: the cutoff `F` is `C²`, Lipschitz and bounded by some `M`.
`exists_c2_cone_trajectory_of_lipschitz` solves `v = H + t² a` for `|t| < T₀`, where `a` is the
Duhamel average of `F ∘ v` over the backward cone, and bounds `|a|` by `‖duhamelOperator‖ M`. So
`|v| < B + 1` for `0 ≤ t < T`, with `T` small, and there `F ∘ v = f ∘ v`: the cutoff is gone.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped unitInterval

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

/-- **Integral trajectories of a `C²` reaction.** For `f ∈ C²` and `B ≥ 0` there is a time
`0 < T ≤ 1` such that every `C²` free field `H` on `ℝ × ℝ³` with `|H| ≤ B` on the slab
`0 ≤ t ≤ 1` has `C²` functions `v`, `a` on `|t| < T` with `v = H + t² a` there, and with
`|v| < B + 1` and `a (t, x) = ∫₀¹ (1 - s) · (mean over |ω| = 1 of f (v (t s, x + t (1 - s) ω))) ds`
for `0 ≤ t < T`. -/
theorem exists_c2_cone_trajectory {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {B : ℝ} (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 2 H → (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 1 → |H p| ≤ B) →
        ∃ v a : ℝ × ℝ^3 → ℝ, ContDiffOn ℝ 2 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 2 a {p | |p.1| < T} ∧ (∀ p : ℝ × ℝ^3, |p.1| < T → v p = H p + p.1 ^ 2 * a p) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |v p| < B + 1) ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → a p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        f (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  obtain ⟨F, C, hF, hFc, hLip, hmatch⟩ :=
    ContDiff.exists_lipschitzWith_compactSupport_eqOn_closedBall (m := 2) hf (by norm_num) 0
      (add_pos_of_nonneg_of_pos hB one_pos)
  obtain ⟨M, hM⟩ := hF.continuous.bounded_above_of_compact_support hFc
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hM 0)
  obtain ⟨T₀, hT₀, htrajectory⟩ := exists_c2_cone_trajectory_of_lipschitz hF hLip
  -- A time `T ≤ T₀` with `T (K + 1) ≤ 1`, where `K` bounds the remainder `a`.
  set K : ℝ := ‖duhamelOperator‖ * M
  have hK : 0 ≤ K := mul_nonneg duhamelOperator.opNorm_nonneg hM0
  have hK1 : 0 < K + 1 := add_pos_of_nonneg_of_pos hK one_pos
  obtain ⟨T, hT, hTT, hTK⟩ : ∃ T : ℝ, 0 < T ∧ T ≤ T₀ ∧ T * (K + 1) ≤ 1 :=
    ⟨min T₀ (1 / (K + 1)), lt_min hT₀ (one_div_pos.mpr hK1), min_le_left _ _,
      (le_div_iff₀ hK1).mp (min_le_right _ _)⟩
  have hT1 : T ≤ 1 := by cas using [mul_nonneg hT.le hK, hTK, hT]
  refine ⟨T, hT, hT1, fun H hH hbound ↦ ?_⟩
  obtain ⟨v, a, hv, ha, heq, hrem, habound⟩ := htrajectory H hH
  have hlt {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 T) : |p.1| < T₀ := by
    rw [abs_of_nonneg hp.1]
    exact hp.2.trans_le hTT
  have hva (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 T) : |v p| < B + 1 := by
    have hn : |a p| ≤ K :=
      habound M hM0 (fun z ↦ by simpa only [Real.norm_eq_abs] using hM z) p (hlt hp)
    have hsq : p.1 ^ 2 * K ≤ p.1 * K := by
      cas using [hp.1, hK, hp.2.le.trans hT1, mul_nonneg hp.1 hK]
    rw [heq p (hlt hp)]
    refine (abs_add_le _ _).trans_lt ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg p.1)]
    cas using [hbound p ⟨hp.1, hp.2.le.trans hT1⟩, mul_le_mul_of_nonneg_left hn (sq_nonneg p.1),
      hsq, mul_le_mul_of_nonneg_right hp.2.le hK, hTK, hT]
  refine ⟨v, a, hv.mono fun _ hp ↦ hp.trans_le hTT, ha.mono fun _ hp ↦ hp.trans_le hTT,
    fun p hp ↦ heq p (hp.trans_le hTT), hva, fun p hp ↦ ?_⟩
  rw [hrem p (hlt hp)]
  congr 1 with s
  congr 3 with ω
  refine hmatch ?_
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
  exact (hva _ ⟨mul_nonneg hp.1 s.2.1, (mul_le_of_le_one_right hp.1 s.2.2).trans_lt hp.2⟩).le

/-- Every signed real power above two admits a C² integral trajectory
from a bounded C² free field: the case `f = -Real.signedPower r` of
`exists_c2_cone_trajectory`. -/
theorem exists_c2_signedPower_cone_trajectory {r : ℝ} (hr : 2 < r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 2 H → (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 1 → |H p| ≤ B) →
        ∃ v a : ℝ × ℝ^3 → ℝ, ContDiffOn ℝ 2 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 2 a {p | |p.1| < T} ∧ (∀ p : ℝ × ℝ^3, |p.1| < T → v p = H p + p.1 ^ 2 * a p) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |v p| < B + 1) ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → a p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        -Real.signedPower r (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) :=
  exists_c2_cone_trajectory (contDiff_two_signedPower hr).neg hB

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
