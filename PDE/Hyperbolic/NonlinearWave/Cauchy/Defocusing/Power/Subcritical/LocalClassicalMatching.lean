/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalUniqueness
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula
import CAS.ExactTactic

/-!
# Local comparison with a classical branch

A classical comparison field has the retarded representation with its
wave operator. Restriction to a backward cone uses only the equation and the
Cauchy data there. Uniform cone uniqueness then identifies a continuous
integral trajectory with this branch without assuming second derivatives of
the trajectory.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open BoundedContinuousFunction WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The wave operator is a C¹ forcing for a C³ comparison field. -/
private theorem contDiff_one_waveOperator_of_contDiff_three {v : ℝ^4 → ℝ} (hv : ContDiff ℝ 3 v) :
    ContDiff ℝ 1 (waveOperator v) := by
  have hd (i : Fin 4) : ContDiff ℝ 1 (∂[i] (∂[i] v)) := contDiff_partialDeriv_of_succ (m := 1)
      (contDiff_partialDeriv_of_succ (m := 2) hv)
  exact (hd 0).sub (ContDiff.sum fun i _ ↦ hd i.succ)

/-- Every C³ comparison field has the retarded formula with its own Cauchy
traces and wave operator. -/
theorem eq_free_add_duhamel_waveOperator {v : ℝ^4 → ℝ} (hv : ContDiff ℝ 3 v) {t : ℝ} (ht : 0 ≤ t)
    (x : ℝ^3) :
    v (timeSpaceCons t x) = cauchyFreeField (fun y ↦ v (timeSpaceCons 0 y))
      (fun y ↦ (∂[0] v) (timeSpaceCons 0 y)) (t, x) + oddDuhamelSolution 0 (waveOperator v)
      (timeSpaceCons t x) := by
  let g := fun y ↦ v (timeSpaceCons 0 y)
  let h := fun y ↦ (∂[0] v) (timeSpaceCons 0 y)
  have hg : ContDiff ℝ 3 g := hv.comp (contDiff_timeSpaceCons_spatial 3 0)
  have hh : ContDiff ℝ 2 h := (contDiff_partialDeriv_of_succ (m := 2) hv).comp
      (contDiff_timeSpaceCons_spatial 3 0)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hH := contDiff_two_kirchhoffFormula hg hh
  have hF := contDiff_one_waveOperator_of_contDiff_three hv
  rcases ht.eq_or_lt with rfl | ht
  · simp only [cauchyFreeField_initial_position,
      oddDuhamelSolution_zero_eq_normalized _ _ le_rfl, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero]
  have he := eq_retarded_ball_of_zero_data (hv2.sub hH) hF ht
    (fun s hs y ↦ by
      rw [waveOperator_sub hv2.contDiffAt hH.contDiffAt,
        waveOperator_kirchhoffFormula hg hh (by simpa using hs.1), sub_zero])
    (fun y ↦ by simp only [kirchhoffFormula_initial_position, g, sub_self])
    (fun y ↦ by
      rw [partialDeriv_sub (hv2.differentiable (by norm_num) _)
        (hH.differentiable (by norm_num) _), partialDeriv_kirchhoffFormula_initial_velocity
          (hg.of_le (by norm_num)) (hh.of_le (by norm_num))]
      exact sub_self _) x
  rw [← oddDuhamelSolution_eq_retarded_ball hF.continuous x ht.le] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

private theorem physicalPoint_mem_backwardCone {p : ℝ × ℝ^3} (hp : 0 ≤ p.1) (q : Cone) :
    (physicalPoint p q).1 ∈ Icc 0 p.1 ∧ (physicalPoint p q).2 ∈
      closedBall p.2 (p.1 - (physicalPoint p q).1) := by
  refine ⟨⟨mul_nonneg hp (coneTime_mem q).1,
    by simpa only [physicalPoint, mul_one] using
      mul_le_mul_of_nonneg_left (coneTime_mem q).2 hp⟩, ?_⟩
  change ‖p.2 + p.1 • coneSpace q - p.2‖ ≤ p.1 - p.1 * coneTime q
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hp]
  calc
    p.1 * ‖coneSpace q‖ ≤ p.1 * (1 - coneTime q) :=
      mul_le_mul_of_nonneg_left (norm_coneSpace_le q) hp
    _ = _ := by cas

private theorem waveOperator_kirchhoffFormula_nonneg {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    waveOperator (spaceTimeUncurry (kirchhoffFormula g h)) (timeSpaceCons t x) = 0 := by
  have he : EqOn
      (fun t ↦ waveOperator (spaceTimeUncurry (kirchhoffFormula g h)) (timeSpaceCons t x))
      (fun _ ↦ 0) (Ioi 0) := fun t ht ↦
    waveOperator_kirchhoffFormula hg hh (by simpa using ht)
  have hc : Continuous (fun t : ℝ ↦ timeSpaceCons t x) :=
    (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous.comp
      (continuous_id.prodMk continuous_const)
  exact he.closure
    ((continuous_waveOperator_of_contDiff_two (contDiff_two_kirchhoffFormula hg hh)).comp hc)
    continuous_const (by simpa only [closure_Ioi, mem_Ici] using ht)

/-- Initial data agreeing on a base ball give identical Kirchhoff fields on
its closed backward cone, including the lateral boundary and the vertex. -/
theorem coneField_cauchyFreeField_eq_of_eqOn_initialData
    {g h g' h' : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hg' : ContDiff ℝ 3 g') (hh' : ContDiff ℝ 2 h') {p : ℝ × ℝ^3} (hp : 0 < p.1)
    (hgE : EqOn g g' (closedBall p.2 p.1)) (hhE : EqOn h h' (closedBall p.2 p.1)) :
    coneField ⟨cauchyFreeField g h,
      (contDiff_one_cauchyFreeField (hg.of_le (by norm_num))
        (hh.of_le (by norm_num))).continuous⟩ p =
    coneField ⟨cauchyFreeField g' h',
      (contDiff_one_cauchyFreeField (hg'.of_le (by norm_num))
        (hh'.of_le (by norm_num))).continuous⟩ p := by
  have he := eq_on_closed_backwardCone_of_eq_initialData
    (contDiff_two_kirchhoffFormula hg hh) (contDiff_two_kirchhoffFormula hg' hh') p.2
    (fun t ht x _ ↦ waveOperator_kirchhoffFormula_nonneg hg hh ht.1 x)
    (fun t ht x _ ↦ waveOperator_kirchhoffFormula_nonneg hg' hh' ht.1 x)
    (fun x hx ↦ by
      simp only [kirchhoffFormula_initial_position]
      exact hgE (by simpa using hx))
    (fun x hx ↦ by
      rw [partialDeriv_kirchhoffFormula_initial_velocity
          (hg.of_le (by norm_num)) (hh.of_le (by norm_num)),
        partialDeriv_kirchhoffFormula_initial_velocity
          (hg'.of_le (by norm_num)) (hh'.of_le (by norm_num))]
      exact hhE (by simpa using hx))
  ext q
  simpa only [coneField_apply, cauchyFreeField, ContinuousMap.coe_mk] using
    he _ (physicalPoint_mem_backwardCone hp.le q).1 _ (physicalPoint_mem_backwardCone hp.le q).2

/-- A C³ branch satisfying the signed-power equation only on one backward
cone obeys the normalized nonlinear equation on that entire cone. -/
theorem coneField_eq_of_local_classical_signedPower {r : ℝ} (hr : 0 < r)
    {v : ℝ^4 → ℝ} (hv : ContDiff ℝ 3 v) {p : ℝ × ℝ^3} (hp : 0 ≤ p.1)
    (hw : ∀ q : Cone, waveOperator v
      (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2) +
        Real.signedPower r (v (timeSpaceCons (physicalPoint p q).1
          (physicalPoint p q).2)) = 0) :
    let V : C(ℝ × ℝ^3, ℝ) := ⟨fun q ↦ v (timeSpaceCons q.1 q.2),
      hv.continuous.comp (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous⟩
    let g := fun y ↦ v (timeSpaceCons 0 y)
    let h := fun y ↦ (∂[0] v) (timeSpaceCons 0 y)
    let H : C(ℝ × ℝ^3, ℝ) := ⟨cauchyFreeField g h,
      (contDiff_one_cauchyFreeField
        ((hv.of_le (by norm_num)).comp (contDiff_timeSpaceCons_spatial 3 0))
        ((contDiff_partialDeriv_of_succ (m := 1) (hv.of_le (by norm_num))).comp
          (contDiff_timeSpaceCons_spatial 3 0))).continuous⟩
    let f : C(ℝ, ℝ) := ⟨fun z ↦ -Real.signedPower r z,
      (Real.continuous_signedPower hr).neg⟩
    coneField V p = coneField H p + p.1 ^ 2 •
      duhamelOperator (composeCompact f (coneField V p)) := by
  intro V g h H f
  ext q
  simp only [coneField_apply, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, duhamelOperator_apply, composeCompact_apply,
    smul_eq_mul, physicalPoint_descend]
  change v (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2) = _
  rw [eq_free_add_duhamel_waveOperator hv (physicalPoint_mem_backwardCone hp q).1.1,
    oddDuhamelSolution_zero_eq_normalized _ _ (physicalPoint_mem_backwardCone hp q).1.1]
  have hsource (s : I) (ω : Direction) :
      waveOperator v (timeSpaceCons ((physicalPoint p q).1 * (s : ℝ))
        ((physicalPoint p q).2 + (physicalPoint p q).1 • ((1 - (s : ℝ)) • (ω : ℝ^3)))) =
      f (V (physicalPoint (physicalPoint p q) (rim s ω))) := by
    have he := eq_neg_of_add_eq_zero_left (hw (descend q (rim s ω)))
    rw [physicalPoint_descend] at he
    exact he
  simp_rw [hsource]
  change cauchyFreeField g h (physicalPoint p q) +
    (p.1 * coneTime q) ^ 2 * _ = cauchyFreeField g h (physicalPoint p q) + _
  simp only [mul_pow, mul_assoc]

/-- A continuous signed-power integral trajectory agrees with a C³ branch
on a short backward cone when their Cauchy data agree on its base ball. Only
the branch has pointwise second derivatives; its PDE is needed on this cone. -/
theorem eq_on_cone_of_local_classical_signedPower {r L M : ℝ} (hr : 1 ≤ r) (hM : 0 ≤ M)
    {u : ℝ × ℝ^3 → ℝ} (hu : ContinuousOn u {q | |q.1| < L}) {v : ℝ^4 → ℝ} (hv : ContDiff ℝ 3 v)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hue : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 L → u q = cauchyFreeField g h q +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ -Real.signedPower r
      (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons q.1 q.2))
    {p : ℝ × ℝ^3} (hp : p.1 ∈ Ioo 0 L)
    (hposition : ∀ x ∈ closedBall p.2 p.1, g x = v (timeSpaceCons 0 x))
    (hvelocity : ∀ x ∈ closedBall p.2 p.1, h x = (∂[0] v) (timeSpaceCons 0 x))
    (hw : ∀ q : Cone, waveOperator v (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2) +
      Real.signedPower r (v (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2)) = 0)
    (huB : ∀ q : Cone, |u (physicalPoint p q)| ≤ M)
    (hvB : ∀ q : Cone, |v (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2)| ≤ M)
    (hsmall : p.1 ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1) :
    ∀ q : Cone, u (physicalPoint p q) = v (timeSpaceCons (physicalPoint p q).1
      (physicalPoint p q).2) := by
  let P : {q : ℝ × ℝ^3 | |q.1| < L} :=
    ⟨p, by simpa only [mem_ofPred_eq, abs_of_pos hp.1] using hp.2⟩
  let V : C(ℝ × ℝ^3, ℝ) := ⟨fun q ↦ v (timeSpaceCons q.1 q.2),
    hv.continuous.comp (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous⟩
  let H : C(ℝ × ℝ^3, ℝ) := ⟨cauchyFreeField g h,
    (contDiff_one_cauchyFreeField (hg.of_le (by norm_num))
      (hh.of_le (by norm_num))).continuous⟩
  let f : C(ℝ, ℝ) := ⟨fun z ↦ -Real.signedPower r z,
    (Real.continuous_signedPower (zero_lt_one.trans_le hr)).neg⟩
  have hg' : ContDiff ℝ 3 (fun x : ℝ^3 ↦ v (timeSpaceCons 0 x)) :=
    hv.comp (contDiff_timeSpaceCons_spatial 3 0)
  have hh' : ContDiff ℝ 2 (fun x : ℝ^3 ↦ (∂[0] v) (timeSpaceCons 0 x)) :=
    (contDiff_partialDeriv_of_succ (m := 2) hv).comp (contDiff_timeSpaceCons_spatial 3 0)
  have hHsame := coneField_cauchyFreeField_eq_of_eqOn_initialData hg hh hg' hh'
    hp.1 hposition hvelocity
  have huN : ‖physicalCone hu P‖ ≤ M := (BoundedContinuousFunction.norm_le hM).mpr huB
  have hvN : ‖coneField V p‖ ≤ M := by
    refine (BoundedContinuousFunction.norm_le hM).mpr fun q ↦ ?_
    simpa only [coneField_apply, V, ContinuousMap.coe_mk, Real.norm_eq_abs] using hvB q
  have huE := physicalCone_eq_of_free_integral_eq hu H f
    (fun q hq ↦ by
      rw [hue q hq, oddDuhamelSolution_zero_eq_normalized _ _ hq.1]
      rfl) P hp.1.le
  have hvE := coneField_eq_of_local_classical_signedPower (zero_lt_one.trans_le hr) hv hp.1.le hw
  dsimp only at hvE
  rw [← hHsame] at hvE
  have he := eq_of_signedPower_cone_equations hr (coneField H p)
    (physicalCone hu P) (coneField V p) huN hvN hsmall huE hvE
  intro q
  have heq := congrArg (fun a : Cone →ᵇ ℝ ↦ a q) he
  simpa only [physicalCone_apply, coneField_apply, V, P, ContinuousMap.coe_mk] using heq

/-- Continuity supplies a uniform comparison time for bounded spatial
centers. Amplitude bounds and the short-cone contraction condition are derived, so the remaining
hypotheses are local Cauchy agreement and the branch PDE. -/
theorem exists_pos_eq_on_cone_of_local_classical_signedPower {r L R : ℝ} (hr : 1 ≤ r) (hL : 0 < L)
    {u : ℝ × ℝ^3 → ℝ} (hu : ContinuousOn u {q | |q.1| < L}) {v : ℝ^4 → ℝ} (hv : ContDiff ℝ 3 v)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hue : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 L → u q = cauchyFreeField g h q +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ -Real.signedPower r
      (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons q.1 q.2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < L ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ioo 0 δ → ‖p.2‖ ≤ R → (∀ x ∈ closedBall p.2 p.1,
        g x = v (timeSpaceCons 0 x)) → (∀ x ∈ closedBall p.2 p.1,
        h x = (∂[0] v) (timeSpaceCons 0 x)) → (∀ t ∈ Icc 0 p.1, ∀ x ∈ closedBall p.2 (p.1 - t),
        waveOperator v (timeSpaceCons t x) + Real.signedPower r (v (timeSpaceCons t x)) = 0) →
        ∀ q : Cone, u (physicalPoint p q) =
        v (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2) := by
  let a := L / 2
  have ha : 0 < a := half_pos hL
  have haL : a < L := half_lt_self hL
  let K : Set (ℝ × ℝ^3) := Icc 0 a ×ˢ closedBall 0 (R + a)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : K ⊆ {q | |q.1| < L} := fun q hq ↦
    (abs_of_nonneg hq.1.1).trans_lt (hq.1.2.trans_lt haL)
  have hV : Continuous (fun q : ℝ × ℝ^3 ↦ v (timeSpaceCons q.1 q.2)) :=
    hv.continuous.comp (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((hu.mono hsub).prodMk hV.continuousOn)
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1 :=
    (((continuous_id.pow 2).mul continuous_const).mul continuous_const).continuousAt.eventually
      (gt_mem_nhds (by simp))
  obtain ⟨η, hη, hηsmall⟩ := Metric.mem_nhds_iff.mp hsmall
  let δ := min η a
  have hδ : 0 < δ := lt_min hη ha
  have hδa : δ ≤ a := min_le_right _ _
  have hδL : δ < L := hδa.trans_lt haL
  refine ⟨δ, hδ, hδL, fun p hp hpR hpos hvel hw ↦ ?_⟩
  have hmem (q : Cone) : physicalPoint p q ∈ K := by
    have hq := physicalPoint_mem_backwardCone hp.1.le q
    refine ⟨⟨hq.1.1, hq.1.2.trans (hp.2.le.trans hδa)⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have hdist : ‖(physicalPoint p q).2 - p.2‖ ≤ p.1 - (physicalPoint p q).1 := hq.2
    have hn' : ‖(physicalPoint p q).2‖ ≤
        ‖(physicalPoint p q).2 - p.2‖ + ‖p.2‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((physicalPoint p q).2 - p.2) p.2
    linarith [hq.1.1, hp.2.le.trans hδa]
  apply eq_on_cone_of_local_classical_signedPower hr hM hu hv hg hh hue
    ⟨hp.1, hp.2.trans hδL⟩ hpos hvel (fun q ↦ hw _ (physicalPoint_mem_backwardCone hp.1.le q).1 _
        (physicalPoint_mem_backwardCone hp.1.le q).2)
  · exact fun q ↦ ((norm_fst_le (u (physicalPoint p q),
      v (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2))).trans
        (hB _ (hmem q))).trans (le_max_left _ _)
  · exact fun q ↦ ((norm_snd_le (u (physicalPoint p q),
      v (timeSpaceCons (physicalPoint p q).1 (physicalPoint p q).2))).trans
        (hB _ (hmem q))).trans (le_max_left _ _)
  · apply hηsmall
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hp.1] using
      hp.2.trans_le (min_le_left η a)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
