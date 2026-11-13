/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.ImplicitFunction.IntegralEquation
public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.SegmentFields
import CAS.ExactTactic

/-!
# Construction of the variable-coefficient characteristic solution

Uniform local uniqueness identifies the restrictions of the implicit cone
solutions. Evaluation at the vertex therefore constructs one C¹ spacetime
field satisfying the characteristic integral equation. The same uniqueness
proves finite propagation directly, before any second derivatives are used.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- A cone point in the scalar spatial coordinate. -/
def segmentPoint (p : ℝ × ℝ) (q : Cone) : ℝ × ℝ :=
  (p.1 * coneTime q, p.2 + p.1 * lineSpace q)

/-- Subcones have no larger absolute time. -/
theorem abs_segmentPoint_time_le (p : ℝ × ℝ) (q : Cone) :
    |(segmentPoint p q).1| ≤ |p.1| := by
  change |p.1 * coneTime q| ≤ |p.1|
  rw [abs_mul, abs_of_nonneg (coneTime_mem q).1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (coneTime_mem q).2 (abs_nonneg p.1)

/-- Parameters of the weighted implicit equation. -/
def segmentParameter (h a : C(ℝ, ℝ)) (p : ℝ × ℝ) :
    ℝ × ((Cone →ᵇ ℝ) × (Cone →ᵇ ℝ)) :=
  (p.1, segmentFreeField h p, segmentCoefficient a p)

/-- Bounded velocity and coefficient give a uniform parameter neighborhood. -/
theorem segmentParameter_mem_ball (h a : ℝ →ᵇ ℝ) {δ : ℝ} {p : ℝ × ℝ}
    (hp : |p.1| < δ / (‖h‖ + ‖a‖ + 1)) :
    segmentParameter h.toContinuousMap a.toContinuousMap p ∈ Metric.ball 0 δ := by
  have hlt := (lt_div_iff₀ (by positivity : 0 < ‖h‖ + ‖a‖ + 1)).mp hp
  have ht : |p.1| ≤ |p.1| * (‖h‖ + ‖a‖ + 1) := by
    nlinarith [norm_nonneg h, norm_nonneg a, abs_nonneg p.1]
  have hh : |p.1| * ‖h‖ ≤ |p.1| * (‖h‖ + ‖a‖ + 1) := by
    nlinarith [norm_nonneg a, abs_nonneg p.1]
  have ha : |p.1| * ‖a‖ ≤ |p.1| * (‖h‖ + ‖a‖ + 1) := by
    nlinarith [norm_nonneg h, abs_nonneg p.1]
  simp only [Metric.mem_ball, dist_zero_right, segmentParameter, Prod.norm_def,
    Real.norm_eq_abs, max_lt_iff]
  exact ⟨ht.trans_lt hlt, (norm_segmentFreeField_le h p).trans_lt (hh.trans_lt hlt),
    (norm_segmentCoefficient_le a p).trans_lt (ha.trans_lt hlt)⟩

/-- Every initial point of a subcone lies in the terminal characteristic interval. -/
theorem abs_segmentInitialDirection_le (q : Cone) (b : I) :
    |lineSpace q + coneTime q * (2 * (b : ℝ) - 1)| ≤ 1 := by
  have hcoord : |lineSpace q| ≤ ‖coneSpace q‖ := by
    simpa only [lineSpace_apply, Real.norm_eq_abs] using (PiLp.norm_apply_le (coneSpace q) 0)
  have hq : |lineSpace q| ≤ 1 - coneTime q := hcoord.trans (norm_coneSpace_le q)
  have hb : |2 * (b : ℝ) - 1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [b.2.1], by linarith [b.2.2]⟩
  have := mul_le_mul_of_nonneg_left hb (coneTime_mem q).1
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (coneTime_mem q).1]
  linarith

/-- C¹ reaction, coefficient, and bounded velocity construct the
characteristic solution. The last clause is finite propagation from the data. -/
theorem exists_segment_solution {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (h a : ℝ →ᵇ ℝ)
    (hh : ContDiff ℝ 1 h) (ha : ContDiff ℝ 1 a) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ℝ × ℝ → ℝ,
      ContDiffOn ℝ 1 v {p | |p.1| < T} ∧
      (∀ p : ℝ × ℝ, |p.1| < T →
        v p = p.1 * (∫ b : I, h (p.2 + p.1 * (2 * (b : ℝ) - 1))) +
          p.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
            ∫ b : I, a (p.2 + p.1 * ((1 - (s : ℝ)) * (2 * (b : ℝ) - 1))) *
              f (v (p.1 * (s : ℝ),
                p.2 + p.1 * ((1 - (s : ℝ)) * (2 * (b : ℝ) - 1))))) ∧
      ∀ p : ℝ × ℝ, |p.1| < T →
        (∀ y : ℝ, |y - p.2| ≤ |p.1| → h y = 0) → v p = 0 := by
  let N := composeCompact (α := Cone) ⟨f, hf.continuous⟩
  obtain ⟨δ, r, hδ, hr, ψ, hψreg, hψsmall, hψeq, hψunique⟩ :=
    PDE.Analysis.exists_local_weighted_integral_solution (k := 0) segmentOperator
      (contDiff_composeCompact hf)
  let T := δ / (‖h‖ + ‖a‖ + 1)
  let A := segmentParameter h.toContinuousMap a.toContinuousMap
  have hA {p : ℝ × ℝ} (hp : |p.1| < T) : A p ∈ Metric.ball 0 δ := segmentParameter_mem_ball h a hp
  have hrestrict {p : ℝ × ℝ} (hp : |p.1| < T) (q : Cone) :
      ψ (A (segmentPoint p q)) = restrictCone q (ψ (A p)) := by
    apply hψunique _ (hA ((abs_segmentPoint_time_le p q).trans_lt hp))
    · exact (norm_restrictCone_le q _).trans_lt (hψsmall _ (hA hp))
    · have he := hψeq _ (hA hp)
      change ψ (A p) = segmentFreeField h.toContinuousMap p +
        p.1 • segmentOperator (segmentCoefficient a.toContinuousMap p * N (ψ (A p))) at he
      have hc : segmentCoefficient a.toContinuousMap (segmentPoint p q) *
          N (restrictCone q (ψ (A p))) = coneTime q • restrictCone q
            (segmentCoefficient a.toContinuousMap p * N (ψ (A p))) := by
        rw [show segmentPoint p q = (p.1 * coneTime q, p.2 + p.1 * lineSpace q) from rfl,
          ← restrictCone_segmentCoefficient]
        ext z
        simp only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.smul_apply,
          restrictCone_apply, N, composeCompact_apply, smul_eq_mul]
        cas
      change restrictCone q (ψ (A p)) = segmentFreeField h.toContinuousMap
        (segmentPoint p q) + (p.1 * coneTime q) •
          segmentOperator (segmentCoefficient a.toContinuousMap (segmentPoint p q) *
            N (restrictCone q (ψ (A p))))
      conv_lhs => rw [he]
      rw [map_add, map_smul, restrictCone_segmentFreeField, hc, map_smul]
      congr 1
      ext z
      simp only [BoundedContinuousFunction.smul_apply, restrictCone_apply,
        segmentOperator_descend, smul_eq_mul]
      cas
  let v : ℝ × ℝ → ℝ := fun p ↦ ψ (A p) vertex
  have hv {p : ℝ × ℝ} (hp : |p.1| < T) (q : Cone) :
      v (segmentPoint p q) = ψ (A p) q := by
    dsimp only [v]
    rw [hrestrict hp q, restrictCone_apply, descend_vertex_right]
  refine ⟨T, div_pos hδ (by positivity), v, ?_, ?_, ?_⟩
  · have hAc : ContDiff ℝ 1 A := contDiff_fst.prodMk
        ((contDiff_segmentFreeField hh).prodMk (contDiff_segmentCoefficient ha))
    exact (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hψreg.comp hAc.contDiffOn (fun _ hp ↦ hA hp))
  · intro p hp
    have he := congrArg (fun w : Cone →ᵇ ℝ ↦ w vertex) (hψeq _ (hA hp))
    change v p = segmentFreeField h.toContinuousMap p vertex + p.1 *
      segmentOperator (segmentCoefficient a.toContinuousMap p * N (ψ (A p))) vertex at he
    rw [he, segmentFreeField_apply, segmentOperator_apply]
    have ht : coneTime vertex = 1 := rfl
    have hx : lineSpace vertex = 0 := rfl
    simp only [ht, hx, mul_one, zero_add, one_mul, one_pow, descend_vertex_left]
    congr 1
    simp only [BoundedContinuousFunction.mul_apply, segmentCoefficient_apply,
      N, composeCompact_apply]
    have hpoint (s b : I) : segmentPoint p (segmentRim s b) =
        (p.1 * (s : ℝ), p.2 + p.1 * ((1 - (s : ℝ)) * (2 * (b : ℝ) - 1))) := rfl
    have hspace (s b : I) : lineSpace (segmentRim s b) = (1 - (s : ℝ)) * (2 * (b : ℝ) - 1) := rfl
    simp_rw [← hv hp, hpoint, hspace]
    simp only [coe_toContinuousMap, ContinuousMap.coe_mk, mul_assoc, ← integral_const_mul]
    congr 1 with s
    congr 1 with z
    cas
  · intro p hp hzero
    have hH : segmentFreeField h.toContinuousMap p = 0 := by
      ext q
      rw [segmentFreeField_apply]
      have he (b : I) : h (p.2 + p.1 * (lineSpace q + coneTime q * (2 * (b : ℝ) - 1))) = 0 := by
        apply hzero
        rw [add_sub_cancel_left, abs_mul]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (abs_segmentInitialDirection_le q b) (abs_nonneg _)
      simp only [coe_toContinuousMap, he, integral_zero, mul_zero]
      rfl
    have hN0 : N 0 = 0 := by ext q; exact hf0
    have he := hψunique (A p) (hA hp) 0 (by simpa using hr) (by
      change 0 = segmentFreeField h.toContinuousMap p +
        p.1 • segmentOperator (segmentCoefficient a.toContinuousMap p * N 0)
      simp only [hH, hN0, mul_zero, map_zero, smul_zero, add_zero])
    change ψ (A p) vertex = 0
    rw [he]
    rfl

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
