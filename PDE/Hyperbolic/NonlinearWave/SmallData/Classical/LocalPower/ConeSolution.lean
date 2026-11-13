/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitFunction.IntegralEquation
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.FreeField
import CAS.ExactTactic

/-!
# A classical field satisfying the nonlinear cone equation

The implicit function theorem constructs fields on compact normalized cones.
Uniqueness in its uniform neighborhood identifies restrictions to smaller cones.
Consequently evaluation at the vertex gives one spacetime field satisfying
the Kirchhoff integral equation on a uniform time interval.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower

/-- The physical point represented by a point in a normalized backward cone. -/
def physicalPoint (p : ℝ × ℝ^3) (q : Cone) : ℝ × ℝ^3 :=
  (p.1 * coneTime q, p.2 + p.1 • coneSpace q)

/-- All physical points of a cone have no larger absolute time. -/
theorem abs_physicalPoint_time_le (p : ℝ × ℝ^3) (q : Cone) :
    |(physicalPoint p q).1| ≤ |p.1| := by
  change |p.1 * coneTime q| ≤ |p.1|
  rw [abs_mul, abs_of_nonneg (coneTime_mem q).1]
  simpa using mul_le_mul_of_nonneg_left (coneTime_mem q).2 (abs_nonneg p.1)

/-- The free field and time together are the parameters of the implicit equation. -/
def coneParameter (h : C(ℝ^3, ℝ)) (p : ℝ × ℝ^3) : ℝ × (Cone →ᵇ ℝ) :=
  (p.1, freeField h p)

/-- A uniform bound on the velocity puts every spatial center in the same
implicit-function neighborhood. -/
theorem coneParameter_mem_ball (h : ℝ^3 →ᵇ ℝ) {δ : ℝ} {p : ℝ × ℝ^3} (hp : |p.1| < δ / (‖h‖ + 1)) :
    coneParameter h.toContinuousMap p ∈ Metric.ball 0 δ := by
  have hlt := (lt_div_iff₀ (by positivity : 0 < ‖h‖ + 1)).mp hp
  have ht : |p.1| ≤ |p.1| * (‖h‖ + 1) := by nlinarith [norm_nonneg h, abs_nonneg p.1]
  have hh : |p.1| * ‖h‖ ≤ |p.1| * (‖h‖ + 1) := by nlinarith [abs_nonneg p.1]
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
  exact ⟨by simpa only [coneParameter, Real.norm_eq_abs] using ht.trans_lt hlt,
    (norm_freeField_le h p).trans_lt (hh.trans_lt hlt)⟩

/-- For a C² scalar source and bounded C² velocity, the normalized Kirchhoff
equation has a jointly C² solution on a uniform open time strip. -/
theorem exists_cone_solution {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h : ℝ^3 →ᵇ ℝ) (hh : ContDiff ℝ 2 h) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 2 v {p | |p.1| < T} ∧
      ∀ p : ℝ × ℝ^3, |p.1| < T →
        v p = p.1 * unitSphereAverage 3 h p.2 p.1 +
          p.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
            ((∫ ω : Direction,
              f (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
                ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  let N := composeCompact (α := Cone) ⟨f, hf.continuous⟩
  obtain ⟨δ, r, hδ, _, ψ, hψreg, hψsmall, hψeq, hψunique⟩ :=
    PDE.Analysis.exists_local_integral_solution (k := 1) duhamelOperator
      (contDiff_composeCompact hf)
  let T := δ / (‖h‖ + 1)
  let A := coneParameter h.toContinuousMap
  have hA {p : ℝ × ℝ^3} (hp : |p.1| < T) : A p ∈ Metric.ball 0 δ := coneParameter_mem_ball h hp
  have hrestrict {p : ℝ × ℝ^3} (hp : |p.1| < T) (q : Cone) :
      ψ (A (physicalPoint p q)) = restrictCone q (ψ (A p)) := by
    apply hψunique _ (hA ((abs_physicalPoint_time_le p q).trans_lt hp))
    · exact (norm_restrictCone_le q _).trans_lt (hψsmall _ (hA hp))
    · have he := hψeq _ (hA hp)
      change ψ (A p) = freeField h.toContinuousMap p + p.1 ^ 2 • duhamelOperator (N (ψ (A p))) at he
      calc
        restrictCone q (ψ (A p)) = restrictCone q (freeField h.toContinuousMap p) +
              p.1 ^ 2 • restrictCone q (duhamelOperator (N (ψ (A p)))) := by
          conv_lhs => rw [he]
          rw [map_add, map_smul]
        _ = (A (physicalPoint p q)).2 + (A (physicalPoint p q)).1 ^ 2 •
              duhamelOperator (N (restrictCone q (ψ (A p)))) := by
          rw [restrictCone_freeField]
          apply congrArg (fun w ↦ freeField h.toContinuousMap (physicalPoint p q) + w)
          have hN : restrictCone q (N (ψ (A p))) =
              N (restrictCone q (ψ (A p))) := by ext z; rfl
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
  refine ⟨T, div_pos hδ (by positivity), v, ?_, ?_⟩
  · have hAc : ContDiff ℝ 2 A := contDiff_fst.prodMk (contDiff_freeField hh)
    have hw := hψreg.comp hAc.contDiffOn (fun _ hp ↦ hA hp)
    exact (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn hw
  · intro p hp
    have he := congrArg (fun w : Cone →ᵇ ℝ ↦ w vertex) (hψeq _ (hA hp))
    change v p = freeField h.toContinuousMap p vertex +
      p.1 ^ 2 * duhamelOperator (N (ψ (A p))) vertex at he
    rw [he, freeField_apply, duhamelOperator_apply]
    simp only [N, composeCompact_apply, descend_vertex_left]
    simp only [vertex, coneTime, coneSpace, mul_one, smul_zero, add_zero, one_pow, one_mul]
    congr 2
    congr 1 with s
    congr 3 with ω
    exact congrArg f (hv hp (rim s ω)).symm

end WaveEquation.SmallData.Classical.LocalPower
