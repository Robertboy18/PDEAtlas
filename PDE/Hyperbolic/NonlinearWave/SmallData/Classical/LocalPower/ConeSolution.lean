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

`LowerPower.exists_cone_solution_with_remainder` does this for every positive finite
order: a `C^(k+1)` scalar reaction and a bounded `C^(k+1)` velocity give a `C^(k+1)` solution,
and the integral term, after removing its explicit factor `t²`, has the same regularity. The
case `k = 0` records information at the initial slice without asserting C² regularity for a
merely C¹ reaction. `exists_cone_solution` is the case `k = 1` without the remainder.
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

/-- The normalized nonlinear integral equation has a solution and a regular
remainder for every positive finite differentiability order: for a reaction and a bounded
velocity of class `C^(k+1)` there are a time `T > 0` and fields `v`, `a` of class `C^(k+1)` on
`|t| < T` with `v = t * (spherical mean of h) + t² a`, where `a` is the normalized Duhamel
integral of `f ∘ v`. -/
theorem LowerPower.exists_cone_solution_with_remainder {k : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ (k + 1) f) (h : ℝ^3 →ᵇ ℝ) (hh : ContDiff ℝ (k + 1) h) :
    ∃ T : ℝ, 0 < T ∧ ∃ v a : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ (k + 1) v {p | |p.1| < T} ∧
      ContDiffOn ℝ (k + 1) a {p | |p.1| < T} ∧
      (∀ p : ℝ × ℝ^3, |p.1| < T →
        v p = p.1 * unitSphereAverage 3 h p.2 p.1 + p.1 ^ 2 * a p) ∧
      ∀ p : ℝ × ℝ^3, |p.1| < T →
        a p = ∫ s : I, (1 - (s : ℝ)) *
          ((∫ ω : Direction,
            f (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
              ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  let N := composeCompact (α := Cone) ⟨f, hf.continuous⟩
  obtain ⟨δ, r, hδ, _, ψ, hψreg, hψsmall, hψeq, hψunique⟩ :=
    PDE.Analysis.exists_local_integral_solution (k := k) duhamelOperator
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
          simp only [smul_apply, restrictCone_apply,
            duhamelOperator_descend, hN, smul_eq_mul]
          change p.1 ^ 2 * (coneTime q ^ 2 * _) = (p.1 * coneTime q) ^ 2 * _
          cas
  let v : ℝ × ℝ^3 → ℝ := fun p ↦ ψ (A p) vertex
  have hv {p : ℝ × ℝ^3} (hp : |p.1| < T) (q : Cone) :
      v (physicalPoint p q) = ψ (A p) q := by
    dsimp only [v]
    rw [hrestrict hp q, restrictCone_apply, descend_vertex_right]
  let a : ℝ × ℝ^3 → ℝ := fun p ↦ duhamelOperator (N (ψ (A p))) vertex
  have hAc : ContDiff ℝ (k + 1) A := contDiff_fst.prodMk (contDiff_freeField hh)
  have hw := hψreg.comp (s := {p : ℝ × ℝ^3 | |p.1| < T}) hAc.contDiffOn (fun _ hp ↦ hA hp)
  have ha := duhamelOperator.contDiff.comp_contDiffOn
    ((contDiff_composeCompact hf).comp_contDiffOn hw)
  refine ⟨T, div_pos hδ (by positivity), v, a, ?_, ?_, ?_, ?_⟩
  · exact (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn hw
  · exact (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn ha
  · intro p hp
    have he := congrArg (fun w : Cone →ᵇ ℝ ↦ w vertex) (hψeq _ (hA hp))
    change v p = freeField h.toContinuousMap p vertex + p.1 ^ 2 * a p at he
    simpa only [freeField_apply, coe_toContinuousMap, vertex, coneTime, coneSpace, mul_one,
      smul_zero, add_zero] using he
  · intro p hp
    change duhamelOperator (N (ψ (A p))) vertex = _
    rw [duhamelOperator_apply]
    simp only [N, composeCompact_apply, descend_vertex_left]
    simp only [vertex, coneTime, one_pow, one_mul]
    congr 1 with s
    congr 3 with ω
    exact congrArg f (hv hp (rim s ω)).symm

/-- For a C² scalar source and bounded C² velocity, the normalized Kirchhoff
equation has a jointly C² solution on a uniform open time strip. This is
`LowerPower.exists_cone_solution_with_remainder` at order two, without its remainder. -/
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
  obtain ⟨T, hT, v, a, hv, -, heq, hint⟩ :=
    LowerPower.exists_cone_solution_with_remainder (k := 1) hf h hh
  exact ⟨T, hT, v, hv, fun p hp ↦ by rw [heq p hp, hint p hp]⟩

end WaveEquation.SmallData.Classical.LocalPower
