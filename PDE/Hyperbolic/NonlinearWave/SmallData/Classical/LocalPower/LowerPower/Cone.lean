/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.ConeSolution
import CAS.ExactTactic

/-!
# A cone solution and its regular remainder

A C¹ scalar reaction and bounded C¹ velocity give a C¹ solution of the
Kirchhoff integral equation on a uniform open time strip. The integral term,
after removing its explicit factor `t²`, has the same finite regularity.
This records useful information at the initial slice without asserting C²
regularity for a merely C¹ reaction.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- The normalized nonlinear integral equation has a solution and a regular
remainder for every positive finite differentiability order. -/
theorem exists_cone_solution_with_remainder {k : ℕ} {f : ℝ → ℝ}
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
  have hAc : ContDiff ℝ (k + 1) A := contDiff_fst.prodMk (contDiff_freeField hh)
  have hw := hψreg.comp hAc.contDiffOn (fun _ hp ↦ hA hp)
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

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
