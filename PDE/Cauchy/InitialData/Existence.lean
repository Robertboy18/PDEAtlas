/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.NormalForm.Existence
public import PDE.Cauchy.InitialData.Normalization

/-!
# Analytic scalar existence with a data extension

An analytic extension of the Cauchy data is subtracted before solving the
zero-data equation. Noncharacteristicity is required only at its initial jet.
Continuity then gives a common neighborhood on which the normalized solution
satisfies the original equation. `Hypersurface/Existence` applies this in a
level chart.

This is the reduction to zero Cauchy data in Evans, §4.6.3(a), on the hyperplane `x 0 = 0`;
`hprincipal` is Evans's noncharacteristic condition `a_(0,...,0,k) ≠ 0` for the pure time
derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(a).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Topology
open Filter PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}


/-- A noncharacteristic analytic equation admits an analytic solution carrying
the entire lower hyperplane jet of an analytic data extension. The coefficient
functions depend on position and every derivative below the equation order. -/
theorem exists_analytic_solution_of_data_extension
    (a : Sym (Fin (d + 1)) (k + 1) →
      ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (G : ℝ^(d + 1) → ℝ)
    (ha : ∀ α, AnalyticAt ℝ (a α) (0, coordinateJetLT (k + 1) G 0))
    (hb : AnalyticAt ℝ b (0, coordinateJetLT (k + 1) G 0))
    (hG : AnalyticAt ℝ G 0)
    (hprincipal : a (Sym.replicate (k + 1) 0) (0, coordinateJetLT (k + 1) G 0) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : ℝ^(d + 1) → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r, x 0 = 0 →
        coordinateJetLT (k + 1) u x = coordinateJetLT (k + 1) G x) ∧
      ∀ x ∈ Metric.ball 0 r,
        ∑ α, a α (x, coordinateJetLT (k + 1) u x) * coordinateDeriv α u x =
          b (x, coordinateJetLT (k + 1) u x) := by
  obtain ⟨r, hr, w, hw, htrace, hP⟩ := exists_analytic_solution_zero
    (normalizedCoefficients a G) (normalizedForcing a b G)
    (analyticAt_normalizedCoefficients ha hG hprincipal)
    (analyticAt_normalizedForcing ha hb hG hprincipal)
  have hw0 := hw 0 (Metric.mem_ball_self hr)
  have harg0 : arguments (k + 1) w 0 = 0 := by
    have hj := htrace 0 (Metric.mem_ball_self hr) rfl
    funext α
    cases α with
    | inl α => exact congrFun (congrFun hj α.1) α.2
    | inr i => rfl
  have hshift : AnalyticAt ℝ
      (fun x ↦ shiftedArguments (k + 1) G (arguments (k + 1) w x)) 0 :=
    (analyticAt_shiftedArguments hG).comp_of_eq (analyticAt_arguments hw0) harg0
  have hshift0 :
      shiftedArguments (k + 1) G (arguments (k + 1) w 0) =
        (0, coordinateJetLT (k + 1) G 0) := by
    rw [harg0, shiftedArguments_zero]
  have hden : ∀ᶠ x in 𝓝 (0 : ℝ^(d + 1)),
      a (Sym.replicate (k + 1) 0)
        (shiftedArguments (k + 1) G (arguments (k + 1) w x)) ≠ 0 :=
    ((ha _).comp_of_eq hshift hshift0).continuousAt.eventually_ne
      (by simpa only [Function.comp_apply, hshift0] using hprincipal)
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.Eventually.and (Metric.ball_mem_nhds 0 hr)
      (hG.eventually_analyticAt.and hden))
  refine ⟨s, hs, G + w, ?_, ?_, ?_⟩
  · intro x hx
    exact (hball hx).2.1.add (hw x (hball hx).1)
  · intro x hx ht
    have hj := htrace x (hball hx).1 ht
    funext j α
    change coordinateDeriv α (G + w) x = coordinateDeriv α G x
    rw [coordinateDeriv_add α (hball hx).2.1.contDiffAt (hw x (hball hx).1).contDiffAt]
    exact add_eq_left.mpr (congrFun (congrFun hj j) α)
  · intro x hx
    have hnonzero :
        a (Sym.replicate (k + 1) 0) (x, coordinateJetLT (k + 1) (G + w) x) ≠ 0 := by
      simpa only [shiftedArguments_arguments (hball hx).2.1 (hw x (hball hx).1)]
        using (hball hx).2.2
    exact (equation_add_iff a b (hball hx).2.1 (hw x (hball hx).1) hnonzero).mpr
      (hP x (hball hx).1)

end PDE.Cauchy.Quasilinear.Analytic
