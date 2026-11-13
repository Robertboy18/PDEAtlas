/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Trace
public import PDE.Cauchy.Formal.Convergence
public import PDE.Cauchy.Equation.PowerSeries

/-!
# Analytic existence for the scalar equation with zero Cauchy data

The convergent scalar formal solution defines an analytic function on a
Euclidean ball of positive radius. Its coordinate derivatives have the prescribed
formal expansions, so it satisfies the scalar PDE. Vanishing time coefficients
give the whole zero lower jet on the initial hyperplane. `exists_analytic_solution_zero`
solves the problem (14) of Evans, §4.6.3, with the equation solved for the pure time
derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, (14).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Topology
open Filter PDE.Analysis.MultiIndex MvPowerSeries

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

local notation "J" => (Σ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ))
local notation "T" => {α : Sym (Fin (d + 1)) (k + 1) // α ≠ Sym.replicate (k + 1) 0}
local notation "A" => J ⊕ Fin (d + 1)

/-- A normalized analytic scalar equation of any positive order has an analytic
solution with zero Cauchy data on a Euclidean ball of positive radius. -/
theorem exists_analytic_solution_zero
    (a : T → (A → ℝ) → ℝ) (b : (A → ℝ) → ℝ)
    (ha : ∀ α, AnalyticAt ℝ (a α) 0) (hb : AnalyticAt ℝ b 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : ℝ^(d + 1) → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r, x 0 = 0 → coordinateJetLT (k + 1) u x = 0) ∧
      ∀ x ∈ Metric.ball 0 r,
        coordinateDeriv (Sym.replicate (k + 1) 0) u x = rightHandSide a b u x := by
  choose pa hpa using ha
  obtain ⟨pb, hpb⟩ := hb
  obtain ⟨v, hvzero, hveq, hvr⟩ := exists_convergent_formal_solution pa pb
    (fun α ↦ (hpa α).radius_pos) hpb.radius_pos
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)
  let u (x : ℝ^(d + 1)) : ℝ := v.toFormalMultilinearSeries.sum (e x)
  have hp : HasFPowerSeriesAt (fun x ↦ u (WithLp.toLp 2 x))
      v.toFormalMultilinearSeries 0 := by
    simpa only [u, e, PiLp.coe_continuousLinearEquiv, WithLp.ofLp_toLp] using
      (v.toFormalMultilinearSeries.hasFPowerSeriesOnBall hvr).hasFPowerSeriesAt
  have hua : AnalyticAt ℝ u 0 := by
    have hs := (v.toFormalMultilinearSeries.hasFPowerSeriesOnBall hvr).hasFPowerSeriesAt
    exact hs.analyticAt.comp_of_eq (e.analyticAt 0) (map_zero e)
  have hd (α : J) : AnalyticAt ℝ
      (fun x ↦ coordinateDeriv α.2 u (WithLp.toLp 2 x)) 0 :=
    (analyticAt_coordinateDeriv hua α.2).comp_of_eq (e.symm.analyticAt 0) (map_zero e.symm)
  choose pd hpd using hd
  have htrace (α : J) :
      (fun x : Fin d → ℝ ↦ coordinateDeriv α.2 u (WithLp.toLp 2 (Fin.cons 0 x))) =ᶠ[𝓝 0] 0 :=
    (hpd α).eventuallyEq_zero_finCons_iff.mpr (by
      rw [hp.toMvPowerSeries_coordinateDeriv α.2 (hpd α),
        toMvPowerSeries_toFormalMultilinearSeries]
      exact constantCoeff_formalDerivativeTuple hvzero α)
  have harg0 : arguments (k + 1) u 0 = 0 := by
    funext α
    cases α with
    | inl α =>
      simpa only [arguments, Sum.elim_inl, ← Matrix.vecCons.eq_1, Matrix.cons_zero_zero,
        WithLp.toLp_zero, Pi.zero_apply]
        using (htrace α).eq_of_nhds
    | inr i => rfl
  have htop : AnalyticAt ℝ
      (fun x ↦ coordinateDeriv (Sym.replicate (k + 1) 0) u (WithLp.toLp 2 x)) 0 :=
    (analyticAt_coordinateDeriv hua _).comp_of_eq (e.symm.analyticAt 0) (map_zero e.symm)
  obtain ⟨ptop, hptop⟩ := htop
  obtain ⟨prhs, hprhs⟩ :=
    (analyticAt_rightHandSide (fun α ↦ (hpa α).analyticAt) hpb.analyticAt hua harg0).comp_of_eq
      (e.symm.analyticAt 0) (map_zero e.symm)
  have hEq :
      (fun x ↦ coordinateDeriv (Sym.replicate (k + 1) 0) u (WithLp.toLp 2 x)) =ᶠ[𝓝 0]
        (fun x ↦ rightHandSide a b u (WithLp.toLp 2 x)) := by
    apply hptop.eventuallyEq_of_toMvPowerSeries_eq hprhs
    rw [hp.toMvPowerSeries_coordinateDeriv _ hptop,
      toMvPowerSeries_rightHandSide hpa hpb hp harg0 hprhs,
      toMvPowerSeries_toFormalMultilinearSeries,
      Sym.coe_replicate, iteratedPDeriv_replicate]
    exact hveq
  have hEqNative :
      coordinateDeriv (Sym.replicate (k + 1) 0) u =ᶠ[𝓝 0] rightHandSide a b u := by
    filter_upwards [hEq.comp_tendsto (e.continuous.tendsto' 0 0 (map_zero e))] with x hx
    change coordinateDeriv (Sym.replicate (k + 1) 0) u (WithLp.toLp 2 (e x)) =
      rightHandSide a b u (WithLp.toLp 2 (e x)) at hx
    simpa only [e, PiLp.coe_continuousLinearEquiv, WithLp.toLp_ofLp] using hx
  have htail : Tendsto (fun x : ℝ^(d + 1) ↦ Fin.tail (e x)) (𝓝 0) (𝓝 0) := by
    have h : AnalyticAt ℝ (fun x : ℝ^(d + 1) ↦ Fin.tail (e x)) 0 :=
      AnalyticAt.pi fun j ↦
        (EuclideanSpace.proj j.succ : ℝ^(d + 1) →L[ℝ] ℝ).analyticAt 0
    have hz : Fin.tail (e (0 : ℝ^(d + 1))) = 0 := by
      ext j
      rfl
    exact hz ▸ h.continuousAt.tendsto
  have htraceNative (α : J) :
      ∀ᶠ x : ℝ^(d + 1) in 𝓝 0, x 0 = 0 → coordinateDeriv α.2 u x = 0 := by
    filter_upwards [(htrace α).comp_tendsto htail] with x hx ht
    have heq : WithLp.toLp 2 (Fin.cons 0 (Fin.tail (e x))) = x := by
      ext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [PiLp.toLp_apply, Fin.cons_zero] using ht.symm
      · rfl
    simpa only [Function.comp_apply, heq, Pi.zero_apply] using hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hua.eventually_analyticAt.and (hEqNative.and (eventually_all.mpr htraceNative)))
  refine ⟨r, hr, u, fun x hx ↦ (hball hx).1, ?_, fun x hx ↦ (hball hx).2.1⟩
  intro x hx ht
  funext j α
  exact (hball hx).2.2 ⟨j, α⟩ ht

end PDE.Cauchy.Quasilinear.Analytic
