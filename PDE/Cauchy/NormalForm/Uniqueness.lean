/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Trace.Coordinate
public import PDE.Cauchy.Equation.PowerSeries
public import PDE.Cauchy.Formal.JetSystem.Equations
public import PDE.Cauchy.Formal.Recursion

/-!
# Analytic germ uniqueness for the scalar Cauchy equation

Zero traces of the pure time derivatives determine the first time coefficients.
The scalar equation then determines every later coefficient by the formal
recurrence, and equal power series give equal analytic germs. This is the observation at the
start of step 4 in the proof of Evans, §4.6.3, Theorem 2: the equation and the data determine
every derivative of a solution at the origin. Evans's Theorem 2 itself states only existence.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, proof of Theorem 2, step 4.
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

/-- Analytic solutions of the normalized scalar equation with zero Cauchy data
agree as germs. The Cauchy hypotheses are equalities on the initial hyperplane,
and only the pure time derivatives below the equation order are required. -/
theorem eventuallyEq_of_analytic_solution_zero
    {a : T → (A → ℝ) → ℝ} {b : (A → ℝ) → ℝ}
    (ha : ∀ α, AnalyticAt ℝ (a α) 0) (hb : AnalyticAt ℝ b 0)
    {u v : ℝ^(d + 1) → ℝ} (hu : AnalyticAt ℝ u 0) (hv : AnalyticAt ℝ v 0)
    (hutrace : ∀ j < k + 1, (fun x : Fin d → ℝ ↦
      coordinateDeriv (Sym.replicate j 0) u (WithLp.toLp 2 (Fin.cons 0 x))) =ᶠ[𝓝 0] 0)
    (hvtrace : ∀ j < k + 1, (fun x : Fin d → ℝ ↦
      coordinateDeriv (Sym.replicate j 0) v (WithLp.toLp 2 (Fin.cons 0 x))) =ᶠ[𝓝 0] 0)
    (hPu : coordinateDeriv (Sym.replicate (k + 1) 0) u =ᶠ[𝓝 0] rightHandSide a b u)
    (hPv : coordinateDeriv (Sym.replicate (k + 1) 0) v =ᶠ[𝓝 0] rightHandSide a b v) :
    u =ᶠ[𝓝 0] v := by
  choose pa hpa using ha
  obtain ⟨pb, hpb⟩ := hb
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)
  have het : Tendsto e.symm (𝓝 0) (𝓝 0) :=
    e.symm.continuous.tendsto' 0 0 (map_zero e.symm)
  have hformal {f : ℝ^(d + 1) → ℝ} (hf : AnalyticAt ℝ f 0)
      {p : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
      (hp : HasFPowerSeriesAt (fun x ↦ f (WithLp.toLp 2 x)) p 0)
      (htrace : ∀ j < k + 1, (fun x : Fin d → ℝ ↦
        coordinateDeriv (Sym.replicate j 0) f (WithLp.toLp 2 (Fin.cons 0 x))) =ᶠ[𝓝 0] 0)
      (hP : coordinateDeriv (Sym.replicate (k + 1) 0) f =ᶠ[𝓝 0] rightHandSide a b f) :
      (∀ j < k + 1, PowerSeries.coeff j (finSuccEquiv ℝ d p.toMvPowerSeries) = 0) ∧
        (pderiv 0)^[k + 1] p.toMvPowerSeries =
          formalRightHandSide (fun α ↦ (pa α).toMvPowerSeries) pb.toMvPowerSeries
            p.toMvPowerSeries := by
    have hd {j : ℕ} (α : Sym (Fin (d + 1)) j) : AnalyticAt ℝ
        (fun x ↦ coordinateDeriv α f (WithLp.toLp 2 x)) 0 :=
      (analyticAt_coordinateDeriv hf α).comp_of_eq (e.symm.analyticAt 0) (map_zero e.symm)
    have hzero (j : ℕ) (hj : j < k + 1) :
        PowerSeries.coeff j (finSuccEquiv ℝ d p.toMvPowerSeries) = 0 := by
      obtain ⟨q, hq⟩ := hd (Sym.replicate j 0)
      exact (hp.eventuallyEq_zero_coordinateDeriv_finCons_iff hq).mp (htrace j hj)
    have harg0 : arguments (k + 1) f 0 = 0 := by
      funext α
      cases α with
      | inl α =>
        obtain ⟨q, hq⟩ := hd α.2
        have ht := hq.eventuallyEq_zero_finCons_iff.mpr (by
          rw [hp.toMvPowerSeries_coordinateDeriv α.2 hq]
          exact constantCoeff_formalDerivativeTuple hzero α)
        simpa only [arguments, Sum.elim_inl, ← Matrix.vecCons.eq_1, Matrix.cons_zero_zero,
          WithLp.toLp_zero, Pi.zero_apply]
          using ht.eq_of_nhds
      | inr i => rfl
    obtain ⟨q, hq⟩ := hd (Sym.replicate (k + 1) 0)
    obtain ⟨r, hr⟩ := (analyticAt_rightHandSide
      (fun α ↦ (hpa α).analyticAt) hpb.analyticAt hf harg0).comp_of_eq
        (e.symm.analyticAt 0) (map_zero e.symm)
    have heq := hq.toMvPowerSeries_eq hr (hP.comp_tendsto het)
    rw [hp.toMvPowerSeries_coordinateDeriv _ hq,
      toMvPowerSeries_rightHandSide hpa hpb hp harg0 hr,
      Sym.coe_replicate, iteratedPDeriv_replicate] at heq
    exact ⟨hzero, heq⟩
  obtain ⟨pu, hpu⟩ := hu.comp_of_eq (e.symm.analyticAt 0) (map_zero e.symm)
  obtain ⟨pv, hpv⟩ := hv.comp_of_eq (e.symm.analyticAt 0) (map_zero e.symm)
  obtain ⟨w, _, hwunique⟩ := existsUnique_formal_solution (Nat.succ_pos k)
    (fun α ↦ (pa α).toMvPowerSeries) pb.toMvPowerSeries
  have hpq : pu.toMvPowerSeries = pv.toMvPowerSeries :=
    (hwunique _ (hformal hu hpu hutrace hPu)).trans
      (hwunique _ (hformal hv hpv hvtrace hPv)).symm
  have heq := (hpu.eventuallyEq_of_toMvPowerSeries_eq hpv hpq).comp_tendsto
    (e.continuous.tendsto' 0 0 (map_zero e))
  filter_upwards [heq] with x hx
  change u (e.symm (e x)) = v (e.symm (e x)) at hx
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx

end PDE.Cauchy.Quasilinear.Analytic
