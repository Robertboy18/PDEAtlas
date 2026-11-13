/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Differentiation
public import PDE.Analysis.Analytic.PowerSeries.IteratedDerivative

/-!
# Mixed derivatives of analytic expansions

Evaluating an iterated Fréchet derivative on coordinate directions gives
the corresponding mixed formal derivative of its commutative expansion.
Analyticity supplies differentiability on a neighborhood at every finite order.
-/

@[expose] public section

open scoped Topology
open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Iterated coordinate differentiation agrees with mixed differentiation
of the commutative Taylor expansion. The tuple order disappears in the formal
multiset of directions. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_iteratedFDeriv_apply
    {f : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) {n : ℕ} (v : Fin n → ι)
    {q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hq : HasFPowerSeriesAt
      (fun x ↦ iteratedFDeriv ℝ n f x (fun i ↦ Pi.single (v i) 1)) q 0) :
    q.toMvPowerSeries =
      MvPowerSeries.iteratedPDeriv (List.ofFn v : Multiset ι) p.toMvPowerSeries := by
  have hI (j : ℕ) (x : ι → ℝ) (hx : AnalyticAt ℝ f x) :
      AnalyticAt ℝ (iteratedFDeriv ℝ j f) x :=
    (show AnalyticOnNhd ℝ f {y | AnalyticAt ℝ f y} from fun _ hy ↦ hy).iteratedFDeriv j x hx
  induction n generalizing q with
  | zero =>
    have hq' : HasFPowerSeriesAt f q 0 := by
      simpa only [iteratedFDeriv_zero_apply] using hq
    simpa only [List.ofFn_zero, Multiset.coe_nil, MvPowerSeries.iteratedPDeriv_zero_multiset]
      using hq'.toMvPowerSeries_eq hp EventuallyEq.rfl
  | succ n ih =>
    let L : (((ι → ℝ) [×n]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ ι → ℝ) ℝ
        (fun i ↦ Pi.single (v i.succ) 1)
    obtain ⟨r, hr⟩ := (L.analyticAt _).comp (hI n 0 hp.analyticAt)
    have hr' : HasFPowerSeriesAt
        (fun x ↦ iteratedFDeriv ℝ n f x (fun i ↦ Pi.single (v i.succ) 1)) r 0 := hr
    have he :
        (fun x ↦ iteratedFDeriv ℝ (n + 1) f x (fun i ↦ Pi.single (v i) 1)) =ᶠ[𝓝 0]
          (fun x ↦ fderiv ℝ
            (fun y ↦ iteratedFDeriv ℝ n f y (fun i ↦ Pi.single (v i.succ) 1))
              x (Pi.single (v 0) 1)) := by
      filter_upwards [hp.analyticAt.eventually_analyticAt] with x hx
      exact (hI n x hx).differentiableAt.iteratedFDeriv_succ_apply_left'
    rw [hr'.toMvPowerSeries_fderiv_apply (v 0) (hq.congr he), ih (Fin.tail v) hr']
    simpa only [List.ofFn_succ, Multiset.cons_coe, Fin.tail_def] using
      (MvPowerSeries.iteratedPDeriv_cons (v 0) (List.ofFn (Fin.tail v))
        p.toMvPowerSeries).symm
