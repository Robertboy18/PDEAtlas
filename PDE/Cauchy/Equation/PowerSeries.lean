/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Composition
public import PDE.Analysis.Analytic.PowerSeries.FiniteOperations
public import PDE.Cauchy.Equation.Basic
public import PDE.Cauchy.Formal.Equation

/-!
# Power-series expansion of the scalar Cauchy equation

Expanding the mixed derivatives and coefficient compositions identifies
the analytic right-hand side with the formal equation. The proof uses only the
formal equation and its admissible substitutions, not the recursion.
-/

@[expose] public noncomputable section

open scoped Topology
open Filter PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

local notation "J" => (Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ))
local notation "T" => {α : Sym (Fin (d + 1)) k // α ≠ Sym.replicate k 0}
local notation "A" => J ⊕ Fin (d + 1)

/-- The power series of the scalar right-hand side is the formal right-hand side
evaluated at the power series of the coefficients and of the unknown. -/
theorem toMvPowerSeries_rightHandSide
    {a : T → (A → ℝ) → ℝ} {b : (A → ℝ) → ℝ}
    {u : ℝ^(d + 1) → ℝ}
    {pa : T → FormalMultilinearSeries ℝ (A → ℝ) ℝ}
    {pb : FormalMultilinearSeries ℝ (A → ℝ) ℝ}
    {pu : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
    (ha : ∀ α, HasFPowerSeriesAt (a α) (pa α) 0) (hb : HasFPowerSeriesAt b pb 0)
    (hu : HasFPowerSeriesAt (fun x ↦ u (WithLp.toLp 2 x)) pu 0)
    (hu0 : arguments k u 0 = 0)
    {r : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
    (hr : HasFPowerSeriesAt (fun x ↦ rightHandSide a b u (WithLp.toLp 2 x)) r 0) :
    r.toMvPowerSeries = formalRightHandSide
      (fun α ↦ (pa α).toMvPowerSeries) pb.toMvPowerSeries pu.toMvPowerSeries := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)).symm
  have he : AnalyticAt ℝ (fun x : Fin (d + 1) → ℝ ↦ WithLp.toLp 2 x) 0 :=
    e.analyticAt 0
  have hua : AnalyticAt ℝ u 0 := by
    have hof : AnalyticAt ℝ (fun y : ℝ^(d + 1) ↦ WithLp.ofLp y) 0 :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)).analyticAt 0
    simpa [Function.comp_def] using hu.analyticAt.comp_of_eq hof (by simp)
  have harg : AnalyticAt ℝ (fun x ↦ arguments k u (WithLp.toLp 2 x)) 0 :=
    (analyticAt_arguments hua).comp_of_eq he (WithLp.toLp_zero 2)
  have harg0 : arguments k u (WithLp.toLp 2 (0 : Fin (d + 1) → ℝ)) = 0 := by
    simpa only [WithLp.toLp_zero] using hu0
  have hargcomp (α : A) : AnalyticAt ℝ
      (fun x ↦ arguments k u (WithLp.toLp 2 x) α) 0 :=
    ((ContinuousLinearMap.proj α : (A → ℝ) →L[ℝ] ℝ).analyticAt _).comp harg
  choose parg hparg using hargcomp
  have hpargeq : (fun α ↦ (parg α).toMvPowerSeries) = formalArguments k pu.toMvPowerSeries := by
    funext α
    cases α with
    | inl α => exact hu.toMvPowerSeries_coordinateDeriv α.2 (hparg (.inl α))
    | inr i => exact (hparg (.inr i)).toMvPowerSeries_proj i
  have hcomp {F : (A → ℝ) → ℝ} {pF : FormalMultilinearSeries ℝ (A → ℝ) ℝ}
      (hF : HasFPowerSeriesAt F pF 0)
      {s : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
      (hs : HasFPowerSeriesAt (fun x ↦ F (arguments k u (WithLp.toLp 2 x))) s 0) :
      s.toMvPowerSeries =
        MvPowerSeries.subst (formalArguments k pu.toMvPowerSeries) pF.toMvPowerSeries := by
    rw [hF.toMvPowerSeries_comp hparg harg0 hs, hpargeq]
  have hac (α : T) : AnalyticAt ℝ (fun x ↦ a α (arguments k u (WithLp.toLp 2 x))) 0 :=
    (ha α).analyticAt.comp_of_eq harg harg0
  choose pac hpac using hac
  have hd (α : T) : AnalyticAt ℝ
      (fun x ↦ coordinateDeriv α.1 u (WithLp.toLp 2 x)) 0 :=
    (analyticAt_coordinateDeriv hua α.1).comp_of_eq he (WithLp.toLp_zero 2)
  choose pd hpd using hd
  have ht (α : T) : AnalyticAt ℝ
      (fun x ↦ a α (arguments k u (WithLp.toLp 2 x)) *
        coordinateDeriv α.1 u (WithLp.toLp 2 x)) 0 :=
    (hpac α).analyticAt.mul (hpd α).analyticAt
  choose pt hpt using ht
  obtain ⟨ps, hps⟩ := Finset.univ.analyticAt_fun_sum fun α _ ↦ (hpt α).analyticAt
  obtain ⟨pf, hpf⟩ := hb.analyticAt.comp_of_eq harg harg0
  have hadd := hps.toMvPowerSeries_add hpf (show HasFPowerSeriesAt
      ((fun x ↦ ∑ α, a α (arguments k u (WithLp.toLp 2 x)) *
        coordinateDeriv α.1 u (WithLp.toLp 2 x)) +
          fun x ↦ b (arguments k u (WithLp.toLp 2 x))) r 0 from hr)
  rw [hadd, hcomp hb hpf, HasFPowerSeriesAt.toMvPowerSeries_sum Finset.univ hpt hps]
  unfold formalRightHandSide
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  rw [(hpac α).toMvPowerSeries_mul (hpd α) (hpt α), hcomp (ha α) (hpac α),
    hu.toMvPowerSeries_coordinateDeriv α.1 (hpd α)]

end PDE.Cauchy.Quasilinear.Analytic
