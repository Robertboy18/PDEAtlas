/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Convergence
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Convergence from a nonnegative diagonal series

Renaming every variable to the same variable collects the coefficients of
each total degree. For nonnegative coefficients, each original coefficient
is bounded by the collected coefficient. Thus convergence on the diagonal
implies native multivariable convergence.
-/

@[expose] public section

noncomputable section

namespace MvPowerSeries

variable {σ τ : Type*}

/-- With nonnegative coefficients, identifying variables can only increase a coefficient. -/
theorem coeff_le_coeff_rename (f : MvPowerSeries σ ℝ)
    (hf : ∀ a, 0 ≤ coeff a f) (g : σ → τ) [Filter.TendstoCofinite g] (a : σ →₀ ℕ) :
    coeff a f ≤ coeff (Finsupp.mapDomain g a) (rename g f) := by
  classical
  rw [coeff_rename]
  exact Finset.single_le_sum (fun b hb ↦ hf b) (by simp)

/-- Nonnegative multivariable coefficients converge if the diagonal scalar series converges. -/
theorem radius_pos_of_rename_constant [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ ℝ)
    (hf : ∀ a, 0 ≤ coeff a f)
    (h : 0 < (FormalMultilinearSeries.ofScalars ℝ
      (fun n ↦ PowerSeries.coeff n (rename (fun _ : σ ↦ ()) f))).radius) :
    0 < f.toFormalMultilinearSeries.radius := by
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n ↦ PowerSeries.coeff n (rename (fun _ : σ ↦ ()) f))).le_mul_pow_of_radius_pos h
  refine f.radius_pos_of_coeff_bound (C := C) hr ?_
  intro a
  have ha : Finsupp.mapDomain (fun _ : σ ↦ ()) a =
      Finsupp.single () (a.sum fun _ ↦ id) := by
    apply Finsupp.ext
    intro u
    cases u
    simp [Finsupp.mapDomain, Finsupp.sum_apply, Function.id_def]
  calc
    ‖coeff a f‖ = coeff a f := Real.norm_of_nonneg (hf a)
    _ ≤ coeff (Finsupp.mapDomain (fun _ : σ ↦ ()) a)
        (rename (fun _ : σ ↦ ()) f) := coeff_le_coeff_rename f hf _ a
    _ = PowerSeries.coeff (a.sum fun _ ↦ id) (rename (fun _ : σ ↦ ()) f) := by
      rw [ha]
      rfl
    _ ≤ ‖PowerSeries.coeff (a.sum fun _ ↦ id) (rename (fun _ : σ ↦ ()) f)‖ :=
      le_abs_self _
    _ ≤ C * r ^ (a.sum fun _ ↦ id) := by
      simpa only [FormalMultilinearSeries.ofScalars_norm] using hbound (a.sum fun _ ↦ id)

end MvPowerSeries
