/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.MajorantBounds
public import PDE.Analysis.Analytic.PowerSeries.TaylorRemainder
public import PDE.Analysis.Analytic.PowerSeries.Truncation
import Mathlib.Analysis.Analytic.Constructions

/-!
# Uniqueness of commutative analytic coefficients

Passing from a commutative formal series to its native multilinear realization
and back preserves every coefficient. More generally, native analytic expansions
have the same commutative coefficients whenever they represent the same germ.
Finite-order Taylor remainders determine the coefficients below that order.
-/

@[expose] public section

open scoped Topology
open Filter Asymptotics

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MvPowerSeries

/-- Commutative coefficient extraction is a retraction of native realization. -/
theorem toMvPowerSeries_toFormalMultilinearSeries (f : MvPowerSeries ι ℝ) :
    f.toFormalMultilinearSeries.toMvPowerSeries = f := by
  apply ext_of_toFormalMultilinearSeries_apply
  intro n x
  exact FormalMultilinearSeries.ofMultiindexCoefficients_multiindexCoeff_apply
    f.toFormalMultilinearSeries n x

end MvPowerSeries

namespace FormalMultilinearSeries

/-- Commutative coefficient extraction preserves subtraction. -/
theorem toMvPowerSeries_sub (p q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) :
    (p - q).toMvPowerSeries = p.toMvPowerSeries - q.toMvPowerSeries := by
  ext a
  change (p - q).multiindexCoeff a = p.multiindexCoeff a - q.multiindexCoeff a
  simp only [multiindexCoeff, ContinuousMultilinearMap.symCoefficient,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> simp

/-- A zero homogeneous diagonal has zero commutative coefficients in that degree. -/
theorem multiindexCoeff_eq_zero_of_apply_eq_zero
    (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (a : ι →₀ ℕ)
    (h : ∀ x, p (a.sum fun _ ↦ _root_.id) (fun _ ↦ x) = 0) :
    p.multiindexCoeff a = 0 := by
  let f := p.toMvPowerSeries
  let n := a.sum fun _ ↦ _root_.id
  have ht : f.truncTotal (n + 1) = f.truncTotal n := by
    apply MvPolynomial.funext
    intro x
    simp only [MvPowerSeries.eval_truncTotal, partialSum, Finset.sum_range_succ]
    have hd : f.toFormalMultilinearSeries n (fun _ ↦ x) = 0 := by
      rw [show f.toFormalMultilinearSeries n (fun _ ↦ x) = p n (fun _ ↦ x) from
        ofMultiindexCoefficients_multiindexCoeff_apply p n x]
      exact h x
    rw [hd, add_zero]
  have hc := congrArg (fun P : MvPolynomial ι ℝ ↦ P.coeff a) ht
  rw [MvPowerSeries.coeff_truncTotal f (show a.degree < n + 1 from Nat.lt_succ_self n),
    MvPowerSeries.coeff_truncTotal_eq_zero f (show n ≤ a.degree from le_rfl)] at hc
  exact hc

end FormalMultilinearSeries

/-- Native expansions of the same germ have identical commutative coefficients. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_eq {f g : (ι → ℝ) → ℝ}
    {p q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {x : ι → ℝ}
    (hp : HasFPowerSeriesAt f p x) (hq : HasFPowerSeriesAt g q x)
    (hfg : f =ᶠ[𝓝 x] g) : p.toMvPowerSeries = q.toMvPowerSeries := by
  have hz : HasFPowerSeriesAt 0 (p - q) x := by
    simpa only [sub_self] using (hp.congr hfg).sub hq
  apply MvPowerSeries.ext
  intro a
  have hc := (p - q).multiindexCoeff_eq_zero_of_apply_eq_zero a
    (hz.apply_eq_zero (a.sum fun _ ↦ id))
  change MvPowerSeries.coeff a p.toMvPowerSeries = MvPowerSeries.coeff a q.toMvPowerSeries
  apply sub_eq_zero.mp
  change MvPowerSeries.coeff a (p.toMvPowerSeries - q.toMvPowerSeries) = 0
  rw [← FormalMultilinearSeries.toMvPowerSeries_sub]
  exact hc

/-- A Taylor remainder of order `N` forces all commutative coefficients below `N` to vanish. -/
theorem HasFPowerSeriesAt.multiindexCoeff_eq_zero_of_isBigO_norm_pow
    {f : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) {N : ℕ}
    (hf : f =O[𝓝 0] fun x ↦ ‖x‖ ^ N) (a : ι →₀ ℕ) (ha : a.sum (fun _ ↦ id) < N) :
    p.multiindexCoeff a = 0 :=
  p.multiindexCoeff_eq_zero_of_apply_eq_zero a (hp.apply_eq_zero_of_isBigO_norm_pow hf ha)
