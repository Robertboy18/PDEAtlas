/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Energy.Balance
public import PDE.Hyperbolic.Classical.VariableCoefficient.Energy.Bounds
public import PDE.Hyperbolic.Classical.VariableCoefficient.Energy.Flux
public import PDE.Analysis.Calculus.CompactEnergy.SublevelCutoff
import PDE.FDeriv.Calculus

/-!
# Weighted energy on characteristic sublevels

The cutoff contributes the nonpositive term `χ'/ε (F · Dq - H)`.
The remaining coefficient term is bounded on a fixed compact sublevel.
The equation is used only where the cutoff is positive.
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open PDE.Common PDE.Analysis

variable {n : ℕ}

/-- Product differentiation separates a weight from the local matrix energy balance. -/
theorem weighted_energy_balance {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {u φ : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (ha : ∀ i j, ContDiffAt ℝ 1 (fun x ↦ a x i j) (spatialPart p))
    (hu : ContDiffAt ℝ 2 u p) (hφ : DifferentiableAt ℝ φ p) :
    (∂[0] (fun z ↦ φ z * energyDensity a u z)) p -
        ∑ j, (∂[j.succ] (fun z ↦ φ z * energyFlux a u j z)) p =
      φ p * ((∂[0] (energyDensity a u)) p -
        ∑ j, (∂[j.succ] (energyFlux a u j)) p) +
      ((∂[0] φ) p * energyDensity a u p -
        ∑ j, (∂[j.succ] φ) p * energyFlux a u j p) := by
  rw [PDE.partialDeriv_mul hφ ((contDiffAt_energyDensity ha hu).differentiableAt one_ne_zero)]
  simp_rw [PDE.partialDeriv_mul hφ ((contDiffAt_energyFlux ha hu _).differentiableAt one_ne_zero)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The characteristic contribution of the shrinking cutoff is nonpositive. -/
theorem cutoff_characteristic_term_nonpos {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ x i j, a x i j = a x j i) (hpos : ∀ x (v : ℝ^n), 0 ≤ ∑ i, ∑ j, a x i j * v i * v j)
    {q : ℝ^n → ℝ} (hq : Continuous q) (hqd : ∀ x, q x ≠ 0 → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, q x ≠ 0 → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) (u : ℝ^(n + 1) → ℝ)
    {r ε t : ℝ} (hε : 0 < ε) (ht : t < r - ε) (x : ℝ^n) :
    (∂[0] (sublevelCutoff q r ε)) (timeSpaceCons t x) * energyDensity a u (timeSpaceCons t x) - ∑ j,
      (∂[j.succ] (sublevelCutoff q r ε)) (timeSpaceCons t x) *
      energyFlux a u j (timeSpaceCons t x) ≤ 0 := by
  by_cases hz : q x = 0
  · have heq := sublevelCutoff_eventuallyEq_one hq hε
      (p := timeSpaceCons t x) (by simpa using ht) (by simpa using hz)
    have hd (i : Fin (n + 1)) :
        (∂[i] (sublevelCutoff q r ε)) (timeSpaceCons t x) = 0 := by
      rw [PDE.partialDeriv_congr_nhds i heq]
      simp
    simp [hd]
  · have hqc := hqd x hz
    have hw := (contDiffAt_sublevelCutoff hq hqd hε
      (p := timeSpaceCons t x) (by simpa using ht)).differentiableAt one_ne_zero
    rw [partialDeriv_time_sublevelCutoff hw]
    simp_rw [partialDeriv_spatial_sublevelCutoff hε hqc]
    let k := deriv Real.smoothTransition ((r - t - q x) / ε) / ε
    have hk : 0 ≤ k := sublevelCutoff_slope_nonneg hε _
    have hf := energyFlux_eikonal_le u (timeSpaceCons t x) (WithLp.toLp 2 fun i ↦ (∂[i] q) x)
      (by simpa using hsymm x) (by simpa using hpos x) (by simpa using heik x hz)
    have halgebra : -deriv Real.smoothTransition ((r - t - q x) / ε) / ε *
            energyDensity a u (timeSpaceCons t x) -
          (∑ j, -deriv Real.smoothTransition ((r - t - q x) / ε) / ε *
            (∂[j] q) x * energyFlux a u j (timeSpaceCons t x)) =
        k * ((∑ j, energyFlux a u j (timeSpaceCons t x) * (∂[j] q) x) -
          energyDensity a u (timeSpaceCons t x)) := by
      simp only [k, neg_div, mul_assoc, ← Finset.mul_sum]
      simp_rw [mul_comm ((∂[_] q) x)]
      ring
    rw [halgebra]
    exact mul_nonpos_of_nonneg_of_nonpos hk (sub_nonpos.mpr hf)

/-- The weighted matrix energy satisfies the compact-sublevel differential inequality. -/
theorem weighted_energy_local_inequality {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {q : ℝ^n → ℝ}
    (hq : Continuous q) (hqd : ∀ x, q x ≠ 0 → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, q x ≠ 0 → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {u : ℝ^(n + 1) → ℝ}
    {r ε t D : ℝ} (hε : 0 < ε) (ht : 0 < t) (htr : t < r - ε) (x : ℝ^n)
    (hu : ContDiffAt ℝ 2 u (timeSpaceCons t x))
    (hpde : q x < r - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hbound : ∀ y, q y ≤ r → ‖coefficientDivergence a y‖ ≤ D) :
    (∂[0] (fun p ↦ sublevelCutoff q r ε p * energyDensity a u p))
        (timeSpaceCons t x) -
      (∑ j, (∂[j.succ]
        (fun p ↦ sublevelCutoff q r ε p * energyFlux a u j p)) (timeSpaceCons t x)) ≤
      (1 + D ^ 2 / θ) * (sublevelCutoff q r ε (timeSpaceCons t x) *
        energyDensity a u (timeSpaceCons t x)) := by
  have hlocal (i j : Fin n) : ContDiffAt ℝ 1 (fun y ↦ a y i j) (spatialPart (timeSpaceCons t x)) :=
    (ha i j).contDiffAt
  have hw := (contDiffAt_sublevelCutoff hq hqd hε
    (p := timeSpaceCons t x) (by simpa using htr)).differentiableAt one_ne_zero
  rw [weighted_energy_balance hlocal hu hw]
  have hchar := cutoff_characteristic_term_nonpos hsymm
    (quadratic_nonneg_of_elliptic hθ hell) hq hqd heik u hε htr x
  by_cases hx : q x < r - t
  · rw [energy_balance hlocal (by simpa using hsymm x) hu, hpde hx, mul_zero, zero_sub]
    have hb := coefficient_remainder_le_energy hθ hell u (timeSpaceCons t x)
      (by simpa using hbound x (hx.le.trans (sub_le_self r ht.le)))
    have hh := mul_le_mul_of_nonneg_left
      ((neg_le_abs _).trans hb) (sublevelCutoff_nonneg q r ε (timeSpaceCons t x))
    nlinarith
  · rw [sublevelCutoff_eq_zero hε (le_of_not_gt hx)]
    simpa using hchar

end WaveEquation.VariableCoefficient
