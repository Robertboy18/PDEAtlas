/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.CoefficientBounds
public import PDE.Analysis.Analytic.PowerSeries.Geometric
public import PDE.Analysis.Analytic.PowerSeries.Majorization

/-!
# Geometric majorants from native analytic expansions

Exponential coefficient estimates imply domination by one geometric denominator.
In particular, a native positive-radius multilinear expansion supplies such a
majorant without an assumed convergence certificate for its coordinate series.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace MvPowerSeries

variable {σ : Type*} [Fintype σ]

/-- An exponential coefficient bound gives a multivariable geometric majorant. -/
theorem isMajorizedOn_C_mul_inv_C_sub_sum_X {f : MvPowerSeries σ ℝ} {M r : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r)
    (hf : ∀ a, ‖coeff a f‖ ≤ M * r ^ (a.sum fun _ ↦ id)) :
    IsMajorizedOn f (C (M * r⁻¹) * (C r⁻¹ - ∑ i : σ, X i)⁻¹) Set.univ := by
  intro a ha
  rw [coeff_C_mul]
  calc
    ‖coeff a f‖ ≤ M * r ^ (a.sum fun _ ↦ id) := hf a
    _ = (M * r⁻¹) * (r⁻¹)⁻¹ ^ (a.sum (fun _ ↦ id) + 1) := by
      rw [inv_inv, pow_succ]
      symm
      calc
        _ = (M * r ^ (a.sum fun _ ↦ id)) * (r⁻¹ * r) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hr.ne', mul_one]
    _ ≤ (M * r⁻¹) * coeff a (C r⁻¹ - ∑ i : σ, X i)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_pow_le_coeff_inv_C_sub_sum_X (inv_pos.mpr hr) a)
        (mul_nonneg hM (inv_nonneg.mpr hr.le))

end MvPowerSeries

namespace FormalMultilinearSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The commutative coordinate series of a real native multilinear expansion. -/
def toMvPowerSeries (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) : MvPowerSeries ι ℝ :=
  p.multiindexCoeff

/-- Every native positive-radius expansion has a derived geometric coefficient majorant. -/
theorem exists_geometric_majorant (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ)
    (hp : 0 < p.radius) :
    ∃ ρ α : ℝ, 0 < ρ ∧ 0 < α ∧ MvPowerSeries.IsMajorizedOn p.toMvPowerSeries
      (MvPowerSeries.C α * (MvPowerSeries.C ρ - ∑ i : ι, MvPowerSeries.X i)⁻¹) Set.univ := by
  obtain ⟨M, r, hM, hr, hbound⟩ := p.exists_pos_multiindexCoeff_bound hp
  refine ⟨r⁻¹, M * r⁻¹, inv_pos.mpr hr, mul_pos hM (inv_pos.mpr hr), ?_⟩
  exact MvPowerSeries.isMajorizedOn_C_mul_inv_C_sub_sum_X hM.le hr hbound

/-- A finite family of native analytic expansions admits one common geometric majorant.
The statement includes an empty family. -/
theorem exists_geometric_majorant_family {η : Type*} [Finite η]
    (p : η → FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (hp : ∀ i, 0 < (p i).radius) :
    ∃ ρ α : ℝ, 0 < ρ ∧ 0 < α ∧ ∀ j, MvPowerSeries.IsMajorizedOn (p j).toMvPowerSeries
      (MvPowerSeries.C α * (MvPowerSeries.C ρ - ∑ i : ι, MvPowerSeries.X i)⁻¹) Set.univ := by
  classical
  let := Fintype.ofFinite η
  choose M r hM hr hbound using fun i ↦ (p i).exists_pos_multiindexCoeff_bound (hp i)
  let C : ℝ := 1 + ∑ i, M i
  let s : ℝ := 1 + ∑ i, r i
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ ↦ (hM i).le)
  have hs : 0 < s := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ ↦ (hr i).le)
  have hMC (i : η) : M i ≤ C :=
    (Finset.single_le_sum (fun j _ ↦ (hM j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hrs (i : η) : r i ≤ s :=
    (Finset.single_le_sum (fun j _ ↦ (hr j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨s⁻¹, C * s⁻¹, inv_pos.mpr hs, mul_pos hC (inv_pos.mpr hs), fun i ↦ ?_⟩
  apply MvPowerSeries.isMajorizedOn_C_mul_inv_C_sub_sum_X hC.le hs
  intro a
  exact (hbound i a).trans (mul_le_mul (hMC i)
    (pow_le_pow_left₀ (hr i).le (hrs i) _) (pow_nonneg (hr i).le _) hC.le)

end FormalMultilinearSeries
