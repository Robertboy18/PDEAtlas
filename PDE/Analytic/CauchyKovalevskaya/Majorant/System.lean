/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analytic.CauchyKovalevskaya.Majorant.CoefficientBounds
public import PDE.Analytic.CauchyKovalevskaya.Majorant.ScalarConvergence

/-!
# The scalar root as a majorizing Cauchy system

All matrix entries and forcing components use the same geometric series in the
state and spatial variables. With `2 κ = m (d + 1)`, the quadratic scalar root
solves this entire system. The spatial sum remains empty when there are no
spatial variables, and the forcing remains present. This is step 6 of the proof of
Evans, §4.6.3, Theorem 2, where the majorizing problem (29) with geometric coefficients
has the solution (33).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, proof of Theorem 2, (29) and (33).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MvPowerSeries
open scoped BigOperators

noncomputable section

namespace PDE.Analytic.CauchyKovalevskaya

/-- The common coefficient series for the majorizing matrix and forcing. -/
def coefficientMajorant (d m : ℕ) (ρ α : ℝ) : MvPowerSeries (Fin m ⊕ Fin d) ℝ :=
  C α * (C ρ - ∑ i : Fin m ⊕ Fin d, X i)⁻¹

/-- The scalar root solves every component of the common-coefficient majorizing system. -/
theorem scalarMajorant_formal_eq (d m : ℕ) (ρ α κ : ℝ) (hρ : ρ ≠ 0)
    (hκ : 2 * κ = (m : ℝ) * ((d : ℝ) + 1)) (i : Fin m) :
    pderiv 0 (scalarMajorant d ρ α κ) =
      formalRightHandSide (fun _ _ _ ↦ coefficientMajorant d m ρ α)
        (fun _ ↦ coefficientMajorant d m ρ α) (fun _ ↦ scalarMajorant d ρ α κ) i := by
  classical
  let v := scalarMajorant d ρ α κ
  let a := formalArguments (fun _ : Fin m ↦ v)
  have ha : HasSubst a := hasSubst_formalArguments
    (fun _ ↦ initial_trace_scalarMajorant d ρ α κ)
  let g := substAlgHom (R := ℝ) ha
  let D := subst a (coefficientMajorant d m ρ α)
  let q := spatialDenominator d ρ - 2 * C κ * v
  let s := spatialDenominator d ρ - C (m : ℝ) * v
  have hden : g (C ρ - ∑ j : Fin m ⊕ Fin d, X j) = s := by
    simp only [map_sub, map_sum, g, substAlgHom_X]
    rw [Fintype.sum_sum_type]
    simp only [formalArguments, substAlgHom_apply, subst_C, Sum.elim_inl,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Sum.elim_inr,
      spatialDenominator, map_natCast, a, s]
    ring
  have hD : D * s = C α := by
    have hunit : constantCoeff (C ρ - ∑ j : Fin m ⊕ Fin d, X j) ≠ 0 := by
      simpa using hρ
    calc
      D * s = g (coefficientMajorant d m ρ α) * g (C ρ - ∑ j : Fin m ⊕ Fin d, X j) := by
        rw [hden]
        simp only [D, g, substAlgHom_apply]
      _ = g (C α) := by
        rw [← map_mul]
        congr 1
        simp only [coefficientMajorant, mul_assoc, MvPowerSeries.inv_mul_cancel _ hunit,
          mul_one]
      _ = C α := by simp [g, substAlgHom_apply]
  have hq : q + (d : MvPowerSeries (Fin (d + 1)) ℝ) * m * v = s := by
    have hκ' : 2 * (C κ : MvPowerSeries (Fin (d + 1)) ℝ) =
        (m : MvPowerSeries (Fin (d + 1)) ℝ) * (d + 1) := by
      simpa only [map_mul, map_add, map_ofNat, map_natCast, map_one] using congrArg C hκ
    dsimp [q, s]
    rw [hκ']
    simp only [map_natCast]
    ring
  have ht : q * pderiv 0 v = C α := scalarMajorant_pderiv_zero d ρ α κ hρ
  have hx (j : Fin d) : q * pderiv j.succ v = v :=
    scalarMajorant_pderiv_succ d ρ α κ hρ j
  have hR : q * formalRightHandSide (fun _ _ _ ↦ coefficientMajorant d m ρ α)
      (fun _ ↦ coefficientMajorant d m ρ α) (fun _ ↦ v) i = C α := by
    change q * ((∑ j : Fin d, ∑ _k : Fin m, D * pderiv j.succ v) + D) = C α
    calc
      q * ((∑ j : Fin d, ∑ _k : Fin m, D * pderiv j.succ v) + D) =
          (∑ j : Fin d, ∑ _k : Fin m, D * (q * pderiv j.succ v)) + D * q := by
        simp only [mul_add, Finset.mul_sum, mul_comm, mul_left_comm]
      _ = D * (q + (d : MvPowerSeries (Fin (d + 1)) ℝ) * m * v) := by
        simp only [hx, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ = C α := by rw [hq]; exact hD
  have hqunit : IsUnit q := isUnit_iff_constantCoeff.mpr
    (isUnit_iff_ne_zero.mpr (by simpa [q, v] using hρ))
  exact hqunit.mul_left_cancel (ht.trans hR.symm)

/-- Majorization by the constructed scalar root gives convergence of the formal solution. -/
theorem radius_pos_formal_solution {d m : ℕ} {ρ α : ℝ}
    (hρ : 0 < ρ) (hα : 0 ≤ α)
    {B : Fin d → Fin m → Fin m → MvPowerSeries (Fin m ⊕ Fin d) ℝ}
    {c : Fin m → MvPowerSeries (Fin m ⊕ Fin d) ℝ}
    {u : Fin m → MvPowerSeries (Fin (d + 1)) ℝ}
    (hu₀ : ∀ i, PowerSeries.constantCoeff (finSuccEquiv ℝ d (u i)) = 0)
    (hu : ∀ i, pderiv 0 (u i) = formalRightHandSide B c u i)
    (hB : ∀ j i k, IsMajorizedOn (B j i k) (coefficientMajorant d m ρ α) Set.univ)
    (hc : ∀ i, IsMajorizedOn (c i) (coefficientMajorant d m ρ α) Set.univ) (i : Fin m) :
    0 < (u i).toFormalMultilinearSeries.radius := by
  let κ : ℝ := (m : ℝ) * ((d : ℝ) + 1) / 2
  have hκ : 2 * κ = (m : ℝ) * ((d : ℝ) + 1) := by dsimp [κ]; ring
  have hcomp := formal_solution_isMajorizedOn hu₀
    (fun _ ↦ initial_trace_scalarMajorant d ρ α κ) hu
    (scalarMajorant_formal_eq d m ρ α κ hρ.ne' hκ) hB hc i
  exact (radius_pos_scalarMajorant d ρ α κ hρ hα (by dsimp [κ]; positivity)).trans_le
    hcomp.radius_le

end PDE.Analytic.CauchyKovalevskaya
