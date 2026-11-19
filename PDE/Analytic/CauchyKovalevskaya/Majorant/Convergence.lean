/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.MajorantBounds
public import PDE.Analytic.CauchyKovalevskaya.Majorant.System

/-!
# Convergence of the formal Cauchy solution

Power series of the matrix entries and forcing with positive radius have a common
geometric majorant. The time recursion then produces a formal solution whose
`FormalMultilinearSeries` has positive radius.

This is the method of majorants in the proof of Evans, §4.6.3, Theorem 2, (26)-(34). The
common majorant is the geometric series from the proof of Lemma (Majorants) (ii) in §4.6.2,
which Evans also uses in step 6.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.2, Lemma (Majorants), and §4.6.3, proof of
  Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MvPowerSeries

namespace PDE.Analytic.CauchyKovalevskaya

/-- Coefficient series of positive radius give a convergent formal solution of the
reduced Cauchy system that vanishes on the whole initial hyperplane. -/
theorem exists_convergent_formal_solution {d m : ℕ}
    (B : Fin d → Fin m → Fin m →
      FormalMultilinearSeries ℝ ((Fin m ⊕ Fin d) → ℝ) ℝ)
    (c : Fin m → FormalMultilinearSeries ℝ ((Fin m ⊕ Fin d) → ℝ) ℝ)
    (hB : ∀ j i k, 0 < (B j i k).radius) (hc : ∀ i, 0 < (c i).radius) :
    ∃ u : Fin m → MvPowerSeries (Fin (d + 1)) ℝ,
      (∀ i, PowerSeries.constantCoeff (finSuccEquiv ℝ d (u i)) = 0) ∧
      (∀ i, pderiv 0 (u i) = formalRightHandSide
        (fun j i k ↦ (B j i k).toMvPowerSeries) (fun i ↦ (c i).toMvPowerSeries) u i) ∧
      ∀ i, 0 < (u i).toFormalMultilinearSeries.radius := by
  let p : ((Fin d × Fin m × Fin m) ⊕ Fin m) →
      FormalMultilinearSeries ℝ ((Fin m ⊕ Fin d) → ℝ) ℝ :=
    Sum.elim (fun j ↦ B j.1 j.2.1 j.2.2) c
  have hp (i) : 0 < (p i).radius := by
    cases i with
    | inl j => exact hB j.1 j.2.1 j.2.2
    | inr i => exact hc i
  obtain ⟨ρ, α, hρ, hα, hmajor⟩ := FormalMultilinearSeries.exists_geometric_majorant_family p hp
  obtain ⟨u, hu, _⟩ := existsUnique_formal_solution
    (fun j i k ↦ (B j i k).toMvPowerSeries) (fun i ↦ (c i).toMvPowerSeries)
  refine ⟨u, hu.1, hu.2, fun i ↦ ?_⟩
  exact radius_pos_formal_solution hρ hα.le hu.1 hu.2
    (fun j i k ↦ hmajor (.inl (j, i, k))) (fun i ↦ hmajor (.inr i)) i

end PDE.Analytic.CauchyKovalevskaya
