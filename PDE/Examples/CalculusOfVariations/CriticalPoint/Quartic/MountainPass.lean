/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.CriticalPoint.Quartic.PalaisSmale
public import PDE.Analysis.Variational.CriticalPoint.Minimax.MountainPass
import CAS.ExactTactic

/-!
# A mountain pass for an energy unbounded below

For any unit vector in any complete real Hilbert space, the quartic energy has a
positive barrier on the radius-one-half sphere and negative energy at twice that
vector. With the Palais–Smale condition `palaisSmale_energy`, the mountain pass theorem
gives a nonzero critical point at the minimax value over paths (`exists_mountain_pass`).
The energy has no lower bound (`energy_not_bddBelow`).
-/

@[expose] public noncomputable section

open Set
open scoped RealInnerProductSpace Gradient

namespace PDE.Examples.CriticalPoint.Quartic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Restricting the energy to the unit direction gives the ordinary scalar quartic. -/
theorem energy_smul {e : H} (he : ‖e‖ = 1) (t : ℝ) :
    energy e (t • e) = t ^ 2 - t ^ 4 := by
  simp [energy, norm_smul, inner_smul_right, he,
    Real.norm_eq_abs, sq_abs]

omit [CompleteSpace H] in
/-- On the sphere of radius `1/2` the energy is at least `3/16`. -/
theorem sphere_barrier {e : H} (he : ‖e‖ = 1) {u : H} (hu : ‖u‖ = 1 / 2) :
    (3 / 16 : ℝ) ≤ energy e u := by
  have hs : |⟪e, u⟫| ≤ 1 / 2 := by simpa only [hu] using abs_inner_le_norm he u
  obtain ⟨hl, hr⟩ := abs_le.mp hs
  have hs2 : ⟪e, u⟫ ^ 2 ≤ 1 / 4 := by cas
  have hs4 : ⟪e, u⟫ ^ 4 ≤ 1 / 16 := by cas
  rw [energy, hu]
  cas

/-- The mountain pass theorem for the quartic energy, in every Hilbert dimension. -/
theorem exists_mountain_pass {e : H} (he : ‖e‖ = 1) :
    (3 / 16 : ℝ) ≤ PDE.Analysis.Variational.pathMinimax (energy e) 0 ((2 : ℝ) • e) ∧
      ∃ u : H, u ≠ 0 ∧
        energy e u = PDE.Analysis.Variational.pathMinimax (energy e) 0 ((2 : ℝ) • e) ∧
        ∇ (energy e) u = 0 := by
  apply (palaisSmale_energy he).mountain_pass (contDiff_energy e)
    (gradient_energy_lipschitzOn_balls he) (by simp [energy])
    (r := 1 / 2) (by cas) (by cas) (fun _ hu ↦ sphere_barrier he hu)
  · simp only [norm_smul, he]
    cas
  · rw [energy_smul he]
    cas

omit [CompleteSpace H] in
/-- The energy has no global lower bound. -/
theorem energy_not_bddBelow {e : H} (he : ‖e‖ = 1) : ¬ BddBelow (range (energy e)) := by
  rintro ⟨b, hb⟩
  let t := |b| + 2
  have ht : 2 ≤ t := by dsimp [t]; linarith [abs_nonneg b]
  have ht2 : 2 ≤ t ^ 2 := by cas
  have htt : t ≤ t ^ 2 := by cas
  have hprod := mul_nonneg (sub_nonneg.mpr ht2) (sq_nonneg t)
  have hsmall : t ^ 2 - t ^ 4 ≤ -t := by cas
  have hbabs : -t < b := by dsimp [t]; linarith [neg_abs_le b]
  have hlower := hb (mem_range_self (t • e))
  rw [energy_smul he] at hlower
  linarith

end PDE.Examples.CriticalPoint.Quartic
