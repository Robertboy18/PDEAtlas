/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Momentum.Balance

/-!
# Bounds for the spatial wave stress

Each stress entry is bounded by the derivative energy and the absolute
potential. This algebraic estimate does not use the wave equation.
-/

@[expose] public noncomputable section

namespace WaveEquation

/-- Each entry of the spatial stress is bounded by the classical wave energy density plus
the absolute value of the potential. -/
theorem abs_waveSpatialStress_le_energy_add_abs_potential
    {n : ℕ} (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (i j : Fin n) (p : ℝ^(n + 1)) :
    |waveSpatialStress V u i j p| ≤ classicalWaveEnergyDensity u p + |V (u p)| := by
  classical
  have hnorm : ‖classicalWaveSpatialGradient u p‖ ^ 2 =
      ∑ k : Fin n, (∂[k.succ] u) p ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [classicalWaveSpatialGradient_apply]
  have hsingle (k : Fin n) : (∂[k.succ] u) p ^ 2 ≤ ∑ l : Fin n, (∂[l.succ] u) p ^ 2 :=
    Finset.single_le_sum (fun l _ ↦ sq_nonneg ((∂[l.succ] u) p)) (Finset.mem_univ k)
  unfold waveSpatialStress waveLagrangianDensity classicalWaveEnergyDensity
  rw [hnorm]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    apply abs_le.mpr
    constructor <;> nlinarith [hsingle i, sq_nonneg ((∂[0] u) p),
      sq_nonneg ((∂[i.succ] u) p), le_abs_self (V (u p)), neg_abs_le (V (u p))]
  · simp only [hij, ↓reduceIte, add_zero]
    have hpair : (∂[i.succ] u) p ^ 2 + (∂[j.succ] u) p ^ 2 ≤ ∑ k : Fin n, (∂[k.succ] u) p ^ 2 :=
      Finset.add_le_sum (fun k _ ↦ sq_nonneg ((∂[k.succ] u) p))
        (Finset.mem_univ i) (Finset.mem_univ j) hij
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg ((∂[i.succ] u) p + (∂[j.succ] u) p),
      sq_nonneg ((∂[i.succ] u) p - (∂[j.succ] u) p), sq_nonneg ((∂[0] u) p), abs_nonneg (V (u p))]

end WaveEquation
