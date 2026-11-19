/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Balance
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.FDeriv.Calculus

/-!
# Momentum balance for a scalar wave

The spatial stress has the same sign convention as the physical energy flux.
Only a C¹ potential is used. The identity retains the wave residual.
-/

@[expose] public noncomputable section

namespace WaveEquation

variable {n : ℕ}

/-- Spatial stress with momentum density `uₜ Dₓu`. -/
def waveSpatialStress (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (i j : Fin n) (p : ℝ^(n + 1)) : ℝ :=
  (∂[i.succ] u) p * (∂[j.succ] u) p +
    if i = j then waveLagrangianDensity V u p else 0

/-- Momentum balance before imposing the PDE, with no derivative of the reaction. -/
theorem waveSpatialStress_balance {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hV : ContDiffAt ℝ 1 V (u p)) (hu : ContDiffAt ℝ 2 u p) (i : Fin n) :
    (∂[0] (classicalWaveEnergyFlux u i)) p - (∑ j : Fin n, (∂[j.succ] (waveSpatialStress V u i j))
      p) = (∂[i.succ] u) p * semilinearWaveOperator V u p := by
  classical
  have hp (k : Fin (n + 1)) := (PDE.contDiffAt_partialDeriv 1 hu k).differentiableAt one_ne_zero
  have hL := (contDiffAt_waveLagrangianDensity hV hu).differentiableAt one_ne_zero
  have hterm (j : Fin n) : (∂[j.succ] (waveSpatialStress V u i j)) p =
        (∂[j.succ] (∂[i.succ] u)) p * (∂[j.succ] u) p +
          (∂[i.succ] u) p * (∂[j.succ] (∂[j.succ] u)) p +
            if i = j then (∂[j.succ] (waveLagrangianDensity V u)) p else 0 := by
    unfold waveSpatialStress
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      rw [PDE.partialDeriv_add (i := j.succ) ((hp j.succ).fun_mul (hp j.succ)) hL,
        PDE.partialDeriv_mul (hp j.succ) (hp j.succ)]
    · simp only [hij, ↓reduceIte, add_zero]
      exact PDE.partialDeriv_mul (hp i.succ) (hp j.succ)
  have hsum : (∑ j : Fin n, (∂[j.succ] (waveSpatialStress V u i j)) p) = (∑ j : Fin n,
          (∂[j.succ] u) p * (∂[i.succ] (∂[j.succ] u)) p) +
          (∂[i.succ] u) p * (∑ j : Fin n, (∂[j.succ] (∂[j.succ] u)) p) +
            (∂[i.succ] (waveLagrangianDensity V u)) p := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [PDE.partialDeriv_partialDeriv_comm_at j.succ i.succ hu, mul_comm]
  rw [hsum, partialDeriv_waveLagrangianDensity (hV.differentiableAt one_ne_zero) hu i.succ]
  unfold classicalWaveEnergyFlux
  rw [PDE.partialDeriv_mul (hp 0) (hp i.succ), PDE.partialDeriv_partialDeriv_comm_at 0 i.succ hu]
  simp only [semilinearWaveOperator, waveOperator]
  ring

/-- C1 potential and C2 field give C1 spatial stress, without differentiating the reaction. -/
theorem contDiffAt_waveSpatialStress {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiffAt ℝ 1 V (u p)) (hu : ContDiffAt ℝ 2 u p)
    (i j : Fin n) : ContDiffAt ℝ 1 (waveSpatialStress V u i j) p := by
  classical
  unfold waveSpatialStress
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    exact ((PDE.contDiffAt_partialDeriv 1 hu j.succ).mul
      (PDE.contDiffAt_partialDeriv 1 hu j.succ)).add (contDiffAt_waveLagrangianDensity hV hu)
  · simp only [hij, ↓reduceIte, add_zero]
    exact (PDE.contDiffAt_partialDeriv 1 hu i.succ).mul (PDE.contDiffAt_partialDeriv 1 hu j.succ)

end WaveEquation
