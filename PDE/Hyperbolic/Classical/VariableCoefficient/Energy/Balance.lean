/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Operator
import PDE.FDeriv.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Local energy balance for an autonomous principal matrix

For the nondivergence wave equation the energy is not conserved locally.
Differentiating the coefficients in the spatial flux leaves
`-uₜ ∑ᵢⱼ (∂ⱼ aⁱʲ) uᵢ`. Symmetry cancels the two differentiated gradient
factors; autonomy eliminates a time derivative of the matrix.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

namespace WaveEquation.VariableCoefficient

open PDE.Common

variable {n : ℕ}

/-- An autonomous spatial coefficient has zero time derivative after lifting. -/
theorem partialDeriv_time_spatialPart {f : ℝ^n → ℝ} {p : ℝ^(n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPart p)) :
    (∂[0] (fun y ↦ f (spatialPart y))) p = 0 := by
  have h := hf.hasFDerivAt.comp p (spatialPartCLM n).hasFDerivAt
  change fderiv ℝ (f ∘ spatialPart) p (EuclideanSpace.single 0 1) = 0
  rw [h.fderiv, ContinuousLinearMap.comp_apply, spatialPartCLM_single_zero, map_zero]

/-- Spatial derivatives commute with the autonomous spatial lift. -/
theorem partialDeriv_succ_spatialPart {f : ℝ^n → ℝ} {p : ℝ^(n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPart p)) (j : Fin n) :
    (∂[j.succ] (fun y ↦ f (spatialPart y))) p = (∂[j] f) (spatialPart p) := by
  have h := hf.hasFDerivAt.comp p (spatialPartCLM n).hasFDerivAt
  change fderiv ℝ (f ∘ spatialPart) p (EuclideanSpace.single j.succ 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, spatialPartCLM_single_succ]
  rfl

/-- The local balance identity includes the full coefficient-divergence remainder. -/
theorem energy_balance {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (ha : ∀ i j, ContDiffAt ℝ 1 (fun x ↦ a x i j) (spatialPart p))
    (hsymm : ∀ i j, a (spatialPart p) i j = a (spatialPart p) j i) (hu : ContDiffAt ℝ 2 u p) :
    (∂[0] (energyDensity a u)) p - ∑ j, (∂[j.succ] (energyFlux a u j)) p =
      (∂[0] u) p * waveOperator a u p - (∂[0] u) p * ∑ i, ∑ j,
      (∂[j] (fun x ↦ a x i j)) (spatialPart p) * (∂[i.succ] u) p := by
  let w := (∂[0] u)
  let v := fun i : Fin n ↦ (∂[i.succ] u)
  let A := fun i j : Fin n ↦ fun y : ℝ^(n + 1) ↦ a (spatialPart y) i j
  have hw : DifferentiableAt ℝ w p :=
    (PDE.contDiffAt_partialDeriv 1 hu 0).differentiableAt one_ne_zero
  have hv (i : Fin n) : DifferentiableAt ℝ (v i) p :=
    (PDE.contDiffAt_partialDeriv 1 hu i.succ).differentiableAt one_ne_zero
  have hA (i j : Fin n) : DifferentiableAt ℝ (A i j) p :=
    ((ha i j).comp p (spatialPartCLM n).contDiff.contDiffAt).differentiableAt one_ne_zero
  have hAv (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ A i j y * v i y) p := (hA i j).mul (hv i)
  have hAt (i j : Fin n) : (∂[0] (A i j)) p = 0 :=
    partialDeriv_time_spatialPart ((ha i j).differentiableAt one_ne_zero)
  have hAx (i j : Fin n) : (∂[j.succ] (A i j)) p = (∂[j] (fun x ↦ a x i j)) (spatialPart p) :=
    partialDeriv_succ_spatialPart ((ha i j).differentiableAt one_ne_zero) j
  have hmix (i : Fin n) : (∂[0] (v i)) p = (∂[i.succ] w) p :=
    PDE.partialDeriv_partialDeriv_comm_at 0 i.succ hu
  have hsecond (i j : Fin n) : (∂[j.succ] (v i)) p = (∂[i.succ] (v j)) p :=
    PDE.partialDeriv_partialDeriv_comm_at j.succ i.succ hu
  have hrow (i : Fin n) : DifferentiableAt ℝ (fun y ↦ ∑ j, A i j y * v i y * v j y) p :=
    DifferentiableAt.fun_sum fun j _ ↦ (hAv i j).mul (hv j)
  have hqt : (∂[0] (fun y ↦ ∑ i, ∑ j, A i j y * v i y * v j y)) p =
      ∑ i, ∑ j, (A i j p * (∂[0] (v i)) p * v j p + A i j p * v i p * (∂[0] (v j)) p) := by
    rw [PDE.partialDeriv_sum _ fun i _ ↦ hrow i]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PDE.partialDeriv_sum _ fun j _ ↦ (hAv i j).fun_mul (hv j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [PDE.partialDeriv_mul (hAv i j) (hv j), PDE.partialDeriv_mul (hA i j) (hv i), hAt]
    ring
  have hswap : (∑ i, ∑ j, A i j p * (∂[0] (v i)) p * v j p) =
      ∑ i, ∑ j, A i j p * v i p * (∂[0] (v j)) p := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp [A]
    rw [hsymm j i]
    ring
  have ht : (∂[0] (energyDensity a u)) p =
      w p * (∂[0] w) p + ∑ i, ∑ j, A i j p * v i p * (∂[0] (v j)) p := by
    change (∂[0] (fun y ↦ (1 / 2 : ℝ) * (w y ^ 2 + ∑ i, ∑ j, A i j y * v i y * v j y))) p = _
    have hquad := DifferentiableAt.fun_sum (u := Finset.univ) fun i _ ↦ hrow i
    rw [PDE.partialDeriv_mul (differentiableAt_const _) ((hw.fun_pow 2).fun_add hquad),
      PDE.partialDeriv_add (hw.fun_pow 2) hquad, PDE.partialDeriv_sq 0 hw, hqt,
      PDE.partialDeriv_const]
    simp only [Finset.sum_add_distrib]
    rw [hswap]
    ring
  have hflux (j : Fin n) : (∂[j.succ] (energyFlux a u j)) p =
      ∑ i, (A i j p * v i p * (∂[0] (v j)) p + w p * (∂[j.succ] (A i j)) p * v i p +
        w p * A i j p * (∂[i.succ] (v j)) p) := by
    change (∂[j.succ] (fun y ↦ w y * ∑ i, A i j y * v i y)) p = _
    rw [PDE.partialDeriv_mul hw (DifferentiableAt.fun_sum fun i _ ↦ hAv i j),
      PDE.partialDeriv_sum _ fun i _ ↦ hAv i j, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PDE.partialDeriv_mul (hA i j) (hv i), ← hmix, hsecond]
    ring
  rw [ht]
  simp only [hflux, hAx, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j i ↦ A i j p * v i p * (∂[0] (v j)) p)]
  simp only [waveOperator]
  change _ = w p * ((∂[0] w) p - ∑ i, ∑ j, A i j p * (∂[i.succ] (v j)) p) -
      w p * ∑ i, ∑ j, (∂[j] (fun x ↦ a x i j)) (spatialPart p) * v i p
  rw [Finset.sum_comm (f := fun j i ↦ w p * (∂[j] (fun x ↦ a x i j)) (spatialPart p) * v i p),
    Finset.sum_comm (f := fun j i ↦ w p * A i j p * (∂[i.succ] (v j)) p)]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

end WaveEquation.VariableCoefficient
