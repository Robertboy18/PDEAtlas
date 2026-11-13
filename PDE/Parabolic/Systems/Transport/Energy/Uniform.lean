/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Energy.Strong
import PDE.Parabolic.Systems.Transport.Energy.Coefficients

/-!
# A data-independent uniform strong-solution bound

Compactness of the coefficient curve supplies its value and derivative
bounds. The energy constant is then fixed before the viscosity, forcing,
initial datum, or solution. Continuity of the trace realizes the H¹ maximum
on the whole closed time interval, including its endpoints.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev
open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

/-- One constant controls the closed-time H¹ maximum and the L²(L²) norm of the
velocity of every strong solution with viscosity between zero and one.
It is chosen from the coefficient curve before all data and solutions. -/
theorem exists_uniform_transport_diffusion_constant
    (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b))
    (hsym : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ∀ (B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ),
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
        wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q) →
      ∀ (f : Fin m → ℝ × ℝ^n → ℝ)
        (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
          (volume.restrict (Ioc a b))),
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
        wkpBaseCoordinateCLM (F t p) x = f p (t, x)) →
      ∀ (q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
        (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
          (volume.restrict (Ioc a b)))
        (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
          (volume.restrict (Ioc a b)))
        (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      IsStrongTransportDiffusionSolution ε a b B f q U G z →
      ∃ t ∈ Icc a b, IsMaxOn (fun s ↦ ‖z s‖) (Icc a b) t ∧
        ‖z t‖ + ‖(ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
          (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ))).compLpL
            2 (volume.restrict (Ioc a b)) G‖ ≤ C * (‖q‖ + ‖F‖) := by
  obtain ⟨K, M, hK0, hM0, hK, hM⟩ := exists_transport_energy_coefficient_bounds A hA
  let E := Real.exp ((K + 1) * (b - a))
  let D := 3 * ((n : ℝ) * (1 + (K + 1) * (b - a) * E) +
    1 + (m : ℝ) * M ^ 2 * (b - a) * E)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hK1 : 0 ≤ K + 1 := by linarith
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨E + D + 2, by linarith, ?_⟩
  intro ε hε hε1 B hB f F hf q U G z h
  obtain ⟨hz, hv⟩ := h.energy_squares hε hε1 hab hK0 A hsym hK hM0 hM hB F hf
  obtain ⟨t, ht, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) h.continuousOn.norm
  have hstate : ‖z t‖ ^ 2 ≤ E * (‖q‖ ^ 2 + ‖F‖ ^ 2) := by
    calc
      _ ≤ (‖q‖ ^ 2 + ‖F‖ ^ 2) * Real.exp ((K + 1) * (t - a)) := hz t ht
      _ ≤ (‖q‖ ^ 2 + ‖F‖ ^ 2) * E :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hK1))
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := mul_comm _ _
  have hnorm {v c : ℝ} (hv0 : 0 ≤ v) (hc : 0 ≤ c)
      (hsq : v ^ 2 ≤ c * (‖q‖ ^ 2 + ‖F‖ ^ 2)) :
      v ≤ (c + 1) * (‖q‖ + ‖F‖) := by
    apply (sq_le_sq₀ hv0
      (mul_nonneg (by linarith) (add_nonneg (norm_nonneg q) (norm_nonneg F)))).mp
    have hdata : ‖q‖ ^ 2 + ‖F‖ ^ 2 ≤ (‖q‖ + ‖F‖) ^ 2 := by
      nlinarith only [mul_nonneg (norm_nonneg q) (norm_nonneg F)]
    have hc' : c ≤ (c + 1) ^ 2 := by nlinarith only [sq_nonneg c, hc]
    calc
      _ ≤ c * (‖q‖ ^ 2 + ‖F‖ ^ 2) := hsq
      _ ≤ c * (‖q‖ + ‖F‖) ^ 2 := mul_le_mul_of_nonneg_left hdata hc
      _ ≤ (c + 1) ^ 2 * (‖q‖ + ‖F‖) ^ 2 :=
        mul_le_mul_of_nonneg_right hc' (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  have hzbound := hnorm (norm_nonneg (z t)) hE hstate
  have hvbound := hnorm (norm_nonneg _) hD hv
  refine ⟨t, ht, hmax, ?_⟩
  calc
    _ ≤ (E + 1) * (‖q‖ + ‖F‖) + (D + 1) * (‖q‖ + ‖F‖) :=
      add_le_add hzbound hvbound
    _ = _ := by ring

end PDE.Parabolic.Systems
