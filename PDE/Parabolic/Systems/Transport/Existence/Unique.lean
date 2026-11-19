/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Existence.Strong
public import PDE.Parabolic.Systems.Transport.Uniqueness.Strong
import PDE.Parabolic.Systems.Transport.Energy.Coefficients

/-!
# Unique strong solutions with mollified initial data

Continuity of the W¹,∞ coefficient curve on the compact time interval
provides the derivative bound needed for uniqueness. With the mollified
initial data, this gives a unique strong solution. No energy estimate or
separate coefficient bound is assumed.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Sobolev

variable {n m : ℕ} {ε a b : ℝ}

/-- Continuous symmetric matrix coefficients yield a unique strong
solution from any positively mollified H¹ datum. The time interval, viscosity,
and mollifier scale are unrestricted apart from positivity. -/
theorem exists_unique_strongTransportDiffusionSolution_mollified
    (hε : 0 < ε) (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b))
    (hsym : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p))
    (B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ)
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (f : Fin m → ℝ × ℝ^n → ℝ)
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F p t) x = f p (t, x))
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (g : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :
    ∃ (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
        (volume.restrict (Ioc a b)))
      (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
        (volume.restrict (Ioc a b)))
      (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      IsStrongTransportDiffusionSolution ε a b B f
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM μ hδ) g) U G z ∧
      (∀ V H w, IsStrongTransportDiffusionSolution ε a b B f
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM μ hδ) g) V H w →
        V = U ∧ H = G ∧ EqOn w z (Icc a b)) := by
  obtain ⟨U, G, z, hz⟩ :=
    exists_strongTransportDiffusionSolution_mollified hε hab A hA B hB F f hf μ hδ g
  obtain ⟨K, N, hK0, _hN0, hK, _hN⟩ := exists_transport_energy_coefficient_bounds A hA
  refine ⟨U, G, z, hz, ?_⟩
  intro V H w hw
  exact IsStrongTransportDiffusionSolution.unique
    hε.le hab hK0 A hsym hK hB F hf V U H G w z hw hz

end PDE.Parabolic.Systems
