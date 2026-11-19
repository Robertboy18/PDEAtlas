/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.SchwartzData
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.FourierDatum
import PDE.Hyperbolic.NonlinearWave.Critical.ForwardEnergy

/-!
# Uniform Fourier data at every positive quintic restart

The compact-data Cauchy problem supplies speed-one support and one
energy bound throughout a finite forward lifespan. Schwartz restart data therefore have one Fourier
norm bound before any start, cone or prefix is chosen.
-/

@[expose] public noncomputable section

open Set PDE PDE.Common PDE.Analysis
open scoped ContDiff SchwartzMap

namespace WaveEquation.Critical

/-- Original compact Cauchy data give a single Fourier data bound for every
positive restart. The data are chosen before any cone or prefix. -/
theorem exists_uniform_schwartz_restart_data_of_quintic_cauchy {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (g h : ℝ^3 → ℝ) (hu : ContDiffOn ℝ ∞ u {p | 0 ≤ p 0 ∧ p 0 < T}) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Ioo 0 T, ∃ gₛ hₛ : 𝓢(ℝ^3, ℝ),
      (∀ x, u (timeSpaceCons s x) = gₛ x) ∧
      (∀ x, (∂[0] u) (timeSpaceCons s x) = hₛ x) ∧
      ‖Strichartz.initialEnergyDatum (gₛ.postcompCLM Complex.ofRealCLM)
        (hₛ.postcompCLM Complex.ofRealCLM)‖ ≤ C := by
  obtain ⟨R, E, hsupp, hE⟩ := exists_support_and_uniform_energy_of_quintic_cauchy
    hT g h (hu.of_le (by simp)) hgc hhc hwave hpos hvel
  have hui : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T} := hu.mono fun _ hp ↦ ⟨hp.1.le, hp.2⟩
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  refine ⟨2 * |E| + 1, by positivity, fun s hs ↦ ?_⟩
  obtain ⟨gₛ, hₛ, hgs, hhs⟩ := exists_schwartz_cauchyData_of_forward_support hui
    (fun q hq ↦ hsupp q ⟨hq.1.le, hq.2⟩) hs
  refine ⟨gₛ, hₛ, hgs, hhs, ?_⟩
  have hdata := Strichartz.norm_initialEnergyDatum_sq_le_two_mul_energy
    gₛ hₛ s (Real.signedPowerPotential 5)
    (Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5))
    (fun x ↦ (hui.contDiffAt (hopen.mem_nhds (by simpa using hs))).differentiableAt
      (by simp)) hgs hhs (hE s hs).1
  have hbound := (hE s hs).2
  have hn := norm_nonneg (Strichartz.initialEnergyDatum
    (gₛ.postcompCLM Complex.ofRealCLM) (hₛ.postcompCLM Complex.ofRealCLM))
  nlinarith [sq_nonneg (‖Strichartz.initialEnergyDatum
    (gₛ.postcompCLM Complex.ofRealCLM) (hₛ.postcompCLM Complex.ofRealCLM)‖ - 1),
    le_abs_self E, abs_nonneg E]

end WaveEquation.Critical
