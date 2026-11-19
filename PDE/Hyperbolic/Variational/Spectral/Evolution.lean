/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.EnergyExpansion
public import PDE.Hyperbolic.Variational.EnergyLimit
public import PDE.Hyperbolic.Variational.Spectral.Finite

/-!
# Constructing strongly continuous waves from a weak eigenbasis

The displacement data belong to `V` and the velocity data only to the pivot
space `H`. Energy convergence of the displacement expansion and ordinary
Hilbert-basis convergence of the velocity supply the initial approximation.
The finite spectral equations then give convergence in `C([0,T]; V × H)`,
both integrated wave equations, and exact conservation of energy.

This construction assumes a complete countable weak eigenbasis.
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.Variational

open Filter Set MeasureTheory
open scoped Topology InnerProductSpace Interval BigOperators

variable {V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Spectral projections of arbitrary energy data converge in `V × H`.
The velocity datum need not lie in the image of `V`. -/
theorem tendsto_finiteSpectralWave_initial (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (J : V →L[ℝ] H)
    (hJ : Function.Injective J) (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (e : ℕ → V) (he : ∀ i, J (e i) = basis i)
    (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ) (q₀ : V) (p₀ : H) :
    Tendsto (fun n ↦
      (finiteSpectralDisplacement lambda e (Finset.range n)
        (fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)) 0,
       J (finiteSpectralVelocity lambda e (Finset.range n)
        (fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)) 0)))
      atTop (𝓝 (q₀, p₀)) := by
  have hq := PDE.Analysis.Variational.hasSum_weakEigenfunction_expansion
    B hsymm hc hcoercive J hJ basis lambda hlambda e he hweak q₀
  have hp : HasSum (fun i ↦ ⟪basis i, p₀⟫_ℝ • basis i) p₀ := by
    simpa only [basis.repr_apply_apply] using basis.hasSum_repr p₀
  simpa only [finiteSpectralDisplacement_zero, finiteSpectralVelocity_zero,
    map_sum, map_smul, he] using hq.tendsto_sum_nat.prodMk_nhds hp.tendsto_sum_nat

/-- A complete weak eigenbasis constructs a homogeneous wave for arbitrary
energy data on every finite forward interval. Strong energy continuity and
exact conservation follow from the spectral approximations; neither is an
assumption on a weak limit. -/
theorem exists_energy_wave_of_weakEigenbasis (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (J : V →L[ℝ] H)
    (hJ : Function.Injective J) (K : H →L[ℝ] V →L[ℝ] ℝ) (hK : ∀ p w, K p w = ⟪p, J w⟫_ℝ)
    (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ) (hlambda : ∀ i, 0 ≤ lambda i) (e : ℕ → V)
    (he : ∀ i, J (e i) = basis i) (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ) (q₀ : V)
    (p₀ : H) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → V × H, ContinuousOn u (Icc 0 T) ∧
      TendstoUniformlyOn (fun n t ↦
        (finiteSpectralDisplacement lambda e (Finset.range n)
          (fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)) t,
         J (finiteSpectralVelocity lambda e (Finset.range n)
          (fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)) t)))
        u atTop (Icc 0 T) ∧
      u 0 = (q₀, p₀) ∧
      (∀ t ∈ Icc 0 T, autonomousWaveEnergy B (u t) =
        autonomousWaveEnergy B (q₀, p₀)) ∧
      (∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, (u s).2) = J (u t).1 - J q₀) ∧
      (∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, -(B (u s).1)) = K (u t).2 - K p₀) := by
  let data : ℕ → ℝ × ℝ := fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)
  apply exists_energy_solution_of_classical_wave_approximations B hsymm hc hcoercive J K hK
    (fun n ↦ finiteSpectralDisplacement lambda e (Finset.range n) data)
    (fun n ↦ finiteSpectralVelocity lambda e (Finset.range n) data)
    (fun n ↦ finiteSpectralAcceleration lambda e (Finset.range n) data) hT
  · exact fun n t _ ↦ hasDerivAt_finiteSpectralDisplacement lambda e (Finset.range n) data t
  · exact fun n t _ ↦ hasDerivAt_finiteSpectralVelocity lambda e (Finset.range n) data t
  · exact fun n t _ w ↦ finiteSpectralWave_equation B J lambda e
      (fun i v ↦ by rw [hweak, he]) (Finset.range n) data t w
  · exact tendsto_finiteSpectralWave_initial
      B hsymm hc hcoercive J hJ basis lambda hlambda e he hweak q₀ p₀

/-- The same spectral approximations have one strongly continuous limit for
all real times. Conservation of difference energy makes convergence uniform
even on the entire real line for each fixed initial state. -/
theorem exists_global_continuous_energy_wave_of_weakEigenbasis (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (J : V →L[ℝ] H) (hJ : Function.Injective J) (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (e : ℕ → V) (he : ∀ i, J (e i) = basis i)
    (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ) (q₀ : V) (p₀ : H) :
    ∃ u : ℝ → V × H, Continuous u ∧
      TendstoUniformlyOn (fun n t ↦
        (finiteSpectralDisplacement lambda e (Finset.range n)
          (fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)) t,
         J (finiteSpectralVelocity lambda e (Finset.range n)
          (fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)) t)))
        u atTop univ ∧
      u 0 = (q₀, p₀) ∧
      ∀ t, autonomousWaveEnergy B (u t) = autonomousWaveEnergy B (q₀, p₀) := by
  let data : ℕ → ℝ × ℝ := fun i ↦ (⟪basis i, J q₀⟫_ℝ, ⟪basis i, p₀⟫_ℝ)
  let q := fun n ↦ finiteSpectralDisplacement lambda e (Finset.range n) data
  let v := fun n ↦ finiteSpectralVelocity lambda e (Finset.range n) data
  let d := fun n ↦ finiteSpectralAcceleration lambda e (Finset.range n) data
  have hq (n : ℕ) (t : ℝ) : HasDerivAt (q n) (v n t) t :=
    hasDerivAt_finiteSpectralDisplacement lambda e (Finset.range n) data t
  have hv (n : ℕ) (t : ℝ) : HasDerivAt (v n) (d n t) t :=
    hasDerivAt_finiteSpectralVelocity lambda e (Finset.range n) data t
  have heq (n : ℕ) (t : ℝ) (w : V) : ⟪J (d n t), J w⟫_ℝ + B (q n t) w = 0 :=
    finiteSpectralWave_equation B J lambda e
      (fun i z ↦ by rw [hweak, he]) (Finset.range n) data t w
  have henergy (n : ℕ) (t : ℝ) : autonomousWaveEnergy B (q n t, J (v n t)) =
        autonomousWaveEnergy B (q n 0, J (v n 0)) := by
    by_cases ht : 0 ≤ t
    · exact autonomousWaveEnergy_eq_initial_of_hasDerivAt B hsymm J
        (a := 0) (b := t) (fun s _ ↦ hq n s) (fun s _ ↦ hv n s)
        (fun s _ ↦ heq n s (v n s)) t ⟨ht, le_rfl⟩
    · exact (autonomousWaveEnergy_eq_initial_of_hasDerivAt B hsymm J
        (a := t) (b := 0) (fun s _ ↦ hq n s) (fun s _ ↦ hv n s)
        (fun s _ ↦ heq n s (v n s)) 0 ⟨(le_of_not_ge ht), le_rfl⟩).symm
  have hdifference (n m : ℕ) (t : ℝ) :
      autonomousWaveEnergy B ((q n t, J (v n t)) - (q m t, J (v m t))) =
        autonomousWaveEnergy B ((q n 0, J (v n 0)) - (q m 0, J (v m 0))) := by
    by_cases ht : 0 ≤ t
    · exact autonomousWaveEnergy_difference_eq_initial_of_hasDerivAt B hsymm J (a := 0) (b := t)
        (fun s _ ↦ hq n s) (fun s _ ↦ hq m s) (fun s _ ↦ hv n s) (fun s _ ↦ hv m s)
        (fun s _ ↦ heq n s) (fun s _ ↦ heq m s) t ⟨ht, le_rfl⟩
    · exact (autonomousWaveEnergy_difference_eq_initial_of_hasDerivAt B hsymm J (a := t) (b := 0)
        (fun s _ ↦ hq n s) (fun s _ ↦ hq m s) (fun s _ ↦ hv n s) (fun s _ ↦ hv m s)
        (fun s _ ↦ heq n s) (fun s _ ↦ heq m s) 0 ⟨(le_of_not_ge ht), le_rfl⟩).symm
  obtain ⟨u, hucont, hu, hu0, hE⟩ := exists_continuousOn_limit_conserving_autonomousWaveEnergy
      B hc hcoercive (fun n t ↦ (q n t, J (v n t))) univ 0 (mem_univ _) (q₀, p₀)
      (tendsto_finiteSpectralWave_initial
        B hsymm hc hcoercive J hJ basis lambda hlambda e he hweak q₀ p₀)
      (fun n ↦ (continuous_finiteSpectralWave J lambda e (Finset.range n) data).continuousOn)
      (fun n t _ ↦ henergy n t) (fun n m t _ ↦ (hdifference n m t).le)
  exact ⟨u, continuousOn_univ.mp hucont, hu, hu0, fun t ↦ hE t (mem_univ _)⟩

end Hyperbolic.Variational
