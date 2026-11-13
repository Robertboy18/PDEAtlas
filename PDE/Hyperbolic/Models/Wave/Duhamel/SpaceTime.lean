/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Integration.Retarded.InitialTrace
public import PDE.Hyperbolic.Models.Wave.Duhamel.Equation

/-!
# Retarded wave families in spacetime

Duhamel's construction integrates homogeneous waves indexed by the time at
which the forcing acts. These lemmas keep the time coordinate first, as in
the wave constructors, and carry out the change to product coordinates once.
The kernel may depend merely continuously on its index.
-/

@[expose] public noncomputable section

open PDE (time)

namespace WaveEquation

open PDE.Analysis PDE.Common

variable {n : ℕ}

/-- Superpose the wave emitted at each source time, evaluated at its elapsed age. -/
def retardedWave (F : ℝ → ℝ^(n + 1) → ℝ) : ℝ^(n + 1) → ℝ :=
  fun p ↦ retardedIntegral (fun s q ↦ F s (joinSpaceTime q)) (splitSpaceTime p)

/-- At time zero the integration interval collapses. -/
@[simp]
theorem retardedWave_initial (F : ℝ → ℝ^(n + 1) → ℝ) (x : ℝ^n) :
    retardedWave F (timeSpaceCons 0 x) = 0 := by
  simp [retardedWave, splitSpaceTime, time]

variable {F : ℝ → ℝ^(n + 1) → ℝ}
  (hF : ∀ s, ContDiff ℝ 2 (F s))
  (hjet : ∀ j ≤ 2, Continuous
    (fun p : ℝ × ℝ^(n + 1) ↦ iteratedFDeriv ℝ j (F p.1) p.2))

include hF hjet

private theorem continuous_join_jets (j : ℕ) (hj : j ≤ 2) :
    Continuous (fun p : ℝ × (ℝ^n × ℝ) ↦ iteratedFDeriv ℝ j (F p.1 ∘ joinSpaceTime) p.2) :=
  PDE.continuous_iteratedFDeriv_comp_linear_family
    (f := F) (L := fun _ ↦ (spaceTimeContinuousLinearEquiv n).symm.toContinuousLinearMap)
    (fun s ↦ (hF s).of_le (by exact_mod_cast hj)) (hjet j hj) continuous_const

/-- A continuously indexed `C²` wave family with zero initial displacement has a
jointly `C²` retarded field. -/
theorem contDiff_two_retardedWave (hzero : ∀ s x, F s (timeSpaceCons 0 x) = 0) :
    ContDiff ℝ 2 (retardedWave F) :=
  (contDiff_two_retardedIntegral
    (fun s ↦ (hF s).comp (spaceTimeContinuousLinearEquiv n).symm.contDiff)
    (continuous_join_jets hF hjet) hzero).comp (spaceTimeContinuousLinearEquiv n).contDiff

/-- A zero initial kernel value makes the full first derivative of the retarded field zero. -/
theorem fderiv_retardedWave_initial (x : ℝ^n) (hzero : F 0 (timeSpaceCons 0 x) = 0) :
    fderiv ℝ (retardedWave F) (timeSpaceCons 0 x) = 0 := by
  have hc : Continuous (fun p : ℝ × (ℝ^n × ℝ) ↦ (F p.1 ∘ joinSpaceTime) p.2) :=
    PDE.continuous_of_continuous_iteratedFDeriv_zero_family (f := fun s ↦ F s ∘ joinSpaceTime)
      (continuous_join_jets hF hjet 0 (by omega))
  have hD : Continuous (fun p : ℝ × (ℝ^n × ℝ) ↦ fderiv ℝ (F p.1 ∘ joinSpaceTime) p.2) :=
    PDE.continuous_of_continuous_iteratedFDeriv_zero_family
      (f := fun s ↦ fderiv ℝ (F s ∘ joinSpaceTime)) (PDE.continuous_iteratedFDeriv_fderiv_family
        (f := fun s ↦ F s ∘ joinSpaceTime) (j := 0)
        (continuous_join_jets hF hjet 1 (by omega)))
  have hd := hasFDerivAt_retardedIntegral_initial
    (fun s ↦ ((hF s).comp (spaceTimeContinuousLinearEquiv n).symm.contDiff).differentiable
      (by norm_num)) hc hD hzero
  have hcomp := hd.comp (timeSpaceCons 0 x) (spaceTimeContinuousLinearEquiv n).hasFDerivAt
  change fderiv ℝ (fun p ↦ retardedIntegral (fun s q ↦ F s (joinSpaceTime q)) (splitSpaceTime p))
      (timeSpaceCons 0 x) = 0
  simpa only [Function.comp_def, ContinuousLinearMap.zero_comp,
    spaceTimeContinuousLinearEquiv_apply, spaceTimeContinuousLinearEquiv_symm_apply]
      using hcomp.fderiv

/-- The retarded wave operator is the kernel's initial velocity plus its integrated residual.
The formula holds for signed times. -/
theorem waveOperator_retardedWave (hzero : ∀ s x, F s (timeSpaceCons 0 x) = 0) (x : ℝ^n) (t : ℝ) :
    waveOperator (retardedWave F) (timeSpaceCons t x) = (∂[0] (F t)) (timeSpaceCons 0 x) +
      ∫ s in (0 : ℝ)..t, waveOperator (F s) (timeSpaceCons (t - s) x) := by
  let L := (spaceTimeContinuousLinearEquiv n).symm.toContinuousLinearMap
  have hsplit (s : ℝ) : (fun q ↦ (F s ∘ joinSpaceTime) (splitSpaceTime q)) = F s := by
    funext q
    simp
  have he := waveOperator_retardedIntegral (F := fun s ↦ F s ∘ joinSpaceTime)
    (fun s ↦ (hF s).comp L.contDiff) (continuous_join_jets hF hjet) hzero x t
  simp only [hsplit] at he
  have hb : fderiv ℝ (F t ∘ joinSpaceTime) (x, 0) (0, 1) =
      (∂[0] (F t)) (timeSpaceCons 0 x) := by
    change fderiv ℝ (F t ∘ L) (x, 0) (0, 1) = _
    rw [fderiv_comp _ ((hF t).differentiable (by norm_num) _) L.differentiableAt,
      L.fderiv, ContinuousLinearMap.comp_apply]
    have hL : L (0, 1) = EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) := by
      ext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [L, joinSpaceTime, timeSpaceCons]
    rw [hL]
    rfl
  rwa [hb] at he

end WaveEquation
