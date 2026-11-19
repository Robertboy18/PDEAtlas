/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCutoffWeak
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCutoffRestriction

/-!
# Exterior forcing introduced by local wave cutoffs

The localized massive-wave forcing differs from the whole-space nonlinear
source only outside the region where the cutoff is one. This error remains
square-integrable in time for every local energy weak solution.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω S : Set (ℝ^n)} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- On the unit region, the cutoff state equals restriction of the original state. -/
theorem restrict_localCutoffStateCLM (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω) (hη : ∀ y ∈ S, η y = 1)
    (z : H¹(Ω) × DerivLp n 2 Ω) :
    restrictStateCLM hS.measurableSet (localCutoffStateCLM hΩ η hηΩ z) =
      (restrictCLM hS.measurableSet hSΩ z.1, restrictDerivLp hSΩ z.2) := by
  change (restrictCLM hS.measurableSet (subset_univ S) (localCutoffDisplacementCLM hΩ η hηΩ z.1),
      restrictDerivLp (subset_univ S) (localCutoffVelocityCLM hΩ.measurableSet η z.2)) = _
  apply Prod.ext
  · simpa only [one_smul] using restrict_localCutoffDisplacementCLM hΩ hS hSΩ η hηΩ hη z.1
  · simpa only [one_smul] using
      restrict_localCutoffVelocityCLM hΩ.measurableSet hS.measurableSet hSΩ η hη z.2

/-- The nonlinear error created by the spatial cutoff. -/
def localCutoffError (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω)
    (hf : LipschitzWith L f) (hf0 : f 0 = 0) (z : H¹(Ω) × DerivLp n 2 Ω) :
    DerivLp n 2 univ :=
  localCutoffForcing hΩ η hη hf hf0 z -
    source hf hf0 (localCutoffStateCLM hΩ η hη z)

/-- The cutoff error vanishes on every open region where the cutoff is one. -/
theorem restrict_localCutoffError (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω) (hη : ∀ y ∈ S, η y = 1)
    (hf : LipschitzWith L f) (hf0 : f 0 = 0) (z : H¹(Ω) × DerivLp n 2 Ω) :
    restrictDerivLp (subset_univ S) (localCutoffError hΩ η hηΩ hf hf0 z) = 0 := by
  rw [localCutoffError, map_sub, sub_eq_zero, localCutoffForcing, map_sub,
    restrict_localCutoffCommutatorCLM hΩ hS hSΩ η hηΩ hη z.1, sub_zero,
    restrict_localCutoffVelocityCLM hΩ.measurableSet hS.measurableSet hSΩ η hη,
    one_smul, map_sub, source, map_sub]
  apply congrArg₂ (fun a b : DerivLp n 2 S ↦ a - b)
  · have h := congrArg (fun w : H¹(S) × DerivLp n 2 S ↦ wkpBaseCoordinateCLM w.1)
      (restrict_localCutoffStateCLM hΩ hS hSΩ η hηΩ hη z)
    exact h.symm
  · rw [← localReaction_restrict hf hf0 hS.measurableSet,
      restrict_localCutoffStateCLM hΩ hS hSΩ η hηΩ hη z,
      localReaction_restrict_between hf hf0 hS.measurableSet hSΩ]

/-- The cutoff error has the same time integrability as the local energy state. -/
theorem memLp_localCutoffError (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) (hf : LipschitzWith L f) (hf0 : f 0 = 0) {μ : Measure ℝ}
    {u : ℝ → H¹(Ω) × DerivLp n 2 Ω} (hu : MemLp u 2 μ) :
    MemLp (fun t ↦ localCutoffError hΩ η hη hf hf0 (u t)) 2 μ := by
  have hzero : source hf hf0 0 = 0 := by
    simp only [source, Prod.fst_zero, reaction, map_zero, LipschitzWith.compLp_zero, sub_zero]
  have hD : MemLp (fun t ↦ localCutoffStateCLM hΩ η hη (u t)) 2 μ :=
    (localCutoffStateCLM hΩ η hη).comp_memLp' hu
  have hs : MemLp (fun t ↦ source hf hf0 (localCutoffStateCLM hΩ η hη (u t))) 2 μ :=
    (source_lipschitz hf hf0).comp_memLp hzero hD
  exact (memLp_localCutoffForcing hΩ η hη hf hf0 hu).sub hs

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
