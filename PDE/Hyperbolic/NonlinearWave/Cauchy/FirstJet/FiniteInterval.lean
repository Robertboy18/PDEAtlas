/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.WeakFormulation

/-!
# Finite-interval uniqueness for first-jet energy waves

A competing solution needs to satisfy the integrated PDE only on the finite
interval under comparison. The predicate `IsEnergySolutionOn hf hf0 x τ u` is the general
`Cauchy.IsEnergySolutionOn` on `[0, τ]` for the first-jet acceleration, and uniqueness is the
general `Cauchy.IsEnergySolutionOn.eqOn_Icc`. Compactness also gives bounded energy on each such
interval.

The spatial data are whole-space H¹ × L² data; Evans, §12.2.1, Theorem 1, takes local data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The energy PDE on one closed time interval, with both initial data: the general
`Cauchy.IsEnergySolutionOn` on `[0, τ]` for the acceleration `Δu - f(Du,v,u)`. Values
of the representing curve outside this interval are irrelevant. -/
abbrev IsEnergySolutionOn (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) (τ : NNReal)
    (u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ) : Prop :=
  Cauchy.IsEnergySolutionOn (acceleration hf hf0) x (Icc 0 (τ : ℝ)) u

variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}
variable {x : H¹(ℝ^n) × DerivLp n 2 univ} {τ : NNReal}
variable {u v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}

/-- A global energy solution restricts to each finite interval. -/
theorem IsEnergySolution.on (h : IsEnergySolution hf hf0 x u) (τ : NNReal) :
    IsEnergySolutionOn hf hf0 x τ u :=
  h.mono Icc_subset_Ici_self

/-- Linear identification derives the mild representation from the finite-time PDE. This is
`Cauchy.IsEnergySolutionOn.isMildSolutionOn` for the force `source hf hf0` and the vector field
`nonlinearMap hf hf0`. -/
theorem IsEnergySolutionOn.isMildSolutionOn {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolutionOn hf hf0 x τ u) (hτ : 0 < (τ : ℝ)) :
    (linearSemigroup n).IsMildSolutionOn (nonlinearMap hf hf0)
      ((C).symm x) τ (energyTrace u τ) :=
  Cauchy.IsEnergySolutionOn.isMildSolutionOn (G := nonlinearMap hf hf0) h
    (source_lipschitz hf hf0).continuous (source_sub_massForm hf hf0) (fun _ ↦ rfl) hτ

/-- Two solutions on a finite interval agree there. -/
theorem IsEnergySolutionOn.eqOn (hu : IsEnergySolutionOn hf hf0 x τ u)
    (hv : IsEnergySolutionOn hf hf0 x τ v) : EqOn u v (Icc 0 (τ : ℝ)) := by
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz (n := n) hf hf0
  exact hu.eqOn_Icc hv (source_lipschitz hf hf0).continuous (source_sub_massForm hf hf0)
    (fun _ ↦ rfl) hK.locallyLipschitz

/-- Arbitrary whole-space energy data give a unique finite-time PDE solution
on every closed forward interval, with bounded natural energy norm. -/
theorem exists_unique_energySolutionOn (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) (τ : NNReal) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolutionOn hf hf0 x τ u ∧
      (∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc 0 (τ : ℝ), ‖u t‖ ≤ R) ∧ ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ,
      IsEnergySolutionOn hf hf0 x τ v → EqOn u v (Icc 0 (τ : ℝ)) := by
  obtain ⟨u, hu⟩ := exists_energySolution hf hf0 x
  exact ⟨u, hu.on τ, (hu.on τ).exists_norm_bound, fun _ hv ↦ (hu.on τ).eqOn hv⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
