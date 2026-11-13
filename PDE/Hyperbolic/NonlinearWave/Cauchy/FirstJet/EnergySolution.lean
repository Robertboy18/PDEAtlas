/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Lipschitz

/-!
# Global first-derivative nonlinear waves for whole-space energy data

The semigroup construction yields solutions of `u_tt - Δu + f(Du,u_t,u) = 0`
for arbitrary `H¹ × L²` data and globally Lipschitz `f` fixing zero. The solution predicate
`IsEnergySolution hf hf0 x u` is `IsEnergySolutionOn` on `[0, ∞)` for the acceleration
`Δu - f(Du,u_t,u)`: both integrated equations and the strong initial traces are part of it.
Existence and uniqueness are the general theorems `exists_isEnergySolutionOn_Ici` and
`IsEnergySolutionOn.eqOn_Ici` for the force `u - f(Du,u_t,u)`; uniqueness holds among solutions
of the integrated equations, without assuming a mild representation.

This is Theorem 1(i) of Evans, §12.2.1, for whole-space energy data; Evans takes local data
`g ∈ H¹_loc`, `h ∈ L²_loc`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2, definition of a weak solution; §12.2.1, Theorem 1(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The distributional acceleration `Δu - f(Du,v,u)` in the H¹ dual. -/
def acceleration (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) : StrongDual ℝ H¹(ℝ^n) :=
  -(energyTriple n).pivotToDual (reaction hf hf0 z) - gradientForm n z.1

/-- The auxiliary mass cancels, leaving the wave equation's acceleration. -/
theorem source_sub_massForm (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    (energyTriple n).pivotToDual (source hf hf0 z) - massForm n z.1 = acceleration hf hf0 z := by
  simp only [source, acceleration, gradientForm, map_sub, sub_apply]
  change _ - _ - _ = -_ - (_ - (energyTriple n).pivotToDual ((energyTriple n).inclusion z.1))
  abel

/-- The weak acceleration is continuous in the full energy state. -/
theorem continuous_acceleration (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    Continuous (acceleration hf hf0) :=
  ((energyTriple n).pivotToDual.continuous.comp (reaction_lipschitz hf hf0).continuous).neg.sub
      ((gradientForm n).continuous.comp continuous_fst)

/-- A forward energy solution of `u_tt - Δu + f(Du,v,u) = 0` with displacement and
velocity data `x`: `IsEnergySolutionOn` on `[0, ∞)` for the acceleration `Δu - f(Du,v,u)`. The
two integral equations give the time derivatives in L² and the H¹ dual; all spatial derivatives
are the Sobolev weak derivatives. -/
abbrev IsEnergySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ) : Prop :=
  IsEnergySolutionOn (acceleration hf hf0) x (Ici 0) u

/-- Arbitrary whole-space energy data admit a forward global solution. There is
no smallness, compact-support, extra spatial regularity, or finite-lifetime
assumption. Negative times merely supply a continuous extension for integration. -/
theorem exists_energySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolution hf hf0 x u := by
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz (n := n) hf hf0
  exact exists_isEnergySolutionOn_Ici (source_lipschitz hf hf0).continuous
    (source_sub_massForm hf hf0) (fun _ ↦ rfl) hK x

/-- The PDE's integral equations imply the mild equation for the constructed
whole-space generator on every positive finite interval. This is
`IsEnergySolutionOn.isMildSolutionOn` for the force `source hf hf0` and the vector field
`nonlinearMap hf hf0`. -/
theorem IsEnergySolution.isMildSolutionOn {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0 x u) {τ : NNReal} (hτ : 0 < (τ : ℝ)) :
    (linearSemigroup n).IsMildSolutionOn (nonlinearMap hf hf0) ((C).symm x) τ
    (energyTrace u τ) :=
  IsEnergySolutionOn.isMildSolutionOn (G := nonlinearMap hf hf0) (τ := τ)
    (h.mono Icc_subset_Ici_self) (source_lipschitz hf hf0).continuous
    (source_sub_massForm hf hf0) (fun _ ↦ rfl) hτ

/-- Two global energy solutions with the same data agree at every nonnegative
time. No mild representation is assumed of either solution. -/
theorem IsEnergySolution.eqOn {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hu : IsEnergySolution hf hf0 x u) (hv : IsEnergySolution hf hf0 x v) :
    EqOn u v (Ici 0) := by
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz (n := n) hf hf0
  exact IsEnergySolutionOn.eqOn_Ici hu hv (source_lipschitz hf hf0).continuous
    (source_sub_massForm hf hf0) (fun _ ↦ rfl) hK.locallyLipschitz

/-- Forward global existence and uniqueness of the whole-space first-derivative nonlinear wave
Cauchy problem for arbitrary natural energy data and globally Lipschitz `f`
vanishing at zero. The conclusion is the integrated weak PDE, its initial
traces, and uniqueness among all forward energy-continuous solutions. -/
theorem exists_unique_energySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolution hf hf0 x u ∧
      ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ, IsEnergySolution hf hf0 x v → EqOn u v (Ici 0) := by
  obtain ⟨u, hu⟩ := exists_energySolution hf hf0 x
  exact ⟨u, hu, fun _ hv ↦ hu.eqOn hv⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
