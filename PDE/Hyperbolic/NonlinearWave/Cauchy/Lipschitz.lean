/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.EnergySolution

/-!
# The whole-space wave equation with a globally Lipschitz scalar reaction

For arbitrary data in `H¹(ℝ^n) × L²(ℝ^n)` and a globally Lipschitz scalar
nonlinearity `f` with `f 0 = 0`, the equation `u_tt - Δu + f(u) = 0` has a forward global
energy solution, unique among energy solutions.

A globally Lipschitz scalar function vanishing at zero induces a globally Lipschitz
map on spatial L². Vanishing at zero is needed on the infinite-measure space:
a nonzero constant source does not lie in L². The scalar composition in the
reaction term is mathlib's L² composition, which agrees almost everywhere with pointwise
application of `f`.

The solution predicate `IsEnergySolution hf hf0 x u` is `IsEnergySolutionOn` on `[0, ∞)` for the
acceleration `Δu - f(u)`: the integrated PDE in L² and the H¹ dual, together with continuity in
the energy space and strong initial traces. The gradient form is the sum of spatial
weak-gradient pairings, as proved in `gradientForm_apply`. Existence and uniqueness are the
general theorems `exists_isEnergySolutionOn_Ici` and `IsEnergySolutionOn.eqOn_Ici` for the force
`u - f(u)`, whose mass term cancels the mass in the constructed linear generator.

`exists_unique_energySolution` is the case `f = f(u)` of Evans, §12.2.1, Theorem 1(i), with data
`g ∈ H¹(ℝⁿ)`, `h ∈ L²(ℝⁿ)` in place of `H¹_loc × L²_loc`, `f` Lipschitz as in (2) and `f(0) = 0`
as assumed throughout §12.2: the problem (1) has a solution for all `t ≥ 0`, unique among energy
solutions. These are continuous into `H¹(ℝⁿ) × L²(ℝⁿ)`, a smaller class than the weak solutions
of §12.2, which have `u ∈ L²(0, T; H¹_loc)` and `u' ∈ L²(0, T; L²_loc)`. Evans solves problems on
balls by a contraction for small times and joins them by finite propagation speed. We work on the
whole space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2, equation (1) and the definition of a weak solution;
  §12.2.1, equation (2), Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval ENNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : ℝ → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The spatial force `u - f(u)` in L², with its almost-everywhere composition
constructed from the scalar Lipschitz map. -/
def source (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (u : H¹(ℝ^n)) : DerivLp n 2 univ :=
  (energyTriple n).inclusion u - hf.compLp hf0 ((energyTriple n).inclusion u)

/-- The source is globally Lipschitz from H¹ to L². -/
theorem source_lipschitz (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    LipschitzWith ((1 + L) * ‖(energyTriple n).inclusion‖₊) (source (n := n) hf hf0) := by
  have h := (LipschitzWith.id.sub (hf.lipschitzWith_compLp hf0
    (μ := domainMeasure n univ) (p := 2))).comp (energyTriple n).inclusion.lipschitzWith
  exact h

/-- The mass-canceling semilinear vector field in the energy Hilbert space. -/
def nonlinearMap (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    C(EnergyState n, EnergyState n) where
  toFun z := (C).symm (0, source hf hf0 (C z).1)
  continuous_toFun := (C).symm.continuous.comp
    (continuous_const.prodMk ((source_lipschitz hf hf0).continuous.comp
      ((C).continuous.fst)))

/-- The energy vector field has a global Lipschitz constant. -/
theorem nonlinearMap_lipschitz (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    ∃ K : NNReal, LipschitzWith K (nonlinearMap (n := n) hf hf0) := by
  have hP := ((ContinuousLinearMap.fst ℝ H¹(ℝ^n) (DerivLp n 2 univ)).comp
    (C).toContinuousLinearMap).lipschitzWith
  have h := (C).symm.toContinuousLinearMap.lipschitzWith.comp
    ((LipschitzWith.const (0 : H¹(ℝ^n))).prodMk ((source_lipschitz hf hf0).comp hP))
  exact ⟨_, h⟩

/-- The distributional acceleration `Δu - f(u)`, valued in the H¹ dual. -/
def acceleration (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (u : H¹(ℝ^n)) : StrongDual ℝ H¹(ℝ^n) :=
  -(energyTriple n).pivotToDual (hf.compLp hf0 ((energyTriple n).inclusion u)) -
    gradientForm n u

/-- Cancellation of the auxiliary mass leaves exactly `Δu - f(u)`. -/
theorem source_sub_massForm (hf : LipschitzWith L f) (hf0 : f 0 = 0) (u : H¹(ℝ^n)) :
    (energyTriple n).pivotToDual (source hf hf0 u) - massForm n u = acceleration hf hf0 u := by
  simp only [source, acceleration, gradientForm, map_sub, sub_apply]
  change _ - _ - _ = -_ - (_ - (energyTriple n).pivotToDual ((energyTriple n).inclusion u))
  abel

/-- The weak acceleration depends continuously on the displacement in H¹. -/
theorem continuous_acceleration (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    Continuous (acceleration (n := n) hf hf0) := by
  have h := ((energyTriple n).pivotToDual.continuous.comp
    (source_lipschitz hf hf0).continuous).sub (massForm n).continuous
  change Continuous (fun u ↦ (energyTriple n).pivotToDual (source hf hf0 u) - massForm n u) at h
  simpa only [source_sub_massForm hf hf0] using h

/-- A forward energy solution of `u_tt - Δu + f(u) = 0` with displacement and
velocity data `x`: `IsEnergySolutionOn` on `[0, ∞)` for the acceleration `Δu - f(u)`. The two
integral equations give the time derivatives in L² and the H¹ dual; all spatial derivatives
are the Sobolev weak derivatives. -/
abbrev IsEnergySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ) : Prop :=
  IsEnergySolutionOn (fun z ↦ acceleration hf hf0 z.1) x (Ici 0) u

/-- Arbitrary whole-space energy data admit a forward global solution. There is
no smallness, compact-support, extra spatial regularity, or finite-lifetime
assumption. Negative times merely supply a continuous extension for integration. -/
theorem exists_energySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolution hf hf0 x u := by
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz (n := n) hf hf0
  exact exists_isEnergySolutionOn_Ici (F := fun z ↦ source hf hf0 z.1)
    ((source_lipschitz hf hf0).continuous.comp continuous_fst)
    (fun z ↦ source_sub_massForm hf hf0 z.1) (fun _ ↦ rfl) hK x

/-- The PDE's integral equations imply the mild equation for the constructed
whole-space generator on every positive finite interval. This is
`IsEnergySolutionOn.isMildSolutionOn` for the force `u - f(u)` and the vector field
`nonlinearMap hf hf0`. -/
theorem IsEnergySolution.isMildSolutionOn {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0 x u) {τ : NNReal} (hτ : 0 < (τ : ℝ)) :
    (linearSemigroup n).IsMildSolutionOn (nonlinearMap hf hf0)
      ((C).symm x) τ (energyTrace u τ) :=
  IsEnergySolutionOn.isMildSolutionOn (F := fun z ↦ source hf hf0 z.1)
    (G := nonlinearMap hf hf0) (τ := τ) (h.mono Icc_subset_Ici_self)
    ((source_lipschitz hf hf0).continuous.comp continuous_fst)
    (fun z ↦ source_sub_massForm hf hf0 z.1) (fun _ ↦ rfl) hτ

/-- Two global energy solutions with the same data agree at every nonnegative
time. No mild representation is assumed of either solution. -/
theorem IsEnergySolution.eqOn {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hu : IsEnergySolution hf hf0 x u) (hv : IsEnergySolution hf hf0 x v) :
    EqOn u v (Ici 0) := by
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz (n := n) hf hf0
  exact IsEnergySolutionOn.eqOn_Ici (F := fun z ↦ source hf hf0 z.1) hu hv
    ((source_lipschitz hf hf0).continuous.comp continuous_fst)
    (fun z ↦ source_sub_massForm hf hf0 z.1) (fun _ ↦ rfl) hK.locallyLipschitz

/-- Forward global existence and uniqueness of the whole-space semilinear wave
Cauchy problem for arbitrary natural energy data and globally Lipschitz `f`
vanishing at zero. The conclusion is the integrated weak PDE, its initial
traces, and uniqueness among all forward energy-continuous solutions. -/
theorem exists_unique_energySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolution hf hf0 x u ∧
      ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ, IsEnergySolution hf hf0 x v → EqOn u v (Ici 0) := by
  obtain ⟨u, hu⟩ := exists_energySolution hf hf0 x
  exact ⟨u, hu, fun _ hv ↦ hu.eqOn hv⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
