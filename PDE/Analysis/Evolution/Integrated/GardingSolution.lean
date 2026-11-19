/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# Weak solutions with time regularity and a Gårding estimate

A structure collecting the conclusions of the existence theorem. The derivative is
linked to the solution by the weak derivative identity and the equation, and
the continuous pivot curve represents the same Bochner class.

## Implementation notes

A weak solution persists through later arguments, so `GardingWeakSolutionOn` is a structure
that carries its data (state, derivative and continuous pivot evolution) together with the
predicate `IsGardingWeakSolutionOn` for its equation, uniqueness, initial trace and energy
estimate. Intermediate energy bounds, convergence facts and compatibility conditions stay
predicates or explicit hypotheses, so that no theorem asks for a record that carries no
mathematical data.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The equation, uniqueness, trace, and Gårding estimate for prescribed solution classes
and their continuous evolution. These properties are conclusions of the existence theorem. -/
structure IsGardingWeakSolutionOn
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (uInit : H) (a b theta gamma : ℝ)
    (state : Lp V 2 (volume.restrict (Ioc a b)))
    (derivative : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (evolution : ContinuousPivotEvolutionOn T (fun t ↦ state t) (fun t ↦ derivative t) a b) :
    Prop where
  /-- The integrated equation with the prescribed initial datum. -/
  solution : IsGelfandIntegratedWeakSolution T B ell state uInit
  /-- Uniqueness among all integrated weak solutions with the same data. -/
  unique : ∀ v, IsGelfandIntegratedWeakSolution T B ell v uInit → v = state
  /-- The derivative satisfies the distributional identity. -/
  weakDerivative : HasGelfandWeakTimeDerivativeOn T state derivative
  /-- The continuous representative attains the initial datum. -/
  initial : evolution.representative a = uInit
  /-- The equation holds almost everywhere as an identity in the energy dual. -/
  residual : (derivative : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)]
    fun t ↦ ell t - B t (state t)
  /-- The integrated Gårding estimate on every initial subinterval. -/
  energy : ∀ t ∈ Icc a b,
    (1 / 2 : ℝ) * ‖evolution.representative t‖ ^ 2 +
        (theta / 2) * (∫ s in a..t, ‖state s‖ ^ 2) ≤
      (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
        (1 / (2 * theta)) * (∫ s in a..t, ‖ell s‖ ^ 2) +
        gamma * (∫ s in a..t, ‖evolution.representative s‖ ^ 2)

/-- A weak solution together with its derived time regularity and Gårding estimate.
The proof fields are grouped separately from the state, derivative, and continuous evolution. -/
structure GardingWeakSolutionOn
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (uInit : H) (a b theta gamma : ℝ) where
  /-- The energy-space Bochner solution. -/
  state : Lp V 2 (volume.restrict (Ioc a b))
  /-- Its weak time derivative. -/
  derivative : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))
  /-- The continuous pivot representative of this state and derivative. -/
  evolution : ContinuousPivotEvolutionOn T (fun t ↦ state t) (fun t ↦ derivative t) a b
  /-- The derived weak equation, trace, uniqueness, and energy estimate. -/
  properties : IsGardingWeakSolutionOn T B ell uInit a b theta gamma state derivative evolution

/-- Replacing the load by an almost-everywhere equal function preserves the
solution and every prefix energy estimate. -/
def GardingWeakSolutionOn.congrForcing
    {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell ell' : ℝ → StrongDual ℝ V}
    {uInit : H} {a b theta gamma : ℝ}
    (U : GardingWeakSolutionOn T B ell uInit a b theta gamma)
    (h : ell =ᵐ[volume.restrict (Ioc a b)] ell') :
    GardingWeakSolutionOn T B ell' uInit a b theta gamma := by
  refine ⟨U.state, U.derivative, U.evolution, ⟨U.properties.solution.congr_forcing_ae h,
    ?_, U.properties.weakDerivative, U.properties.initial, ?_, ?_⟩⟩
  · intro v hv
    exact U.properties.unique v (hv.congr_forcing_ae h.symm)
  · filter_upwards [U.properties.residual, h] with t ht hft
    rw [ht, hft]
  · intro t ht
    have hm : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
      volume.restrict_mono_set (Ioc_subset_Ioc_right ht.2)
    have hi : (∫ s in a..t, ‖ell s‖ ^ 2) = ∫ s in a..t, ‖ell' s‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
      exact integral_congr_ae ((h.filter_mono (ae_mono hm)).fun_comp (fun z ↦ ‖z‖ ^ 2))
    simpa only [hi] using U.properties.energy t ht

end PDE.Analysis.Evolution
