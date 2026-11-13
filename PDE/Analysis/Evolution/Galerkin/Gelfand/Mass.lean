/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Analysis.Evolution.Hilbert.Riesz

/-!
# Pivot mass operators on Galerkin spaces

The pivot inner product induces a positive-definite bilinear form on every
finite-dimensional trial space. We define that form, its Riesz operator with
respect to the inherited energy-space inner product, and the continuous linear
equivalence obtained from injectivity of the Gelfand embedding. On a finite-dimensional
trial space the pivot norm also controls the energy norm: `‖u‖_V ≤ K_S ‖ι u‖_H` with a
constant `K_S > 0` depending on `S`.

Evans takes the basis orthonormal in `L²` (§7.1.2, equation (13)), which makes his mass
matrix the identity; on a general trial space the mass operator has to be inverted.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, equations (13) and (16).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open InnerProductSpace
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
section GelfandGalerkinMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The mass form on a trial space induced by the pivot Hilbert space:
`M_S(u,v) = ⟪i(u),i(v)⟫_H`. The time-derivative term of the Galerkin equation uses this
form, not the inherited inner product of `V`. -/
def trialPivotForm
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V) :
    S →L[ℝ] StrongDual ℝ S :=
  (ContinuousLinearMap.toSesqForm (T.inclusion.comp S.subtypeL)).comp
    (T.inclusion.comp S.subtypeL)

/-- The trial pivot form is the pivot inner product of the included vectors. -/
@[simp]
theorem trialPivotForm_apply
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V) (u v : S) :
    trialPivotForm T S u v =
      inner ℝ (T.inclusion (u : V)) (T.inclusion (v : V)) :=
  rfl

/-- Riesz representative, in the trial-space inner product, of the pivot
mass form. -/
def trialMassOperator
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [CompleteSpace S] : S →L[ℝ] S :=
  continuousLinearMapOfBilin (trialPivotForm T S)

/-- Injectivity of `V ↪ H` makes the trial mass operator nonsingular. -/
theorem trialMassOperator_injective
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [CompleteSpace S] :
    Function.Injective (trialMassOperator T S) := by
  apply LinearMap.ker_eq_bot.mp
  ext u
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hu
    have hinner : inner ℝ (T.inclusion (u : V)) (T.inclusion (u : V)) = 0 := by
      rw [← trialPivotForm_apply T S u u, ← continuousLinearMapOfBilin_apply]
      have hu' : continuousLinearMapOfBilin (trialPivotForm T S) u = 0 := by
        simpa [trialMassOperator] using hu
      rw [hu']
      simp
    have hinc : T.inclusion (u : V) = 0 := by
      simpa only [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hinner
    exact Subtype.ext (T.injective (by simpa using hinc))
  · rintro rfl
    simp

/-- On a finite-dimensional trial space the injective pivot mass operator is
a continuous linear equivalence. -/
def trialMassEquiv
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S] : S ≃L[ℝ] S :=
  ContinuousLinearEquiv.ofBijective (trialMassOperator T S)
    (by
      rw [LinearMap.ker_eq_bot]
      exact trialMassOperator_injective T S)
    (by
      rw [LinearMap.range_eq_top]
      exact LinearMap.injective_iff_surjective.mp (trialMassOperator_injective T S))

/--
The pivot inclusion of a finite-dimensional trial space is anti-Lipschitz.

Equivalently, the energy norm on the trial space is controlled by the pivot norm, with a
constant depending on the trial space.
-/
theorem exists_trialInclusion_antilipschitzWith
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] :
    ∃ K > 0, AntilipschitzWith K (T.inclusion.comp S.subtypeL) := by
  exact
    ((T.inclusion.comp S.subtypeL).toLinearMap.injective_iff_antilipschitz).mp
      (T.injective.comp Subtype.val_injective)

/--
A chosen inverse norm bound for the pivot inclusion of a finite-dimensional
trial space.
-/
def trialInclusionInverseBound
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] : NNReal :=
  Classical.choose (exists_trialInclusion_antilipschitzWith T S)

/-- The chosen inverse bound is strictly positive. -/
theorem trialInclusionInverseBound_pos
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] :
    0 < trialInclusionInverseBound T S :=
  (Classical.choose_spec (exists_trialInclusion_antilipschitzWith T S)).1

/-- The chosen inverse bound makes the trial inclusion anti-Lipschitz. -/
theorem trialInclusionInverseBound_antilipschitz
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] :
    AntilipschitzWith (trialInclusionInverseBound T S)
      (T.inclusion.comp S.subtypeL) :=
  (Classical.choose_spec (exists_trialInclusion_antilipschitzWith T S)).2

/--
The trial-space norm is bounded by the pivot norm with the chosen
finite-dimensional inverse inclusion constant.
-/
theorem norm_trial_le_trialInclusionInverseBound_mul_norm_inclusion
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] (u : S) :
    ‖u‖ ≤ (trialInclusionInverseBound T S : ℝ) *
      ‖T.inclusion (u : V)‖ := by
  simpa using
    (T.inclusion.comp S.subtypeL).bound_of_antilipschitz
      (trialInclusionInverseBound_antilipschitz T S) u

end GelfandGalerkinMass

end Galerkin

end PDE.Analysis.Evolution
