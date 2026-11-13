/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local wave-strength parameterization for conservation-law systems

The analytic step in the proof of Theorem 4 of Evans, §11.2.4, composes wave curves in
characteristic order, (44)-(47). At zero strengths, the columns of the derivative are the right
characteristic vectors, as in (49). When these vectors form a basis, the finite-dimensional
inverse function theorem gives:

* open neighborhoods of zero strength and the left state;
* one wave-strength vector for each nearby right state;
* uniqueness of that vector inside the source neighborhood.

The result is an `OpenPartialHomeomorph`, which records existence,
uniqueness, openness, and continuity of the local parameterization.

This is the inverse-function-theorem step for a `LocalWaveFamily`.
`WaveCurve.Construction` constructs that family from the flux hypotheses;
`Riemann.Construction` and `Riemann.InitialValue` assemble its elementary waves
and prove the initial weak equation and strong trace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, Theorem 4 and its proof, equations (44)-(49).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}
variable {flux : ℝ^m → ℝ^m}
variable {fields : Fin m → CharacteristicField flux}
variable {states : Set (ℝ^m)}

namespace LocalWaveFamily

/-- Continuous linear equivalence whose columns are a prescribed basis.
It maps a Euclidean coordinate vector `v` to `∑ k, v k • basis k`. -/
def basisCoordinateEquiv
    (basis : Module.Basis (Fin m) ℝ (ℝ^m)) :
    ℝ^m ≃L[ℝ] ℝ^m :=
  (EuclideanSpace.equiv (Fin m) ℝ).trans basis.equivFunL.symm

/-- The coordinate equivalence sends `v` to the combination `∑ k, v k • basis k`
of the basis vectors. -/
theorem basisCoordinateEquiv_apply (basis : Module.Basis (Fin m) ℝ (ℝ^m)) (v : ℝ^m) :
    basisCoordinateEquiv basis v = ∑ k, v k • basis k := by
  change basis.equivFunL.symm (WithLp.ofLp v) = ∑ k, v k • basis k
  exact basis.equivFun_symm_apply (WithLp.ofLp v)

/-- If the characteristic vectors at the left state are a basis, the
derivative of the ordered wave map is the associated linear equivalence. -/
theorem composedWaveDerivative_eq_basisCoordinateEquiv (W : LocalWaveFamily flux fields states)
    (left : ℝ^m) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    W.composedWaveDerivative left = (basisCoordinateEquiv basis : ℝ^m →L[ℝ] ℝ^m) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [W.composedWaveDerivative_apply]
  change (∑ k, v k • (fields k).rightEigenvector left) = basisCoordinateEquiv basis v
  rw [basisCoordinateEquiv_apply]
  simp_rw [hbasis]

/-- The ordered wave map has an invertible strict derivative at zero whenever
the right characteristic vectors at the left state form a basis. -/
theorem hasStrictFDerivAt_composedWaveMap_basis (W : LocalWaveFamily flux fields states)
    (left : ℝ^m) (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    HasStrictFDerivAt (W.composedWaveMap left) (basisCoordinateEquiv basis : ℝ^m →L[ℝ] ℝ^m) 0 :=
  (W.hasStrictFDerivAt_composedWaveMap left hleft).congr_fderiv
    (W.composedWaveDerivative_eq_basisCoordinateEquiv left basis hbasis)

/-- The local homeomorphism from wave strengths to right states supplied by
the inverse function theorem. -/
def localRiemannHomeomorph
    (W : LocalWaveFamily flux fields states) (left : ℝ^m) (hleft : left ∈ states)
    (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis :
      ∀ k, (fields k).rightEigenvector left = basis k) :
    OpenPartialHomeomorph (ℝ^m) (ℝ^m) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (W.composedWaveMap left)
    (W.hasStrictFDerivAt_composedWaveMap_basis left hleft basis hbasis)

/-- The forward map of the local strength chart is the ordered wave map. -/
@[simp]
theorem localRiemannHomeomorph_apply (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) (strength : ℝ^m) :
    W.localRiemannHomeomorph left hleft basis hbasis strength = W.composedWaveMap left strength :=
  rfl

/-- Zero strength belongs to the source neighborhood of the local solver. -/
theorem zero_mem_localRiemannHomeomorph_source (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    0 ∈ (W.localRiemannHomeomorph left hleft basis hbasis).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (W.hasStrictFDerivAt_composedWaveMap_basis left hleft basis hbasis)

/-- The left state belongs to the target neighborhood of the local solver. -/
theorem left_mem_localRiemannHomeomorph_target (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    left ∈ (W.localRiemannHomeomorph left hleft basis hbasis).target := by
  simpa [localRiemannHomeomorph] using HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target
      (W.hasStrictFDerivAt_composedWaveMap_basis left hleft basis hbasis)

/-- Wave strengths selected by the local inverse for a right state. -/
def localRiemannStrength
    (W : LocalWaveFamily flux fields states) (left : ℝ^m) (hleft : left ∈ states)
    (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis :
      ∀ k, (fields k).rightEigenvector left = basis k)
    (right : ℝ^m) : ℝ^m :=
  (W.localRiemannHomeomorph left hleft basis hbasis).symm right

/-- The locally selected wave strengths depend continuously on the right
state throughout the target neighborhood. -/
theorem continuousOn_localRiemannStrength (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    ContinuousOn (W.localRiemannStrength left hleft basis hbasis)
      (W.localRiemannHomeomorph left hleft basis hbasis).target := by
  change ContinuousOn (fun right ↦ (W.localRiemannHomeomorph left hleft basis hbasis).symm right)
    (W.localRiemannHomeomorph left hleft basis hbasis).target
  exact (W.localRiemannHomeomorph left hleft basis hbasis).continuousOn_symm

/-- The local solver assigns zero wave strength when both states coincide. -/
@[simp]
theorem localRiemannStrength_left (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    W.localRiemannStrength left hleft basis hbasis left = 0 := by
  let e := W.localRiemannHomeomorph left hleft basis hbasis
  have hzero : (0 : ℝ^m) ∈ e.source := by
    simpa only [e] using W.zero_mem_localRiemannHomeomorph_source left hleft basis hbasis
  have hinv := e.left_inv hzero
  simpa only [e, localRiemannStrength, localRiemannHomeomorph_apply,
    W.composedWaveMap_zero] using hinv

/-- At the base state the selected strengths tend to zero. This allows all
local wave-construction conditions to be enforced before choosing the nearby
right state. -/
theorem tendsto_localRiemannStrength (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    Filter.Tendsto (W.localRiemannStrength left hleft basis hbasis) (nhds left) (nhds 0) := by
  have hcont := (W.continuousOn_localRiemannStrength left hleft basis hbasis).continuousAt
      ((W.localRiemannHomeomorph left hleft basis hbasis).open_target.mem_nhds
        (W.left_mem_localRiemannHomeomorph_target left hleft basis hbasis))
  simpa only [ContinuousAt, W.localRiemannStrength_left] using hcont

/-- The selected strengths lie in the source neighborhood whenever the
right state lies in the target neighborhood. -/
theorem localRiemannStrength_mem_source (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) {right : ℝ^m}
    (hright : right ∈ (W.localRiemannHomeomorph left hleft basis hbasis).target) :
    W.localRiemannStrength left hleft basis hbasis right ∈
      (W.localRiemannHomeomorph left hleft basis hbasis).source :=
  (W.localRiemannHomeomorph left hleft basis hbasis).map_target hright

/-- Applying the ordered waves with the selected strengths reaches the
prescribed nearby right state. -/
theorem composedWaveMap_localRiemannStrength (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) {right : ℝ^m}
    (hright : right ∈ (W.localRiemannHomeomorph left hleft basis hbasis).target) :
    W.composedWaveMap left (W.localRiemannStrength left hleft basis hbasis right) = right :=
  (W.localRiemannHomeomorph left hleft basis hbasis).right_inv hright

/-- Uniqueness of local wave strengths inside the source neighborhood. -/
theorem localRiemannStrength_unique (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) {right strength : ℝ^m}
    (hstrength : strength ∈ (W.localRiemannHomeomorph left hleft basis hbasis).source)
    (hmap : W.composedWaveMap left strength = right) :
    strength = W.localRiemannStrength left hleft basis hbasis right := by
  let e := W.localRiemannHomeomorph left hleft basis hbasis
  calc
    strength = e.symm (e strength) := (e.left_inv hstrength).symm
    _ = e.symm right :=
      congrArg e.symm <| by
        simpa [e] using hmap

/-- The inverse-function-theorem step in the proof of Theorem 4 of Evans, §11.2.4.

There are open neighborhoods of zero strength and the left state such that
every right state in the target has exactly one ordered strength vector in
the source. This statement is an analytic parameterization theorem. -/
theorem existsUnique_localRiemann_strength (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    ∃ source target : Set (ℝ^m), IsOpen source ∧ IsOpen target ∧ 0 ∈ source ∧ left ∈ target ∧
      ∀ right ∈ target, ∃! strength : ℝ^m, strength ∈ source ∧
      W.composedWaveMap left strength = right := by
  let e := W.localRiemannHomeomorph left hleft basis hbasis
  refine ⟨e.source, e.target, e.open_source, e.open_target,
      W.zero_mem_localRiemannHomeomorph_source left hleft basis hbasis,
      W.left_mem_localRiemannHomeomorph_target left hleft basis hbasis, ?_⟩
  intro right hright
  refine ⟨W.localRiemannStrength left hleft basis hbasis right, ⟨W.localRiemannStrength_mem_source
          left hleft basis hbasis hright,
        W.composedWaveMap_localRiemannStrength left hleft basis hbasis hright⟩, ?_⟩
  intro strength hstrength
  exact W.localRiemannStrength_unique left hleft basis hbasis hstrength.1 hstrength.2

end LocalWaveFamily

end PDE.Hyperbolic.ConservationLaw.System
