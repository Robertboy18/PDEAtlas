/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.Analysis.Evolution.Time.WeakDerivative.AbsolutelyContinuous
import PDE.Analysis.Evolution.Time.WeakDerivative.Euclidean

/-!
# Constructing one-dimensional Sobolev classes

On the real line, a Sobolev function of order one is the same thing as an absolutely continuous
function with integrable derivative: if `f ∈ L¹(ℝ)` is absolutely continuous on every compact
interval and its pointwise derivative `f' = g` (which exists almost everywhere) is again in `L¹(ℝ)`,
then `g` is the weak derivative of `f`, and `f` determines an element of `W^{1,1}(ℝ)`. We state that
direction of the classical characterization of `W^{1,p}` on an interval (Brezis, Chapter 8) as a
constructor for the graph-space model `WkpSpace 1 1 1`.

The converse, that every `W^{1,1}(ℝ)` class has an absolutely continuous
representative, is `Slicing.AbsolutelyContinuousRepresentative`.

## Main definitions and results

* `oneDimensionalPullback`: the identification
  `ℝ^1 ≃ ℝ` used to transport real-line functions to the Euclidean model.
* `mkW11OfAbsolutelyContinuous`: the `W^{1,1}(ℝ)` element built from `f`, `g`,
  the integrability hypotheses, absolute continuity on intervals, and the
  almost-everywhere derivative identity.
* `mkW11OfAbsolutelyContinuous_base_ae`,
  `mkW11OfAbsolutelyContinuous_derivative_ae`: its base coordinate is `f` and
  its derivative coordinate is `g`, up to null sets.

## Implementation notes

The weak-derivative identity is obtained from the one-dimensional time
derivative theory (`HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval`)
and then transported along `PiLp.equivOfUnique`; integrability of
the pulled-back functions uses that this equivalence is measure preserving.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for the description of `W^{1,p}` on an interval by absolutely
  continuous functions.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

/-- Pull a real-line function back to one-dimensional Euclidean space. -/
def oneDimensionalPullback (f : ℝ → ℝ) : ℝ^1 → ℝ :=
  fun x ↦ f ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x)

/-- The two coordinate rows of the `W^{1,1}(ℝ)` element built from a
representative `f` and its almost-everywhere derivative `g`: the base row is the
pullback of `f`, the derivative row is the pullback of `g`. -/
def w11Rows (f g : ℝ → ℝ) :
    DerivIndex 1 1 → ℝ^1 → ℝ :=
  fun a ↦
    if a.toList = [] then oneDimensionalPullback f
    else oneDimensionalPullback g

private theorem oneDimensionalPullback_memLp
    {f : ℝ → ℝ} (hf : MemLp f 1 (volume : Measure ℝ)) :
    MemLp (oneDimensionalPullback f) 1
      (volume : Measure (ℝ^1)) := by
  let e := (PiLp.equivOfUnique 2 ℝ
    (fun _ : Fin 1 ↦ ℝ)).symm
  have hmp : MeasurePreserving e.symm
      (volume : Measure (ℝ^1)) (volume : Measure ℝ) :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        ((MeasureTheory.volume_preserving_funUnique
          (Fin 1) ℝ).symm _))
  change
    MemLp
      (f ∘ (PiLp.equivOfUnique 2 ℝ
        (fun _ : Fin 1 ↦ ℝ)))
      1 (volume : Measure (ℝ^1))
  simpa [e] using hf.comp_measurePreserving hmp

/-- The base row of `w11Rows` is the pullback of the representative. -/
theorem w11Rows_base (f g : ℝ → ℝ) :
    w11Rows f g (baseIndex 1 1) = oneDimensionalPullback f := by
  simp [w11Rows]

/-- Both rows of `w11Rows` are integrable on the real line when the
representative and its derivative are. -/
theorem w11Rows_memLp
    (f g : ℝ → ℝ)
    (hf : MemLp f 1 (volume : Measure ℝ))
    (hg : MemLp g 1 (volume : Measure ℝ)) :
    ∀ a, MemLp (w11Rows f g a) 1
      (domainMeasure 1 Set.univ) := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    simp only [w11Rows, baseIndex_toList, ite_eq_left, domainMeasure,
      Measure.restrict_univ]
    exact oneDimensionalPullback_memLp hf
  · subst a
    simp only [w11Rows, singleDerivIndex_toList, List.cons_ne_nil, ite_false,
      domainMeasure,
      Measure.restrict_univ]
    exact oneDimensionalPullback_memLp hg

/-- Each row of `w11Rows` is the corresponding weak derivative of the pullback
of an absolutely continuous representative. -/
theorem w11Rows_hasWeakDerivative
    (f g : ℝ → ℝ)
    (hf : MemLp f 1 (volume : Measure ℝ))
    (hg : MemLp g 1 (volume : Measure ℝ))
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x ∂volume, HasDerivAt f (g x) x) :
    ∀ a, HasWeakDerivativeOn (n := 1) Set.univ a.toList
      (oneDimensionalPullback f) (w11Rows f g a) := by
  have htime : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn Set.univ f g :=
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
      (hf.locallyIntegrable (by norm_num))
      (hg.locallyIntegrable (by norm_num)) hAC hderiv
  have hfirst :
      HasWeakDerivativeOn (n := 1) Set.univ [0]
        (oneDimensionalPullback f)
        (oneDimensionalPullback g) := by
    have h := htime.to_hasWeakDerivativeOn (ContinuousLinearMap.id ℝ ℝ)
    change
      HasWeakDerivativeOn (n := 1) Set.univ [0]
        (fun x ↦
          f ((PiLp.equivOfUnique 2 ℝ
            (fun _ : Fin 1 ↦ ℝ)) x))
        (fun x ↦
          g ((PiLp.equivOfUnique 2 ℝ
            (fun _ : Fin 1 ↦ ℝ)) x))
    exact h
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hfLocal :
        LocallyIntegrableOn (oneDimensionalPullback f) Set.univ
          (volume : Measure (ℝ^1)) :=
      (oneDimensionalPullback_memLp hf).locallyIntegrable
        (by norm_num) |>.locallyIntegrableOn Set.univ
    have hnil :
        HasWeakDerivativeOn (n := 1) Set.univ []
          (oneDimensionalPullback f)
          (oneDimensionalPullback f) := by
      exact hasWeakDerivativeOn_nil hfLocal
    simpa [w11Rows] using hnil
  · subst a
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simpa [w11Rows] using hfirst

/-- Construct a global `W^{1,1}(ℝ)` graph-space element from an `L¹`
absolutely continuous representative and its `L¹` almost-everywhere
derivative. -/
noncomputable def mkW11OfAbsolutelyContinuous
    (f g : ℝ → ℝ)
    (hf : MemLp f 1 (volume : Measure ℝ))
    (hg : MemLp g 1 (volume : Measure ℝ))
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x ∂volume, HasDerivAt f (g x) x) :
    W^{1,1}(ℝ^1) :=
  mkWkpSpaceOnOfWeakDerivatives
    (n := 1) (k := 1) (p := (1 : ℝ≥0∞)) (Ω := Set.univ)
    (oneDimensionalPullback f) (w11Rows f g)
    (w11Rows_base f g) (w11Rows_memLp f g hf hg)
    (w11Rows_hasWeakDerivative f g hf hg hAC hderiv)

/-- The base coordinate of `mkW11OfAbsolutelyContinuous` is the Euclidean
pullback of the supplied representative. -/
theorem mkW11OfAbsolutelyContinuous_base_ae
    (f g : ℝ → ℝ)
    (hf : MemLp f 1 (volume : Measure ℝ))
    (hg : MemLp g 1 (volume : Measure ℝ))
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x ∂volume, HasDerivAt f (g x) x) :
    (((mkW11OfAbsolutelyContinuous f g hf hg hAC hderiv :
        WkpAmbientOn 1 1 1 Set.univ)
      (baseIndex 1 1) : DerivLp 1 1 Set.univ) : ℝ^1 → ℝ)
      =ᵐ[volume] oneDimensionalPullback f := by
  simpa [mkW11OfAbsolutelyContinuous, domainMeasure,
    w11Rows_base] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (oneDimensionalPullback f) (w11Rows f g)
      (w11Rows_base f g) (w11Rows_memLp f g hf hg)
      (w11Rows_hasWeakDerivative f g hf hg hAC hderiv)
      (baseIndex 1 1)

/-- The first derivative coordinate of
`mkW11OfAbsolutelyContinuous` is the Euclidean pullback of the supplied
almost-everywhere derivative. -/
theorem mkW11OfAbsolutelyContinuous_derivative_ae
    (f g : ℝ → ℝ)
    (hf : MemLp f 1 (volume : Measure ℝ))
    (hg : MemLp g 1 (volume : Measure ℝ))
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x ∂volume, HasDerivAt f (g x) x) :
    (((mkW11OfAbsolutelyContinuous f g hf hg hAC hderiv :
        WkpAmbientOn 1 1 1 Set.univ)
      (singleDerivIndex 1 0) :
      DerivLp 1 1 Set.univ) : ℝ^1 → ℝ)
      =ᵐ[volume] oneDimensionalPullback g := by
  simpa [mkW11OfAbsolutelyContinuous, domainMeasure, w11Rows] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (oneDimensionalPullback f) (w11Rows f g)
      (w11Rows_base f g) (w11Rows_memLp f g hf hg)
      (w11Rows_hasWeakDerivative f g hf hg hAC hderiv)
      (singleDerivIndex 1 0)

end SobolevSpace.GraphSpace
