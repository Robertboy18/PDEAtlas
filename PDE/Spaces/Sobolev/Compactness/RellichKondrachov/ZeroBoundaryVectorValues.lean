/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Operator.CompactConvergence
public import PDE.Spaces.Sobolev.Compactness.Rellich.VectorValues
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.ZeroBoundaryFiniteExponent

/-!
# Compactness of the values of zero-boundary Sobolev systems

## Motivation

A sequence of vector fields `g + w_j` has a fixed boundary datum `g` and corrections `w_j` that
converge weakly in the product of the zero-boundary spaces `W₀^{1,p}`. Do the fields converge
weakly in the product of the full spaces, and do their values converge strongly in `Lᵖ`, on a
bounded set whose boundary has no regularity?

## The idea

Both hold. The inclusion of the product of the zero-boundary spaces is linear and continuous,
so it preserves weak convergence, and adding `g` does too. For the values, the Euclidean value
of a system is assembled from the scalar values, each scalar inclusion `W₀^{1,p}(Ω) → Lᵖ(Ω)` is
compact on a bounded measurable set, a finite product of compact maps is compact, and a compact
map sends weakly convergent sequences to strongly convergent ones.

## Main results

All are for every number of components, every dimension, every finite exponent `p ≥ 1` and
every bounded measurable set.

* `vectorWkpValueCLM_comp_vectorWkp0SubtypeL_isCompactOperator`: the value map restricted to
  the product of the zero-boundary spaces is compact.
* `tendsto_weak_add_vectorWkp0SubtypeL` (all sets and exponents): weak convergence of the
  corrections gives weak convergence of the fields.
* `tendsto_vectorWkpValueCLM_add_vectorWkp0SubtypeL`: weak convergence of the corrections gives
  strong `Lᵖ` convergence of the values of the fields.

## Relations

* The compactness is `wkp0BaseCoordinate_isCompactOperator_of_bounded` in each component,
  joined by `ContinuousLinearMap.isCompactOperator_pi` and
  `Rellich.vectorWkpValueCLM_eq_euclideanTuple`.
* `Rellich.vectorWkpValueCLM_isCompactOperator_of_c1Domain` is the compactness on the full
  space, for `p = 2` and a domain with a C¹ extension atlas.
* `PDE.CalculusOfVariations.exists_minimizer_vectorWkpLIntegral_prescribed_boundary` uses the
  two convergence statements.

## What stays open

Nothing for this statement; the full space without boundary regularity is not compact in `Lᵖ`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.RellichKondrachov

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inclusion of a finite product of zero-boundary Sobolev spaces into the product of the
full spaces. -/
def vectorWkp0SubtypeL : (Fin m → W₀^{1,p}(Ω)) →L[ℝ] (Fin m → W^{1,p}(Ω)) :=
  ContinuousLinearMap.pi fun i ↦
    (Submodule.subtypeL (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule).comp
      (ContinuousLinearMap.proj i)

/-- The inclusion acts on each component as the coercion. -/
@[simp]
theorem vectorWkp0SubtypeL_apply (w : Fin m → W₀^{1,p}(Ω)) (i : Fin m) :
    vectorWkp0SubtypeL w i = (w i : W^{1,p}(Ω)) :=
  rfl

/-- On a bounded measurable set and for a finite exponent, the Euclidean value map of a system
is compact on the product of the zero-boundary spaces. No boundary regularity is assumed. -/
theorem vectorWkpValueCLM_comp_vectorWkp0SubtypeL_isCompactOperator
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (hp : p ≠ ∞) :
    IsCompactOperator
      ((vectorWkpValueCLM (m := m) (p := p) (Ω := Ω)).comp vectorWkp0SubtypeL) := by
  let W₀ := W^{1,p}(Ω)
  let V₀ := W₀^{1,p}(Ω)
  let _ : NormedAddCommGroup W₀ := Submodule.normedAddCommGroup (wkpSubmoduleOn n 1 p Ω)
  let _ : NormedSpace ℝ W₀ := Submodule.normedSpace (wkpSubmoduleOn n 1 p Ω)
  let _ : NormedAddCommGroup V₀ := Submodule.normedAddCommGroup
    (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule
  let _ : NormedSpace ℝ V₀ := Submodule.normedSpace
    (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule
  have hpi := ContinuousLinearMap.isCompactOperator_pi (𝕜 := ℝ)
    (E := Fin m → V₀) (F := fun _ : Fin m ↦ Lp ℝ p (domainMeasure n Ω))
    (fun i : Fin m ↦
      ((wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)).comp
        (Submodule.subtypeL (wkp0SubmoduleOn (n := n) (k := 1) (p := p)
          (Ω := Ω)).toSubmodule)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ↦ V₀) i))
    fun i ↦ (wkp0BaseCoordinate_isCompactOperator_of_bounded hΩ hbounded hp).comp_clm _
  have heq : (vectorWkpValueCLM (m := m) (p := p) (Ω := Ω)).comp vectorWkp0SubtypeL =
      Lp.euclideanTuple.comp (ContinuousLinearMap.pi fun i : Fin m ↦
        ((wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)).comp
          (Submodule.subtypeL (wkp0SubmoduleOn (n := n) (k := 1) (p := p)
            (Ω := Ω)).toSubmodule)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ↦ V₀) i)) := by
    rw [Rellich.vectorWkpValueCLM_eq_euclideanTuple]
    rfl
  rw [heq]
  exact hpi.clm_comp Lp.euclideanTuple

/-- Weak convergence of zero-boundary corrections gives weak convergence of the fields with a
fixed boundary datum, in the product of the full Sobolev spaces. -/
theorem tendsto_weak_add_vectorWkp0SubtypeL (g : Fin m → W^{1,p}(Ω)) {ι : Type*}
    {l : Filter ι} {w : ι → Fin m → W₀^{1,p}(Ω)} {wLimit : Fin m → W₀^{1,p}(Ω)}
    (hw : Tendsto (fun j ↦ toWeakSpace ℝ (Fin m → W₀^{1,p}(Ω)) (w j)) l
      (𝓝 (toWeakSpace ℝ (Fin m → W₀^{1,p}(Ω)) wLimit))) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) (g + vectorWkp0SubtypeL (w j))) l
      (𝓝 (toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) (g + vectorWkp0SubtypeL wLimit))) := by
  have hweak : Tendsto
      (fun j ↦ toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) (vectorWkp0SubtypeL (w j))) l
      (𝓝 (toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) (vectorWkp0SubtypeL wLimit))) :=
    (WeakSpace.map vectorWkp0SubtypeL).continuous.continuousAt.tendsto.comp hw
  simpa only [map_add] using
    (tendsto_const_nhds.add hweak : Tendsto
      (fun j ↦ toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) g +
        toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) (vectorWkp0SubtypeL (w j))) l
      (𝓝 (toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) g +
        toWeakSpace ℝ (Fin m → W^{1,p}(Ω)) (vectorWkp0SubtypeL wLimit))))

/-- On a bounded measurable set and for a finite exponent, weak convergence of zero-boundary
corrections gives strong `Lᵖ` convergence of the values of the fields with a fixed boundary
datum. -/
theorem tendsto_vectorWkpValueCLM_add_vectorWkp0SubtypeL
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (hp : p ≠ ∞)
    (g : Fin m → W^{1,p}(Ω)) {w : ℕ → Fin m → W₀^{1,p}(Ω)} {wLimit : Fin m → W₀^{1,p}(Ω)}
    (hw : Tendsto (fun j ↦ toWeakSpace ℝ (Fin m → W₀^{1,p}(Ω)) (w j)) atTop
      (𝓝 (toWeakSpace ℝ (Fin m → W₀^{1,p}(Ω)) wLimit))) :
    Tendsto (fun j ↦ vectorWkpValueCLM (g + vectorWkp0SubtypeL (w j))) atTop
      (𝓝 (vectorWkpValueCLM (g + vectorWkp0SubtypeL wLimit))) := by
  let W₀ := W^{1,p}(Ω)
  let V₀ := W₀^{1,p}(Ω)
  let _ : NormedAddCommGroup W₀ := Submodule.normedAddCommGroup (wkpSubmoduleOn n 1 p Ω)
  let _ : NormedSpace ℝ W₀ := Submodule.normedSpace (wkpSubmoduleOn n 1 p Ω)
  let _ : NormedAddCommGroup V₀ := Submodule.normedAddCommGroup
    (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule
  let _ : NormedSpace ℝ V₀ := Submodule.normedSpace
    (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule
  have h := PDE.Analysis.tendsto_compactOperator_of_tendsto_weak (X := Fin m → V₀) _
    (vectorWkpValueCLM_comp_vectorWkp0SubtypeL_isCompactOperator (m := m) hΩ hbounded hp) hw
  simpa only [map_add, ContinuousLinearMap.comp_apply] using
    (tendsto_const_nhds (x := vectorWkpValueCLM g)).add h

end SobolevSpace.GraphSpace.RellichKondrachov
