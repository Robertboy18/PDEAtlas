/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.OneDimensionalCritical
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import PDE.Spaces.Sobolev.Calculus.Slicing.FundamentalTheorem

/-!
# Absolutely continuous representatives on the line

Every global `W^{1,1}(ℝ)` graph-space element has a selected bounded
continuous representative. We prove that the selected representative
is absolutely continuous on every compact interval and that its classical
derivative agrees almost everywhere with the stored weak-derivative
coordinate.

The proof combines the weak fundamental theorem of calculus with Mathlib's absolute continuity of
indefinite integrals, `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`, and
its Lebesgue differentiation theorem, `LocallyIntegrable.ae_hasDerivAt_integral`.

Classically, a `W^{1,1}` function on an interval has a continuous representative `ū` with
`ū(b) - ū(a) = ∫_a^b u'`, hence absolutely continuous, hence differentiable almost everywhere with
derivative `u'` (Brezis, *Functional Analysis, Sobolev Spaces and PDE*, Chapter 8). The
representative used here is the bounded continuous one supplied by the critical one-dimensional
Morrey endpoint.

## Main results

* `representative`, `weakDerivativeRepresentative`: the continuous
  representative and the stored weak derivative, in the real coordinate.
* `intervalIntegral_weakDerivativeRepresentative_eq_sub`: the fundamental
  theorem `∫_a^b u' = ū(b) - ū(a)`.
* `absolutelyContinuousOnInterval_representative`: `ū` is absolutely
  continuous on every compact interval.
* `ae_hasDerivAt_representative`: `ū' = u'` almost everywhere.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for the absolutely continuous representative of a `W^{1,p}` function on
  an interval and the identity `ū(b) - ū(a) = ∫_a^b u'`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, p. 259, which states that on an interval
  `u ∈ W^{1,p}` exactly when `u` agrees a.e. with an absolutely continuous function whose derivative
  lies in `L^p`, and leaves the proof to the exercises.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory PDE.Common Set
open scoped ENNReal Topology Sobolev

namespace AbsolutelyContinuousRepresentative

/-- The selected continuous representative of a global `W^{1,1}(ℝ)` class,
written in the standard real coordinate. -/
def representative (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦
    CriticalOneDimensional.boundedContinuousRepresentative U
      ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)

/-- The stored first weak derivative, written in the standard real
coordinate. -/
def weakDerivativeRepresentative
    (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦
    (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
      (GraphSpace.singleDerivIndex 1 0) :
      GraphSpace.DerivLp 1 1 Set.univ) :
      ℝ^1 → ℝ) ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)

/-- The selected representative belongs to `L¹(ℝ)`. -/
theorem representative_memLp
    (U : W^{1,1}(ℝ^1)) :
    MemLp (representative U) 1 (volume : Measure ℝ) := by
  have hbase :
      MemLp
        (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.baseIndex 1 1) :
          GraphSpace.DerivLp 1 1 Set.univ) : ℝ^1 → ℝ)
        1 (volume : Measure (ℝ^1)) := by
    simpa [domainMeasure] using
      (MeasureTheory.Lp.memLp
        ((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.baseIndex 1 1)))
  have hcontinuous :
      MemLp
        (fun x ↦
          CriticalOneDimensional.boundedContinuousRepresentative U x)
        1 (volume : Measure (ℝ^1)) :=
    (memLp_congr_ae
      (CriticalOneDimensional.boundedContinuousRepresentative_ae U)).2
      hbase
  change
    MemLp
      (fun t ↦
        CriticalOneDimensional.boundedContinuousRepresentative U
          ((PiLp.equivOfUnique 2 ℝ
            (fun _ : Fin 1 ↦ ℝ)).symm t))
      1 (volume : Measure ℝ)
  exact hcontinuous.comp_measurePreserving
    ((PiLp.volume_preserving_toLp (Fin 1)).comp
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))

/-- The real-coordinate weak derivative belongs to `L¹(ℝ)`. -/
theorem weakDerivativeRepresentative_memLp
    (U : W^{1,1}(ℝ^1)) :
    MemLp (weakDerivativeRepresentative U) 1
      (volume : Measure ℝ) := by
  have hU :
      MemLp
        (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.singleDerivIndex 1 0) :
          GraphSpace.DerivLp 1 1 Set.univ) :
          ℝ^1 → ℝ)
        1 (volume : Measure (ℝ^1)) := by
    simpa [domainMeasure] using
      (MeasureTheory.Lp.memLp
        ((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.singleDerivIndex 1 0)))
  change
    MemLp
      (fun t ↦
        (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.singleDerivIndex 1 0) :
          GraphSpace.DerivLp 1 1 Set.univ) :
          ℝ^1 → ℝ)
          ((PiLp.equivOfUnique 2 ℝ
            (fun _ : Fin 1 ↦ ℝ)).symm t))
      1 (volume : Measure ℝ)
  exact hU.comp_measurePreserving
    ((PiLp.volume_preserving_toLp (Fin 1)).comp
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))

private theorem hasWeakDerivativeOn_representative
    (U : W^{1,1}(ℝ^1)) :
    HasWeakDerivativeOn (n := 1) Set.univ [0]
      (fun x ↦
        CriticalOneDimensional.boundedContinuousRepresentative U x)
      (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
        (GraphSpace.singleDerivIndex 1 0) :
        GraphSpace.DerivLp 1 1 Set.univ) :
        ℝ^1 → ℝ) := by
  have hbase :
      GraphSpace.baseRepresentative U =ᵐ[
          domainMeasure 1 (Set.univ : Set (ℝ^1))]
        fun x ↦
          CriticalOneDimensional.boundedContinuousRepresentative U x := by
    simpa [domainMeasure] using
      (CriticalOneDimensional.boundedContinuousRepresentative_ae U).symm
  have hproperty :
      HasWeakDerivativeOn (n := 1) Set.univ [0]
        (GraphSpace.baseRepresentative U)
        (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.singleDerivIndex 1 0) :
          GraphSpace.DerivLp 1 1 Set.univ) :
          ℝ^1 → ℝ) := by
    simpa [GraphSpace.singleDerivIndex_toList,
      GraphSpace.baseRepresentative] using
      (U.property (GraphSpace.singleDerivIndex 1 0))
  exact
    (hasWeakDerivativeOn_congr_ae
      (n := 1) (Ω := Set.univ) (α := ([0] : List (Fin 1)))
      hbase (MeasureTheory.ae_eq_refl _)).mp hproperty

/-- The selected representative satisfies the literal weak fundamental
theorem of calculus. -/
theorem intervalIntegral_weakDerivativeRepresentative_eq_sub
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    (∫ t in a..b, weakDerivativeRepresentative U t) =
      representative U b - representative U a := by
  exact FundamentalTheorem.intervalIntegral_weakDerivative_eq_sub
    (fun x ↦
      CriticalOneDimensional.boundedContinuousRepresentative U x)
    (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
      (GraphSpace.singleDerivIndex 1 0) :
      GraphSpace.DerivLp 1 1 Set.univ) :
      ℝ^1 → ℝ)
    (CriticalOneDimensional.boundedContinuousRepresentative U).continuous
    (by
      simpa [domainMeasure] using
        (MeasureTheory.Lp.memLp
          ((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
            (GraphSpace.singleDerivIndex 1 0))))
    (hasWeakDerivativeOn_representative U)
    a b

/-- The selected representative is absolutely continuous on every compact
interval. -/
theorem absolutelyContinuousOnInterval_representative
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (representative U) a b := by
  have hG :
      Integrable (weakDerivativeRepresentative U)
        (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mp
      (weakDerivativeRepresentative_memLp U)
  have hprimitive :
      AbsolutelyContinuousOnInterval
        (fun x ↦ ∫ t in a..x, weakDerivativeRepresentative U t)
        a b :=
    hG.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      Set.left_mem_uIcc
  have hconst :
      AbsolutelyContinuousOnInterval
        (fun _ : ℝ ↦ representative U a) a b :=
    (LipschitzWith.const (representative U a)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  apply (hconst.add hprimitive).congr
  intro x _hx
  change representative U a +
      (∫ t in a..x, weakDerivativeRepresentative U t) =
    representative U x
  rw [intervalIntegral_weakDerivativeRepresentative_eq_sub]
  ring

/-- The derivative of the selected representative agrees almost everywhere
with the stored weak derivative. -/
theorem ae_hasDerivAt_representative
    (U : W^{1,1}(ℝ^1)) :
    ∀ᵐ x ∂volume,
      HasDerivAt (representative U)
        (weakDerivativeRepresentative U x) x := by
  have hG :
      Integrable (weakDerivativeRepresentative U)
        (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mp
      (weakDerivativeRepresentative_memLp U)
  filter_upwards
    [LocallyIntegrable.ae_hasDerivAt_integral hG.locallyIntegrable] with x hx
  have hprimitive :=
    (hx 0).const_add (representative U 0)
  apply hprimitive.congr_of_eventuallyEq
  filter_upwards with y
  change representative U y =
    representative U 0 +
      (∫ t in 0..y, weakDerivativeRepresentative U t)
  rw [intervalIntegral_weakDerivativeRepresentative_eq_sub]
  ring

end AbsolutelyContinuousRepresentative

end SobolevSpace
