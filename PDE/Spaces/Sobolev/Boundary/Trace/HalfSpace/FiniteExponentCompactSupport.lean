/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.CompactSupport
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentCompletion
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponent

/-!
# Finite-exponent traces of compactly supported C1 functions

Boundary charts of a `C1` domain turn smooth functions into compactly
supported `C1` functions, not smooth ones. We extend the
finite-exponent flat trace agreement theorem to that natural chartwise core:
for every real `p ≥ 1` and every compactly supported `C1` function `f` on
`ℝ^(n+1)`, the completed trace `traceLp n p` of the `W^{1,p}` element carried
by `f` on the upper half-space is the literal boundary restriction
`y ↦ f (y, 0)`, as an element of `Lᵖ(ℝ^n)`.

The argument mirrors `Trace.HalfSpace.CompactSupport` (the `p = 2` case): the
compactly supported `C1` functions embed in `W^{1,p}` through their
classical derivatives, they contain the smooth global test functions and hence
have dense image, the finite-exponent flat estimate
`‖f(·,0)‖_{Lᵖ} ≤ p^{1/p} ‖f‖_{W^{1,p}}` holds on this core, and the resulting
completion is identified with the canonical trace from
`Trace.HalfSpace.FiniteExponentCompletion`.

## Main results

* `toUpperW1p`, `toUpperW1pLinear`: the embedding of compactly supported `C1`
  functions into `W^{1,p}` of the upper half-space, with `toUpperW1p_coordinate_ae`
  identifying the coordinates with the classical derivatives.
* `denseRange_toUpperW1pLinear`: this embedding has dense range.
* `boundaryLpLinear`, `boundaryLpLinear_apply_ae`: literal boundary restriction in
  tangential coordinates as an `Lᵖ(ℝ^n)` element.
* `traceLp_c1`: the completed finite-exponent flat trace agrees with literal boundary
  restriction on compactly supported `C1` functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, step 1 of the proof, (1), p. 272. Evans
  proves the flat estimate with an unspecified constant by Young's inequality; we track the constant
  `p^{1/p}` through the same step for `p > 1`, and for `p = 1` integrate directly.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.HalfSpace.CompactSupport

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ}

/-- A compactly supported `C1` function as an upper-half-space
`W^{1,p}` function. -/
noncomputable def toUpperW1p (p : ℝ)
    (f : c1CompactSubmodule n) :
    W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) :=
  GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := HalfSpace.upper (n + 1))
    (f := (f : ℝ^(n + 1) → ℝ)) (contDiff f)
    (derivative_memLp_at (ENNReal.ofReal p) f)

/-- Coordinates of `toUpperW1p` are the corresponding classical
derivatives almost everywhere. -/
theorem toUpperW1p_coordinate_ae (p : ℝ)
    (f : c1CompactSubmodule n)
    (a : GraphSpace.DerivIndex (n + 1) 1) :
    ((((toUpperW1p p f :
        GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
          (HalfSpace.upper (n + 1))) a :
        GraphSpace.DerivLp (n + 1) (ENNReal.ofReal p)
          (HalfSpace.upper (n + 1))) : ℝ^(n + 1) → ℝ)) =ᵐ[
      domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      fun x ↦ iteratedPartialDeriv (n := n + 1) a.toList
        (f : ℝ^(n + 1) → ℝ) x :=
  GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := HalfSpace.upper (n + 1))
    (f := (f : ℝ^(n + 1) → ℝ)) (contDiff f)
    (derivative_memLp_at (ENNReal.ofReal p) f) a

/-- The compact-`C¹` Sobolev embedding is additive. -/
theorem toUpperW1p_add (p : ℝ)
    (f g : c1CompactSubmodule n) :
    toUpperW1p p (f + g) = toUpperW1p p f + toUpperW1p p g := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  have hcoord :
      (((toUpperW1p p f + toUpperW1p p g :
          W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a) =
        (toUpperW1p p f :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a +
        (toUpperW1p p g :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a := by
    rfl
  rw [hcoord]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [toUpperW1p_coordinate_ae p (f + g) a,
      toUpperW1p_coordinate_ae p f a,
      toUpperW1p_coordinate_ae p g a,
      MeasureTheory.Lp.coeFn_add
        ((toUpperW1p p f :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a)
        ((toUpperW1p p g :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a)] with x hadd hf hg hsum
  rw [hadd, hsum]
  simp only [Pi.add_apply]
  rw [hf, hg]
  have hlen : a.toList.length ≤ 1 := a.toList_length_le
  exact congrFun
    (PDE.iteratedPartialDeriv_add_of_contDiff a.toList
      ((contDiff f).of_le (by exact_mod_cast hlen))
      ((contDiff g).of_le (by exact_mod_cast hlen))) x

/-- The compact-`C¹` Sobolev embedding commutes with scalar multiplication. -/
theorem toUpperW1p_smul (p : ℝ)
    (c : ℝ)
    (f : c1CompactSubmodule n) :
    toUpperW1p p (c • f) = c • toUpperW1p p f := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  have hcoord :
      (((c • toUpperW1p p f :
          W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a) =
        c • (toUpperW1p p f :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a := by
    rfl
  rw [hcoord]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [toUpperW1p_coordinate_ae p (c • f) a,
      toUpperW1p_coordinate_ae p f a,
      MeasureTheory.Lp.coeFn_smul
        (p := ENNReal.ofReal p) (c := c)
        ((toUpperW1p p f :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a)] with x hsmul hf hcoord
  rw [hsmul, hcoord]
  simp only [Pi.smul_apply]
  rw [hf]
  exact congrFun
    (PDE.iteratedPartialDeriv_const_smul
      (n := n + 1) c a.toList (f : ℝ^(n + 1) → ℝ)) x

/-- The finite-exponent compact-`C1` Sobolev embedding is linear. -/
noncomputable def toUpperW1pLinear (p : ℝ) :
    c1CompactSubmodule n →ₗ[ℝ]
      W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) where
  toFun := toUpperW1p p
  map_add' := toUpperW1p_add p
  map_smul' := toUpperW1p_smul p

/-- On smooth global test functions, the compact-`C1` embedding agrees with
the standard finite-exponent test embedding. -/
theorem toUpperW1p_ofGlobalTestFunction (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (φ : Trace.HalfSpace.GlobalTestFunction n) :
    toUpperW1p p (ofGlobalTestFunction φ) =
      Trace.HalfSpace.globalTestFunctionToUpperW1pLinear n p φ := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  apply MeasureTheory.Lp.ext
  have hc1 := toUpperW1p_coordinate_ae p (ofGlobalTestFunction φ) a
  rw [Trace.HalfSpace.globalTestFunctionToUpperW1pLinear_eq_mk]
  have hsmooth := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := HalfSpace.upper (n + 1)) (f := φ.1.toFun)
    φ.1.contDiff φ.1.hasCompactSupport a
  exact hc1.trans hsmooth.symm

/-- Compactly supported `C1` functions have dense image in upper-half-space
`W^{1,p}`, because they contain the smooth core. -/
theorem denseRange_toUpperW1pLinear (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    DenseRange (toUpperW1pLinear (n := n) p) := by
  apply
    (Trace.HalfSpace.denseRange_globalTestFunctionToUpperW1pLinear n p).mono
  rintro u ⟨φ, rfl⟩
  exact ⟨ofGlobalTestFunction φ, toUpperW1p_ofGlobalTestFunction p φ⟩

/-- Literal boundary restriction of a compactly supported `C¹` function in
tangential `L^p` coordinates. -/
noncomputable def boundaryLpLinear (p : ℝ) :
    c1CompactSubmodule n →ₗ[ℝ]
      MeasureTheory.Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^n)) where
  toFun f := (boundaryValue_memLp_at (ENNReal.ofReal p) f).toLp
    (Trace.HalfSpace.smoothBoundaryValue (f : ℝ^(n + 1) → ℝ))
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by
      simp [Trace.HalfSpace.smoothBoundaryValue,
        Trace.HalfSpace.normalSlice]
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by
      simp [Trace.HalfSpace.smoothBoundaryValue,
        Trace.HalfSpace.normalSlice]

/-- Almost-everywhere formula for finite-exponent compact-`C¹` boundary
restriction. -/
theorem boundaryLpLinear_apply_ae (p : ℝ) (f : c1CompactSubmodule n) :
    (boundaryLpLinear p f : ℝ^n → ℝ) =ᵐ[(volume : Measure (ℝ^n))]
      Trace.HalfSpace.smoothBoundaryValue (f : ℝ^(n + 1) → ℝ) :=
  (boundaryValue_memLp_at (ENNReal.ofReal p) f).coeFn_toLp

private theorem coordinate_norm_rpow_eq_integral
    (p : ℝ) (hp : 1 ≤ p)
    (f : c1CompactSubmodule n)
    (a : GraphSpace.DerivIndex (n + 1) 1) :
    ‖((toUpperW1p p f :
        GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
          (HalfSpace.upper (n + 1))) a)‖ ^ p =
      ∫ x in HalfSpace.upper (n + 1),
        |iteratedPartialDeriv (n := n + 1) a.toList
          (f : ℝ^(n + 1) → ℝ) x| ^ p := by
  let v :=
    ((toUpperW1p p f :
      GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
        (HalfSpace.upper (n + 1))) a)
  have hv :
      (v : ℝ^(n + 1) → ℝ) =ᵐ[
        domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
        fun x ↦ iteratedPartialDeriv (n := n + 1) a.toList
          (f : ℝ^(n + 1) → ℝ) x := by
    simpa [v] using toUpperW1p_coordinate_ae p f a
  have hpow :=
    MeasureTheory.norm_toLp_rpow_eq_integral_abs
      (zero_lt_one.trans_le hp) (MeasureTheory.Lp.memLp v)
  rw [MeasureTheory.Lp.toLp_coeFn] at hpow
  calc
    ‖((toUpperW1p p f :
        GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
          (HalfSpace.upper (n + 1))) a)‖ ^ p =
        ∫ x, |v x| ^ p
          ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := hpow
    _ = ∫ x,
        |iteratedPartialDeriv (n := n + 1) a.toList
          (f : ℝ^(n + 1) → ℝ) x| ^ p
          ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = ∫ x in HalfSpace.upper (n + 1),
        |iteratedPartialDeriv (n := n + 1) a.toList
          (f : ℝ^(n + 1) → ℝ) x| ^ p := rfl

private theorem boundary_norm_rpow_eq_integral
    (p : ℝ) (hp : 1 ≤ p) (f : c1CompactSubmodule n) :
    ‖boundaryLpLinear p f‖ ^ p =
      ∫ y : ℝ^n,
        |Trace.HalfSpace.smoothBoundaryValue
          (f : ℝ^(n + 1) → ℝ) y| ^ p := by
  simpa [boundaryLpLinear] using
    MeasureTheory.norm_toLp_rpow_eq_integral_abs
      (zero_lt_one.trans_le hp) (boundaryValue_memLp_at (ENNReal.ofReal p) f)

/-- Finite-exponent Evans trace estimate for compactly supported `C1`
functions. -/
private theorem norm_boundaryLpLinear_le (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (f : c1CompactSubmodule n) :
    ‖boundaryLpLinear p f‖ ≤
      p ^ (1 / p) * ‖toUpperW1p p f‖ := by
  let U := (toUpperW1p p f :
    GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
      (HalfSpace.upper (n + 1)))
  let b := GraphSpace.baseIndex (n + 1) 1
  let d := GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)
  have htrace :=
    Trace.HalfSpace.smooth_boundary_integral_abs_rpow_le_upper_energy
      (n := n) (contDiff f) (hasCompactSupport f) hp
  have hbase :
      ‖U b‖ ^ p =
        ∫ x in HalfSpace.upper (n + 1),
          |(f : ℝ^(n + 1) → ℝ) x| ^ p := by
    simpa [b, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      coordinate_norm_rpow_eq_integral p hp f b
  have hnormal :
      ‖U d‖ ^ p =
        ∫ x in HalfSpace.upper (n + 1),
          |(∂[Fin.last n]
            (f : ℝ^(n + 1) → ℝ)) x| ^ p := by
    simpa [d, GraphSpace.singleDerivIndex_toList,
      iteratedPartialDeriv] using
      coordinate_norm_rpow_eq_integral p hp f d
  have hpow :
      ‖boundaryLpLinear p f‖ ^ p ≤
        (p - 1) * ‖U b‖ ^ p + ‖U d‖ ^ p := by
    calc
      _ = ∫ y : ℝ^n,
          |Trace.HalfSpace.smoothBoundaryValue
            (f : ℝ^(n + 1) → ℝ) y| ^ p :=
        boundary_norm_rpow_eq_integral p hp f
      _ ≤ (p - 1) *
          (∫ x in HalfSpace.upper (n + 1),
            |(f : ℝ^(n + 1) → ℝ) x| ^ p) +
          (∫ x in HalfSpace.upper (n + 1),
            |(∂[Fin.last n]
              (f : ℝ^(n + 1) → ℝ)) x| ^ p) := htrace
      _ = (p - 1) * ‖U b‖ ^ p + ‖U d‖ ^ p := by
        rw [← hbase, ← hnormal]
  have hb : ‖U b‖ ^ p ≤ ‖U‖ ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) (PiLp.norm_apply_le U b)
      (le_of_lt (zero_lt_one.trans_le hp))
  have hd : ‖U d‖ ^ p ≤ ‖U‖ ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) (PiLp.norm_apply_le U d)
      (le_of_lt (zero_lt_one.trans_le hp))
  have hpow' : ‖boundaryLpLinear p f‖ ^ p ≤ p * ‖U‖ ^ p := by
    calc
      _ ≤ (p - 1) * ‖U b‖ ^ p + ‖U d‖ ^ p := hpow
      _ ≤ (p - 1) * ‖U‖ ^ p + ‖U‖ ^ p := by
        gcongr
      _ = p * ‖U‖ ^ p := by ring
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hconst : 0 ≤ p ^ (1 / p) := Real.rpow_nonneg hp0.le _
  apply (Real.rpow_le_rpow_iff
    (norm_nonneg _)
    (mul_nonneg hconst (norm_nonneg _)) hp0).mp
  rw [Real.mul_rpow hconst (norm_nonneg _)]
  have hppow : (p ^ (1 / p)) ^ p = p := by
    rw [← Real.rpow_mul hp0.le]
    field_simp
    exact Real.rpow_one p
  rw [hppow]
  exact hpow'

/-- Auxiliary completion from the compactly supported `C¹` core. -/
private noncomputable def traceLpFromCompactC1 (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) →L[ℝ]
      MeasureTheory.Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^n)) :=
  (boundaryLpLinear p).extendOfNorm (toUpperW1pLinear p)

private theorem boundaryLpLinear_ofGlobalTestFunction
    (p : ℝ) (φ : Trace.HalfSpace.GlobalTestFunction n) :
    boundaryLpLinear p (ofGlobalTestFunction φ) =
      Trace.HalfSpace.globalTestFunctionBoundaryLpLinear n p φ := by
  apply MeasureTheory.Lp.ext
  have hmem :
      MemLp (Trace.HalfSpace.smoothBoundaryValue φ.1.toFun)
        (ENNReal.ofReal p) (volume : Measure (ℝ^n)) :=
    (Trace.HalfSpace.smoothBoundaryValue_continuous
      (n := n) φ.1.contDiff.continuous).memLp_of_hasCompactSupport
      (Trace.HalfSpace.smoothBoundaryValue_hasCompactSupport
        (n := n) φ.1.hasCompactSupport)
  exact (boundaryLpLinear_apply_ae p (ofGlobalTestFunction φ)).trans
    (by
      simpa [ofGlobalTestFunction,
        Trace.HalfSpace.globalTestFunctionBoundaryLpLinear] using
        hmem.coeFn_toLp.symm)

/-- The auxiliary compact-C¹ completion is the canonical finite-exponent trace. -/
private theorem traceLpFromCompactC1_eq_traceLp (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p) :
    traceLpFromCompactC1 (n := n) p = Trace.HalfSpace.traceLp n p hp := by
  have hcomp :
      (traceLpFromCompactC1 (n := n) p :
        W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) →
          MeasureTheory.Lp ℝ (ENNReal.ofReal p)
            (volume : Measure (ℝ^n))) ∘
        Trace.HalfSpace.globalTestFunctionToUpperW1pLinear n p =
      (Trace.HalfSpace.traceLp n p hp :
        W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) →
          MeasureTheory.Lp ℝ (ENNReal.ofReal p)
            (volume : Measure (ℝ^n))) ∘
        Trace.HalfSpace.globalTestFunctionToUpperW1pLinear n p := by
    funext φ
    change traceLpFromCompactC1 (n := n) p
        (Trace.HalfSpace.globalTestFunctionToUpperW1pLinear n p φ) =
      Trace.HalfSpace.traceLp n p hp
        (Trace.HalfSpace.globalTestFunctionToUpperW1pLinear n p φ)
    calc
      _ = traceLpFromCompactC1 (n := n) p
          (toUpperW1p p (ofGlobalTestFunction φ)) := by
        rw [toUpperW1p_ofGlobalTestFunction]
      _ = boundaryLpLinear p (ofGlobalTestFunction φ) := by
        exact LinearMap.extendOfNorm_eq
          (denseRange_toUpperW1pLinear (n := n) p)
          ⟨p ^ (1 / p), fun f ↦ by
            simpa [toUpperW1pLinear] using
              norm_boundaryLpLinear_le p hp f⟩
          (ofGlobalTestFunction φ)
      _ = Trace.HalfSpace.globalTestFunctionBoundaryLpLinear n p φ :=
        boundaryLpLinear_ofGlobalTestFunction p φ
      _ = Trace.HalfSpace.traceLp n p hp
          (Trace.HalfSpace.globalTestFunctionToUpperW1pLinear n p φ) :=
        (Trace.HalfSpace.traceLp_smooth n p hp φ).symm
  have hfun :=
    (Trace.HalfSpace.denseRange_globalTestFunctionToUpperW1pLinear n p).equalizer
      (traceLpFromCompactC1 (n := n) p).continuous
      (Trace.HalfSpace.traceLp n p hp).continuous hcomp
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- The completed finite-exponent flat trace agrees with literal boundary
restriction for every compactly supported `C1` function. -/
theorem traceLp_c1 (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 ≤ p) (f : c1CompactSubmodule n) :
    Trace.HalfSpace.traceLp n p hp (toUpperW1p p f) =
      boundaryLpLinear p f := by
  rw [← traceLpFromCompactC1_eq_traceLp p hp]
  exact LinearMap.extendOfNorm_eq
    (denseRange_toUpperW1pLinear (n := n) p)
    ⟨p ^ (1 / p), fun g ↦ by
      simpa [toUpperW1pLinear] using
        norm_boundaryLpLinear_le p hp g⟩ f

end Trace.HalfSpace.CompactSupport
end SobolevSpace
