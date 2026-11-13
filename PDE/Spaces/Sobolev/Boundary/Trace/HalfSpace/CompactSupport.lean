/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.SurfaceMeasure
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Flat traces of compactly supported C¹ functions

A `C¹` change of variables does not preserve `C∞`, so the test-function
agreement theorem for the flat trace is not by itself sufficient for boundary
charts. We prove the finite-regularity extension: the flat
trace agrees with literal boundary restriction for every compactly supported
`C¹` function. The proof uses the same Evans estimate and identifies the
resulting completion with the trace from smooth test
functions.

## Main results

* `c1CompactSubmodule`, `toUpperH1Linear`: compactly supported `C¹` functions on `ℝ^(n+1)`
  and their linear embedding into `H¹` of the upper half-space via classical derivatives.
* `denseRange_toUpperH1Linear`: this embedding has dense range, since it extends the smooth
  test-function core.
* `trace_c1`: the flat trace of `toUpperH1 f` is the literal boundary restriction of `f`.
* `flatTrace_c1`, `flatTrace_c1_apply_ae`: the same statement for the intrinsic trace with
  values in `L²` of the flat surface measure, including the a.e. representative form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, step 1 of the proof, (1), p. 272, the
  estimate `∫_Γ |u|^p dx' ≤ C ∫_{B⁺} (|u|^p + |Du|^p) dx` for `C¹` functions near a flat boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace
namespace Trace.HalfSpace.CompactSupport

open MeasureTheory Set Function
open scoped ENNReal Sobolev

variable {n : ℕ}

/-- Compactly supported `C¹` real-valued functions on `ℝ^(n+1)`, as a
linear subspace of all functions. -/
noncomputable def c1CompactSubmodule (n : ℕ) :
    Submodule ℝ (ℝ^(n + 1) → ℝ) where
  carrier f := ContDiff ℝ 1 f ∧ HasCompactSupport f
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := by
    rintro f g ⟨hf, hfc⟩ ⟨hg, hgc⟩
    exact ⟨hf.add hg, hfc.add hgc⟩
  smul_mem' := by
    rintro c f ⟨hf, hfc⟩
    refine ⟨?_, ?_⟩
    · change ContDiff ℝ 1 (fun x ↦ c * f x)
      exact hf.const_smul c
    · change HasCompactSupport (fun x ↦ c * f x)
      exact hfc.smul_left (f := fun _ ↦ c)

/-- Elements of `c1CompactSubmodule n` are `C¹`. -/
theorem contDiff (f : c1CompactSubmodule n) : ContDiff ℝ 1 (f : ℝ^(n + 1) → ℝ) :=
  f.property.1

/-- Elements of `c1CompactSubmodule n` have compact support. -/
theorem hasCompactSupport (f : c1CompactSubmodule n) :
    HasCompactSupport (f : ℝ^(n + 1) → ℝ) :=
  f.property.2

/-- Every classical derivative of a compactly supported `C¹` function lies in `Lᵖ` of the
upper half-space, for every exponent `p`. -/
theorem derivative_memLp_at (p : ℝ≥0∞)
    (f : c1CompactSubmodule n) (a : GraphSpace.DerivIndex (n + 1) 1) :
    MemLp
      (fun x ↦ iteratedPartialDeriv (n := n + 1) a.toList
        (f : ℝ^(n + 1) → ℝ) x)
      p (domainMeasure (n + 1) (HalfSpace.upper (n + 1))) := by
  have hlen : a.toList.length ≤ 1 := a.toList_length_le
  have hfreg : ContDiff ℝ (a.toList.length : ℕ∞)
      (f : ℝ^(n + 1) → ℝ) :=
    (contDiff f).of_le (by exact_mod_cast hlen)
  have hd : Continuous (fun x ↦
      iteratedPartialDeriv (n := n + 1) a.toList
        (f : ℝ^(n + 1) → ℝ) x) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le
      (n := n + 1) hfreg a.toList le_rfl).continuous
  exact hd.memLp_of_hasCompactSupport
    (SobolevSpace.hasCompactSupport_iteratedPartialDeriv
      (n := n + 1) (f := (f : ℝ^(n + 1) → ℝ))
      (hasCompactSupport f) a.toList)

/-- A compactly supported `C¹` function as an upper-half-space
`H¹` function using its classical derivatives. -/
noncomputable def toUpperH1 (f : c1CompactSubmodule n) :
    H¹(HalfSpace.upper (n + 1)) :=
  GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
    (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
    (Ω := HalfSpace.upper (n + 1))
    (f := (f : ℝ^(n + 1) → ℝ)) (contDiff f)
    (derivative_memLp_at 2 f)

/-- Each coordinate of `toUpperH1 f` (the function itself at the base index, a first partial
derivative at a derivative index) agrees a.e. on the upper half-space with the corresponding
classical derivative of `f`. -/
theorem toUpperH1_coordinate_ae (f : c1CompactSubmodule n)
    (a : GraphSpace.DerivIndex (n + 1) 1) :
    ((((toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
        (HalfSpace.upper (n + 1))) a : GraphSpace.DerivLp (n + 1) 2
        (HalfSpace.upper (n + 1))) : ℝ^(n + 1) → ℝ)) =ᵐ[
      domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      fun x ↦ iteratedPartialDeriv (n := n + 1) a.toList
        (f : ℝ^(n + 1) → ℝ) x := by
  exact GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
    (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
    (Ω := HalfSpace.upper (n + 1))
    (f := (f : ℝ^(n + 1) → ℝ)) (contDiff f) (derivative_memLp_at 2 f) a

/-- The classical `H¹` embedding is additive. -/
theorem toUpperH1_add (f g : c1CompactSubmodule n) :
    toUpperH1 (f + g) = toUpperH1 f + toUpperH1 g := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  have hcoord :
      (((toUpperH1 f + toUpperH1 g :
          H¹(HalfSpace.upper (n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1))) a) =
        (toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1))) a +
        (toUpperH1 g : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1))) a := by
    simp [PiLp.add_apply]
  rw [hcoord]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [toUpperH1_coordinate_ae (f + g) a,
      toUpperH1_coordinate_ae f a,
      toUpperH1_coordinate_ae g a,
      MeasureTheory.Lp.coeFn_add
        ((toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1))) a)
        ((toUpperH1 g : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1))) a)] with x hadd hf hg hsum
  rw [hadd, hsum]
  simp only [Pi.add_apply]
  rw [hf, hg]
  have hlen : a.toList.length ≤ 1 := a.toList_length_le
  exact congrFun
    (PDE.iteratedPartialDeriv_add_of_contDiff a.toList
      ((contDiff f).of_le (by exact_mod_cast hlen))
      ((contDiff g).of_le (by exact_mod_cast hlen))) x

/-- The classical `H¹` embedding commutes with scalar multiplication. -/
theorem toUpperH1_smul (c : ℝ) (f : c1CompactSubmodule n) :
    toUpperH1 (c • f) = c • toUpperH1 f := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  have hcoord :
      (((c • toUpperH1 f :
          H¹(HalfSpace.upper (n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1))) a) =
        c • (toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1))) a := by
    simp [PiLp.smul_apply]
  rw [hcoord]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [toUpperH1_coordinate_ae (c • f) a,
      toUpperH1_coordinate_ae f a,
      MeasureTheory.Lp.coeFn_smul (p := (2 : ℝ≥0∞)) (c := c)
        ((toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1))) a)] with x hsmul hf hcoord
  rw [hsmul, hcoord]
  simp only [Pi.smul_apply]
  rw [hf]
  exact congrFun
    (PDE.iteratedPartialDeriv_const_smul
      (n := n + 1) c a.toList (f : ℝ^(n + 1) → ℝ)) x

/-- The finite-regularity classical embedding is linear. -/
noncomputable def toUpperH1Linear :
    c1CompactSubmodule n →ₗ[ℝ]
      H¹(HalfSpace.upper (n + 1)) where
  toFun := toUpperH1
  map_add' := toUpperH1_add
  map_smul' := toUpperH1_smul

/-- Include a smooth compactly supported test function in the C¹ source. -/
noncomputable def ofGlobalTestFunction
    (φ : Trace.HalfSpace.GlobalTestFunction n) : c1CompactSubmodule n :=
  ⟨φ.1.toFun, φ.1.contDiff.of_le (by simp), φ.1.hasCompactSupport⟩

/-- On smooth global test functions the `C¹` embedding agrees with the smooth embedding
`globalTestFunctionToUpperH1Linear` from which the flat trace was completed. -/
theorem toUpperH1_ofGlobalTestFunction
    (φ : Trace.HalfSpace.GlobalTestFunction n) :
    toUpperH1 (ofGlobalTestFunction φ) =
      Trace.HalfSpace.globalTestFunctionToUpperH1Linear n φ := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  apply MeasureTheory.Lp.ext
  have hc1 := toUpperH1_coordinate_ae (ofGlobalTestFunction φ) a
  rw [Trace.HalfSpace.globalTestFunctionToUpperH1Linear_eq_mk]
  have hsmooth := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
    (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
    (Ω := HalfSpace.upper (n + 1)) (f := φ.1.toFun)
    φ.1.contDiff φ.1.hasCompactSupport a
  exact hc1.trans hsmooth.symm

/-- Compactly supported C¹ functions still have dense image in upper
half-space `H¹`, since they contain the smooth classical core. -/
theorem denseRange_toUpperH1Linear : DenseRange (toUpperH1Linear (n := n)) := by
  apply (Trace.HalfSpace.denseRange_globalTestFunctionToUpperH1Linear n).mono
  rintro u ⟨φ, rfl⟩
  exact ⟨ofGlobalTestFunction φ, toUpperH1_ofGlobalTestFunction φ⟩

/-- The literal boundary restriction of a compactly supported `C¹` function lies in `Lᵖ(ℝ^n)`
for every exponent `p`. -/
theorem boundaryValue_memLp_at (p : ℝ≥0∞) (f : c1CompactSubmodule n) :
    MemLp (Trace.HalfSpace.smoothBoundaryValue
      (f : ℝ^(n + 1) → ℝ)) p (volume : Measure (ℝ^n)) :=
  (Trace.HalfSpace.smoothBoundaryValue_continuous
      (n := n) (contDiff f).continuous).memLp_of_hasCompactSupport
    (Trace.HalfSpace.smoothBoundaryValue_hasCompactSupport
      (n := n) (hasCompactSupport f))

/-- Literal restriction of a compactly supported C¹ function to the flat
boundary, in tangential coordinates. -/
noncomputable def boundaryLinear :
    c1CompactSubmodule n →ₗ[ℝ]
      MeasureTheory.Lp ℝ 2 (volume : Measure (ℝ^n)) where
  toFun f := (boundaryValue_memLp_at 2 f).toLp
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

/-- The `L²` boundary restriction of `f` is a.e. equal to the pointwise boundary value
`y ↦ f (y, 0)` in tangential coordinates. -/
theorem boundaryLinear_apply_ae (f : c1CompactSubmodule n) :
    (boundaryLinear f : ℝ^n → ℝ) =ᵐ[(volume : Measure (ℝ^n))]
      Trace.HalfSpace.smoothBoundaryValue (f : ℝ^(n + 1) → ℝ) :=
  (boundaryValue_memLp_at 2 f).coeFn_toLp

private theorem upper_base_integral_eq_coordinate_sq
    (f : c1CompactSubmodule n) :
    (∫ x in HalfSpace.upper (n + 1), (f : ℝ^(n + 1) → ℝ) x ^ 2) =
      ‖((toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1)))
        (GraphSpace.baseIndex (n + 1) 1))‖ ^ 2 := by
  let U := toUpperH1 f
  let v := ((U : GraphSpace.WkpAmbientOn (n + 1) 1 2
    (HalfSpace.upper (n + 1))) (GraphSpace.baseIndex (n + 1) 1))
  have hv : (v : ℝ^(n + 1) → ℝ) =ᵐ[
      domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      (f : ℝ^(n + 1) → ℝ) := by
    simpa [v, U, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      toUpperH1_coordinate_ae f (GraphSpace.baseIndex (n + 1) 1)
  calc
    (∫ x in HalfSpace.upper (n + 1), (f : ℝ^(n + 1) → ℝ) x ^ 2) =
        ∫ x, (v x) ^ 2
          ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = ‖v‖ ^ 2 := (MeasureTheory.Lp.norm_sq_eq_integral_sq v).symm

private theorem upper_normal_integral_eq_coordinate_sq
    (f : c1CompactSubmodule n) :
    (∫ x in HalfSpace.upper (n + 1),
        (∂[Fin.last n] (f : ℝ^(n + 1) → ℝ)) x ^ 2) =
      ‖((toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
          (HalfSpace.upper (n + 1)))
        (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)))‖ ^ 2 := by
  let U := toUpperH1 f
  let v := ((U : GraphSpace.WkpAmbientOn (n + 1) 1 2
    (HalfSpace.upper (n + 1)))
    (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)))
  have hv : (v : ℝ^(n + 1) → ℝ) =ᵐ[
      domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      fun x ↦ (∂[Fin.last n] (f : ℝ^(n + 1) → ℝ)) x := by
    simpa [v, U, GraphSpace.singleDerivIndex_toList,
      iteratedPartialDeriv] using
      toUpperH1_coordinate_ae f
        (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n))
  calc
    (∫ x in HalfSpace.upper (n + 1),
        (∂[Fin.last n] (f : ℝ^(n + 1) → ℝ)) x ^ 2) =
        ∫ x, (v x) ^ 2
          ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = ‖v‖ ^ 2 := (MeasureTheory.Lp.norm_sq_eq_integral_sq v).symm

private theorem boundary_norm_sq_eq_integral (f : c1CompactSubmodule n) :
    ‖boundaryLinear f‖ ^ 2 =
      ∫ y : ℝ^n,
        Trace.HalfSpace.smoothBoundaryValue
          (f : ℝ^(n + 1) → ℝ) y ^ 2 := by
  let v := boundaryLinear f
  have hv : (v : ℝ^n → ℝ) =ᵐ[(volume : Measure (ℝ^n))]
      Trace.HalfSpace.smoothBoundaryValue (f : ℝ^(n + 1) → ℝ) :=
    boundaryLinear_apply_ae f
  calc
    ‖v‖ ^ 2 = ∫ y, (v y) ^ 2 :=
      MeasureTheory.Lp.norm_sq_eq_integral_sq v
    _ = ∫ y, Trace.HalfSpace.smoothBoundaryValue
        (f : ℝ^(n + 1) → ℝ) y ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hv] with y hy
      rw [hy]

/-- Evans' flat trace estimate at finite regularity. -/
private theorem norm_boundaryLinear_le (f : c1CompactSubmodule n) :
    ‖boundaryLinear f‖ ≤ ‖toUpperH1 f‖ := by
  let U := (toUpperH1 f : GraphSpace.WkpAmbientOn (n + 1) 1 2
    (HalfSpace.upper (n + 1)))
  have htrace := Trace.HalfSpace.smooth_boundary_integral_sq_le_upper_energy
    (n := n) (contDiff f) (hasCompactSupport f)
  have htrace' : ‖boundaryLinear f‖ ^ 2 ≤
      ‖U (GraphSpace.baseIndex (n + 1) 1)‖ ^ 2 +
        ‖U (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n))‖ ^ 2 := by
    calc
      _ = ∫ y : ℝ^n, Trace.HalfSpace.smoothBoundaryValue
          (f : ℝ^(n + 1) → ℝ) y ^ 2 := boundary_norm_sq_eq_integral f
      _ ≤ (∫ x in HalfSpace.upper (n + 1),
          (f : ℝ^(n + 1) → ℝ) x ^ 2) +
          ∫ x in HalfSpace.upper (n + 1),
            (∂[Fin.last n] (f : ℝ^(n + 1) → ℝ)) x ^ 2 := by
        simpa using htrace
      _ = _ := by
        rw [upper_base_integral_eq_coordinate_sq f,
          upper_normal_integral_eq_coordinate_sq f]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact htrace'.trans
    (GraphSpace.base_norm_sq_add_single_norm_sq_le U (Fin.last n))

/-- Auxiliary completion from the compactly supported C¹ core. -/
private noncomputable def traceFromCompactC1 :
    H¹(HalfSpace.upper (n + 1)) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  boundaryLinear.extendOfNorm toUpperH1Linear

private theorem boundaryLinear_ofGlobalTestFunction
    (φ : Trace.HalfSpace.GlobalTestFunction n) :
    boundaryLinear (ofGlobalTestFunction φ) =
      Trace.HalfSpace.globalTestFunctionBoundaryLinear n φ := by
  apply MeasureTheory.Lp.ext
  exact (boundaryLinear_apply_ae (ofGlobalTestFunction φ)).trans
    (Trace.HalfSpace.globalTestFunctionBoundaryLinear_apply_ae n φ).symm

/-- The auxiliary compact-C¹ completion is the canonical flat trace. -/
private theorem traceFromCompactC1_eq_trace :
    traceFromCompactC1 (n := n) = Trace.HalfSpace.trace n := by
  have hcomp : (traceFromCompactC1 (n := n) :
      H¹(HalfSpace.upper (n + 1)) →
        MeasureTheory.Lp ℝ 2 (volume : Measure (ℝ^n))) ∘
      Trace.HalfSpace.globalTestFunctionToUpperH1Linear n =
      (Trace.HalfSpace.trace n :
        H¹(HalfSpace.upper (n + 1)) →
          MeasureTheory.Lp ℝ 2 (volume : Measure (ℝ^n))) ∘
        Trace.HalfSpace.globalTestFunctionToUpperH1Linear n := by
    funext φ
    change traceFromCompactC1 (n := n)
        (Trace.HalfSpace.globalTestFunctionToUpperH1Linear n φ) =
      Trace.HalfSpace.trace n
        (Trace.HalfSpace.globalTestFunctionToUpperH1Linear n φ)
    calc
      traceFromCompactC1 (n := n)
          (Trace.HalfSpace.globalTestFunctionToUpperH1Linear n φ) =
          traceFromCompactC1 (n := n)
            (toUpperH1 (ofGlobalTestFunction φ)) := by
        rw [toUpperH1_ofGlobalTestFunction]
      _ =
          boundaryLinear (ofGlobalTestFunction φ) := by
        exact LinearMap.extendOfNorm_eq
          (denseRange_toUpperH1Linear (n := n))
          ⟨1, fun f ↦ by
            simpa [toUpperH1Linear] using norm_boundaryLinear_le f⟩
          (ofGlobalTestFunction φ)
      _ = Trace.HalfSpace.globalTestFunctionBoundaryLinear n φ :=
        boundaryLinear_ofGlobalTestFunction φ
      _ = Trace.HalfSpace.trace n
          (Trace.HalfSpace.globalTestFunctionToUpperH1Linear n φ) :=
        (Trace.HalfSpace.trace_smooth n φ).symm
  have hfun :=
    (Trace.HalfSpace.denseRange_globalTestFunctionToUpperH1Linear n).equalizer
      (traceFromCompactC1 (n := n)).continuous
      (Trace.HalfSpace.trace n).continuous hcomp
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- The flat trace agrees with literal boundary restriction for every
compactly supported C¹ function. -/
theorem trace_c1 (f : c1CompactSubmodule n) :
    Trace.HalfSpace.trace n (toUpperH1 f) = boundaryLinear f := by
  rw [← traceFromCompactC1_eq_trace (n := n)]
  exact LinearMap.extendOfNorm_eq
    (denseRange_toUpperH1Linear (n := n))
    ⟨1, fun g ↦ by
      simpa [toUpperH1Linear] using norm_boundaryLinear_le g⟩ f

/-- Intrinsic hyperplane form of `trace_c1`. -/
theorem flatTrace_c1 (f : c1CompactSubmodule n) :
    Boundary.Geometry.SurfaceMeasure.flatTrace (n := n) (toUpperH1 f) =
      (Boundary.Geometry.SurfaceMeasure.liftLp (n := n) 2).toContinuousLinearMap
        (boundaryLinear f) := by
  simp only [Boundary.Geometry.SurfaceMeasure.flatTrace, ContinuousLinearMap.comp_apply]
  rw [trace_c1]

/-- Representative form of the intrinsic compact-C¹ trace theorem: on the
flat hyperplane, the trace is the original function almost everywhere. -/
theorem flatTrace_c1_apply_ae (f : c1CompactSubmodule n) :
    (Boundary.Geometry.SurfaceMeasure.flatTrace (n := n) (toUpperH1 f) :
      ℝ^(n + 1) → ℝ) =ᵐ[Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := n)]
      (f : ℝ^(n + 1) → ℝ) := by
  rw [flatTrace_c1]
  have hlift := Boundary.Geometry.SurfaceMeasure.liftLp_apply_ae
    (n := n) 2 (boundaryLinear f)
  have hboundary :=
    (Boundary.Geometry.SurfaceMeasure.measurePreserving_flatProjection
      (n := n)).quasiMeasurePreserving.ae (boundaryLinear_apply_ae f)
  have hflatMeas : MeasurableSet
      {x : ℝ^(n + 1) | x (Fin.last n) = 0} := by
    rw [← Boundary.Geometry.SurfaceMeasure.frontier_upperHalfSpace (n := n)]
    exact isClosed_frontier.measurableSet
  have hmem : ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := n),
      x (Fin.last n) = 0 := by
    simpa [Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure] using
      (MeasureTheory.ae_restrict_mem
        (μ := Measure.euclideanHausdorffMeasure n)
        (s := {x : ℝ^(n + 1) | x (Fin.last n) = 0})
        hflatMeas)
  filter_upwards [hlift, hboundary, hmem] with x hxlift hxboundary hxflat
  change ((Boundary.Geometry.SurfaceMeasure.liftLp (n := n) 2 (boundaryLinear f) :
    MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := n))) :
      ℝ^(n + 1) → ℝ) x = (f : ℝ^(n + 1) → ℝ) x
  rw [hxlift, hxboundary]
  simp only [Trace.HalfSpace.smoothBoundaryValue,
    Trace.HalfSpace.normalSlice]
  change (f : ℝ^(n + 1) → ℝ)
      (Boundary.Geometry.SurfaceMeasure.flatEmbedding
        (Boundary.Geometry.SurfaceMeasure.flatProjection x)) =
      (f : ℝ^(n + 1) → ℝ) x
  rw [Boundary.Geometry.SurfaceMeasure.flatEmbedding_flatProjection_of_last_eq_zero hxflat]

end Trace.HalfSpace.CompactSupport
end SobolevSpace
