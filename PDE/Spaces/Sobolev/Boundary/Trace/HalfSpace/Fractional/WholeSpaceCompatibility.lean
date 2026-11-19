/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.Real
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.SchwartzAgreement
public import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Operator
import PDE.Spaces.Sobolev.Fractional.WholeSpace.IntegrationByParts
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Physical agreement of Bessel and half-space traces

On compactly supported smooth functions the Fourier restriction is literal
boundary evaluation. Global smooth density and the integer Bessel–graph
equivalence extend this identity to every whole-space `H¹` element. Thus the
fractional trace realizes the completed `L²` boundary trace.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory BesselPotentialSpace
open scoped ENNReal BesselPotentialSpace SchwartzMap Topology Sobolev

namespace SobolevSpace.Trace.HalfSpace.Fractional

open SobolevSpace.Fractional SobolevSpace.Fractional.Trace GraphSpace

/-- The integer Bessel–graph equivalence at real order one.
It transports the natural-number cast of the integer order to the real
order used by the trace operator. -/
def h1GraphEquiv (d : ℕ) : HsSpaceReal d 1 ≃L[ℝ] W^{1,2}(ℝ^d) := by
  exact cast (congrArg (fun s : ℝ ↦ HsSpaceReal d s ≃L[ℝ] W^{1,2}(ℝ^d))
    (Nat.cast_one (R := ℝ))) (toWkpSpaceCLE d 1)

private def testBessel {d : ℕ} (s : ℝ) (hs : 0 ≤ s) (φ : TestFunctionOn d Set.univ) :
    HsSpaceReal d s :=
  HsSpaceReal.ofPhysical hs
    (SchwartzMap.memSobolev (p := 2) (s := s) (testFunctionToSchwartz φ.1)).toBesselPotentialSpace
    (isRealL2_ofSchwartz hs _ (fun _ ↦ rfl))

private theorem toWkpSpaceCLE_testBessel {d : ℕ} (k : ℕ) (φ : TestFunctionOn d Set.univ) :
    toWkpSpaceCLE d k (testBessel k (Nat.cast_nonneg k) φ) =
      testFunctionToWkp (k := k) (p := 2) φ := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change (graphTuple (Nat.cast_nonneg k) (testBessel k (Nat.cast_nonneg k) φ).val
    (HsSpaceReal.isRealL2_toL2Fun _ _) (baseIndex d k) : ℝ^d → ℝ) =ᵐ[_] _
  rw [graphTuple_baseIndex]
  have hφ := testFunctionToWkp_coordinate_ae (k := k) (p := 2) φ (baseIndex d k)
  have hg := coeFn_toDerivLp
    (toL2Fun (Nat.cast_nonneg k)
      (SchwartzMap.memSobolev (p := 2) (s := (k : ℝ))
        (testFunctionToSchwartz φ.1)).toBesselPotentialSpace)
  rw [toL2Fun_ofSchwartz] at hg
  have hs : (testFunctionToSchwartz φ.1).toLp 2 volume =ᵐ[domainMeasure d Set.univ]
      testFunctionToSchwartz φ.1 := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      (testFunctionToSchwartz φ.1).coeFn_toLp 2 (volume : Measure ℝ^d)
  filter_upwards [hg, hφ, hs] with x h1 h2 h3
  change (toDerivLp (toL2Fun (Nat.cast_nonneg k)
    (SchwartzMap.memSobolev (p := 2) (s := (k : ℝ))
      (testFunctionToSchwartz φ.1)).toBesselPotentialSpace)) x = _
  rw [toL2Fun_ofSchwartz, h1, h2]
  simp only [reOfL2, h3, testFunctionToSchwartz_apply, Complex.ofReal_re,
    baseIndex_toList, iteratedPartialDeriv]
  rfl

private theorem cast_equiv_testBessel {d : ℕ} {s t : ℝ} (h : s = t)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (e : HsSpaceReal d s ≃L[ℝ] W^{1,2}(ℝ^d))
    (φ : TestFunctionOn d Set.univ) :
    (cast (congrArg (fun r : ℝ ↦ HsSpaceReal d r ≃L[ℝ] W^{1,2}(ℝ^d)) h) e)
      (testBessel t ht φ) = e (testBessel s hs φ) := by
  subst t
  rfl

private theorem h1GraphEquiv_testBessel {d : ℕ} (φ : TestFunctionOn d Set.univ) :
    h1GraphEquiv d (testBessel 1 zero_le_one φ) = testFunctionToH1Linear φ := by
  rw [h1GraphEquiv, cast_equiv_testBessel (Nat.cast_one (R := ℝ)) (Nat.cast_nonneg 1)]
  exact toWkpSpaceCLE_testBessel 1 φ

private theorem physicalTrace_testBessel (n : ℕ) (φ : GlobalTestFunction n) :
    HsSpaceReal.toL2FunCLM n (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (wholeSpaceTraceRealCLM n (testBessel 1 zero_le_one φ)) =
      globalTestFunctionBoundaryLinear n φ := by
  apply Lp.ext
  have ht := HsSpaceReal.toL2FunCLM_apply_ae
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (wholeSpaceTraceRealCLM n (testBessel 1 zero_le_one φ))
  change _ =ᵐ[volume] fun x ↦ (toL2Fun _
    (wholeSpaceTraceCLM n
      (SchwartzMap.memSobolev (p := 2) (s := 1)
        (testFunctionToSchwartz φ.1)).toBesselPotentialSpace) x).re at ht
  rw [wholeSpaceTraceCLM_ofSchwartz, toL2Fun_ofSchwartz] at ht
  filter_upwards [ht, (schwartzBoundaryCLM n (testFunctionToSchwartz φ.1)).coeFn_toLp 2,
    globalTestFunctionBoundaryLinear_apply_ae n φ] with y h1 h2 h3
  rw [h1, h2, h3, schwartzBoundaryCLM_apply, testFunctionToSchwartz_apply,
    Complex.ofReal_re]
  rfl

private theorem denseRange_globalTestH1 (d : ℕ) :
    DenseRange (testFunctionToH1Linear (n := d) (Ω := Set.univ)) := by
  intro U
  rw [mem_closure_iff_seq_limit]
  obtain ⟨f, hf, hcs, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier d) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) 1 U
  let φ : ℕ → TestFunctionOn d Set.univ := fun m ↦
    ⟨_root_.TestFunction.mk (f m) (hf m) (hcs m) (Set.subset_univ _), Set.subset_univ _⟩
  refine ⟨fun m ↦ testFunctionToH1Linear (φ m), fun m ↦ ⟨φ m, rfl⟩, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hlim

/-- Restricting a whole-space real `H¹` element and taking its `L²` trace
agrees with the physical representative of its Fourier-defined fractional trace. -/
theorem trace_restrict_toWkpSpace (n : ℕ) (u : HsSpaceReal (n + 1) 1) :
    trace n (restrictCLM (k := 1) (p := 2)
      (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _)
        (h1GraphEquiv (n + 1) u)) =
      HsSpaceReal.toL2FunCLM n (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (wholeSpaceTraceRealCLM n u) := by
  let A := (trace n).comp (restrictCLM (k := 1) (p := 2)
    (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _))
  let B := (HsSpaceReal.toL2FunCLM n (by norm_num : (0 : ℝ) ≤ 1 / 2)).comp
    ((wholeSpaceTraceRealCLM n).comp (h1GraphEquiv (n + 1)).symm.toContinuousLinearMap)
  have hcore (φ : GlobalTestFunction n) :
      A (testFunctionToH1Linear φ) = B (testFunctionToH1Linear φ) := by
    change trace n (globalTestFunctionToUpperH1Linear n φ) = _
    rw [trace_smooth, ← h1GraphEquiv_testBessel φ]
    simp only [B, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    exact (physicalTrace_testBessel n φ).symm
  have h := (denseRange_globalTestH1 (n + 1)).equalizer A.continuous B.continuous (funext hcore)
  have hu := congrFun h (h1GraphEquiv (n + 1) u)
  simpa only [A, B, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using hu

end SobolevSpace.Trace.HalfSpace.Fractional
