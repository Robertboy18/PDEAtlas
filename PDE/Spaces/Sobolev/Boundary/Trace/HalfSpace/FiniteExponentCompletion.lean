/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
import PDE.Spaces.Sobolev.Approximation.Density.ExtensionDomain
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponent
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Operator

/-!
# Completed finite-exponent trace on the upper half-space

For every real `p ≥ 1`, we extend classical boundary restriction
from globally smooth compactly supported functions to a bounded operator

`W^{1,p}(ℝ^(n+1)_+) → Lᵖ(ℝ^n)`.

The construction uses the smooth finite-exponent estimate from
`Trace.HalfSpace.FiniteExponent`, density supplied by the half-space extension
operator, and `LinearMap.extendOfNorm`. The completed trace agrees with literal
restriction on the smooth core and has norm bound `p ^ (1 / p)`.
At `p = 1`, this gives a contraction `W^{1,1} → L¹`; the endpoint estimate
comes directly from the fundamental theorem of calculus on each normal slice.

## Main results

* `globalTestFunctionToUpperW1pLinear`, `denseRange_globalTestFunctionToUpperW1pLinear`:
  the smooth core and its density in `W^{1,p}(ℝ^(n+1)_+)`.
* `traceLp`: the completed trace operator, for real `p ≥ 1`.
* `traceLp_smooth`: on the smooth core it is literal boundary restriction.
* `norm_traceLp_le`: the operator norm is at most `p ^ (1 / p)`.
* `boundaryLpTwoEquivL2_traceLp`: for `p = 2` the finite-exponent trace agrees with the
  Hilbert-space trace `Trace.HalfSpace.trace` under the canonical identifications
  `upperW1pTwoEquivH1` and `boundaryLpTwoEquivL2`.

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
namespace Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ}

section Completion

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/--
Restriction of a global smooth test function to the completed upper-half-space
`W^{1,p}` graph space.
-/
noncomputable def globalTestFunctionToUpperW1pLinear :
    GlobalTestFunction n →ₗ[ℝ]
      W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) :=
  (GraphSpace.restrictCLM
      (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
      (HalfSpace.measurableSet_upper (n := n + 1))
      (Set.subset_univ _)).toLinearMap.comp
    (GraphSpace.testFunctionToWkpLinear
      (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := Set.univ))

/--
The upper-half-space test embedding agrees with the classical smooth
Sobolev graph element.
-/
theorem globalTestFunctionToUpperW1pLinear_eq_mk
    (φ : GlobalTestFunction n) :
    globalTestFunctionToUpperW1pLinear n p φ =
      GraphSpace.mkWkpSpaceOnOfContDiff
        (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := HalfSpace.upper (n + 1))
        φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  apply MeasureTheory.Lp.ext
  have hrestrict := GraphSpace.restrictCLM_apply_ae
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _)
    (GraphSpace.testFunctionToWkpLinear
      (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := Set.univ) φ) a
  have hglobal := GraphSpace.testFunctionToWkp_coordinate_ae
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := Set.univ) φ a
  have hhalf := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := HalfSpace.upper (n + 1)) φ.1.toFun
    φ.1.contDiff φ.1.hasCompactSupport a
  have hglobal' :
      ((((GraphSpace.testFunctionToWkpLinear
          (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := Set.univ) φ :
          W^{1,ENNReal.ofReal p}(ℝ^(n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p) Set.univ) a :
          GraphSpace.DerivLp (n + 1) (ENNReal.ofReal p) Set.univ) :
          ℝ^(n + 1) → ℝ) =ᵐ[domainMeasure (n + 1) Set.univ]
      fun x ↦ iteratedPartialDeriv (n := n + 1) a.toList φ.1.toFun x := by
    simpa only [GraphSpace.testFunctionToWkpLinear_apply] using hglobal
  have hres :
      ((((globalTestFunctionToUpperW1pLinear n p φ :
          W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) a :
          GraphSpace.DerivLp (n + 1) (ENNReal.ofReal p)
            (HalfSpace.upper (n + 1))) : ℝ^(n + 1) → ℝ) =ᵐ[
        domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      ((((GraphSpace.testFunctionToWkpLinear
          (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := Set.univ) φ :
          W^{1,ENNReal.ofReal p}(ℝ^(n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p) Set.univ) a :
          GraphSpace.DerivLp (n + 1) (ENNReal.ofReal p) Set.univ) :
          ℝ^(n + 1) → ℝ) := by
    simpa [globalTestFunctionToUpperW1pLinear] using hrestrict
  have hglobal_restrict :
      ((((GraphSpace.testFunctionToWkpLinear
          (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := Set.univ) φ :
          W^{1,ENNReal.ofReal p}(ℝ^(n + 1))) :
          GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p) Set.univ) a :
          GraphSpace.DerivLp (n + 1) (ENNReal.ofReal p) Set.univ) :
          ℝ^(n + 1) → ℝ) =ᵐ[
        domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      fun x ↦ iteratedPartialDeriv (n := n + 1) a.toList φ.1.toFun x :=
    MeasureTheory.ae_restrict_of_ae
      (s := HalfSpace.upper (n + 1)) (by
        have hglobal_volume :
            ((((GraphSpace.testFunctionToWkpLinear
                (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
                (Ω := Set.univ) φ :
                W^{1,ENNReal.ofReal p}(ℝ^(n + 1))) :
                GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
                  Set.univ) a :
                GraphSpace.DerivLp (n + 1) (ENNReal.ofReal p) Set.univ) :
                ℝ^(n + 1) → ℝ) =ᵐ[volume]
              fun x ↦ iteratedPartialDeriv
                (n := n + 1) a.toList φ.1.toFun x := by
          simpa [domainMeasure] using hglobal'
        filter_upwards [hglobal_volume] with x hx
        exact hx)
  exact hres.trans (hglobal_restrict.trans hhalf.symm)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- The flat boundary value of a global test function lies in `Lᵖ(ℝ^n)` for
every real exponent `p`. -/
theorem smoothBoundaryValue_memLp_ofReal
    (φ : GlobalTestFunction n) :
    MemLp (smoothBoundaryValue φ.1.toFun) (ENNReal.ofReal p)
      (volume : Measure (ℝ^n)) :=
  (smoothBoundaryValue_continuous (n := n) φ.1.contDiff.continuous)
    |>.memLp_of_hasCompactSupport
      (smoothBoundaryValue_hasCompactSupport (n := n) φ.1.hasCompactSupport)

/--
Classical boundary restriction on the global smooth test core, represented in
`Lᵖ(ℝ^n)`.
-/
noncomputable def globalTestFunctionBoundaryLpLinear :
    GlobalTestFunction n →ₗ[ℝ]
      Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^n)) where
  toFun φ :=
    (smoothBoundaryValue_memLp_ofReal n p φ).toLp
      (smoothBoundaryValue φ.1.toFun)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by
      simp [smoothBoundaryValue, normalSlice]
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by
      simp [smoothBoundaryValue, normalSlice]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
private theorem boundary_norm_rpow_eq_integral
    (hp : 1 ≤ p) (φ : GlobalTestFunction n) :
    ‖globalTestFunctionBoundaryLpLinear n p φ‖ ^ p =
      ∫ y : ℝ^n, |smoothBoundaryValue φ.1.toFun y| ^ p := by
  simpa [globalTestFunctionBoundaryLpLinear] using
    MeasureTheory.norm_toLp_rpow_eq_integral_abs
      (zero_lt_one.trans_le hp) (smoothBoundaryValue_memLp_ofReal n p φ)

private theorem coordinate_norm_rpow_eq_integral
    (hp : 1 ≤ p) (φ : GlobalTestFunction n)
    (a : GraphSpace.DerivIndex (n + 1) 1) :
    ‖((globalTestFunctionToUpperW1pLinear n p φ :
        GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
          (HalfSpace.upper (n + 1))) a)‖ ^ p =
      ∫ x in HalfSpace.upper (n + 1),
        |iteratedPartialDeriv (n := n + 1)
          a.toList φ.1.toFun x| ^ p := by
  let v :=
    ((globalTestFunctionToUpperW1pLinear n p φ :
      GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
        (HalfSpace.upper (n + 1))) a)
  have hv :
      (v : ℝ^(n + 1) → ℝ) =ᵐ[
        domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
        fun x ↦ iteratedPartialDeriv
          (n := n + 1) a.toList φ.1.toFun x := by
    dsimp only [v]
    rw [globalTestFunctionToUpperW1pLinear_eq_mk]
    simpa using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := HalfSpace.upper (n + 1)) φ.1.toFun
        φ.1.contDiff φ.1.hasCompactSupport a)
  have hpow :=
    MeasureTheory.norm_toLp_rpow_eq_integral_abs
      (zero_lt_one.trans_le hp) (MeasureTheory.Lp.memLp v)
  rw [MeasureTheory.Lp.toLp_coeFn] at hpow
  calc
    ‖((globalTestFunctionToUpperW1pLinear n p φ :
        GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
          (HalfSpace.upper (n + 1))) a)‖ ^ p =
        ∫ x, |v x| ^ p
          ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := hpow
    _ = ∫ x,
        |iteratedPartialDeriv (n := n + 1) a.toList φ.1.toFun x| ^ p
          ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = ∫ x in HalfSpace.upper (n + 1),
        |iteratedPartialDeriv (n := n + 1) a.toList φ.1.toFun x| ^ p := rfl

private theorem norm_globalTestFunctionBoundaryLpLinear_le
    (hp : 1 ≤ p) (φ : GlobalTestFunction n) :
    ‖globalTestFunctionBoundaryLpLinear n p φ‖ ≤
      p ^ (1 / p) * ‖globalTestFunctionToUpperW1pLinear n p φ‖ := by
  let U := (globalTestFunctionToUpperW1pLinear n p φ :
    GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p)
      (HalfSpace.upper (n + 1)))
  let b := GraphSpace.baseIndex (n + 1) 1
  let d := GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)
  have htrace := smooth_boundary_integral_abs_rpow_le_upper_energy
    (n := n) (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport hp
  have hbase :
      ‖U b‖ ^ p =
        ∫ x in HalfSpace.upper (n + 1), |φ.1.toFun x| ^ p := by
    simpa [b, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      coordinate_norm_rpow_eq_integral n p hp φ b
  have hnormal :
      ‖U d‖ ^ p =
        ∫ x in HalfSpace.upper (n + 1),
          |(∂[Fin.last n] φ.1.toFun) x| ^ p := by
    simpa [d, GraphSpace.singleDerivIndex_toList,
      iteratedPartialDeriv] using
      coordinate_norm_rpow_eq_integral n p hp φ d
  have hpow :
      ‖globalTestFunctionBoundaryLpLinear n p φ‖ ^ p ≤
        (p - 1) * ‖U b‖ ^ p + ‖U d‖ ^ p := by
    calc
      _ = ∫ y : ℝ^n, |smoothBoundaryValue φ.1.toFun y| ^ p :=
        boundary_norm_rpow_eq_integral n p hp φ
      _ ≤ (p - 1) *
          (∫ x in HalfSpace.upper (n + 1), |φ.1.toFun x| ^ p) +
          (∫ x in HalfSpace.upper (n + 1),
            |(∂[Fin.last n] φ.1.toFun) x| ^ p) := htrace
      _ = (p - 1) * ‖U b‖ ^ p + ‖U d‖ ^ p := by
        rw [← hbase, ← hnormal]
  have hb : ‖U b‖ ^ p ≤ ‖U‖ ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) (PiLp.norm_apply_le U b)
      (le_of_lt (zero_lt_one.trans_le hp))
  have hd : ‖U d‖ ^ p ≤ ‖U‖ ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) (PiLp.norm_apply_le U d)
      (le_of_lt (zero_lt_one.trans_le hp))
  have hpow' :
      ‖globalTestFunctionBoundaryLpLinear n p φ‖ ^ p ≤
        p * ‖U‖ ^ p := by
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

private theorem exists_smooth_compactSupport_approximation_upperW1p
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
    ∃ f_m : ℕ → (ℝ^(n + 1) → ℝ),
    ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
    ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
      Filter.Tendsto
        (fun m ↦
          ‖(GraphSpace.mkWkpSpaceOnOfContDiff
              (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
              (Ω := HalfSpace.upper (n + 1))
              (f := f_m m) (hf_m m) (hcs_m m)) - u‖)
        Filter.atTop (nhds 0) := by
  apply GraphSpace.approximation_WkpSpaceOn
    (n := n + 1) (p := ENNReal.ofReal p)
    (Approximation.standardMollifier (n + 1)) ENNReal.ofReal_ne_top 1
    (HalfSpace.upper (n + 1)) u (HalfSpace.isOpen_upper (n := n + 1))
  exact Extension.GraphSpace.HalfSpace.exists_representativeExtensionOperator
    (n := n + 1) (p := ENNReal.ofReal p)

/--
Restrictions of globally smooth compactly supported functions are dense in the
upper-half-space `W^{1,p}` graph space.
-/
theorem denseRange_globalTestFunctionToUpperW1pLinear :
    DenseRange (globalTestFunctionToUpperW1pLinear n p) := by
  rw [DenseRange]
  intro u
  rw [mem_closure_iff_seq_limit]
  obtain ⟨f, hf, hcs, hlim⟩ :=
    exists_smooth_compactSupport_approximation_upperW1p n p u
  let φ : ℕ → GlobalTestFunction n := fun m ↦
    ⟨_root_.TestFunction.mk
      (f m) (hf m) (hcs m) (Set.subset_univ _), Set.subset_univ _⟩
  refine ⟨fun m ↦ globalTestFunctionToUpperW1pLinear n p (φ m), ?_, ?_⟩
  · intro m
    exact ⟨φ m, rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hφ_toFun (m : ℕ) : (φ m).1.toFun = f m := by
      funext x
      rfl
    simp_rw [globalTestFunctionToUpperW1pLinear_eq_mk, hφ_toFun]
    exact hlim

/--
The completed finite-exponent trace from the upper-half-space `W^{1,p}` graph
space to boundary `Lᵖ`, for `1 ≤ p`.
-/
noncomputable def traceLp (_hp : 1 ≤ p) :
    W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^n)) :=
  (globalTestFunctionBoundaryLpLinear n p).extendOfNorm
    (globalTestFunctionToUpperW1pLinear n p)

/--
The completed finite-exponent trace agrees with literal boundary restriction
on globally smooth compactly supported functions.
-/
theorem traceLp_smooth (hp : 1 ≤ p) (φ : GlobalTestFunction n) :
    traceLp n p hp (globalTestFunctionToUpperW1pLinear n p φ) =
      globalTestFunctionBoundaryLpLinear n p φ := by
  exact LinearMap.extendOfNorm_eq
    (denseRange_globalTestFunctionToUpperW1pLinear n p)
    ⟨p ^ (1 / p), norm_globalTestFunctionBoundaryLpLinear_le n p hp⟩ φ

/--
The completed finite-exponent trace has operator bound `p ^ (1 / p)`,
equal to one at the endpoint `p = 1`.
-/
theorem norm_traceLp_le (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
    ‖traceLp n p hp u‖ ≤ p ^ (1 / p) * ‖u‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (denseRange_globalTestFunctionToUpperW1pLinear n p)
    (p ^ (1 / p))
    (norm_globalTestFunctionBoundaryLpLinear_le n p hp) u

end Completion

/-! ## Compatibility with the Hilbert trace -/

section ExponentTwo

variable (n : ℕ)

/-- Canonical identification of the real-exponent `W^{1,2}` half-space with
the Hilbert-space alias `H¹`. -/
noncomputable def upperW1pTwoEquivH1 :
    W^{1,(ENNReal.ofReal (2 : ℝ))}(HalfSpace.upper (n + 1)) ≃L[ℝ]
      H¹(HalfSpace.upper (n + 1)) :=
  GraphSpace.WkpSpaceOn.congrExponent (ENNReal.ofReal_ofNat 2) _ _ _

/-- Canonical identification of boundary `L^(ENNReal.ofReal 2)` with
boundary `L²`. -/
noncomputable def boundaryLpTwoEquivL2 :
    Lp ℝ (ENNReal.ofReal (2 : ℝ)) (volume : Measure (ℝ^n)) ≃L[ℝ]
      Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  MeasureTheory.Lp.congrExponent (ENNReal.ofReal_ofNat 2) volume

/-- The canonical `W^{1,2} ≃ H¹` identification commutes with the smooth
half-space test-function embeddings. -/
theorem upperW1pTwoEquivH1_globalTestFunction
    (φ : GlobalTestFunction n) :
    upperW1pTwoEquivH1 n (globalTestFunctionToUpperW1pLinear n 2 φ) =
      globalTestFunctionToUpperH1Linear n φ := by
  apply eq_of_heq
  rw [globalTestFunctionToUpperW1pLinear_eq_mk,
    globalTestFunctionToUpperH1Linear_eq_mk]
  exact (GraphSpace.WkpSpaceOn.congrExponent_apply_heq
    (ENNReal.ofReal_ofNat 2) _ _ _
    (GraphSpace.mkWkpSpaceOnOfContDiff
      (n := n + 1) (k := 1) (p := ENNReal.ofReal (2 : ℝ))
      (Ω := HalfSpace.upper (n + 1))
      φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport)).trans
    (GraphSpace.mkWkpSpaceOnOfContDiff_congrExponent
      (ENNReal.ofReal_ofNat 2) φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport)

/-- The canonical `L^(ENNReal.ofReal 2) ≃ L²` identification commutes with
literal smooth boundary restriction. -/
theorem boundaryLpTwoEquivL2_globalTestFunction
    (φ : GlobalTestFunction n) :
    boundaryLpTwoEquivL2 n (globalTestFunctionBoundaryLpLinear n 2 φ) =
      globalTestFunctionBoundaryLinear n φ := by
  apply eq_of_heq
  exact (MeasureTheory.Lp.congrExponent_apply_heq
    (ENNReal.ofReal_ofNat 2) volume
    (globalTestFunctionBoundaryLpLinear n 2 φ)).trans (by
      unfold globalTestFunctionBoundaryLpLinear
        globalTestFunctionBoundaryLinear
      let hp : MemLp (smoothBoundaryValue φ.1.toFun)
          (ENNReal.ofReal (2 : ℝ)) (volume : Measure (ℝ^n)) :=
        (smoothBoundaryValue_continuous (n := n)
          φ.1.contDiff.continuous).memLp_of_hasCompactSupport
            (smoothBoundaryValue_hasCompactSupport
              (n := n) φ.1.hasCompactSupport)
      let hq : MemLp (smoothBoundaryValue φ.1.toFun)
          2 (volume : Measure (ℝ^n)) :=
        (smoothBoundaryValue_continuous (n := n)
          φ.1.contDiff.continuous).memLp_of_hasCompactSupport
            (smoothBoundaryValue_hasCompactSupport
              (n := n) φ.1.hasCompactSupport)
      change HEq
        (hp.toLp (smoothBoundaryValue φ.1.toFun))
        (hq.toLp (smoothBoundaryValue φ.1.toFun))
      exact MeasureTheory.MemLp.toLp_heq_of_exponent_eq
        (ENNReal.ofReal_ofNat 2) hp hq)

/-- Commuting-diagram form of compatibility between the finite `p = 2` trace
and the Hilbert trace. -/
theorem boundaryLpTwoEquivL2_traceLp
    (u : W^{1,(ENNReal.ofReal (2 : ℝ))}(HalfSpace.upper (n + 1))) :
    boundaryLpTwoEquivL2 n (traceLp n 2 (by norm_num) u) =
      trace n (upperW1pTwoEquivH1 n u) := by
  let lhs :
      W^{1,(ENNReal.ofReal (2 : ℝ))}(HalfSpace.upper (n + 1)) →L[ℝ]
        Lp ℝ 2 (volume : Measure (ℝ^n)) :=
    (boundaryLpTwoEquivL2 n).toContinuousLinearMap.comp
      (traceLp n 2 (by norm_num))
  let rhs :
      W^{1,(ENNReal.ofReal (2 : ℝ))}(HalfSpace.upper (n + 1)) →L[ℝ]
        Lp ℝ 2 (volume : Measure (ℝ^n)) :=
    (trace n).comp (upperW1pTwoEquivH1 n).toContinuousLinearMap
  have hcomp :
      (lhs : _ → _) ∘ globalTestFunctionToUpperW1pLinear n 2 =
        (rhs : _ → _) ∘ globalTestFunctionToUpperW1pLinear n 2 := by
    funext φ
    simp only [lhs, rhs, ContinuousLinearMap.comp_apply, Function.comp_apply]
    rw [traceLp_smooth]
    change boundaryLpTwoEquivL2 n
        (globalTestFunctionBoundaryLpLinear n 2 φ) =
      trace n
        (upperW1pTwoEquivH1 n
          (globalTestFunctionToUpperW1pLinear n 2 φ))
    rw [boundaryLpTwoEquivL2_globalTestFunction,
      upperW1pTwoEquivH1_globalTestFunction, trace_smooth]
  have hfun :=
    (denseRange_globalTestFunctionToUpperW1pLinear n 2).equalizer
      lhs.continuous rhs.continuous hcomp
  exact congrFun hfun u

end ExponentTwo

end Trace.HalfSpace
end SobolevSpace
