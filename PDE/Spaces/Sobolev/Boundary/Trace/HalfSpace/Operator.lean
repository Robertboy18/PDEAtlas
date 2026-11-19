/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Approximation.Density.Restriction
public import PDE.Spaces.Sobolev.Calculus.Slicing.Normal
import PDE.Spaces.Sobolev.Approximation.Density.ExtensionDomain
import PDE.Spaces.Sobolev.Boundary.Trace.HalfLine.Core
import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator
import PDE.Spaces.Sobolev.GraphSpace.Norms
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Trace on a flat boundary

The model trace theorem on the upper half-space. Using the volume-preserving
tangential-normal decomposition from `Boundary.Geometry.TangentialNormal`, we
integrate the one-dimensional endpoint estimate over the flat boundary and extend
the resulting map to the half-space `H¹` completion.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, pp. 271-273, whose proof starts from the
  trace estimate for `C¹` functions near a flat boundary.
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

variable {n : ℕ} {F : Type*}

/-! ## Integrating one-dimensional endpoint estimates -/

private theorem integral_boundary_sq_le_of_slice_bounds
    (F G : ℝ^n × ℝ → ℝ)
    (hBoundary : Integrable (fun y : ℝ^n ↦ F (y, 0) ^ 2))
    (hF : Integrable (fun p ↦ F p ^ 2)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure))
    (hG : Integrable (fun p ↦ G p ^ 2)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure))
    (hSlice : ∀ y : ℝ^n,
      F (y, 0) ^ 2 ≤
        (∫ t, F (y, t) ^ 2 ∂positiveNormalMeasure) +
          ∫ t, G (y, t) ^ 2 ∂positiveNormalMeasure) :
    (∫ y : ℝ^n, F (y, 0) ^ 2) ≤
      (∫ p, F p ^ 2
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) +
        ∫ p, G p ^ 2
          ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure) := by
  have hFinner : Integrable
      (fun y : ℝ^n ↦ ∫ t, F (y, t) ^ 2 ∂positiveNormalMeasure) :=
    hF.integral_prod_left
  have hGinner : Integrable
      (fun y : ℝ^n ↦ ∫ t, G (y, t) ^ 2 ∂positiveNormalMeasure) :=
    hG.integral_prod_left
  calc
    (∫ y : ℝ^n, F (y, 0) ^ 2) ≤
        ∫ y : ℝ^n,
          ((∫ t, F (y, t) ^ 2 ∂positiveNormalMeasure) +
            ∫ t, G (y, t) ^ 2 ∂positiveNormalMeasure) :=
      integral_mono hBoundary (hFinner.add hGinner) hSlice
    _ = (∫ y : ℝ^n, ∫ t, F (y, t) ^ 2 ∂positiveNormalMeasure) +
          ∫ y : ℝ^n, ∫ t, G (y, t) ^ 2 ∂positiveNormalMeasure :=
      integral_add hFinner hGinner
    _ = (∫ p, F p ^ 2
          ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) +
          ∫ p, G p ^ 2
            ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure) := by
      rw [integral_prod _ hF, integral_prod _ hG]

/-! ## Smooth boundary values -/

/-- Classical boundary restriction to the final-coordinate hyperplane. -/
def smoothBoundaryValue (f : ℝ^(n + 1) → F) (y : ℝ^n) : F :=
  normalSlice f y 0

private theorem smoothBoundaryValue_sq_le_slice_energy
    {f : ℝ^(n + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (y : ℝ^n) :
    smoothBoundaryValue f y ^ 2 ≤
      (∫ t, normalSlice f y t ^ 2 ∂positiveNormalMeasure) +
        ∫ t, normalDerivativeInSplit f (y, t) ^ 2
          ∂positiveNormalMeasure := by
  have h := Trace.HalfLine.endpoint_value_sq_le_integral_add_integral
    (normalSlice_contDiff hf y) (normalSlice_hasCompactSupport hfc y)
  simp_rw [deriv_normalSlice hf y] at h
  simpa [smoothBoundaryValue, positiveNormalMeasure] using h

/-- The classical boundary value of a continuous ambient function is continuous. -/
theorem smoothBoundaryValue_continuous [NormedAddCommGroup F] {f : ℝ^(n + 1) → F}
    (hf : Continuous f) : Continuous (smoothBoundaryValue (n := n) f) := by
  have hp : Continuous (fun y : ℝ^n ↦ ((y, 0) : ℝ^n × ℝ)) :=
    continuous_id.prodMk continuous_const
  change Continuous
    ((fun p : ℝ^n × ℝ ↦ normalSlice f p.1 p.2) ∘
      fun y : ℝ^n ↦ (y, 0))
  exact (normalSlice_product_continuous (n := n) hf).comp hp

/-- Restriction to the flat boundary preserves compact support. -/
theorem smoothBoundaryValue_hasCompactSupport [Zero F] {f : ℝ^(n + 1) → F}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (smoothBoundaryValue (n := n) f) := by
  let K : Set (ℝ^n) :=
    (fun x : ℝ^(n + 1) ↦ (splitTangentialNormal x).1) '' tsupport f
  have hproj : Continuous
      (fun x : ℝ^(n + 1) ↦ (splitTangentialNormal x).1) :=
    continuous_fst.comp
      (tangentialNormalContinuousLinearEquiv (n := n)).continuous
  have hK : IsCompact K := hfc.image hproj
  apply HasCompactSupport.intro hK
  intro y hy
  by_contra hne
  apply hy
  refine ⟨joinTangentialNormal (y, 0), subset_tsupport _ hne, ?_⟩
  simp

private theorem smooth_boundary_integral_sq_le_product_energy
    {f : ℝ^(n + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    (∫ y : ℝ^n, smoothBoundaryValue f y ^ 2) ≤
      (∫ p, normalSlice f p.1 p.2 ^ 2
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) +
      ∫ p, normalDerivativeInSplit f p ^ 2
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure) := by
  have hBoundary : Integrable (fun y : ℝ^n ↦ smoothBoundaryValue f y ^ 2) :=
    (smoothBoundaryValue_continuous (n := n) hf.continuous).pow 2
      |>.integrable_of_hasCompactSupport
        (by
          simpa [pow_two] using
            (smoothBoundaryValue_hasCompactSupport (n := n) hfc).mul_right)
  have hF : Integrable
      (fun p : ℝ^n × ℝ ↦ normalSlice f p.1 p.2 ^ 2)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    (normalSlice_product_continuous (n := n) hf.continuous).pow 2
      |>.integrable_of_hasCompactSupport
        (by
          simpa [pow_two] using
            (normalSlice_product_hasCompactSupport (n := n) hfc).mul_right)
  have hG : Integrable
      (fun p : ℝ^n × ℝ ↦ normalDerivativeInSplit f p ^ 2)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    (normalDerivativeInSplit_continuous (n := n) hf).pow 2
      |>.integrable_of_hasCompactSupport
        (by
          simpa [pow_two] using
            (normalDerivativeInSplit_hasCompactSupport (n := n) hfc).mul_right)
  exact integral_boundary_sq_le_of_slice_bounds
    (n := n)
    (fun p ↦ normalSlice f p.1 p.2)
    (normalDerivativeInSplit f)
    hBoundary hF hG
    (smoothBoundaryValue_sq_le_slice_energy hf hfc)

private theorem integral_normalSlice_sq_eq_integral_upper
    (f : ℝ^(n + 1) → ℝ) :
    (∫ p, normalSlice f p.1 p.2 ^ 2
      ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) =
      ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩), f x ^ 2 := by
  simpa [normalSlice] using
    (integral_joinTangentialNormal_eq_integral_upper
      (n := n) (g := fun x ↦ f x ^ 2))

private theorem integral_normalDerivativeInSplit_sq_eq_integral_upper
    (f : ℝ^(n + 1) → ℝ) :
    (∫ p, normalDerivativeInSplit f p ^ 2
      ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) =
      ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
        (∂[Fin.last n] f) x ^ 2 := by
  simpa [normalDerivativeInSplit] using
    (integral_joinTangentialNormal_eq_integral_upper
      (n := n)
      (g := fun x ↦ (∂[Fin.last n] f) x ^ 2))

/-- The flat-boundary `H¹` trace estimate with constant one: for a compactly supported C¹
function `f`, the integral of the square of its boundary values is at most the integral of
`f ^ 2 + (∂ₙf) ^ 2` over the upper half-space, `∂ₙ` the normal derivative. Compare Evans §5.5,
proof of Theorem 1. -/
theorem smooth_boundary_integral_sq_le_upper_energy
    {f : ℝ^(n + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    (∫ y : ℝ^n, smoothBoundaryValue f y ^ 2) ≤
      (∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩), f x ^ 2) +
      ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
        (∂[Fin.last n] f) x ^ 2 := by
  simpa [integral_normalSlice_sq_eq_integral_upper,
    integral_normalDerivativeInSplit_sq_eq_integral_upper] using
    smooth_boundary_integral_sq_le_product_energy (n := n) hf hfc

/-! ## Completion to the `H¹` trace operator -/

section Completion

variable (n : ℕ)

/-- Globally smooth compactly supported functions in `ℝ^(n+1)`. -/
abbrev GlobalTestFunction (n : ℕ) :=
  GraphSpace.TestFunctionOn (n + 1) (Set.univ : Set (ℝ^(n + 1)))

/-- Restriction of a global test function to the upper half-space, as
an `H¹` function with its classical first derivatives. -/
noncomputable def globalTestFunctionToUpperH1Linear :
    GlobalTestFunction (n := n) →ₗ[ℝ]
      H¹(HalfSpace.upper (n + 1)) :=
  (GraphSpace.restrictCLM (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
      (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _)).toLinearMap.comp
    (GraphSpace.testFunctionToH1Linear
      (n := n + 1) (Ω := Set.univ))

/-- The restricted global construction agrees with the direct smooth Sobolev
construction on the upper half-space. -/
theorem globalTestFunctionToUpperH1Linear_eq_mk
    (φ : GlobalTestFunction (n := n)) :
    globalTestFunctionToUpperH1Linear n φ =
      GraphSpace.mkWkpSpaceOnOfContDiff
        (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
        (Ω := HalfSpace.upper (n + 1))
        (f := φ.1.toFun) φ.1.contDiff φ.1.hasCompactSupport := by
  exact GraphSpace.restrictCLM_mkWkpSpaceOnOfContDiff
    (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _)
    φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport

/-- The flat boundary value of a global test function is square integrable. -/
theorem smoothBoundaryValue_memLp (φ : GlobalTestFunction (n := n)) :
    MemLp (smoothBoundaryValue φ.1.toFun) 2 (volume : Measure (ℝ^n)) :=
  (smoothBoundaryValue_continuous (n := n) φ.1.contDiff.continuous).memLp_of_hasCompactSupport
    (smoothBoundaryValue_hasCompactSupport (n := n) φ.1.hasCompactSupport)

/-- Literal restriction to the flat boundary on global test functions, valued
in `L²(ℝ^n)`. -/
noncomputable def globalTestFunctionBoundaryLinear :
    GlobalTestFunction (n := n) →ₗ[ℝ]
      MeasureTheory.Lp ℝ 2 (volume : Measure (ℝ^n)) where
  toFun φ := (smoothBoundaryValue_memLp n φ).toLp (smoothBoundaryValue φ.1.toFun)
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

/-- The `L²` coercion of the classical boundary restriction agrees almost
everywhere with literal evaluation on the flat boundary. -/
theorem globalTestFunctionBoundaryLinear_apply_ae
    (φ : GlobalTestFunction (n := n)) :
    (globalTestFunctionBoundaryLinear n φ : ℝ^n → ℝ) =ᵐ[
      (volume : Measure (ℝ^n))] smoothBoundaryValue φ.1.toFun :=
  (smoothBoundaryValue_memLp n φ).coeFn_toLp

private theorem upper_base_integral_eq_coordinate_sq
    (φ : GlobalTestFunction n) :
    (∫ x in HalfSpace.upper (n + 1), φ.1.toFun x ^ 2) =
      ‖((globalTestFunctionToUpperH1Linear n φ :
          GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1)))
        (GraphSpace.baseIndex (n + 1) 1))‖ ^ 2 := by
  let U := globalTestFunctionToUpperH1Linear n φ
  let v := ((U : GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1)))
    (GraphSpace.baseIndex (n + 1) 1))
  have hv : (v : ℝ^(n + 1) → ℝ) =ᵐ[domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      φ.1.toFun := by
    change ((((globalTestFunctionToUpperH1Linear n φ :
      H¹(HalfSpace.upper (n + 1))) :
      GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1)))
      (GraphSpace.baseIndex (n + 1) 1) :
        GraphSpace.DerivLp (n + 1) 2 (HalfSpace.upper (n + 1))) : ℝ^(n + 1) → ℝ) =ᵐ[_] _
    rw [globalTestFunctionToUpperH1Linear_eq_mk]
    simpa [v, U, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
        (Ω := HalfSpace.upper (n + 1)) (f := φ.1.toFun)
        φ.1.contDiff φ.1.hasCompactSupport (GraphSpace.baseIndex (n + 1) 1))
  calc
    (∫ x in HalfSpace.upper (n + 1), φ.1.toFun x ^ 2) =
        ∫ x, (v x) ^ 2 ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := by
          apply integral_congr_ae
          filter_upwards [hv] with x hx
          rw [hx]
    _ = ‖v‖ ^ 2 := (MeasureTheory.Lp.norm_sq_eq_integral_sq v).symm

private theorem upper_normal_integral_eq_coordinate_sq
    (φ : GlobalTestFunction n) :
    (∫ x in HalfSpace.upper (n + 1),
        (∂[Fin.last n] φ.1.toFun) x ^ 2) =
      ‖((globalTestFunctionToUpperH1Linear n φ :
          GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1)))
        (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)))‖ ^ 2 := by
  let U := globalTestFunctionToUpperH1Linear n φ
  let v := ((U : GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1)))
    (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)))
  have hv : (v : ℝ^(n + 1) → ℝ) =ᵐ[domainMeasure (n + 1) (HalfSpace.upper (n + 1))]
      fun x ↦ (∂[Fin.last n] φ.1.toFun) x := by
    change ((((globalTestFunctionToUpperH1Linear n φ :
      H¹(HalfSpace.upper (n + 1))) :
      GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1)))
      (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)) :
        GraphSpace.DerivLp (n + 1) 2 (HalfSpace.upper (n + 1))) : ℝ^(n + 1) → ℝ) =ᵐ[_] _
    rw [globalTestFunctionToUpperH1Linear_eq_mk]
    simpa [v, U, GraphSpace.singleDerivIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
        (Ω := HalfSpace.upper (n + 1)) (f := φ.1.toFun)
        φ.1.contDiff φ.1.hasCompactSupport
        (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n)))
  calc
    (∫ x in HalfSpace.upper (n + 1),
        (∂[Fin.last n] φ.1.toFun) x ^ 2) =
        ∫ x, (v x) ^ 2 ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := by
          apply integral_congr_ae
          filter_upwards [hv] with x hx
          rw [hx]
    _ = ‖v‖ ^ 2 := (MeasureTheory.Lp.norm_sq_eq_integral_sq v).symm

private theorem boundary_norm_sq_eq_integral (φ : GlobalTestFunction n) :
    ‖globalTestFunctionBoundaryLinear n φ‖ ^ 2 =
      ∫ y : ℝ^n, smoothBoundaryValue φ.1.toFun y ^ 2 := by
  let v := globalTestFunctionBoundaryLinear n φ
  have hv : (v : ℝ^n → ℝ) =ᵐ[(volume : Measure (ℝ^n))]
      smoothBoundaryValue φ.1.toFun :=
    (smoothBoundaryValue_memLp n φ).coeFn_toLp
  calc
    ‖v‖ ^ 2 = ∫ y, (v y) ^ 2 :=
      MeasureTheory.Lp.norm_sq_eq_integral_sq v
    _ = ∫ y, smoothBoundaryValue φ.1.toFun y ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hv] with y hy
      rw [hy]

private theorem norm_globalTestFunctionBoundaryLinear_le
    (φ : GlobalTestFunction n) :
    ‖globalTestFunctionBoundaryLinear n φ‖ ≤
      ‖globalTestFunctionToUpperH1Linear n φ‖ := by
  let U := (globalTestFunctionToUpperH1Linear n φ :
    GraphSpace.WkpAmbientOn (n + 1) 1 2 (HalfSpace.upper (n + 1)))
  have htrace := smooth_boundary_integral_sq_le_upper_energy
    (n := n) (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport
  have htrace' : ‖globalTestFunctionBoundaryLinear n φ‖ ^ 2 ≤
      ‖U (GraphSpace.baseIndex (n + 1) 1)‖ ^ 2 +
        ‖U (GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n))‖ ^ 2 := by
    calc
      _ = ∫ y : ℝ^n, smoothBoundaryValue φ.1.toFun y ^ 2 :=
        boundary_norm_sq_eq_integral n φ
      _ ≤ (∫ x in HalfSpace.upper (n + 1), φ.1.toFun x ^ 2) +
          ∫ x in HalfSpace.upper (n + 1),
            (∂[Fin.last n] φ.1.toFun) x ^ 2 := by
        simpa using htrace
      _ = _ := by
        rw [upper_base_integral_eq_coordinate_sq n φ,
          upper_normal_integral_eq_coordinate_sq n φ]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact htrace'.trans
    (GraphSpace.base_norm_sq_add_single_norm_sq_le U (Fin.last n))

private theorem exists_smooth_compactSupport_approximation_upperH1
    (u : H¹(HalfSpace.upper (n + 1))) :
    ∃ f_m : ℕ → (ℝ^(n + 1) → ℝ),
    ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
    ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
      Filter.Tendsto
        (fun m ↦
          ‖(GraphSpace.mkWkpSpaceOnOfContDiff
              (n := n + 1) (k := 1) (p := (2 : ℝ≥0∞))
              (Ω := HalfSpace.upper (n + 1))
              (f := f_m m) (hf_m m) (hcs_m m)) - u‖)
        Filter.atTop (nhds 0) := by
  apply GraphSpace.approximation_WkpSpaceOn
    (n := n + 1) (p := (2 : ℝ≥0∞))
    (Approximation.standardMollifier (n + 1)) (by norm_num) 1
    (HalfSpace.upper (n + 1)) u (HalfSpace.isOpen_upper (n := n + 1))
  exact Extension.GraphSpace.HalfSpace.exists_representativeExtensionOperator
    (n := n + 1) (p := (2 : ℝ≥0∞))

/-- Restrictions of global test functions are dense in upper-half-space `H¹`. -/
theorem denseRange_globalTestFunctionToUpperH1Linear :
    DenseRange (globalTestFunctionToUpperH1Linear n) := by
  rw [DenseRange]
  intro u
  rw [mem_closure_iff_seq_limit]
  obtain ⟨f, hf, hcs, hlim⟩ :=
    exists_smooth_compactSupport_approximation_upperH1 n u
  let φ : ℕ → GlobalTestFunction n := fun m ↦
    ⟨_root_.TestFunction.mk (f m) (hf m) (hcs m) (Set.subset_univ _),
      Set.subset_univ _⟩
  refine ⟨fun m ↦ globalTestFunctionToUpperH1Linear n (φ m), ?_, ?_⟩
  · intro m
    exact ⟨φ m, rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hφ_toFun (m : ℕ) : (φ m).1.toFun = f m := by
      funext x
      rfl
    simp_rw [globalTestFunctionToUpperH1Linear_eq_mk, hφ_toFun]
    exact hlim

/-- The continuous trace from `H¹` on the upper half-space in `ℝ^(n + 1)` to `L²(ℝ^n)`
on the flat boundary. -/
noncomputable def trace :
    H¹(HalfSpace.upper (n + 1)) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  (globalTestFunctionBoundaryLinear n).extendOfNorm
    (globalTestFunctionToUpperH1Linear n)

/-- The completed trace agrees with literal boundary restriction on every
globally smooth compactly supported function. -/
theorem trace_smooth (φ : GlobalTestFunction n) :
    trace n (globalTestFunctionToUpperH1Linear n φ) =
      globalTestFunctionBoundaryLinear n φ := by
  exact LinearMap.extendOfNorm_eq
    (denseRange_globalTestFunctionToUpperH1Linear n)
    ⟨1, by simpa using norm_globalTestFunctionBoundaryLinear_le n⟩ φ

/-- Operator estimate for the completed flat trace. -/
theorem norm_trace_le (u : H¹(HalfSpace.upper (n + 1))) :
    ‖trace n u‖ ≤ ‖u‖ := by
  simpa [trace] using LinearMap.norm_extendOfNorm_apply_le
    (denseRange_globalTestFunctionToUpperH1Linear n) 1
    (by simpa using norm_globalTestFunctionBoundaryLinear_le n) u

end Completion

end Trace.HalfSpace
end SobolevSpace
