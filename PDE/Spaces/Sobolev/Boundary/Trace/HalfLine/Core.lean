/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import PDE.Spaces.Sobolev.Approximation.Density.ExtensionDomain
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator
import PDE.Spaces.Sobolev.GraphSpace.Norms
import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Classical endpoint trace on the half-line

For a real `C¹` compactly supported function, integration by parts on `(0, ∞)` gives

`f(0)² = -2 ∫₀^∞ f f'`.

The Cauchy–Schwarz inequality then controls evaluation at the endpoint by the half-line `H¹`
energy: `f(0)² ≤ 2 ‖f‖_{L²} ‖f'‖_{L²} ≤ ‖f‖²_{L²} + ‖f'‖²_{L²}`. This is the one-dimensional trace
inequality, the simplest instance of the fact that `W^{1,p}` functions on an interval are
continuous up to the endpoints with a bound in terms of the `W^{1,p}` norm (Brezis, *Functional
Analysis, Sobolev Spaces and PDE*, Chapter 8). It is the one-dimensional case, with `p = 2`, of
the flat-boundary estimate (1) in step 1 of the proof of Evans, PDE, §5.5, Theorem 1, where a
cutoff `ζ` plays the role of the compact support.

Density turns the estimate into an operator. Restrictions of globally smooth
compactly supported functions are dense in `H¹(0, ∞)`, endpoint evaluation is bounded by `1` on
this dense subspace in the `H¹` norm, and `LinearMap.extendOfNorm` produces the continuous
linear functional `endpointTrace : H¹(0, ∞) → ℝ` of norm at most `1`. It agrees with literal
evaluation at `0` on smooth data and vanishes on `H¹₀(0, ∞)`.

## Main results

* `endpoint_value_sq_eq_neg_two_mul_integral`: the integration-by-parts identity.
* `endpoint_value_sq_le_two_mul_sqrt_integrals`, `endpoint_value_sq_le_integral_add_integral`:
  the multiplicative and additive endpoint bounds.
* `integral_sq_eq_baseCoordinate_norm_sq`, `integral_deriv_sq_eq_firstDerivativeCoordinate_norm_sq`:
  identification of the half-line integrals with the graph-space `H¹` coordinates.
* `denseRange_globalTestFunctionToHalfLineH1Linear`: density of smooth restrictions.
* `endpointTrace`, `endpointTrace_smooth`, `norm_endpointTrace_le`,
  `endpointTrace_eq_zero_of_mem_H10`: the completed trace and its properties.

## Implementation notes

The half-line is `HalfSpace.upper 1 ⊆ ℝ^1`, and the `H¹` space is the graph space
`GraphSpace.H1SpaceOn 1 (HalfSpace.upper 1)`; the two `integral_*` lemmas translate between the
one-dimensional integrals and the norms of the graph-space coordinates.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for Sobolev spaces on an interval.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, pp. 272-273, and step 1 of its proof,
  estimate (1), p. 272.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace
namespace Trace.HalfLine

open MeasureTheory Set
open scoped ENNReal Sobolev

/-- Every `H¹` element on the positive half-line is the `H¹`-norm limit of
restrictions of globally smooth, compactly supported real functions. -/
private theorem exists_smooth_compactSupport_approximation_H1_positiveHalfLine
    (u : H¹(HalfSpace.upper 1)) :
    ∃ f_m : ℕ → (ℝ^1 → ℝ),
    ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
    ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
      Filter.Tendsto
        (fun m ↦
          ‖(GraphSpace.mkWkpSpaceOnOfContDiff
              (n := 1) (k := 1) (p := (2 : ℝ≥0∞))
              (Ω := (HalfSpace.upper 1))
              (f := f_m m) (hf_m m) (hcs_m m)) - u‖)
        Filter.atTop (nhds 0) := by
  apply GraphSpace.approximation_WkpSpaceOn
    (n := 1) (p := (2 : ℝ≥0∞))
    (Approximation.standardMollifier 1) (by norm_num) 1
    (HalfSpace.upper 1) u (HalfSpace.isOpen_upper (n := 1))
  exact Extension.GraphSpace.HalfSpace.exists_representativeExtensionOperator
    (n := 1) (p := (2 : ℝ≥0∞))

/-- The exact integration-by-parts identity behind the endpoint trace estimate. -/
theorem endpoint_value_sq_eq_neg_two_mul_integral
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    f 0 ^ 2 = -2 * ∫ x in Ioi (0 : ℝ), f x * deriv f x := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hsqSmooth : ContDiff ℝ 1 (fun x ↦ f x ^ 2) := hf.pow 2
  have hsqSupport : HasCompactSupport (fun x ↦ f x ^ 2) := by
    have hfc' := hfc
    rw [hasCompactSupport_iff_eventuallyEq] at hfc' ⊢
    filter_upwards [hfc'] with x hx
    simp [hx]
  have hderivSq :
      deriv (fun x ↦ f x ^ 2) = fun x ↦ 2 * (f x * deriv f x) := by
    funext x
    rw [show deriv (fun y ↦ f y ^ 2) x = deriv f x * f x + f x * deriv f x by
      simpa [pow_two] using deriv_fun_mul (hdiff x) (hdiff x)]
    ring
  have hftc := HasCompactSupport.integral_Ioi_deriv_eq
    (f := fun x ↦ f x ^ 2) hsqSmooth hsqSupport (0 : ℝ)
  rw [hderivSq, MeasureTheory.integral_const_mul] at hftc
  linarith

/--
Classical multiplicative endpoint trace inequality on the half-line:

`f(0)² ≤ 2 ‖f‖_{L²(0,∞)} ‖f'‖_{L²(0,∞)}`.
-/
theorem endpoint_value_sq_le_two_mul_sqrt_integrals
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    f 0 ^ 2 ≤
      2 * Real.sqrt (∫ x in Ioi (0 : ℝ), f x ^ 2) *
        Real.sqrt (∫ x in Ioi (0 : ℝ), (deriv f x) ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hderivContinuous : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfLp : MemLp f 2 μ :=
    hf.continuous.memLp_of_hasCompactSupport (μ := μ) hfc
  have hderivLp : MemLp (deriv f) 2 μ :=
    hderivContinuous.memLp_of_hasCompactSupport (μ := μ) hfc.deriv
  have hcs := MeasureTheory.integral_abs_mul_le_sqrt_integral_sq hfLp hderivLp
  have habs :
      |∫ x in Ioi (0 : ℝ), f x * deriv f x| ≤
        ∫ x in Ioi (0 : ℝ), |f x * deriv f x| := by
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun x ↦ f x * deriv f x))
  calc
    f 0 ^ 2 = -2 * ∫ x in Ioi (0 : ℝ), f x * deriv f x :=
      endpoint_value_sq_eq_neg_two_mul_integral hf hfc
    _ ≤ 2 * |∫ x in Ioi (0 : ℝ), f x * deriv f x| := by
      rw [show -2 * (∫ x in Ioi (0 : ℝ), f x * deriv f x) =
        2 * (-(∫ x in Ioi (0 : ℝ), f x * deriv f x)) by ring]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by norm_num)
    _ ≤ 2 * ∫ x in Ioi (0 : ℝ), |f x * deriv f x| := by
      exact mul_le_mul_of_nonneg_left habs (by norm_num)
    _ ≤ 2 * (Real.sqrt (∫ x in Ioi (0 : ℝ), f x ^ 2) *
          Real.sqrt (∫ x in Ioi (0 : ℝ), (deriv f x) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = 2 * Real.sqrt (∫ x in Ioi (0 : ℝ), f x ^ 2) *
          Real.sqrt (∫ x in Ioi (0 : ℝ), (deriv f x) ^ 2) := by ring

/-- The additive `H¹` endpoint trace bound with explicit constant one. -/
theorem endpoint_value_sq_le_integral_add_integral
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    f 0 ^ 2 ≤
      (∫ x in Ioi (0 : ℝ), f x ^ 2) +
        ∫ x in Ioi (0 : ℝ), (deriv f x) ^ 2 := by
  let X : ℝ := ∫ x in Ioi (0 : ℝ), f x ^ 2
  let Y : ℝ := ∫ x in Ioi (0 : ℝ), (deriv f x) ^ 2
  have hX : 0 ≤ X := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hY : 0 ≤ Y := integral_nonneg (fun _ ↦ sq_nonneg _)
  have htrace : f 0 ^ 2 ≤ 2 * Real.sqrt X * Real.sqrt Y := by
    simpa [X, Y] using endpoint_value_sq_le_two_mul_sqrt_integrals hf hfc
  have hsqrtX : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
  have hsqrtY : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY
  change f 0 ^ 2 ≤ X + Y
  nlinarith [sq_nonneg (Real.sqrt X - Real.sqrt Y)]

/-! ## The completed endpoint trace -/

/-- Restrict a global test function to the positive half-line and equip it with its
classical first weak derivative. -/
noncomputable def globalTestFunctionToHalfLineH1Linear :
    GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1)) →ₗ[ℝ]
      H¹(HalfSpace.upper 1) :=
  (GraphSpace.restrictCLM (n := 1) (k := 1) (p := (2 : ℝ≥0∞))
      (HalfSpace.measurableSet_upper (n := 1)) (Set.subset_univ _)).toLinearMap.comp
    (GraphSpace.testFunctionToH1Linear (n := 1) (Ω := Set.univ))

/-- Restriction of the globally constructed Sobolev element agrees with the direct
`mkWkpSpaceOnOfContDiff` construction on the half-line. -/
theorem globalTestFunctionToHalfLineH1Linear_eq_mk
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) :
    globalTestFunctionToHalfLineH1Linear φ =
      GraphSpace.mkWkpSpaceOnOfContDiff
        (n := 1) (k := 1) (p := (2 : ℝ≥0∞))
        (Ω := (HalfSpace.upper 1))
        (f := φ.1.toFun) φ.1.contDiff φ.1.hasCompactSupport := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  apply MeasureTheory.Lp.ext
  have hrestrict := GraphSpace.restrictCLM_apply_ae
    (n := 1) (k := 1) (p := (2 : ℝ≥0∞))
    (HalfSpace.measurableSet_upper (n := 1)) (Set.subset_univ _)
    (GraphSpace.testFunctionToH1Linear (n := 1) (Ω := Set.univ) φ) a
  have hglobal := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
    (n := 1) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Set.univ)
    (f := φ.1.toFun) φ.1.contDiff φ.1.hasCompactSupport a
  have hhalf := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
    (n := 1) (k := 1) (p := (2 : ℝ≥0∞))
    (Ω := (HalfSpace.upper 1)) (f := φ.1.toFun)
    φ.1.contDiff φ.1.hasCompactSupport a
  have hres :
      ((((globalTestFunctionToHalfLineH1Linear φ :
          H¹(HalfSpace.upper 1)) :
          GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1)) a :
          GraphSpace.DerivLp 1 2 (HalfSpace.upper 1)) : ℝ^1 → ℝ) =ᵐ[
        domainMeasure 1 (HalfSpace.upper 1)]
      ((((GraphSpace.testFunctionToH1Linear (n := 1) (Ω := Set.univ)
          φ : W^{1,2}(ℝ^1)) :
          GraphSpace.WkpAmbientOn 1 1 2 Set.univ) a : GraphSpace.DerivLp 1 2 Set.univ) :
          ℝ^1 → ℝ) := by
    simpa [globalTestFunctionToHalfLineH1Linear] using hrestrict
  have hglobal_restrict :
      ((((GraphSpace.testFunctionToH1Linear (n := 1) (Ω := Set.univ)
          φ : W^{1,2}(ℝ^1)) :
          GraphSpace.WkpAmbientOn 1 1 2 Set.univ) a : GraphSpace.DerivLp 1 2 Set.univ) :
          ℝ^1 → ℝ) =ᵐ[domainMeasure 1 (HalfSpace.upper 1)]
        fun x ↦ iteratedPartialDeriv (n := 1) a.toList φ.1.toFun x :=
    MeasureTheory.ae_restrict_of_ae (s := (HalfSpace.upper 1)) (by
      have hglobal' :
          ((((GraphSpace.testFunctionToH1Linear (n := 1) (Ω := Set.univ)
              φ : W^{1,2}(ℝ^1)) :
              GraphSpace.WkpAmbientOn 1 1 2 Set.univ) a :
              GraphSpace.DerivLp 1 2 Set.univ) : ℝ^1 → ℝ) =ᵐ[(volume : Measure (ℝ^1))]
            fun x ↦ iteratedPartialDeriv (n := 1) a.toList φ.1.toFun x := by
        rw [GraphSpace.testFunctionToH1Linear_apply]
        simpa [GraphSpace.testFunctionToH1] using hglobal
      filter_upwards [hglobal'] with x hx
      exact hx)
  exact hres.trans (hglobal_restrict.trans hhalf.symm)

/-- Evaluation at the endpoint on global test functions. -/
def globalTestFunctionEndpointEvalLinear :
    GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1)) →ₗ[ℝ] ℝ where
  toFun φ := φ.1.toFun 0
  map_add' := by simp
  map_smul' := by simp

private theorem restricted_measurePreserving :
    MeasurePreserving (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
      (volume.restrict (Ioi (0 : ℝ)))
      (domainMeasure 1 (HalfSpace.upper 1)) := by
  have h :=
    ((PiLp.volume_preserving_toLp (Fin 1)).comp
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _)).restrict_preimage
      (HalfSpace.measurableSet_upper (n := 1))
  have hpreimage :
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm ⁻¹'
          (HalfSpace.upper 1) = Ioi (0 : ℝ) := by
    ext t
    simp [HalfSpace.upper, PDE.Common.lastIndex]
  have hfun :
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm =
        WithLp.toLp 2 ∘ ⇑(MeasurableEquiv.funUnique (Fin 1) ℝ).symm := by
    ext t
    simp [PiLp.equivOfUnique_symm_apply]
  rw [hfun] at hpreimage ⊢
  rwa [hpreimage] at h

/-- The one-dimensional pullback identifies the half-line `L²` energy of a
global test function with the squared norm of its base graph-space coordinate. -/
theorem integral_sq_eq_baseCoordinate_norm_sq
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) :
    (∫ t in Ioi (0 : ℝ),
        (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t ^ 2) =
      ‖((globalTestFunctionToHalfLineH1Linear φ :
          GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
        (GraphSpace.baseIndex 1 1))‖ ^ 2 := by
  let U := globalTestFunctionToHalfLineH1Linear φ
  let v := ((U : GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
    (GraphSpace.baseIndex 1 1))
  have hv : (v : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 (HalfSpace.upper 1)]
      φ.1.toFun := by
    change ((((globalTestFunctionToHalfLineH1Linear φ :
      H¹(HalfSpace.upper 1)) :
      GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
      (GraphSpace.baseIndex 1 1) : GraphSpace.DerivLp 1 2
        (HalfSpace.upper 1)) : ℝ^1 → ℝ) =ᵐ[_] _
    rw [globalTestFunctionToHalfLineH1Linear_eq_mk]
    simpa [v, U, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := 1) (k := 1) (p := (2 : ℝ≥0∞))
        (Ω := (HalfSpace.upper 1)) (f := φ.1.toFun)
        φ.1.contDiff φ.1.hasCompactSupport (GraphSpace.baseIndex 1 1))
  calc
    (∫ t in Ioi (0 : ℝ),
        (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t ^ 2) =
        ∫ x, φ.1.toFun x ^ 2 ∂domainMeasure 1 (HalfSpace.upper 1) := by
          simpa [Function.comp_def] using
            (restricted_measurePreserving.integral_comp
              (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph.measurableEmbedding
              (fun x ↦ φ.1.toFun x ^ 2))
    _ = ∫ x, (v x) ^ 2 ∂domainMeasure 1 (HalfSpace.upper 1) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = ‖v‖ ^ 2 := (MeasureTheory.Lp.norm_sq_eq_integral_sq v).symm

/-- The one-dimensional pullback identifies the derivative `L²` energy with
the squared norm of the unique first-derivative graph-space coordinate. -/
theorem integral_deriv_sq_eq_firstDerivativeCoordinate_norm_sq
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) :
    (∫ t in Ioi (0 : ℝ),
        (deriv (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t) ^ 2) =
      ‖((globalTestFunctionToHalfLineH1Linear φ :
          GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
        (GraphSpace.singleDerivIndex (n := 1) 0))‖ ^ 2 := by
  let U := globalTestFunctionToHalfLineH1Linear φ
  let v := ((U : GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
    (GraphSpace.singleDerivIndex (n := 1) 0))
  let d : ℝ^1 → ℝ := fun x ↦ (∂[0] φ.1.toFun) x
  have hv : (v : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 (HalfSpace.upper 1)] d := by
    change ((((globalTestFunctionToHalfLineH1Linear φ :
      H¹(HalfSpace.upper 1)) :
      GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
      (GraphSpace.singleDerivIndex (n := 1) 0) : GraphSpace.DerivLp 1 2
        (HalfSpace.upper 1)) : ℝ^1 → ℝ) =ᵐ[_] d
    rw [globalTestFunctionToHalfLineH1Linear_eq_mk]
    simpa [v, U, d, GraphSpace.singleDerivIndex_toList,
      iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := 1) (k := 1) (p := (2 : ℝ≥0∞))
        (Ω := (HalfSpace.upper 1)) (f := φ.1.toFun)
        φ.1.contDiff φ.1.hasCompactSupport
        (GraphSpace.singleDerivIndex (n := 1) 0))
  calc
    (∫ t in Ioi (0 : ℝ),
        (deriv (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t) ^ 2) =
        ∫ t in Ioi (0 : ℝ),
          d ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t) ^ 2 := by
            apply integral_congr_ae
            filter_upwards [] with t
            rw [PDE.deriv_comp_equivOfUnique_symm
              φ.1.toFun t (φ.1.contDiff.differentiable (by simp)).differentiableAt]
    _ = ∫ x, d x ^ 2 ∂domainMeasure 1 (HalfSpace.upper 1) := by
      simpa using
        (restricted_measurePreserving.integral_comp
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph.measurableEmbedding
          (fun x ↦ d x ^ 2))
    _ = ∫ x, (v x) ^ 2 ∂domainMeasure 1 (HalfSpace.upper 1) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = ‖v‖ ^ 2 := (MeasureTheory.Lp.norm_sq_eq_integral_sq v).symm

/-- The endpoint evaluation is bounded by the restricted half-line `H¹` norm. -/
private theorem norm_globalTestFunctionEndpointEvalLinear_le
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) :
    ‖globalTestFunctionEndpointEvalLinear φ‖ ≤
      ‖globalTestFunctionToHalfLineH1Linear φ‖ := by
  let f : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    φ.1.contDiff.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.contDiff
  have hfc : HasCompactSupport f :=
    φ.1.hasCompactSupport.comp_homeomorph
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph
  have htrace := endpoint_value_sq_le_integral_add_integral
    (f := f) (hf.of_le (by simp)) hfc
  have hzero : (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm 0 = 0 := by
    ext i
    fin_cases i
    simp [PiLp.equivOfUnique_symm_apply]
  have hsq : (globalTestFunctionEndpointEvalLinear φ) ^ 2 ≤
      ‖globalTestFunctionToHalfLineH1Linear φ‖ ^ 2 := by
    rw [show ‖globalTestFunctionToHalfLineH1Linear φ‖ ^ 2 =
        ‖((globalTestFunctionToHalfLineH1Linear φ :
            GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
          (GraphSpace.baseIndex 1 1))‖ ^ 2 +
        ‖((globalTestFunctionToHalfLineH1Linear φ :
            GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
          (GraphSpace.singleDerivIndex (n := 1) 0))‖ ^ 2 by
      simpa using
        (GraphSpace.ambient_norm_sq_eq_base_sq_add_sum_deriv_sq
          (globalTestFunctionToHalfLineH1Linear φ :
            GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))),
      ← integral_sq_eq_baseCoordinate_norm_sq φ,
      ← integral_deriv_sq_eq_firstDerivativeCoordinate_norm_sq φ]
    simpa [globalTestFunctionEndpointEvalLinear, f, hzero] using htrace
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    simpa [Real.norm_eq_abs, sq_abs] using hsq)

/-- Restrictions of global test functions are dense in the half-line `H¹` space. -/
theorem denseRange_globalTestFunctionToHalfLineH1Linear :
    DenseRange globalTestFunctionToHalfLineH1Linear := by
  rw [DenseRange]
  intro u
  rw [mem_closure_iff_seq_limit]
  obtain ⟨f, hf, hcs, hlim⟩ :=
    exists_smooth_compactSupport_approximation_H1_positiveHalfLine u
  let φ : ℕ → GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1)) := fun m ↦
    ⟨_root_.TestFunction.mk (f m) (hf m) (hcs m) (Set.subset_univ _),
      Set.subset_univ _⟩
  refine ⟨fun m ↦ globalTestFunctionToHalfLineH1Linear (φ m), ?_, ?_⟩
  · intro m
    exact ⟨φ m, rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hφ_toFun (m : ℕ) : (φ m).1.toFun = f m := by
      funext x
      rfl
    simp_rw [globalTestFunctionToHalfLineH1Linear_eq_mk, hφ_toFun]
    exact hlim

/-- The continuous linear endpoint trace on the positive half-line. -/
noncomputable def endpointTrace :
    H¹(HalfSpace.upper 1) →L[ℝ] ℝ :=
  globalTestFunctionEndpointEvalLinear.extendOfNorm
    globalTestFunctionToHalfLineH1Linear

/-- The completed trace agrees with literal endpoint evaluation on every globally
smooth compactly supported function. -/
theorem endpointTrace_smooth (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) :
    endpointTrace (globalTestFunctionToHalfLineH1Linear φ) = φ.1.toFun 0 := by
  exact LinearMap.extendOfNorm_eq
    denseRange_globalTestFunctionToHalfLineH1Linear
    ⟨1, by simpa using norm_globalTestFunctionEndpointEvalLinear_le⟩ φ

/-- The endpoint trace has operator bound one. -/
theorem norm_endpointTrace_le (u :
    H¹(HalfSpace.upper 1)) :
    ‖endpointTrace u‖ ≤ ‖u‖ := by
  change
    ‖(globalTestFunctionEndpointEvalLinear.extendOfNorm
      globalTestFunctionToHalfLineH1Linear) u‖ ≤ ‖u‖
  simpa only [one_mul] using LinearMap.norm_extendOfNorm_apply_le
    denseRange_globalTestFunctionToHalfLineH1Linear 1
    (by intro φ; simpa only [one_mul] using
      norm_globalTestFunctionEndpointEvalLinear_le φ) u

/-- Every element of `H¹₀(0,∞)` has zero completed endpoint trace.

This is the closure direction of the standard characterization
`H¹₀(0,∞) = ker(trace₀)`: compactly supported smooth functions on the open
half-line vanish at the endpoint, and the trace kernel is closed because the
trace is continuous. -/
theorem endpointTrace_eq_zero_of_mem_H10
    (u : H¹(HalfSpace.upper 1))
    (hu : u ∈ (GraphSpace.h10SubmoduleOn
      (n := 1) (Ω := (HalfSpace.upper 1))).toSubmodule) :
    endpointTrace u = 0 := by
  let Z : Set (H¹(HalfSpace.upper 1)) :=
    {v | endpointTrace v = 0}
  have hZclosed : IsClosed Z := by
    exact isClosed_eq endpointTrace.continuous continuous_const
  have hcore :
      ((GraphSpace.ccSmoothSubmoduleOn
        (n := 1) (Ω := (HalfSpace.upper 1)) :
          Submodule ℝ (H¹(HalfSpace.upper 1))) :
        Set (H¹(HalfSpace.upper 1))) ⊆ Z := by
    intro v hv
    rcases hv with ⟨φ, rfl⟩
    let φg : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1)) := ⟨φ.1, Set.subset_univ _⟩
    have hφ0 : φ.1.toFun 0 = 0 := by
      by_contra hne
      have hmem : (0 : ℝ^1) ∈ (HalfSpace.upper 1) :=
        φ.2 (subset_tsupport φ.1.toFun hne)
      simp [HalfSpace.upper, PDE.Common.lastIndex] at hmem
    have hmap :
        GraphSpace.testFunctionToH1Linear
            (n := 1) (Ω := (HalfSpace.upper 1)) φ =
          globalTestFunctionToHalfLineH1Linear φg := by
      rw [globalTestFunctionToHalfLineH1Linear_eq_mk]
      rfl
    change endpointTrace
      (GraphSpace.testFunctionToH1Linear
        (n := 1) (Ω := (HalfSpace.upper 1)) φ) = 0
    rw [hmap, endpointTrace_smooth]
    exact hφ0
  change u ∈ Z
  exact closure_minimal hcore hZclosed hu


end Trace.HalfLine
end SobolevSpace
