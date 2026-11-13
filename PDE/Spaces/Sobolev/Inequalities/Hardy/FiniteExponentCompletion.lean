/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.HalfLine
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.Spaces.Sobolev.Inequalities.Hardy.Lp

/-!
# Completed Finite-Exponent Hardy Operator

For every real `p > 1`, the classical smooth half-line Hardy inequality, proved in `Hardy.Lp`,
extends to the completed supported-core space `W^{1,p}_0(0,∞)`.

The construction proceeds in three steps:

1. realize the literal quotient `u(x) / x` as an `Lᵖ` function on the smooth
   compactly supported core;
2. prove the operator estimate with constant `p / (p - 1)`;
3. extend the quotient map uniquely by density to the completed zero-trace
   space.

The final estimate depends only on the weak first-derivative coordinate.

## Main results

* `hardyLpTestQuotient`, `hardyLpTestQuotientLinear`: `u ↦ u / x` on the smooth core, as an
  element of `Lᵖ(ℝ)` and as a linear map.
* `norm_deriv_pullback_eq_testFunctionToWkp_coordinate`: the `Lᵖ` norm of the derivative of the
  one-dimensional pullback is the norm of the first-derivative coordinate of the Sobolev bundle.
* `hardyLpTestQuotientLinear_bound_deriv`, `hardyLpTestQuotientLinear_bound`: the core estimate
  with constant `p/(p-1)`, against the derivative coordinate and against the graph norm.
* `hardyW1p0Quotient`: the bounded extension to `Wkp0SpaceOn 1 1 (ofReal p) (HalfSpace.upper 1)`.
* `norm_hardyW1p0Quotient_le_deriv`: `‖hardyW1p0Quotient p hp u‖ₚ ≤ (p/(p-1)) ‖u'‖ₚ` on the
  completed space, with `u'` the weak-derivative coordinate of `u`.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter IX, for the one-dimensional Hardy inequality.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Hardy

open Set
open MeasureTheory
open scoped ENNReal Sobolev

private theorem integral_abs_rpow_eq_integral_Ioi_of_tsupport_subset
    {u : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    (∫ x : ℝ, |u x| ^ p) =
      ∫ x in Set.Ioi (0 : ℝ), |u x| ^ p :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hpos h), abs_zero,
      Real.zero_rpow hp.ne']).symm

/--
The literal Hardy quotient `u(x) / x` of a smooth test function on the
positive half-line, represented as an ambient `Lᵖ(ℝ)` class.
-/
noncomputable def hardyLpTestQuotient
    (p : ℝ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    Lp ℝ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  let u : ℝ → ℝ :=
    φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  (memLp_div_id_of_hasCompactSupport_at
    (p := ENNReal.ofReal p)
    (testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous
    (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
    (testFunctionOn_positiveHalfLine_comp_tsupport φ)).toLp
      (fun r ↦ u r / r)

/--
The test-core quotient is represented almost everywhere by literal division
of the pulled-back one-dimensional test function by the coordinate.
-/
theorem hardyLpTestQuotient_apply_ae
    (p : ℝ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    ((hardyLpTestQuotient p φ :
      Lp ℝ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume]
        fun r ↦
          φ.1.toFun
              ((PiLp.equivOfUnique 2 ℝ
                (fun _ : Fin 1 ↦ ℝ)).symm r) / r := by
  exact (memLp_div_id_of_hasCompactSupport_at
    (p := ENNReal.ofReal p)
    (testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous
    (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
    (testFunctionOn_positiveHalfLine_comp_tsupport φ)).coeFn_toLp

/-- The Hardy quotient as a linear map on the smooth compactly supported core. -/
noncomputable def hardyLpTestQuotientLinear (p : ℝ) :
    GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1) →ₗ[ℝ]
      Lp ℝ (ENNReal.ofReal p) (volume : Measure ℝ) where
  toFun := hardyLpTestQuotient p
  map_add' φ ψ := by
    refine Lp.ext ?_
    filter_upwards [hardyLpTestQuotient_apply_ae p (φ + ψ), hardyLpTestQuotient_apply_ae p φ,
      hardyLpTestQuotient_apply_ae p ψ,
      Lp.coeFn_add (hardyLpTestQuotient p φ) (hardyLpTestQuotient p ψ)] with r hrs hrφ hrψ hradd
    rw [hrs, hradd, Pi.add_apply, hrφ, hrψ, ← add_div]
    rfl
  map_smul' c φ := by
    refine Lp.ext ?_
    filter_upwards [hardyLpTestQuotient_apply_ae p (c • φ), hardyLpTestQuotient_apply_ae p φ,
      Lp.coeFn_smul ((RingHom.id ℝ) c) (hardyLpTestQuotient p φ)] with r hrs hrφ hrsmul
    rw [hrs, hrsmul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, hrφ, ← mul_div_assoc]
    rfl

section FiniteExponent

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/--
The `Lᵖ` norm of the ordinary derivative of the one-dimensional pullback is
the norm of the first weak-derivative coordinate in the Sobolev bundle.
-/
theorem norm_deriv_pullback_eq_testFunctionToWkp_coordinate
    (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    let u : ℝ → ℝ :=
      φ.1.toFun ∘
        (PiLp.equivOfUnique 2 ℝ
          (fun _ : Fin 1 ↦ ℝ)).symm
    let hd : MemLp (deriv u) (ENNReal.ofReal p)
        (volume : Measure ℝ) :=
      ((testFunctionOn_positiveHalfLine_comp_contDiff φ).of_le
        (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).continuous_deriv
        (by norm_num) |>.memLp_of_hasCompactSupport
          (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ).deriv
    ‖hd.toLp (deriv u)‖ =
      ‖((GraphSpace.testFunctionToWkp
          (n := 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper 1) φ :
            GraphSpace.WkpAmbientOn 1 1
              (ENNReal.ofReal p) (HalfSpace.upper 1))
        (GraphSpace.singleDerivIndex (n := 1) 0))‖ := by
  dsimp only
  rw [Lp.norm_toLp, GraphSpace.norm_testFunctionToWkp_coordinate_eq_eLpNorm_toReal]
  congr 1
  let d : ℝ^1 → ℝ := fun x ↦ (∂[0] φ.1.toFun) x
  have hdmeas : AEStronglyMeasurable d (volume : Measure (ℝ^1)) :=
    (PDE.contDiff_top_partialDeriv φ.1.contDiff).continuous.aestronglyMeasurable
  have hdsupp : Function.support d ⊆ HalfSpace.upper 1 := (subset_tsupport d).trans
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).trans φ.2)
  calc eLpNorm (deriv (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm))
        (ENNReal.ofReal p) volume
      = eLpNorm (d ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) (ENNReal.ofReal p)
          volume :=
        eLpNorm_congr_ae (ae_of_all _ fun t ↦ PDE.deriv_comp_equivOfUnique_symm _ t
          (φ.1.contDiff.differentiable (by simp)).differentiableAt)
    _ = eLpNorm d (ENNReal.ofReal p) volume :=
        eLpNorm_comp_measurePreserving hdmeas ((PiLp.volume_preserving_toLp (Fin 1)).comp
          ((volume_preserving_funUnique (Fin 1) ℝ).symm _))
    _ = eLpNorm d (ENNReal.ofReal p) (domainMeasure 1 (HalfSpace.upper 1)) :=
        (eLpNorm_restrict_eq_of_support_subset hdmeas hdsupp).symm
    _ = _ := eLpNorm_congr_ae (ae_of_all _ fun x ↦ by
        simp [d, GraphSpace.singleDerivIndex_toList, iteratedPartialDeriv])

/--
The Hardy estimate on the smooth core, expressed using only the first
Sobolev derivative coordinate.
-/
theorem hardyLpTestQuotientLinear_bound_deriv
    (hp : 1 < p)
    (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    ‖hardyLpTestQuotientLinear p φ‖ ≤
      (p / (p - 1)) *
        ‖((GraphSpace.testFunctionToWkp
            (n := 1) (k := 1) (p := ENNReal.ofReal p)
            (Ω := HalfSpace.upper 1) φ :
              GraphSpace.WkpAmbientOn 1 1
                (ENNReal.ofReal p) (HalfSpace.upper 1))
          (GraphSpace.singleDerivIndex (n := 1) 0))‖ := by
  let u : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hu1 : ContDiff ℝ 1 u := (testFunctionOn_positiveHalfLine_comp_contDiff φ).of_le
    (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  let hq := memLp_div_id_of_hasCompactSupport_at (p := ENNReal.ofReal p)
    (testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous
    (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
    (testFunctionOn_positiveHalfLine_comp_tsupport φ)
  let hd : MemLp (deriv u) (ENNReal.ofReal p) (volume : Measure ℝ) :=
    hu1.continuous_deriv (by norm_num) |>.memLp_of_hasCompactSupport
      (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ).deriv
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hconst : 0 < p / (p - 1) := by positivity
  have hqpos : tsupport (fun x ↦ u x / x) ⊆ Set.Ioi (0 : ℝ) := by
    refine (closure_minimal ?_ (isClosed_tsupport u)).trans
      (testFunctionOn_positiveHalfLine_comp_tsupport φ)
    exact fun x hx ↦ subset_tsupport u fun hux ↦ hx (by simp [hux])
  have hratio : ∀ x ∈ Set.Ioi (0 : ℝ), |u x / x| ^ p = |u x| ^ p * x ^ (-p) := fun x hx ↦ by
    rw [abs_div, abs_of_pos hx, Real.div_rpow (abs_nonneg _) hx.le, Real.rpow_neg hx.le,
      div_eq_mul_inv]
  -- The one-dimensional Hardy inequality for `p`-th powers of the two norms.
  have hpow : ‖hq.toLp (fun x ↦ u x / x)‖ ^ p ≤ (p / (p - 1)) ^ p * ‖hd.toLp (deriv u)‖ ^ p := by
    rw [norm_toLp_rpow_eq_integral_abs hp0 hq, norm_toLp_rpow_eq_integral_abs hp0 hd,
      integral_abs_rpow_eq_integral_Ioi_of_tsupport_subset hp0 hqpos,
      integral_abs_rpow_eq_integral_Ioi_of_tsupport_subset hp0
        ((tsupport_deriv_subset (f := u)).trans (testFunctionOn_positiveHalfLine_comp_tsupport φ)),
      setIntegral_congr_fun measurableSet_Ioi hratio]
    exact hardy_Ioi_lp_of_hasCompactSupport hp hu1
      (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
      (testFunctionOn_positiveHalfLine_comp_tsupport φ)
  change ‖hq.toLp (fun x ↦ u x / x)‖ ≤ _
  rw [← norm_deriv_pullback_eq_testFunctionToWkp_coordinate φ]
  refine (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hconst.le (norm_nonneg _)) hp0).mp ?_
  rwa [Real.mul_rpow hconst.le (norm_nonneg _)]

/--
The smooth-core Hardy quotient is bounded by the full `W^{1,p}` graph norm.
This is the bound used to extend the map to the completed zero-trace space.
-/
theorem hardyLpTestQuotientLinear_bound
    (hp : 1 < p)
    (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    ‖hardyLpTestQuotientLinear p φ‖ ≤
      (p / (p - 1)) *
        ‖GraphSpace.testFunctionToWkp0
          (n := 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper 1) φ‖ := by
  have hcoord :
      ‖((GraphSpace.testFunctionToWkp
          (n := 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper 1) φ :
            GraphSpace.WkpAmbientOn 1 1
              (ENNReal.ofReal p) (HalfSpace.upper 1))
        (GraphSpace.singleDerivIndex (n := 1) 0))‖ ≤
        ‖GraphSpace.testFunctionToWkp0
          (n := 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper 1) φ‖ := by
    simpa [GraphSpace.testFunctionToWkp0_coe] using
      (PiLp.norm_apply_le
        (x := (GraphSpace.testFunctionToWkp
          (n := 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper 1) φ :
            GraphSpace.WkpAmbientOn 1 1
              (ENNReal.ofReal p) (HalfSpace.upper 1)))
        (i := GraphSpace.singleDerivIndex (n := 1) 0))
  exact (hardyLpTestQuotientLinear_bound_deriv hp φ).trans
    (mul_le_mul_of_nonneg_left hcoord (by positivity))

/--
The Hardy quotient operator on the completed finite-exponent zero-trace
space. It is the unique bounded extension of `u ↦ u/x` from smooth compactly
supported functions in the positive half-line.
-/
noncomputable def hardyW1p0Quotient (p : ℝ) (_hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    W₀^{1,(ENNReal.ofReal p)}((HalfSpace.upper 1)) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  (hardyLpTestQuotientLinear p).extendOfNorm
    (GraphSpace.testFunctionToWkp0Linear
      (n := 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper 1))

/--
On a smooth compactly supported test function, the completed operator agrees
with literal division by the half-line coordinate.
-/
theorem hardyW1p0Quotient_testFunction
    (hp : 1 < p)
    (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    hardyW1p0Quotient p hp
        (GraphSpace.testFunctionToWkp0
          (n := 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper 1) φ) =
      hardyLpTestQuotient p φ := by
  exact LinearMap.extendOfNorm_eq
    (GraphSpace.denseRange_testFunctionToWkp0Linear
      (n := 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper 1))
    ⟨p / (p - 1), hardyLpTestQuotientLinear_bound hp⟩ φ

/-- Graph-norm bound for the completed finite-exponent Hardy quotient. -/
theorem norm_hardyW1p0Quotient_le
    (hp : 1 < p)
    (u : W₀^{1,(ENNReal.ofReal p)}((HalfSpace.upper 1))) :
    ‖hardyW1p0Quotient p hp u‖ ≤
      (p / (p - 1)) * ‖u‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (GraphSpace.denseRange_testFunctionToWkp0Linear
      (n := 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper 1))
    (p / (p - 1)) (hardyLpTestQuotientLinear_bound hp) u

/--
Hardy inequality on the positive half-line for the completed operator: for `p > 1` and
`u ∈ W^{1,p}_0`, `‖hardyW1p0Quotient p hp u‖ₚ ≤ (p / (p - 1)) ‖u'‖ₚ`, with `u'` the weak-derivative
coordinate of `u`. The operator `hardyW1p0Quotient` is the bounded extension of `u ↦ u / x` from
the test functions. Optimality of the constant `p / (p - 1)` is not proved here.
-/
theorem norm_hardyW1p0Quotient_le_deriv
    (hp : 1 < p)
    (u : W₀^{1,(ENNReal.ofReal p)}((HalfSpace.upper 1))) :
    ‖hardyW1p0Quotient p hp u‖ ≤
      (p / (p - 1)) *
        ‖(((u : W^{1,ENNReal.ofReal p}(HalfSpace.upper 1)) :
              GraphSpace.WkpAmbientOn 1 1
                (ENNReal.ofReal p) (HalfSpace.upper 1))
          (GraphSpace.singleDerivIndex (n := 1) 0))‖ := by
  refine DenseRange.induction_on
    (GraphSpace.denseRange_testFunctionToWkp0Linear
      (n := 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper 1)) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro φ
    change
      ‖hardyW1p0Quotient p hp
          (GraphSpace.testFunctionToWkp0
            (n := 1) (k := 1) (p := ENNReal.ofReal p)
            (Ω := HalfSpace.upper 1) φ)‖ ≤ _
    rw [hardyW1p0Quotient_testFunction hp]
    exact hardyLpTestQuotientLinear_bound_deriv hp φ

end FiniteExponent

end SobolevSpace.Hardy
