/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
import PDE.Analysis.MeasureTheory.LpNorm
public import PDE.Spaces.Sobolev.Inequalities.Hardy.HalfSpace -- shake: keep

/-!
# Completed Finite-Exponent Hardy Operator on the Upper Half-Space

For every real `p > 1`, the smooth upper-half-space Hardy inequality, proved in
`Hardy.HalfSpace`, extends to the completed supported-core space `W^{1,p}_0(ℝ^n × (0,∞))`.

The quotient by the normal coordinate is first realized as an ambient `Lᵖ`
class on smooth compactly supported functions. Its bound by the normal
weak derivative is then extended by density to the completed zero-trace
space, the generic `W^{k,p}_0` closure.

## Main results

* `hardyUpperHalfSpaceTestQuotient`, `hardyUpperHalfSpaceTestQuotientLinear`: `φ ↦ φ / xₙ` on the
  smooth core, as an `Lᵖ` class and as a linear map.
* `norm_normalDerivative_eq_testFunctionToWkp_coordinate`: the `Lᵖ` norm of `∂ₙ φ` is the norm of
  the normal first-derivative coordinate of the Sobolev bundle.
* `hardyUpperHalfSpaceTestQuotientLinear_bound_normal`,
  `hardyUpperHalfSpaceTestQuotientLinear_bound`: the core estimate with constant `p/(p-1)`,
  against the normal derivative coordinate and against the graph norm.
* `hardyUpperHalfSpaceW1p0Quotient`: the bounded extension to the completed zero-trace space.
* `norm_hardyUpperHalfSpaceW1p0Quotient_le_normalDerivative`: the completed operator has `Lᵖ` norm
  at most `(p/(p-1)) ‖∂ₙ u‖ₚ` on `W^{1,p}_0`, with `∂ₙ u` the normal weak-derivative coordinate.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter IX, for the one-dimensional Hardy inequality,
  which `Hardy.HalfSpace` integrates over the tangential variables.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Hardy

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ}

private theorem integral_abs_rpow_eq_integral_set_of_support_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : X → ℝ} {s : Set X} {p : ℝ} (hp : 0 < p)
    (hs : Function.support u ⊆ s) :
    (∫ x, |u x| ^ p ∂μ) = ∫ x in s, |u x| ^ p ∂μ :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [Function.notMem_support.mp fun h ↦ hx (hs h), abs_zero, Real.zero_rpow hp.ne']).symm

section FiniteExponent

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/--
The literal quotient by the normal coordinate of a smooth compactly supported
upper-half-space test function, represented as an ambient `Lᵖ` class.
-/
noncomputable def hardyUpperHalfSpaceTestQuotient
    (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^(n + 1))) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := Fact.out
  let hdim : Fact (0 < n + 1) := ⟨Nat.zero_lt_succ n⟩
  have hlast :
      PDE.Common.lastIndex (n := n + 1) = Fin.last n := by
    apply Fin.ext
    simp [PDE.Common.lastIndex]
  simpa [hlast] using
    (@memLp_div_last_of_hasCompactSupport
      (n + 1) hdim φ.1.toFun p
      (lt_of_lt_of_le zero_lt_one (ENNReal.one_le_ofReal.mp hp1))
      φ.1.contDiff.continuous φ.1.hasCompactSupport φ.2).toLp
      (fun x ↦ φ.1.toFun x / x (Fin.last n))

private theorem lastIndex_succ : PDE.Common.lastIndex (n := n + 1) = Fin.last n :=
  Fin.ext (by simp [PDE.Common.lastIndex])

/--
The smooth upper-half-space quotient is represented almost everywhere by
literal division by the positive normal coordinate.
-/
theorem hardyUpperHalfSpaceTestQuotient_apply_ae
    (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    ((hardyUpperHalfSpaceTestQuotient n p φ :
      Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^(n + 1)))) :
        ℝ^(n + 1) → ℝ) =ᵐ[volume]
      fun x ↦ φ.1.toFun x / x (Fin.last n) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := Fact.out
  let hdim : Fact (0 < n + 1) := ⟨Nat.zero_lt_succ n⟩
  have hlast :
      PDE.Common.lastIndex (n := n + 1) = Fin.last n := by
    apply Fin.ext
    simp [PDE.Common.lastIndex]
  simpa [hardyUpperHalfSpaceTestQuotient, hlast] using
    (@memLp_div_last_of_hasCompactSupport
      (n + 1) hdim φ.1.toFun p
      (lt_of_lt_of_le zero_lt_one (ENNReal.one_le_ofReal.mp hp1))
      φ.1.contDiff.continuous φ.1.hasCompactSupport φ.2).coeFn_toLp

/-- The normal-coordinate Hardy quotient on the smooth test core. -/
noncomputable def hardyUpperHalfSpaceTestQuotientLinear
    (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1)) →ₗ[ℝ]
      Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^(n + 1))) where
  toFun := hardyUpperHalfSpaceTestQuotient n p
  map_add' φ ψ := by
    refine Lp.ext ?_
    filter_upwards [hardyUpperHalfSpaceTestQuotient_apply_ae n p (φ + ψ),
      hardyUpperHalfSpaceTestQuotient_apply_ae n p φ,
      hardyUpperHalfSpaceTestQuotient_apply_ae n p ψ,
      Lp.coeFn_add (hardyUpperHalfSpaceTestQuotient n p φ) (hardyUpperHalfSpaceTestQuotient n p ψ)]
      with x hsum hφ hψ hadd
    rw [hsum, hadd, Pi.add_apply, hφ, hψ]
    exact add_div _ _ _
  map_smul' c φ := by
    refine Lp.ext ?_
    filter_upwards [hardyUpperHalfSpaceTestQuotient_apply_ae n p (c • φ),
      hardyUpperHalfSpaceTestQuotient_apply_ae n p φ,
      Lp.coeFn_smul ((RingHom.id ℝ) c) (hardyUpperHalfSpaceTestQuotient n p φ)]
      with x hsmul hφ hcoe
    rw [hsmul, hcoe, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, hφ]
    exact mul_div_assoc _ _ _

/-- The normal partial derivative of a smooth compactly supported test function
on the upper half-space lies in every ambient `Lᵖ`. -/
theorem memLp_normalDerivative_of_testFunction
    (p : ℝ≥0∞)
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    MemLp
      (fun x ↦
        (∂[Fin.last n] φ.1.toFun) x)
      p volume :=
  ((φ.1.contDiff.continuous_fderiv (by norm_num)).clm_apply
    continuous_const).memLp_of_hasCompactSupport
    (φ.1.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (Fin.last n) (1 : ℝ)))

/-- The normal derivative of a test function on the upper half-space vanishes off it. -/
private theorem support_normalDerivative_subset
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    Function.support (fun x ↦ (∂[Fin.last n] φ.1.toFun) x) ⊆ HalfSpace.upper (n + 1) :=
  (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans φ.2)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/--
The ambient `Lᵖ` norm of the classical normal derivative equals the normal
first-derivative coordinate norm in the Sobolev test embedding.
-/
theorem norm_normalDerivative_eq_testFunctionToWkp_coordinate
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    ‖(memLp_normalDerivative_of_testFunction
        (n := n) (ENNReal.ofReal p) φ).toLp
        (fun x ↦
          (∂[Fin.last n] φ.1.toFun) x)‖ =
      ‖((GraphSpace.testFunctionToWkp
          (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper (n + 1)) φ :
            GraphSpace.WkpAmbientOn (n + 1) 1
              (ENNReal.ofReal p) (HalfSpace.upper (n + 1)))
        (GraphSpace.singleDerivIndex
          (n := n + 1) (Fin.last n)))‖ := by
  rw [Lp.norm_toLp, GraphSpace.norm_testFunctionToWkp_coordinate_eq_eLpNorm_toReal,
    ← eLpNorm_restrict_eq_of_support_subset
      (memLp_normalDerivative_of_testFunction (ENNReal.ofReal p) φ).aestronglyMeasurable
      (support_normalDerivative_subset φ)]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae (.of_forall fun x ↦ by
    simp [GraphSpace.singleDerivIndex_toList, iteratedPartialDeriv]))

/--
The upper-half-space Hardy estimate on the smooth core, expressed using
only the normal first-derivative Sobolev coordinate.
-/
theorem hardyUpperHalfSpaceTestQuotientLinear_bound_normal
    (hp : 1 < p)
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    ‖hardyUpperHalfSpaceTestQuotientLinear n p φ‖ ≤
      (p / (p - 1)) *
        ‖((GraphSpace.testFunctionToWkp
            (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
            (Ω := HalfSpace.upper (n + 1)) φ :
              GraphSpace.WkpAmbientOn (n + 1) 1
                (ENNReal.ofReal p) (HalfSpace.upper (n + 1)))
          (GraphSpace.singleDerivIndex
            (n := n + 1) (Fin.last n)))‖ := by
  let q : ℝ^(n + 1) → ℝ := fun x ↦ φ.1.toFun x / x (Fin.last n)
  let d : ℝ^(n + 1) → ℝ := fun x ↦ (∂[Fin.last n] φ.1.toFun) x
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hconst : 0 < p / (p - 1) := by positivity
  let hq : MemLp q (ENNReal.ofReal p) volume := by
    simpa [q, lastIndex_succ] using @memLp_div_last_of_hasCompactSupport (n + 1)
      ⟨Nat.zero_lt_succ n⟩ φ.1.toFun p hp0 φ.1.contDiff.continuous φ.1.hasCompactSupport φ.2
  let hd := memLp_normalDerivative_of_testFunction (n := n) (ENNReal.ofReal p) φ
  have hqIntegral : (∫ x, |q x| ^ p) =
      ∫ x in HalfSpace.upper (n + 1), |φ.1.toFun x| ^ p * (x (Fin.last n)) ^ (-p) :=
    (integral_abs_rpow_eq_integral_set_of_support_subset hp0
      fun x hx ↦ φ.2 (subset_tsupport _ (div_ne_zero_iff.1 hx).1)).trans <|
      setIntegral_congr_fun (@HalfSpace.measurableSet_upper (n + 1) ⟨Nat.zero_lt_succ n⟩)
        fun x (hx : 0 < x (Fin.last n)) ↦ by
          change |φ.1.toFun x / x (Fin.last n)| ^ p = _
          rw [abs_div, abs_of_pos hx, Real.div_rpow (abs_nonneg _) hx.le, Real.rpow_neg hx.le]
          ring
  have hnorm : ‖hq.toLp q‖ ≤ p / (p - 1) * ‖hd.toLp d‖ := by
    refine (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hconst.le (norm_nonneg _))
      hp0).mp ?_
    rw [Real.mul_rpow hconst.le (norm_nonneg _), norm_toLp_rpow_eq_integral_abs hp0 hq,
      norm_toLp_rpow_eq_integral_abs hp0 hd, hqIntegral,
      integral_abs_rpow_eq_integral_set_of_support_subset hp0 (support_normalDerivative_subset φ)]
    exact hardy_upperHalfSpace_lp_of_hasCompactSupport (n := n) hp
      (φ.1.contDiff.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)) φ.1.hasCompactSupport φ.2
  rw [show hardyUpperHalfSpaceTestQuotientLinear n p φ = hq.toLp q from
      Lp.ext ((hardyUpperHalfSpaceTestQuotient_apply_ae n p φ).trans hq.coeFn_toLp.symm),
    ← norm_normalDerivative_eq_testFunctionToWkp_coordinate φ]
  exact hnorm

/--
The smooth upper-half-space quotient is bounded by the full `W^{1,p}` graph
norm. This is the estimate used for extension to the supported-core closure.
-/
theorem hardyUpperHalfSpaceTestQuotientLinear_bound
    (hp : 1 < p)
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    ‖hardyUpperHalfSpaceTestQuotientLinear n p φ‖ ≤
      (p / (p - 1)) *
        ‖GraphSpace.testFunctionToWkp0
          (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper (n + 1)) φ‖ := by
  let U := (GraphSpace.testFunctionToWkp (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := HalfSpace.upper (n + 1)) φ :
      GraphSpace.WkpAmbientOn (n + 1) 1 (ENNReal.ofReal p) (HalfSpace.upper (n + 1)))
  refine (hardyUpperHalfSpaceTestQuotientLinear_bound_normal hp φ).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  simpa [GraphSpace.testFunctionToWkp0_coe, U] using
    PiLp.norm_apply_le (x := U) (i := GraphSpace.singleDerivIndex (n := n + 1) (Fin.last n))

/--
The Hardy quotient on the completed finite-exponent zero-trace space of the
upper half-space.
-/
noncomputable def hardyUpperHalfSpaceW1p0Quotient
    (n : ℕ) (p : ℝ) (_hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    W₀^{1,(ENNReal.ofReal p)}((HalfSpace.upper (n + 1))) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^(n + 1))) :=
  (hardyUpperHalfSpaceTestQuotientLinear n p).extendOfNorm
    (GraphSpace.testFunctionToWkp0Linear
      (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper (n + 1)))

/--
On the smooth core, the completed upper-half-space operator agrees with
literal division by the normal coordinate.
-/
theorem hardyUpperHalfSpaceW1p0Quotient_testFunction
    (hp : 1 < p)
    (φ : GraphSpace.TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    hardyUpperHalfSpaceW1p0Quotient n p hp
        (GraphSpace.testFunctionToWkp0
          (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper (n + 1)) φ) =
      hardyUpperHalfSpaceTestQuotient n p φ := by
  exact LinearMap.extendOfNorm_eq
    (GraphSpace.denseRange_testFunctionToWkp0Linear
      (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper (n + 1)))
    ⟨p / (p - 1),
      hardyUpperHalfSpaceTestQuotientLinear_bound hp⟩ φ

/-- Graph-norm estimate for the completed upper-half-space Hardy quotient. -/
theorem norm_hardyUpperHalfSpaceW1p0Quotient_le
    (hp : 1 < p)
    (u : W₀^{1,(ENNReal.ofReal p)}((HalfSpace.upper (n + 1)))) :
    ‖hardyUpperHalfSpaceW1p0Quotient n p hp u‖ ≤
      (p / (p - 1)) * ‖u‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (GraphSpace.denseRange_testFunctionToWkp0Linear
      (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper (n + 1)))
    (p / (p - 1))
    (hardyUpperHalfSpaceTestQuotientLinear_bound hp) u

/--
Hardy inequality on the upper half-space for the completed operator: for `p > 1` and
`u ∈ W^{1,p}_0`, `‖hardyUpperHalfSpaceW1p0Quotient n p hp u‖ₚ ≤ (p / (p - 1)) ‖∂ₙu‖ₚ`, with `∂ₙu`
the weak normal-derivative coordinate of `u`. The operator is the bounded extension of
`u ↦ u / xₙ` from the test functions. Optimality of the constant `p / (p - 1)` is not proved here.
-/
theorem norm_hardyUpperHalfSpaceW1p0Quotient_le_normalDerivative
    (hp : 1 < p)
    (u : W₀^{1,(ENNReal.ofReal p)}((HalfSpace.upper (n + 1)))) :
    ‖hardyUpperHalfSpaceW1p0Quotient n p hp u‖ ≤
      (p / (p - 1)) *
        ‖(((u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
              GraphSpace.WkpAmbientOn (n + 1) 1
                (ENNReal.ofReal p) (HalfSpace.upper (n + 1)))
          (GraphSpace.singleDerivIndex
            (n := n + 1) (Fin.last n)))‖ := by
  refine DenseRange.induction_on (GraphSpace.denseRange_testFunctionToWkp0Linear
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := HalfSpace.upper (n + 1))) u
    (isClosed_le (by fun_prop) (by fun_prop)) fun φ ↦ ?_
  change ‖hardyUpperHalfSpaceW1p0Quotient n p hp (GraphSpace.testFunctionToWkp0
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := HalfSpace.upper (n + 1)) φ)‖ ≤ _
  rw [hardyUpperHalfSpaceW1p0Quotient_testFunction hp]
  exact hardyUpperHalfSpaceTestQuotientLinear_bound_normal hp φ

end FiniteExponent

end SobolevSpace.Hardy
