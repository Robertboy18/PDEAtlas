/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.ZeroTraceIntegration
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.WkpExtensionByZero
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TangentialDerivative
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Zero extension of geometric trace-zero functions on a half-space

The normal Green identity shows that the normal derivative of the zero extension
has no boundary measure when the completed geometric trace vanishes. Tangential
derivatives follow by averaging even and odd reflection. Consequently all weak
derivatives are the zero extensions of the original weak derivatives.

This places the zero extension in the whole-space Sobolev graph from geometric trace zero
alone (`zeroExtendAmbient_mem_of_traceLp_eq_zero`), without assuming membership in the closure of
interior test functions. `zeroExtendOfTraceLpEqZero` is the resulting element of `W^{1,p}(ℝ^(n+1))`,
with its norm and its coordinates. `SobolevSpace.VectorValued.Trace.HalfSpace.zeroExtendCLM`
bundles the extension as a norm-preserving operator on the trace kernel, for any real Banach
codomain.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open GraphSpace
open scoped ENNReal Topology Sobolev

variable {n : ℕ}

local notation "hUpper" =>
  (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n + 1))

/-- Tangential differentiation commutes with zero extension. No boundary trace
assumption is needed in a direction parallel to the boundary. -/
theorem hasWeakDerivativeOn_zeroExtend_ne_last
    {d : ℕ} [Fact (0 < d)] {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d)
    (hi : i ≠ PDE.Common.lastIndex (n := d))
    (u du : DerivLp d p (_root_.SobolevSpace.HalfSpace.upper d))
    (hweak : HasWeakDerivativeOn (_root_.SobolevSpace.HalfSpace.upper d) [i] u du) :
    HasWeakDerivativeOn Set.univ [i]
      (Extension.Lp.zeroExtendLp (_root_.SobolevSpace.HalfSpace.measurableSet_upper d) u)
      (Extension.Lp.zeroExtendLp (_root_.SobolevSpace.HalfSpace.measurableSet_upper d) du) := by
  let E := _root_.SobolevSpace.HalfSpace.evenExtendLp (n := d) (p := p)
  let O := _root_.SobolevSpace.HalfSpace.oddExtendLp (n := d) (p := p)
  have hE := Extension.GraphSpace.HalfSpace.hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last
    (n := d) (p := p) i hi u du hweak
  have hO := Extension.GraphSpace.HalfSpace.hasWeakDerivativeOn_univ_oddExtend_of_upper_ne_last
    (n := d) (p := p) i hi u du hweak
  have havg (v : DerivLp d p (_root_.SobolevSpace.HalfSpace.upper d)) :
      Extension.Lp.zeroExtendLp (_root_.SobolevSpace.HalfSpace.measurableSet_upper d) v =
        (1 / 2 : ℝ) • (E v + O v) := by
    dsimp [E, O, _root_.SobolevSpace.HalfSpace.evenExtendLp,
      _root_.SobolevSpace.HalfSpace.oddExtendLp,
      _root_.SobolevSpace.HalfSpace.embedUpper]
    simp only [add_apply, sub_apply]
    module
  have hae (v : DerivLp d p (_root_.SobolevSpace.HalfSpace.upper d)) :
      (Extension.Lp.zeroExtendLp (_root_.SobolevSpace.HalfSpace.measurableSet_upper d) v :
        ℝ^d → ℝ) =ᵐ[domainMeasure d Set.univ]
          (1 / 2 : ℝ) • ((E v : ℝ^d → ℝ) + (O v : ℝ^d → ℝ)) := by
    rw [havg]
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (E v + O v), Lp.coeFn_add (E v) (O v)]
      with x hx hs
    simpa only [Pi.smul_apply, Pi.add_apply, hs] using hx
  exact (hasWeakDerivativeOn_congr_ae (hae u) (hae du)).mpr
    (hasWeakDerivativeOn_smul (1 / 2 : ℝ) (hasWeakDerivativeOn_add hE hO))

/-- Vanishing geometric trace removes the boundary term in the normal derivative
of the zero extension. -/
theorem hasWeakDerivativeOn_zeroExtend_last (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 ≤ p) (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)))
    (hu : traceLp n p hp u = 0) :
    HasWeakDerivativeOn Set.univ [Fin.last n]
      (Extension.Lp.zeroExtendLp hUpper (wkpBaseCoordinateCLM u))
      (Extension.Lp.zeroExtendLp hUpper
        (wkpCoordinateCLM (singleDerivIndex (n + 1) (Fin.last n)) u)) := by
  refine ⟨memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out,
    memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out, ?_⟩
  intro φ _
  have hgreen := integral_upper_normal_green p hp u ⟨φ, subset_univ _⟩
  rw [hu] at hgreen
  have hbdy : (∫ y : ℝ^n, (0 : Lp ℝ (ENNReal.ofReal p) volume) y *
      smoothBoundaryValue φ.toFun y) = 0 := by
    calc
      _ = ∫ _ : ℝ^n, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^n))]
          with y hy
        exact congrArg (fun t : ℝ ↦ t * smoothBoundaryValue φ.toFun y) hy |>.trans
          (zero_mul _)
      _ = 0 := integral_zero _ _
  rw [hbdy, neg_zero] at hgreen
  simp only [domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
    List.length_cons, List.length_nil, zero_add, pow_one, neg_one_mul]
  rw [Extension.Lp.integral_zeroExtendLp_mul, Extension.Lp.integral_zeroExtendLp_mul]
  exact eq_neg_of_add_eq_zero_left hgreen

/-- Coordinatewise zero extension of a geometric trace-zero function belongs to
the whole-space weak derivative graph. -/
theorem zeroExtendAmbient_mem_of_traceLp_eq_zero (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)))
    (hu : traceLp n p hp u = 0) :
    ZeroTrace.zeroExtendAmbient hUpper u.val ∈
      wkpSubmoduleOn (n + 1) 1 (ENNReal.ofReal p) Set.univ := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    simpa only [baseIndex_toList] using
      hasWeakDerivativeOn_nil
        (memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out)
  · subst a
    simp only [singleDerivIndex_toList, ZeroTrace.zeroExtendAmbient_apply]
    by_cases hi : i = Fin.last n
    · subst i
      exact hasWeakDerivativeOn_zeroExtend_last p hp u hu
    · apply hasWeakDerivativeOn_zeroExtend_ne_last i hi
      simpa only [firstDerivIndex_one] using
        u.property.hasWeakDerivativeOn_first (by norm_num) i

/-- The global Sobolev zero extension constructed directly from geometric trace zero. -/
def zeroExtendOfTraceLpEqZero (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)))
    (hu : traceLp n p hp u = 0) : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)) :=
  ⟨ZeroTrace.zeroExtendAmbient hUpper u.val,
    zeroExtendAmbient_mem_of_traceLp_eq_zero p hp u hu⟩

/-- Zero extension preserves the full first-order Sobolev norm. -/
theorem norm_zeroExtendOfTraceLpEqZero (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)))
    (hu : traceLp n p hp u = 0) :
    ‖zeroExtendOfTraceLpEqZero p hp u hu‖ = ‖u‖ :=
  ZeroTrace.norm_zeroExtendAmbient hUpper u.val

/-- Every weak derivative of the constructed extension is the `Lp` zero extension. -/
theorem zeroExtendOfTraceLpEqZero_coordinate (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 ≤ p) (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)))
    (hu : traceLp n p hp u = 0) (a : DerivIndex (n + 1) 1) :
    wkpCoordinateCLM a (zeroExtendOfTraceLpEqZero p hp u hu) =
      Extension.Lp.zeroExtendLp hUpper (wkpCoordinateCLM a u) :=
  ZeroTrace.zeroExtendAmbient_apply hUpper u.val a

end SobolevSpace.Trace.HalfSpace
