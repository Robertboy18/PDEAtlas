/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.TangentialTranslation
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Operators
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator

/-!
# Boundary regularity: tangential difference quotients

Let `Ω⁺ = {x ∈ ℝ^n : xₙ > 0}` be the flattened half-space and `k ≠ n` a
tangential direction. The forward tangential difference quotient

`Dₖʰ u = h⁻¹ (τₕ u - u)`, `(τₕ u)(x) = u(x + h eₖ)`,

is defined on `Lᵖ(Ω⁺)` directly from the restricted translation isometry,
since tangential translation preserves `Ω⁺` exactly. We develop the
properties needed by the boundary `H²` argument: the almost-everywhere
formula, compatibility with zero extension to `ℝ^n`, the induced endomorphism
of `H¹₀(Ω⁺)` with its coordinate identities, strong convergence of `Dₖʰ u` to
the weak derivative `∂ₖ u` as `h → 0`, and the trace consequence that
tangential derivatives of a zero-trace `H²` field again have zero trace.

## Main results

* `tangentialDifferenceQuotientLp`, `tangentialDifferenceQuotientLp.apply_ae`:
  the `Lᵖ` quotient and its pointwise formula.
* `tangentialDifferenceQuotientL2.zeroExtendLp_eq_global`,
  `tangentialDifferenceQuotientL2.norm_zeroExtend_eq`: tangential quotients
  commute with zero extension, which preserves their norm.
* `exists_restrictedWeakDerivative_of_zeroExtend_with_norm`: a whole-space
  weak derivative of a zero extension restricts to a weak derivative on the
  original domain with no increase in norm.
* `tangentialDifferenceQuotientH10`,
  `tangentialDifferenceQuotientH10_coordinate`,
  `norm_tangentialDifferenceQuotientH10_sq`: the `H¹₀` quotient, its Sobolev
  coordinates, and the exact `H¹` norm decomposition.
* `tendsto_tangentialDifferenceQuotientL2_base`,
  `tendsto_tangentialDifferenceQuotientH10`: convergence of tangential
  quotients to the tangential weak derivative, in `L²` for an `H¹` field and
  in `H¹` for a zero-trace `H²` field.
* `tangentialDerivative_mem_H10`: for `U ∈ H²(Ω⁺)` with zero trace, every
  tangential derivative `∂ₖ U` (`k ≠ n`) lies in `H¹₀(Ω⁺)`.

## Implementation notes

Convergence is proved by extending to `ℝ^n` with the half-space extension
operator, applying the whole-space difference-quotient theory, and
restricting. Membership of `∂ₖ U` in `H¹₀` is obtained as a limit of `H¹₀`
quotients rather than through a trace characterization.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2(a), Theorem 3 (Difference quotients and weak
  derivatives) and the remark on difference quotients near the boundary after its proof,
  pp. 292-293; §6.3.2, step 4 of the proof of Theorem 4, p. 336, and step 3 of the proof of
  Theorem 5 (tangential derivatives keep the zero boundary values), pp. 341-342.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Forward tangential difference quotient on `Lᵖ` of the flattened upper
half-space. -/
noncomputable def tangentialDifferenceQuotientLp
    [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n p (HalfSpace.upper n)) :
    DerivLp n p (HalfSpace.upper n) :=
  h⁻¹ • (tangentialTranslateLp p k hk h u - u)

/-- The restricted tangential quotient agrees almost everywhere with the
classical forward-difference formula. -/
theorem tangentialDifferenceQuotientLp.apply_ae
    [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n p (HalfSpace.upper n)) :
    ((tangentialDifferenceQuotientLp p k hk h u :
        DerivLp n p (HalfSpace.upper n)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        fun x ↦ h⁻¹ *
          (u (x + DifferenceQuotient.coordinateStep k h) - u x) := by
  filter_upwards [tangentialTranslateLp.apply_ae p k hk h u,
    Lp.coeFn_sub (tangentialTranslateLp p k hk h u) u,
    Lp.coeFn_smul h⁻¹ (tangentialTranslateLp p k hk h u - u)] with x ht hs hsm
  simp only [tangentialDifferenceQuotientLp, hsm, Pi.smul_apply, smul_eq_mul, hs, Pi.sub_apply, ht]

/-- Tangential difference quotients commute with zero extension from the
upper half-space.  This is special to tangential directions: membership in
the half-space is unchanged at both points in the difference. -/
theorem tangentialDifferenceQuotientL2.zeroExtendLp_eq_global
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n 2 (HalfSpace.upper n)) :
    Extension.Lp.zeroExtendLp
        (n := n) (p := 2) (Ω := HalfSpace.upper n)
        (HalfSpace.measurableSet_upper (n := n))
        (tangentialDifferenceQuotientLp 2 k hk h u) =
      DifferenceQuotient.differenceQuotientLp 2 k h
        (Extension.Lp.zeroExtendLp
          (n := n) (p := 2) (Ω := HalfSpace.upper n)
          (HalfSpace.measurableSet_upper (n := n)) u) := by
  apply Lp.ext
  let Ωp := HalfSpace.upper n
  have hΩp : MeasurableSet Ωp := HalfSpace.measurableSet_upper (n := n)
  let a := DifferenceQuotient.coordinateStep k h
  let Eu := Extension.Lp.zeroExtendLp (n := n) (p := 2) (Ω := Ωp) hΩp u
  have hzero := Extension.Lp.zeroExtendLp_apply_ae (n := n) (p := 2) (Ω := Ωp) hΩp u
  filter_upwards [Extension.Lp.zeroExtendLp_apply_ae (n := n) (p := 2) (Ω := Ωp) hΩp
      (tangentialDifferenceQuotientLp 2 k hk h u),
    ae_restrict_of_ae (DifferenceQuotient.differenceQuotientL2_apply_ae k h Eu), hzero,
    (Rellich.translationMeasurePreserving (n := n) a).quasiMeasurePreserving.ae_eq_comp hzero,
    ae_restrict_of_ae ((ae_restrict_iff' hΩp).1
      (tangentialDifferenceQuotientLp.apply_ae 2 k hk h u))] with x hl hr hz hzs hd
  simp only [Function.comp_apply, Rellich.translationContinuousMap_apply] at hzs
  rw [hl, hr, hz, hzs]
  simp only [Extension.Lp.extensionByZero]
  by_cases hx : x ∈ Ωp
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Set.indicator_of_mem ((add_coordinateStep_mem_upper_iff k hk h x).2 hx), hd hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem
      fun hmem ↦ hx ((add_coordinateStep_mem_upper_iff k hk h x).1 hmem), sub_zero, mul_zero]

/-- Zero extension preserves the norm of a tangential quotient, so the
restricted and global compactness bounds are identical. -/
theorem tangentialDifferenceQuotientL2.norm_zeroExtend_eq
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n 2 (HalfSpace.upper n)) :
    ‖DifferenceQuotient.differenceQuotientLp 2 k h
      (Extension.Lp.zeroExtendLp
        (n := n) (p := 2) (Ω := HalfSpace.upper n)
        (HalfSpace.measurableSet_upper (n := n)) u)‖ =
      ‖tangentialDifferenceQuotientLp 2 k hk h u‖ := by
  rw [← tangentialDifferenceQuotientL2.zeroExtendLp_eq_global k hk h u,
    Extension.Lp.norm_zeroExtendLp]

/-- A whole-space weak derivative of the zero extension restricts
contractively to the corresponding weak derivative on the original
measurable domain. -/
theorem exists_restrictedWeakDerivative_of_zeroExtend_with_norm
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    (i : Fin n) (v : DerivLp n 2 Ω)
    (G : DerivLp n 2 Set.univ)
    (hG : HasWeakDerivativeOn (n := n) Set.univ [i]
      ((Extension.Lp.zeroExtendLp
        (n := n) (p := 2) (Ω := Ω) hΩ v : DerivLp n 2 Set.univ) :
          ℝ^n → ℝ)
      (G : ℝ^n → ℝ)) :
    ∃ g : DerivLp n 2 Ω,
      ‖g‖ ≤ ‖G‖ ∧
        HasWeakDerivativeOn (n := n) Ω [i]
        (v : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  have hzero := (Extension.Lp.zeroExtendLp_apply_ae (n := n) (p := 2) (Ω := Ω) hΩ v).filter_mono
    (ae_mono (domainMeasure_le (subset_univ Ω)))
  refine ⟨_, norm_restrictDerivLp_le (subset_univ Ω) G, (hG.mono hΩ (subset_univ Ω)).congr_ae ?_
    (restrictDerivLp_apply_ae (subset_univ Ω) G).symm⟩
  filter_upwards [hzero, ae_restrict_mem hΩ] with x hx hxΩ
  rw [hx, Extension.Lp.extensionByZero, Set.indicator_of_mem hxΩ]

/-- Qualitative form of restriction of a whole-space weak derivative of a
zero extension. -/
theorem exists_restrictedWeakDerivative_of_zeroExtend
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    (i : Fin n) (v : DerivLp n 2 Ω)
    (G : DerivLp n 2 Set.univ)
    (hG : HasWeakDerivativeOn (n := n) Set.univ [i]
      ((Extension.Lp.zeroExtendLp
        (n := n) (p := 2) (Ω := Ω) hΩ v : DerivLp n 2 Set.univ) :
          ℝ^n → ℝ)
      (G : ℝ^n → ℝ)) :
    ∃ g : DerivLp n 2 Ω,
      HasWeakDerivativeOn (n := n) Ω [i]
        (v : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  exact (exists_restrictedWeakDerivative_of_zeroExtend_with_norm hΩ i v G hG).imp fun _ h ↦ h.2

/-- Tangential difference quotient as an endomorphism of `H¹₀` on the upper half-space in
`ℝ^n`. Its codomain records admissibility for the flattened weak
equation. -/
noncomputable def tangentialDifferenceQuotientH10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) :
    H¹₀(HalfSpace.upper n) →L[ℝ]
      H¹₀(HalfSpace.upper n) :=
  h⁻¹ • (tangentialTranslateH10 k hk h -
    ContinuousLinearMap.id ℝ
      (H¹₀(HalfSpace.upper n)))

/-- After forgetting the zero-boundary witness, the tangential half-space
quotient is the restriction of the global quotient of the zero extension. -/
theorem tangentialDifferenceQuotientH10_coe
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    ((tangentialDifferenceQuotientH10 k hk h u :
        H¹₀(HalfSpace.upper n)) :
      H¹(HalfSpace.upper n)) =
    restrictCLM (n := n) (k := 1) (p := 2)
      (HalfSpace.measurableSet_upper (n := n))
      (subset_univ (HalfSpace.upper n))
      (DifferenceQuotient.differenceQuotientH1 k h
        (ZeroTrace.zeroExtendH10 (n := n) (Ω := HalfSpace.upper n)
          (HalfSpace.measurableSet_upper (n := n)) u)) := by
  change h⁻¹ •
      (tangentialTranslateH10ToH1OnUpper k h u -
        (u : H¹(HalfSpace.upper n))) = _
  rw [← ZeroTrace.restrict_zeroExtendH10
    (n := n) (Ω := HalfSpace.upper n)
    (HalfSpace.isOpen_upper (n := n)) u]
  simp only [tangentialTranslateH10ToH1OnUpper,
    DifferenceQuotient.differenceQuotientH1_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_sub]

/-- Sharp, step-size-independent estimate for the base coordinate of a
tangential `H¹₀` quotient. -/
theorem norm_baseCoord_tangentialDifferenceQuotientH10_le
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(HalfSpace.upper n)) :
    ‖baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
      (tangentialDifferenceQuotientH10 k hk h u)‖ ≤ ‖u‖ := by
  have hcoe := congrArg (fun V : H¹(HalfSpace.upper n) ↦
    (V : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1))
    (tangentialDifferenceQuotientH10_coe k hk h u)
  exact (congrArg norm hcoe).trans_le ((norm_restrictDerivLp_le (subset_univ _) _).trans
    ((congrArg norm (DifferenceQuotient.differenceQuotientH1_coordinate k h _ _)).trans_le
      (DifferenceQuotient.differenceQuotientL2.zeroExtend_base_norm_le
        (HalfSpace.measurableSet_upper (n := n)) k hh u)))

/-- Every Sobolev coordinate of the `H¹₀` quotient is the corresponding
restricted `L²` quotient. -/
theorem tangentialDifferenceQuotientH10_coordinate
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n))
    (q : DerivIndex n 1) :
    ((((tangentialDifferenceQuotientH10 k hk h u :
        H¹₀(HalfSpace.upper n)) :
        H¹(HalfSpace.upper n)) :
      WkpAmbientOn n 1 2 (HalfSpace.upper n)) q) =
      tangentialDifferenceQuotientLp 2 k hk h
        ((((u : H¹(HalfSpace.upper n)) :
          WkpAmbientOn n 1 2 (HalfSpace.upper n)) q)) := by
  change h⁻¹ •
      (((((tangentialTranslateH10 k hk h u :
        H¹₀(HalfSpace.upper n)) :
          H¹(HalfSpace.upper n)) :
        WkpAmbientOn n 1 2 (HalfSpace.upper n)) q) -
      ((((u : H¹(HalfSpace.upper n)) :
        WkpAmbientOn n 1 2 (HalfSpace.upper n)) q))) = _
  rw [tangentialTranslateH10_coordinate]
  rfl

/-- Base-coordinate specialization of
`tangentialDifferenceQuotientH10_coordinate`. -/
theorem baseCoord_tangentialDifferenceQuotientH10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
        (tangentialDifferenceQuotientH10 k hk h u) =
      tangentialDifferenceQuotientLp 2 k hk h
        (baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
          u) := by
  exact tangentialDifferenceQuotientH10_coordinate k hk h u (baseIndex n 1)

/-- Derivative-coordinate specialization of
`tangentialDifferenceQuotientH10_coordinate`. -/
theorem derivCoord_tangentialDifferenceQuotientH10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) (i : Fin n) :
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n)
        i
        (tangentialDifferenceQuotientH10 k hk h u) =
      tangentialDifferenceQuotientLp 2 k hk h
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n)
          i u) := by
  exact tangentialDifferenceQuotientH10_coordinate k hk h u (singleDerivIndex n i)

/-- A tangential quotient on the upper half-space is the restriction of the
corresponding whole-space quotient whenever the two inputs agree there. -/
theorem tangentialDifferenceQuotientL2_eq_restrict_of_ae
    [Fact (0 < n)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (u : DerivLp n 2 (HalfSpace.upper n))
    (v : DerivLp n 2 Set.univ)
    (hv : (v : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)]
      (u : ℝ^n → ℝ)) :
    tangentialDifferenceQuotientLp 2 k hk h u =
      restrictDerivLp
        (subset_univ (HalfSpace.upper n))
        (DifferenceQuotient.differenceQuotientLp 2 k h v) := by
  apply Lp.ext
  filter_upwards [tangentialDifferenceQuotientLp.apply_ae 2 k hk h u,
    restrictDerivLp_apply_ae (p := (2 : ℝ≥0∞)) (subset_univ (HalfSpace.upper n))
      (DifferenceQuotient.differenceQuotientLp 2 k h v),
    ae_restrict_of_ae (DifferenceQuotient.differenceQuotientL2_apply_ae k h v), hv,
    (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving.ae_eq_comp hv]
    with x hl hr hg hvx hs
  simp only [Function.comp_apply, Rellich.translationContinuousMap_apply] at hs
  rw [hl, hr, hg, hvx, hs]

/-- Tangential quotients of the base coordinate of an upper-half-space
`H¹` field converge strongly in `L²` to its tangential weak derivative. -/
theorem tendsto_tangentialDifferenceQuotientL2_base
    [Fact (0 < n)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (V : H¹(HalfSpace.upper n))
    (h : ℕ → ℝ) (hzero : Tendsto h atTop (𝓝 0))
    (hne : ∀ m, h m ≠ 0) :
    Tendsto
      (fun m ↦ tangentialDifferenceQuotientLp 2 k hk (h m)
        ((V : WkpAmbientOn n 1 2 (HalfSpace.upper n))
          (baseIndex n 1)))
      atTop
      (𝓝 ((V : WkpAmbientOn n 1 2 (HalfSpace.upper n))
        (singleDerivIndex n k))) := by
  let E := SobolevSpace.Extension.GraphSpace.HalfSpace.operator (n := n) (p := (2 : ℝ≥0∞))
  let G : H¹((Set.univ : Set (ℝ^n))) := E.toContinuousLinearMap V
  have hbase : (((G : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) : DerivLp n 2 Set.univ) :
      ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (((V : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1) :
          DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ) := by
    filter_upwards [E.agree_ae V] with x hx
    simpa [G, E] using hx
  have hRV : restrictCLM (n := n) (k := 1) (p := (2 : ℝ≥0∞))
      (HalfSpace.measurableSet_upper (n := n)) (subset_univ (HalfSpace.upper n)) G = V :=
    WkpSpaceOn.ext_of_base_ae (HalfSpace.isOpen_upper (n := n)) _ _
      ((restrictCLM_apply_ae (HalfSpace.measurableSet_upper (n := n))
        (subset_univ (HalfSpace.upper n)) G (baseIndex n 1)).trans hbase)
  have htarget : restrictDerivLp (subset_univ (HalfSpace.upper n))
      ((G : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n k)) =
        (V : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (singleDerivIndex n k) := by
    simpa using congrArg (fun W : H¹(HalfSpace.upper n) ↦
      (W : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (singleDerivIndex n k)) hRV
  rw [← htarget]
  convert ((restrictDerivLp (subset_univ (HalfSpace.upper n))).continuous.tendsto _).comp
    (DifferenceQuotient.tendsto_differenceQuotientL2_base k G h hzero hne) using 1
  funext m
  exact tangentialDifferenceQuotientL2_eq_restrict_of_ae k hk (h m) _ _ hbase

/-- Tangential `H¹₀` quotients of a zero-trace `H²` field converge strongly
in `H¹` to the corresponding first-derivative slice. -/
theorem tendsto_tangentialDifferenceQuotientH10
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2)
          (Ω := HalfSpace.upper n) (by norm_num) U ∈
        (h10SubmoduleOn
          (n := n) (Ω := HalfSpace.upper n)).toSubmodule)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℕ → ℝ) (hzero : Tendsto h atTop (𝓝 0))
    (hne : ∀ m, h m ≠ 0) :
    Tendsto
      (fun m ↦
        ((tangentialDifferenceQuotientH10 k hk (h m)
          ⟨lowerOrderCLM
              (n := n) (k := 1) (m := 2) (p := 2)
              (Ω := HalfSpace.upper n) (by norm_num) U,
            htrace0⟩ :
              H¹₀(HalfSpace.upper n)) :
          H¹(HalfSpace.upper n)))
      atTop
      (𝓝 (derivativeWordCLM
        (n := n) (m := 2) (r := 1) (p := 2)
        (Ω := HalfSpace.upper n) [k] (by simp) U)) := by
  let u : H¹₀(HalfSpace.upper n) := ⟨lowerOrderCLM (n := n) (k := 1) (m := 2) (p := 2)
    (Ω := HalfSpace.upper n) (by norm_num) U, htrace0⟩
  let Uk : H¹(HalfSpace.upper n) := derivativeWordCLM (n := n) (m := 2) (r := 1) (p := 2)
    (Ω := HalfSpace.upper n) [k] (by simp) U
  rw [tendsto_iff_norm_sub_tendsto_zero]
  change Tendsto (fun m ↦ ‖((((tangentialDifferenceQuotientH10 k hk (h m) u :
      H¹₀(HalfSpace.upper n)) : H¹(HalfSpace.upper n)) :
        WkpAmbientOn n 1 2 (HalfSpace.upper n)) - (Uk : WkpAmbientOn n 1 2 (HalfSpace.upper n)))‖)
    atTop (𝓝 0)
  refine tendsto_piLp_norm_of_forall (p := (2 : ℝ≥0∞)) (by norm_num) fun q ↦ ?_
  have hq : q.toList.length + 1 ≤ 2 := by simpa using Nat.add_le_add_right q.toList_length_le 1
  let Vq : H¹(HalfSpace.upper n) := derivativeWordCLM (n := n) (m := 2) (r := 1) (p := 2)
    (Ω := HalfSpace.upper n) q.toList hq U
  have hcoord := tendsto_tangentialDifferenceQuotientL2_base k hk Vq h hzero hne
  rw [show ((Vq : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1) :
      DerivLp n 2 (HalfSpace.upper n)) = ((u : H¹(HalfSpace.upper n)) :
        WkpAmbientOn n 1 2 (HalfSpace.upper n)) q by simp [Vq, u],
    show ((Vq : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (singleDerivIndex n k) :
      DerivLp n 2 (HalfSpace.upper n)) = (Uk : WkpAmbientOn n 1 2 (HalfSpace.upper n)) q from
        congrArg (U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (derivativeWordIndex_eq_of_perm _ _ _ _ _ _ (by simp))] at hcoord
  exact tendsto_iff_norm_sub_tendsto_zero.mp (hcoord.congr fun m ↦
    (tangentialDifferenceQuotientH10_coordinate k hk (h m) u q).symm)

/-- Every tangential first derivative of an `H²` function with zero trace on
the upper half-space also has zero trace. -/
theorem tangentialDerivative_mem_H10
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2)
          (Ω := HalfSpace.upper n) (by norm_num) U ∈
        (h10SubmoduleOn
          (n := n) (Ω := HalfSpace.upper n)).toSubmodule)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) :
    derivativeWordCLM
        (n := n) (m := 2) (r := 1) (p := 2)
        (Ω := HalfSpace.upper n) [k] (by simp) U ∈
      (h10SubmoduleOn
        (n := n) (Ω := HalfSpace.upper n)).toSubmodule := by
  refine (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).isClosed'.mem_of_tendsto
    (tendsto_tangentialDifferenceQuotientH10 U htrace0 k hk (fun m ↦ 1 / ((m : ℝ) + 1))
      tendsto_one_div_add_atTop_nhds_zero_nat fun m ↦ by positivity)
    (Eventually.of_forall fun m ↦ (tangentialDifferenceQuotientH10 k hk _ _).property)

/-- Exact `H¹` norm decomposition of a tangential quotient into its base
coordinate and all quotient-gradient coordinates. -/
theorem norm_tangentialDifferenceQuotientH10_sq
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    ‖tangentialDifferenceQuotientH10 k hk h u‖ ^ 2 =
      ‖tangentialDifferenceQuotientLp 2 k hk h
        (baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
          u)‖ ^ 2 +
      ∑ i : Fin n,
        ‖tangentialDifferenceQuotientLp 2 k hk h
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n)
            i u)‖ ^ 2 := by
  have hdecomp := norm_sq_eq_base_sq_add_sum_deriv_sq
    (n := n) (Ω := HalfSpace.upper n)
    (tangentialDifferenceQuotientH10 k hk h u)
  simpa only [baseCoord_tangentialDifferenceQuotientH10,
    derivCoord_tangentialDifferenceQuotientH10] using hdecomp

end GraphSpace.BoundaryRegularity
end SobolevSpace
