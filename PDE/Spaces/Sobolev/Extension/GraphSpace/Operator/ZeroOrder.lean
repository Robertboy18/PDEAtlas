/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic

/-!
# Zero extension on order-zero Sobolev graph spaces

At Sobolev order zero there are no derivative coordinates: `W^{0,p}(Ω)` is `L^p(Ω)`, the graph
space `WkpSpaceOn n 0 p Ω` has the single coordinate `baseIndex n 0`, and extension by zero
outside `Ω` is a linear isometry into `L^p(ℝ^n)`. This is the one Sobolev order at which zero
extension works; for `k ≥ 1` the jump across `∂Ω` destroys the weak derivatives, which is why the
extension theorem for `W^{1,p}` on a `C¹` domain (Evans, PDE, §5.4) needs reflection and a
partition of unity instead. We bundle the `L^p` zero extension
`Extension.Lp.zeroExtendLp` as an order-zero graph-space `Operator`, so that the general
`HasExtensionOperator` interface has an instance for every measurable set at `k = 0`.

## Main results

* `norm_eq_norm_base_of_order_zero`: the `W^{0,p}` graph norm is the `L^p` norm of the base
  coordinate.
* `zeroExtendₗᵢ`: zero extension as a linear isometry `WkpSpaceOn n 0 p Ω →ₗᵢ[ℝ] WkpSpace n 0 p`.
* `operator`, `operator_apply_base`, `norm_operator_apply`, `norm_operator_le_one`: the bundled
  extension operator, its base coordinate, exact norm preservation, and the operator-norm bound
  `‖E‖ ≤ 1`.
* `restrict_zeroExtend`, `restrictCLM_comp_zeroExtend`: restriction back to `Ω` is a left inverse.
* `exists_extensionOperator`: `HasExtensionOperator n 0 p Ω` for every measurable `Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, p. 268, the remark before Theorem 1 that extension by
  zero does not in general preserve weak first derivatives, and Theorem 1, pp. 268-271, the
  `W^{1,p}` extension by reflection and a partition of unity.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

set_option linter.missingDocs true

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace Extension
namespace GraphSpace

open SobolevSpace.GraphSpace
open SobolevSpace.Extension.Lp

namespace Zero

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- At Sobolev order zero, the graph-space norm is the norm of its unique `Lp`
coordinate. -/
theorem norm_eq_norm_base_of_order_zero (u : W^{0,p}(Ω)) :
    ‖u‖ =
      ‖((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0) : DerivLp n p Ω)‖ := by
  change ‖(u : WkpAmbientOn n 0 p Ω)‖ =
    ‖((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0) : DerivLp n p Ω)‖
  have hu :
      (u : WkpAmbientOn n 0 p Ω) =
        PiLp.single p (baseIndex n 0)
          ((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0)) := by
    ext a
    have ha : a = baseIndex n 0 := a.eq_baseIndex_of_order_zero
    subst a
    simp
  calc
    ‖(u : WkpAmbientOn n 0 p Ω)‖ =
        ‖PiLp.single p (baseIndex n 0)
          ((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0))‖ :=
      congrArg norm hu
    _ = ‖((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0) :
        DerivLp n p Ω)‖ := by
      rw [PiLp.norm_single]

private theorem isWkpOn_k0 (U : WkpAmbientOn n 0 p Ω) :
    IsWkpOn (n := n) (k := 0) (p := p) (Ω := Ω) U := by
  intro a
  have ha : a = baseIndex n 0 := a.eq_baseIndex_of_order_zero
  subst ha
  have hloc := memLp_locallyIntegrableOn_domain
    (MeasureTheory.Lp.memLp (U (baseIndex n 0))) (Fact.out : (1 : ℝ≥0∞) ≤ p)
  simpa only [SobolevSpace.GraphSpace.baseIndex_toList] using hasWeakDerivativeOn_nil hloc

/-- Place an `Lp` function in the unique coordinate of the order-zero ambient
graph space. -/
noncomputable def singleAmbient :
    DerivLp n p Set.univ →L[ℝ] WkpAmbientOn n 0 p Set.univ := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun u ↦
        WithLp.toLp p
          (Pi.single
            (M := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)
            (baseIndex n 0) u)
      map_add' := by
        intro u v
        ext a
        rw [PiLp.toLp_apply
          (p := p) (α := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)]
        rw [PiLp.add_apply]
        rw [PiLp.toLp_apply
          (p := p) (α := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)]
        rw [PiLp.toLp_apply
          (p := p) (α := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)]
        by_cases ha : a = baseIndex n 0
        · subst ha
          rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha]
          simp
      map_smul' := by
        intro c u
        ext a
        rw [PiLp.toLp_apply
          (p := p) (α := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)]
        rw [PiLp.smul_apply]
        rw [PiLp.toLp_apply
          (p := p) (α := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)]
        by_cases ha : a = baseIndex n 0
        · subst ha
          rw [Pi.single_eq_same, Pi.single_eq_same]
          have hc : (RingHom.id ℝ) c = c := rfl
          rw [hc]
        · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha]
          simp }
    1 (by
      intro u
      simp [one_mul])

/-- The single-coordinate ambient element satisfies the order-zero graph-space
predicate. -/
theorem singleAmbient_mem (u : DerivLp n p Set.univ) :
    IsWkpOn (n := n) (k := 0) (p := p) (Ω := (Set.univ : Set (ℝ^n)))
      (singleAmbient (n := n) (p := p) u) :=
  isWkpOn_k0 (n := n) (p := p) (Ω := (Set.univ : Set (ℝ^n))) _

/-- Projection of an order-zero graph-space element onto its unique `Lp`
coordinate. -/
noncomputable def baseProj :
    W^{0,p}(Ω) →L[ℝ] DerivLp n p Ω :=
  (PiLp.proj (p := p) (𝕜 := ℝ)
      (β := fun _ : DerivIndex n 0 ↦ DerivLp n p Ω) (baseIndex n 0)).comp
    (Submodule.subtypeL (wkpSubmoduleOn n 0 p Ω))

private theorem baseProj_apply (u : W^{0,p}(Ω)) :
    baseProj (n := n) (p := p) (Ω := Ω) u =
      ((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0) : DerivLp n p Ω) := by
  simp [baseProj]

/-- Place an `Lp` function on `ℝ^n` in the order-zero graph space `W^{0,p}`. -/
noncomputable def singleWkp :
    DerivLp n p Set.univ →L[ℝ] W^{0,p}(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    (singleAmbient (n := n) (p := p))
    (wkpSubmoduleOn n 0 p (Set.univ : Set (ℝ^n)))
    (fun u0 ↦ singleAmbient_mem (n := n) (p := p) u0)

/-- Zero extension on order-zero graph spaces as a continuous linear map,
built from the `Lp` indicator extension of the single coordinate. -/
noncomputable def extendCLM (hΩmeas : MeasurableSet Ω) :
    W^{0,p}(Ω) →L[ℝ] W^{0,p}(ℝ^n) :=
  (singleWkp (n := n) (p := p)).comp
    ((zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas).comp
      (baseProj (n := n) (p := p) (Ω := Ω)))

private theorem singleAmbient_apply_base (u0 : DerivLp n p Set.univ) :
    (singleAmbient (n := n) (p := p) u0) (baseIndex n 0) = u0 := by
  have :
      (WithLp.toLp p
          (Pi.single
            (M := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)
            (baseIndex n 0) u0)
          (baseIndex n 0)) = u0 := by
    rw [PiLp.toLp_apply
      (p := p) (α := fun _ : DerivIndex n 0 ↦ DerivLp n p Set.univ)]
    simp
  simp [singleAmbient, LinearMap.mkContinuous]

private theorem singleWkp_apply_base (u0 : DerivLp n p Set.univ) :
    ((singleWkp (n := n) (p := p) u0 : WkpAmbientOn n 0 p Set.univ)
        (baseIndex n 0) : DerivLp n p Set.univ) = u0 := by
  change (singleAmbient (n := n) (p := p) u0) (baseIndex n 0) = u0
  exact singleAmbient_apply_base (n := n) (p := p) u0

private theorem extendCLM_apply_base (hΩmeas : MeasurableSet Ω)
    (u : W^{0,p}(Ω)) :
    ((extendCLM (n := n) (p := p) (Ω := Ω) hΩmeas u :
        WkpAmbientOn n 0 p Set.univ) (baseIndex n 0) : DerivLp n p Set.univ) =
      zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas
        (baseProj (n := n) (p := p) (Ω := Ω) u) := by
  change
    ((singleWkp (n := n) (p := p)
          (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas
            (baseProj (n := n) (p := p) (Ω := Ω) u)) :
        WkpAmbientOn n 0 p Set.univ) (baseIndex n 0) : DerivLp n p Set.univ) = _
  exact singleWkp_apply_base (n := n) (p := p) _

/-- Order-zero zero extension preserves the graph-space norm. -/
theorem norm_extendCLM_apply (hΩmeas : MeasurableSet Ω)
    (u : W^{0,p}(Ω)) :
    ‖extendCLM (n := n) (p := p) (Ω := Ω) hΩmeas u‖ = ‖u‖ := by
  calc
    ‖extendCLM (n := n) (p := p) (Ω := Ω) hΩmeas u‖ =
        ‖((extendCLM (n := n) (p := p) (Ω := Ω) hΩmeas u :
          WkpAmbientOn n 0 p Set.univ) (baseIndex n 0) :
            DerivLp n p Set.univ)‖ :=
      norm_eq_norm_base_of_order_zero
        (n := n) (p := p) (Ω := (Set.univ : Set (ℝ^n))) _
    _ = ‖zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas
          ((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0))‖ := by
      rw [extendCLM_apply_base, baseProj_apply]
    _ = ‖((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0) :
          DerivLp n p Ω)‖ :=
      norm_zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas _
    _ = ‖u‖ :=
      (norm_eq_norm_base_of_order_zero (n := n) (p := p) (Ω := Ω) u).symm

/-- Zero extension as a linear isometry
`W^{0,p}(Ω) → W^{0,p}(ℝ^n)`. -/
noncomputable def zeroExtendₗᵢ (hΩmeas : MeasurableSet Ω) :
    W^{0,p}(Ω) →ₗᵢ[ℝ] W^{0,p}(ℝ^n) where
  toLinearMap :=
    (extendCLM (n := n) (p := p) (Ω := Ω) hΩmeas).toLinearMap
  norm_map' := norm_extendCLM_apply (n := n) (p := p) (Ω := Ω) hΩmeas

/-- Zero extension `W^{0,p}(Ω) → W^{0,p}(ℝ^n)` for a measurable set `Ω`. -/
noncomputable def operator (hΩmeas : MeasurableSet Ω) : Operator n 0 p Ω where
  toContinuousLinearMap :=
    (zeroExtendₗᵢ (n := n) (p := p) (Ω := Ω) hΩmeas).toContinuousLinearMap
  agree_ae := by
    intro u
    have hbase :=
      zeroExtendLp_agree_ae (n := n) (p := p) (Ω := Ω) hΩmeas
        (baseProj (n := n) (p := p) (Ω := Ω) u)
    filter_upwards [hbase] with x hx
    calc
      (((extendCLM (n := n) (p := p) (Ω := Ω) hΩmeas u :
            WkpAmbientOn n 0 p Set.univ) (baseIndex n 0)) x) =
          ((zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas
              (baseProj (n := n) (p := p) (Ω := Ω) u) :
                DerivLp n p Set.univ) x) := by
            rw [extendCLM_apply_base]
      _ = ((baseProj (n := n) (p := p) (Ω := Ω) u : DerivLp n p Ω) x) := hx
      _ = (((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0)) x) := by
            rw [baseProj_apply]

/-- The base coordinate of the order-zero graph-space extension is the `Lp`
indicator extension. -/
theorem operator_apply_base (hΩmeas : MeasurableSet Ω)
    (u : W^{0,p}(Ω)) :
    (((operator (n := n) (p := p) (Ω := Ω) hΩmeas).toContinuousLinearMap u :
          WkpAmbientOn n 0 p Set.univ) (baseIndex n 0) :
        DerivLp n p Set.univ) =
      zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas
        ((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0)) := by
  change
    ((extendCLM (n := n) (p := p) (Ω := Ω) hΩmeas u :
        WkpAmbientOn n 0 p Set.univ) (baseIndex n 0) :
      DerivLp n p Set.univ) = _
  rw [extendCLM_apply_base, baseProj_apply]

/-- Measurable-domain zero extension preserves the complete `W^{0,p}`
graph-space norm. -/
theorem norm_operator_apply (hΩmeas : MeasurableSet Ω)
    (u : W^{0,p}(Ω)) :
    ‖(operator (n := n) (p := p) (Ω := Ω) hΩmeas).toContinuousLinearMap u‖ = ‖u‖ :=
  (zeroExtendₗᵢ (n := n) (p := p) (Ω := Ω) hΩmeas).norm_map u

/-- Order-zero graph-space zero extension is injective. -/
theorem operator_injective (hΩmeas : MeasurableSet Ω) :
    Function.Injective
      (operator (n := n) (p := p) (Ω := Ω) hΩmeas).toContinuousLinearMap :=
  (zeroExtendₗᵢ (n := n) (p := p) (Ω := Ω) hΩmeas).injective

/-- Restricting the order-zero zero extension to `Ω` recovers the input. -/
@[simp] theorem restrict_zeroExtend
    (hΩmeas : MeasurableSet Ω) (u : W^{0,p}(Ω)) :
    restrictCLM (n := n) (k := 0) (p := p) hΩmeas (Set.subset_univ Ω)
        ((zeroExtendₗᵢ (n := n) (p := p) (Ω := Ω) hΩmeas) u) =
      u := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  have ha : a = baseIndex n 0 := a.eq_baseIndex_of_order_zero
  subst a
  rw [restrictCLM_apply_coe, restrictAmbient_apply]
  change
    restrictDerivLp (n := n) (p := p) (Set.subset_univ Ω)
        (zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas
          ((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0))) =
      ((u : WkpAmbientOn n 0 p Ω) (baseIndex n 0) : DerivLp n p Ω)
  exact restrict_zeroExtendLp (n := n) (p := p) (Ω := Ω) hΩmeas _

/-- Restriction is a left inverse to order-zero graph-space zero extension. -/
@[simp] theorem restrictCLM_comp_zeroExtend
    (hΩmeas : MeasurableSet Ω) :
    (restrictCLM (n := n) (k := 0) (p := p)
      hΩmeas (Set.subset_univ Ω)).comp
        (zeroExtendₗᵢ
          (n := n) (p := p) (Ω := Ω) hΩmeas).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (W^{0,p}(Ω)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact restrict_zeroExtend (n := n) (p := p) (Ω := Ω) hΩmeas u

/-- The order-zero graph-space zero-extension map has operator norm at most
one. -/
theorem norm_operator_le_one (hΩmeas : MeasurableSet Ω) :
    ‖(operator (n := n) (p := p) (Ω := Ω) hΩmeas).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  simpa using
    (norm_operator_apply (n := n) (p := p) (Ω := Ω) hΩmeas u).le

/-- Every measurable set admits the order-zero graph-space zero-extension
operator. -/
theorem exists_extensionOperator (hΩmeas : MeasurableSet Ω) :
    HasExtensionOperator n 0 p Ω :=
  ⟨operator (n := n) (p := p) (Ω := Ω) hΩmeas⟩

end Zero

end GraphSpace

end Extension

end SobolevSpace

end
