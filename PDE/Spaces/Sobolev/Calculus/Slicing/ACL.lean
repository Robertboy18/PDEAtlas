/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.Coordinate
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.Slicing.ACLClosure

/-!
# Absolutely continuous representatives on almost every coordinate line

We prove the Euclidean ACL theorem along every coordinate direction
for global `W^{1,1}` functions. Smooth compactly supported approximation gives
classical fundamental-theorem identities. A measure-preserving split of the
selected coordinate and the product-space closure theorem then pass those
identities to almost every parallel line.

The resulting representative is explicit: it is the normalized primitive
`lineRepresentative` of the stored weak derivative. It agrees almost
everywhere with the original Sobolev slice, is absolutely continuous on every
compact interval, and has the expected classical derivative almost everywhere.

This is the "absolutely continuous on lines" (ACL) property of Sobolev functions, here for
`u ∈ W^{1,1}(ℝ^(n+1))`: for almost every line parallel to the `i`-th axis, `u` has a representative
that is absolutely continuous on compact intervals and whose classical derivative is the weak
derivative `∂ᵢu` almost everywhere on the line. In one dimension this is the characterization of
`W^{1,p}(I)` by absolutely continuous functions (Brezis,
*Functional Analysis, Sobolev Spaces and PDE*, Chapter 8; Evans, PDE, §5.2.2, p. 259, where it is
left to the exercises). The converse direction, reconstructing `∂ᵢu` from line data, is
`Slicing.ACLConverse`.

## Main results

* `coordinateBaseSlice`, `coordinateWeakDerivativeSlice`: the slices
  `t ↦ u (y, t)` and `t ↦ ∂ᵢu (y, t)` of the stored `L¹` coordinates.
* `coordinateACLRepresentative`: the normalized primitive of the derivative
  slice, the canonical absolutely continuous representative on the line.
* `ae_coordinateSlice_acl`: for almost every `y`, both slices are integrable
  and the representative agrees almost everywhere with the slice of `u`.
* `ae_forall_absolutelyContinuousOnInterval_coordinateACLRepresentative`,
  `ae_hasDerivAt_coordinateACLRepresentative`: on almost every line, the
  representative is absolutely continuous on each compact interval and its
  derivative is the weak derivative slice almost everywhere.
  `ae_absolutelyContinuousOnInterval_coordinateACLRepresentative` is the form for one fixed
  interval.

## Implementation notes

Only `W^{1,1}` on all of `ℝ^(n+1)` is treated, since the argument is a global
`L¹` approximation by smooth compactly supported functions
(`globalApproximation_WkpSpace`) followed by the product-space closure theorem
of `Slicing.ACLClosure`. Local versions follow by cutoff.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for the absolutely continuous representative of a `W^{1,p}` function on
  an interval.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, p. 259, which states this one-dimensional
  characterization, leaves it to the exercises, and remarks that so simple a characterization is
  only available for `n = 1`.
  <https://doi.org/10.1090/gsm/019>
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  Chapman and Hall/CRC, 2015, Chapter 4, Sobolev Functions, pp. 158-207, for absolute continuity of
  Sobolev functions on lines.
  <https://doi.org/10.1201/b18333>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Slices

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

open SobolevSpace.GraphSpace

private theorem integrable_comp_joinCoordinate
    {n : ℕ} (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : Integrable f (volume : Measure (ℝ^(n + 1)))) :
    Integrable (fun p : ℝ^n × ℝ ↦ f (joinCoordinate i p))
      ((volume : Measure (ℝ^n)).prod volume) := by
  have hmp : MeasurePreserving
      (coordinateMeasurableEquiv i).symm
      ((volume : Measure (ℝ^n)).prod volume)
      (volume : Measure (ℝ^(n + 1))) := by
    simpa only [Measure.volume_eq_prod] using
      MeasurePreserving.symm
        (coordinateMeasurableEquiv i)
        (measurePreserving_coordinateMeasurableEquiv i)
  simpa only [Function.comp_def,
    coordinateMeasurableEquiv_symm_apply] using
      hmp.integrable_comp_of_integrable hf

private theorem eLpNorm_comp_joinCoordinate
    {n : ℕ} (i : Fin (n + 1)) (f : ℝ^(n + 1) → ℝ)
    (hf : AEStronglyMeasurable f (volume : Measure (ℝ^(n + 1)))) :
    eLpNorm (fun p : ℝ^n × ℝ ↦ f (joinCoordinate i p)) 1
        ((volume : Measure (ℝ^n)).prod volume) =
      eLpNorm f 1 (volume : Measure (ℝ^(n + 1))) := by
  have hmp : MeasurePreserving
      (coordinateMeasurableEquiv i).symm
      ((volume : Measure (ℝ^n)).prod volume)
      (volume : Measure (ℝ^(n + 1))) := by
    simpa only [Measure.volume_eq_prod] using
      MeasurePreserving.symm
        (coordinateMeasurableEquiv i)
        (measurePreserving_coordinateMeasurableEquiv i)
  simpa only [Function.comp_def,
    coordinateMeasurableEquiv_symm_apply] using
      eLpNorm_comp_measurePreserving (p := (1 : ℝ≥0∞)) hf hmp

private theorem lineRepresentative_coordinateSlice
    {n : ℕ} (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : ℝ^n) :
    lineRepresentative (coordinateSlice i f y)
        (fun t ↦ coordinateDerivativeInSplit i f (y, t)) =
      coordinateSlice i f y := by
  apply lineRepresentative_eq
  · exact (coordinateSlice_contDiff (m := 1) i (hf.of_le (by simp)) y).continuous
      |>.intervalIntegrable 0 1
  · intro a b
    have hslice : ContDiff ℝ 1 (coordinateSlice i f y) :=
      coordinateSlice_contDiff i (hf.of_le (by simp)) y
    have hderiv (t : ℝ) :
        HasDerivAt (coordinateSlice i f y)
          (coordinateDerivativeInSplit i f (y, t)) t := by
      exact (hslice.differentiable (by norm_num) t).hasDerivAt.congr_deriv
        (deriv_coordinateSlice i (hf.of_le (by simp)) y t)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hderiv t)
      ((coordinateDerivativeInSplit_continuous
        i (hf.of_le (by simp))).comp
          (continuous_const.prodMk continuous_id) |>.intervalIntegrable a b)

/-- The selected-coordinate slice of the order-zero representative of a
global `W^{1,1}` element. -/
def coordinateBaseSlice {n : ℕ} (i : Fin (n + 1))
    (U : W^{1,1}(ℝ^(n + 1)))
    (y : ℝ^n) : ℝ → ℝ :=
  coordinateSlice i
    (wkpBaseCoordinateCLM
      (n := n + 1) (m := 1) (p := 1) (Ω := Set.univ) U :
        ℝ^(n + 1) → ℝ)
    y

/-- The selected weak derivative of a global `W^{1,1}` element, restricted
to a parallel coordinate line. -/
def coordinateWeakDerivativeSlice {n : ℕ} (i : Fin (n + 1))
    (U : W^{1,1}(ℝ^(n + 1)))
    (y : ℝ^n) : ℝ → ℝ :=
  coordinateSlice i
    (wkpCoordinateCLM
      (n := n + 1) (p := 1) (Ω := Set.univ)
      (singleDerivIndex (n + 1) i) U :
        ℝ^(n + 1) → ℝ)
    y

/-- The canonical absolutely continuous representative of a coordinate
Sobolev slice. -/
def coordinateACLRepresentative {n : ℕ} (i : Fin (n + 1))
    (U : W^{1,1}(ℝ^(n + 1)))
    (y : ℝ^n) : ℝ → ℝ :=
  lineRepresentative (coordinateBaseSlice i U y)
    (coordinateWeakDerivativeSlice i U y)

/-- `L¹` convergence of `F m → G` on `ℝ^(n+1)`, read through representatives `g m` of `F m`, in
the split coordinates `ℝ^n × ℝ` of `joinCoordinate i`. -/
private theorem tendsto_eLpNorm_comp_joinCoordinate {n : ℕ} (i : Fin (n + 1))
    {F : ℕ → DerivLp (n + 1) 1 Set.univ} {G : DerivLp (n + 1) 1 Set.univ}
    (hF : Tendsto F atTop (𝓝 G)) {g : ℕ → ℝ^(n + 1) → ℝ} (hg : ∀ m, Integrable (g m))
    (hG : Integrable (G : ℝ^(n + 1) → ℝ)) (hFg : ∀ m, (F m : ℝ^(n + 1) → ℝ) =ᵐ[volume] g m) :
    Tendsto (fun m ↦ eLpNorm ((fun p : ℝ^n × ℝ ↦ g m (joinCoordinate i p)) -
      fun p ↦ (G : ℝ^(n + 1) → ℝ) (joinCoordinate i p)) 1 ((volume : Measure (ℝ^n)).prod volume))
      atTop (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F G).1 hF
  simp only [domainMeasure, Measure.restrict_univ] at h
  refine h.congr fun m ↦ ?_
  rw [eLpNorm_congr_ae ((hFg m).sub EventuallyEq.rfl),
    ← eLpNorm_comp_joinCoordinate i _ ((hg m).sub hG).1]
  rfl

/-- Almost every line parallel to the selected coordinate has integrable
value and derivative slices, and its canonical absolutely continuous
representative agrees almost everywhere with the Sobolev value slice. -/
theorem ae_coordinateSlice_acl
    {n : ℕ} (i : Fin (n + 1)) (U : W^{1,1}(ℝ^(n + 1))) :
    ∀ᵐ y : ℝ^n, (
      Integrable (coordinateBaseSlice i U y) volume ∧
      Integrable (coordinateWeakDerivativeSlice i U y) volume ∧
      coordinateACLRepresentative i U y
        =ᵐ[volume] coordinateBaseSlice i U y) := by
  let baseProj : W^{1,1}(ℝ^(n + 1)) →L[ℝ] DerivLp (n + 1) 1 Set.univ :=
    wkpBaseCoordinateCLM (n := n + 1) (m := 1) (p := 1) (Ω := Set.univ)
  let derivProj : W^{1,1}(ℝ^(n + 1)) →L[ℝ] DerivLp (n + 1) 1 Set.univ :=
    wkpCoordinateCLM (n := n + 1) (p := 1) (Ω := Set.univ) (singleDerivIndex (n + 1) i)
  obtain ⟨f_m, hf_m, hcs_m, hU_norm⟩ :=
    globalApproximation_WkpSpace (Approximation.standardMollifier (n + 1)) (by norm_num) 1 U
  let U_m : ℕ → W^{1,1}(ℝ^(n + 1)) := fun m ↦
    mkWkpSpaceOnOfContDiff (n := n + 1) (k := 1) (p := 1) (Ω := Set.univ)
      (f_m m) (hf_m m) (hcs_m m)
  have hU_tendsto : Tendsto U_m atTop (𝓝 U) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [U_m] using hU_norm)
  have hu : Integrable (baseProj U : ℝ^(n + 1) → ℝ) :=
    memLp_one_iff_integrable.mp (by simpa [domainMeasure] using Lp.memLp (baseProj U))
  have hdu : Integrable (derivProj U : ℝ^(n + 1) → ℝ) :=
    memLp_one_iff_integrable.mp (by simpa [domainMeasure] using Lp.memLp (derivProj U))
  have hdfInt (m : ℕ) : Integrable (∂[i] (f_m m)) := by
    refine (PDE.contDiff_top_partialDeriv (hf_m m)).continuous.integrable_of_hasCompactSupport ?_
    simpa [partialDeriv] using
      (hcs_m m).fderiv_apply (𝕜 := ℝ) (v := EuclideanSpace.single i (1 : ℝ))
  have hbase_rep (m : ℕ) : (baseProj (U_m m) : ℝ^(n + 1) → ℝ) =ᵐ[volume] f_m m := by
    simpa [baseProj, U_m, domainMeasure, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (n := n + 1) (k := 1) (p := 1) (Ω := Set.univ)
        (f_m m) (hf_m m) (hcs_m m) (baseIndex (n + 1) 1)
  have hderiv_rep (m : ℕ) :
      (derivProj (U_m m) : ℝ^(n + 1) → ℝ) =ᵐ[volume] ∂[i] (f_m m) := by
    simpa [derivProj, U_m, domainMeasure, singleDerivIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (n := n + 1) (k := 1) (p := 1) (Ω := Set.univ)
        (f_m m) (hf_m m) (hcs_m m) (singleDerivIndex (n + 1) i)
  have hbase := tendsto_eLpNorm_comp_joinCoordinate i
    ((baseProj.continuous.tendsto U).comp hU_tendsto)
    (fun m ↦ (hf_m m).continuous.integrable_of_hasCompactSupport (hcs_m m)) hu hbase_rep
  have hderiv := tendsto_eLpNorm_comp_joinCoordinate i
    ((derivProj.continuous.tendsto U).comp hU_tendsto) hdfInt hdu hderiv_rep
  exact (ae_lineRepresentative_eq_of_prod_L1_approximation
    (integrable_comp_joinCoordinate i hu) (integrable_comp_joinCoordinate i hdu)
    (fun m ↦ (coordinateSlice_product_continuous i (hf_m m).continuous
      ).integrable_of_hasCompactSupport (coordinateSlice_product_hasCompactSupport i (hcs_m m)))
    (fun m ↦ (coordinateDerivativeInSplit_continuous i ((hf_m m).of_le (by simp))
      ).integrable_of_hasCompactSupport (coordinateDerivativeInSplit_hasCompactSupport i (hcs_m m)))
    hbase hderiv fun m y ↦ lineRepresentative_coordinateSlice i (hf_m m) y :)

/-- Almost every canonical coordinate representative agrees with the
selected Sobolev value slice. -/
theorem ae_coordinateACLRepresentative_eq
    {n : ℕ} (i : Fin (n + 1)) (U : W^{1,1}(ℝ^(n + 1))) :
    ∀ᵐ y : ℝ^n,
      coordinateACLRepresentative i U y
        =ᵐ[volume] coordinateBaseSlice i U y := by
  filter_upwards [ae_coordinateSlice_acl i U] with y hy
  exact hy.2.2

/-- On almost every line parallel to the selected coordinate, the canonical
representative is absolutely continuous on the given compact interval. -/
theorem ae_absolutelyContinuousOnInterval_coordinateACLRepresentative
    {n : ℕ} (i : Fin (n + 1)) (U : W^{1,1}(ℝ^(n + 1))) (a b : ℝ) :
    ∀ᵐ y : ℝ^n,
      AbsolutelyContinuousOnInterval
        (coordinateACLRepresentative i U y) a b := by
  filter_upwards [ae_coordinateSlice_acl i U] with y hy
  exact absolutelyContinuousOnInterval_lineRepresentative hy.2.1 a b

/-- On almost every line parallel to the selected coordinate, the canonical
representative is absolutely continuous on every compact interval. The exceptional null set
does not depend on the interval. -/
theorem ae_forall_absolutelyContinuousOnInterval_coordinateACLRepresentative
    {n : ℕ} (i : Fin (n + 1)) (U : W^{1,1}(ℝ^(n + 1))) :
    ∀ᵐ y : ℝ^n, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval
        (coordinateACLRepresentative i U y) a b := by
  filter_upwards [ae_coordinateSlice_acl i U] with y hy a b
  exact absolutelyContinuousOnInterval_lineRepresentative hy.2.1 a b

/-- On almost every line parallel to the selected coordinate, the classical
derivative of the canonical representative equals the stored weak derivative
almost everywhere. -/
theorem ae_hasDerivAt_coordinateACLRepresentative
    {n : ℕ} (i : Fin (n + 1)) (U : W^{1,1}(ℝ^(n + 1))) :
    ∀ᵐ y : ℝ^n, ∀ᵐ t ∂volume,
      HasDerivAt (coordinateACLRepresentative i U y)
        (coordinateWeakDerivativeSlice i U y t) t := by
  filter_upwards [ae_coordinateSlice_acl i U] with y hy
  exact ae_hasDerivAt_lineRepresentative hy.2.1

end SobolevSpace.Slices
