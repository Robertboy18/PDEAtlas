/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.PlanarReflection.Basic

import CAS.ExactTactic

/-!
# Smooth and Sobolev regularity of planar reflection

For a function `f` of `(r, z)` the even reflection `evenReflection2D f` is `f (|r|, z)` and the odd
reflection `oddReflection2D f` is `-f (-r, z)` for `r < 0` and `f (r, z)` otherwise; on `ℝ^2` the
radial coordinate is `x₀` and the axis is `x₀ = 0`. We prove that the reflections are `C¹`, `C²` or
`W^{2,2}` across the axis under conditions on `f` at the axis, that their mixed derivatives are
reflections of those of `f`, and that reflection doubles integrals against an even weight.

## Main results

* `contDiff_one_evenRadialReflection`, `contDiff_two_evenRadialReflection`: if `F` is `C¹` (resp.
  `C²`) and `∂_r F = 0` on the axis, the even reflection of `F` is `C¹` (resp. `C²`).
* `contDiff_one_oddRadialReflection`, `contDiff_two_oddRadialReflection`: if `A` is `C¹` and
  vanishes on the axis, its odd reflection is `C¹`; if `A` is `C²` and also `∂_r² A = 0` on the
  axis, its odd reflection is `C²`.
* `oddRadialReflection_swapped_globalH2`: if `A` is `C²` and vanishes on the axis, and the
  derivatives of order at most two of `A ∘ radialCoordinateSwap2D` are in `L²` of the upper half
  space, then the odd reflection of `A`, composed with the swap, agrees almost everywhere with the
  base coordinate of an element of `W^{2,2}(ℝ²)`.
* `mixedIteratedDeriv2D_evenReflection_all_mixed_orders`: if the radial derivatives of `∂_z^ℓ f` of
  all orders exist and those of odd order vanish on the axis, then `∂_r^(2k) ∂_z^ℓ` of the even
  reflection is the even reflection of `∂_r^(2k) ∂_z^ℓ f` and `∂_r^(2k+1) ∂_z^ℓ` of it is the odd
  reflection of `∂_r^(2k+1) ∂_z^ℓ f`.
* `integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight`: for all `q`, `ℓ`, `f` and `Φ`
  the iterated integral over the plane of `(∂_r^q ∂_z^ℓ Ef)² EΦ`, where `E` is the even reflection,
  is twice the iterated integral over `r > 0` of `(∂_r^q ∂_z^ℓ f)² Φ`;
  `integral_mixedIteratedDeriv2D_oddReflection_sq_mul_evenWeight` is the same identity for the odd
  reflection of `f`.

## How it works

The `C¹` statements assemble the derivative from the two partial derivatives
(`fderiv_eq_partialDeriv_smul_projections`): the radial derivative of the even reflection is the odd
reflection of `∂_r F`, its axial derivative is the even reflection of `∂_z F`
(`partialDeriv_evenRadialReflection_radial`, `partialDeriv_evenRadialReflection_axial`), and the odd
reflection of a continuous function vanishing on the axis is continuous. For `C²` we apply the `C¹`
statements to the partial derivatives; in the even case the condition `∂_r ∂_z F = 0` on the axis
follows from `∂_r F = 0` there by differentiating along the axis (`partialDeriv_axial_axis_eq_zero`)
and the symmetry of second derivatives (`PDE.partialDeriv_partialDeriv_comm`). For `W^{2,2}` we swap
the coordinates (`radialCoordinateSwap2D`) so that the half plane `r > 0` becomes the upper half
space `ℝ^2₊` and apply `oddReflectAmbient_mem_globalH2_of_contDiffOneRepresentative` from
`PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.OddSecondOrder`, with the `C¹` odd
reflection as the required representative. The parity formulas, the classical derivative formulas
for reflections, follow by induction on the radial order from
`deriv_evenReflection2D_eq_oddReflection2D` and `deriv_oddReflection2D_eq_evenReflection2D`, which
need exactly the vanishing of the odd-order rows on the axis. The integral identities use only the
formulas off the axis, which is a null set, and Mathlib's `integral_comp_abs`; they need no
regularity or integrability and do not by themselves give Sobolev membership. The constant identity
`reflectedKInfinity_constant_eq` is closed by the `cas` tactic of SymLean, our verified computer
algebra system.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.4, Proposition 8,
  (247)-(257), pp. 51-52, for the parity extensions (248), the conditions (249) on the axis, the
  derivative formula (253) off the axis and the weighted identity (252), proved by the change of
  variables (256).
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology Sobolev
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace SobolevSpace.Weighted

/-- In two dimensions, a differentiable function whose two coordinate partial derivatives are
`Cⁿ` is `Cⁿ⁺¹`, since its Fréchet derivative is `∂₀G • proj₀ + ∂₁G • proj₁`. -/
private theorem contDiff_succ_of_partialDeriv {G : (ℝ^2) → ℝ} {n : ℕ} (hG : Differentiable ℝ G)
    (h0 : ContDiff ℝ n (fun y ↦ (∂[0] G) y)) (h1 : ContDiff ℝ n (fun y ↦ (∂[1] G) y)) :
    ContDiff ℝ (n + 1) G := by
  refine contDiff_succ_iff_fderiv.2 ⟨hG, by simp, ?_⟩
  rw [funext (fderiv_eq_partialDeriv_smul_projections G)]
  exact (h0.smul contDiff_const).add (h1.smul contDiff_const)

/-- If `F` is `C¹` on `ℝ²` and `∂_r F = 0` on the axis, the even reflection `F (|r|, z)` is `C¹` on
`ℝ²`. -/
theorem contDiff_one_evenRadialReflection
    (F : (ℝ^2) → ℝ) (hF : ContDiff ℝ 1 F)
    (htrace : ∀ z : ℝ,
      (∂[0] F)
        (EuclideanSpace.single (1 : Fin 2) z) = 0) :
    ContDiff ℝ 1 (fun y : (ℝ^2) ↦
      F (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1))) := by
  refine contDiff_succ_of_partialDeriv (n := 0) (differentiable_evenRadialReflection F hF htrace)
    (contDiff_zero.2 ?_) (contDiff_zero.2 ?_)
  · simpa only [partialDeriv_evenRadialReflection_radial F hF htrace] using
      continuous_oddRadialReflectionPoint _
        (PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 0) (i := 0) hF).continuous htrace
  · exact ((PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 0) (i := 1) hF).continuous.comp
      continuous_evenRadialReflectionPoint).congr fun y ↦
        (partialDeriv_evenRadialReflection_axial F hF htrace y).symm

/-- The axial derivative of a `C¹` function vanishes on the axis whenever
the function itself vanishes identically there. -/
theorem partialDeriv_axial_axis_eq_zero
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 1 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (z : ℝ) :
    (∂[1] A)
      (EuclideanSpace.single (1 : Fin 2) z) = 0 := by
  let x : (ℝ^2) := EuclideanSpace.single (1 : Fin 2) z
  have hline : (fun t : ℝ ↦ A
      (x + t • EuclideanSpace.single (1 : Fin 2) 1)) = fun _ ↦ 0 := by
    funext t
    rw [← haxis (z + t)]
    congr 1
    ext i
    fin_cases i <;> simp [x]
  change (∂[1] A) x = 0
  unfold partialDeriv
  rw [← (hA.differentiable (by norm_num) x).lineDeriv_eq_fderiv]
  unfold lineDeriv
  rw [hline]
  simp

/-- If `A` is `C¹` on `ℝ²` and vanishes on the axis, the odd reflection of `A`, equal to
`-A (-r, z)` for `r < 0` and to `A (r, z)` otherwise, is `C¹` on `ℝ²`. -/
theorem contDiff_one_oddRadialReflection
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 1 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0) :
    ContDiff ℝ 1 (fun y : (ℝ^2) ↦ if y 0 < 0 then
      -A (radialSignFlip2D y) else A y) := by
  refine contDiff_succ_of_partialDeriv (n := 0) (differentiable_oddRadialReflection A hA haxis)
    (contDiff_zero.2 ?_) (contDiff_zero.2 ?_)
  · exact ((PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 0) (i := 0) hA).continuous.comp
      continuous_evenRadialReflectionPoint).congr fun y ↦
        (partialDeriv_oddRadialReflection_radial A hA haxis y).symm
  · simpa only [partialDeriv_oddRadialReflection_axial A hA haxis] using
      continuous_oddRadialReflectionPoint _
        (PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 0) (i := 1) hA).continuous
        (partialDeriv_axial_axis_eq_zero A hA haxis)

/-- Let `A` be `C²` on `ℝ²` and zero on the axis, with the derivatives of order at most two of
`A ∘ radialCoordinateSwap2D` in `L²` of the upper half space. Then there are `U ∈ W^{2,2}(ℝ^2₊)`,
whose coordinates are almost everywhere these classical derivatives, and `V ∈ W^{2,2}(ℝ²)`, equal to
the odd reflection `oddReflectAmbient` of `U`, whose base coordinate is almost everywhere the odd
reflection of `A` composed with the swap. The odd reflection of `A` is not assumed to be `C²`. -/
theorem oddRadialReflection_swapped_globalH2_withCoordinates
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 2 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (hmem : ∀ a : SobolevSpace.GraphSpace.DerivIndex 2 2,
      MemLp (iteratedPartialDeriv (n := 2) a.toList
        (A ∘ radialCoordinateSwap2D)) 2
        (SobolevSpace.domainMeasure 2 (SobolevSpace.HalfSpace.upper 2))) :
    ∃ U : W^{2,2}(SobolevSpace.HalfSpace.upper 2),
      ∃ V : W^{2,2}(ℝ^2),
        (∀ (α : List (Fin 2)) (hα : α.length ≤ 2),
          (SobolevSpace.GraphSpace.HigherOrderReflection.coordinateAtList
            (n := 2) (m := 2) U α hα : (ℝ^2) → ℝ) =ᵐ[
              SobolevSpace.domainMeasure 2 (SobolevSpace.HalfSpace.upper 2)]
            fun x ↦ iteratedPartialDeriv (n := 2) α
              (A ∘ radialCoordinateSwap2D) x) ∧
        (V : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ) =
          SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectAmbient
            (n := 2) (m := 2)
            (U : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2
              (SobolevSpace.HalfSpace.upper 2)) ∧
        ((((V : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
          (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) =ᵐ[volume]
          ((fun x : (ℝ^2) ↦ if x 0 < 0 then -A (radialSignFlip2D x) else A x) ∘
            radialCoordinateSwap2D) := by
  let Fs : (ℝ^2) → ℝ := A ∘ radialCoordinateSwap2D
  have hFs : ContDiff ℝ 2 Fs := hA.comp radialCoordinateSwap2D.contDiff
  let U : W^{2,2}(SobolevSpace.HalfSpace.upper 2) :=
    SobolevSpace.GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite
      (n := 2) (k := 2) (p := (2 : ℝ≥0∞)) Fs hFs (by
        simpa [Fs] using hmem)
  let O : (ℝ^2) → ℝ := fun x ↦ if x 0 < 0 then
    -A (radialSignFlip2D x) else A x
  let g : (ℝ^2) → ℝ := O ∘ radialCoordinateSwap2D
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hO1 : ContDiff ℝ 1 O := by
    simpa [O] using contDiff_one_oddRadialReflection A hA1 haxis
  have hg : ContDiff ℝ 1 g := hO1.comp radialCoordinateSwap2D.contDiff
  have hAd := hA1.differentiable one_ne_zero
  have hsource (α : List (Fin 2)) (hα : α.length ≤ 2) :
      (SobolevSpace.GraphSpace.HigherOrderReflection.coordinateAtList
        (n := 2) (m := 2) U α hα : (ℝ^2) → ℝ) =ᵐ[
          SobolevSpace.domainMeasure 2 (SobolevSpace.HalfSpace.upper 2)]
        fun x ↦ iteratedPartialDeriv (n := 2) α Fs x := by
    let a := SobolevSpace.GraphSpace.derivIndexOfList (n := 2) (k := 2) α hα
    have hU := SobolevSpace.GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
      (n := 2) (k := 2) (p := (2 : ℝ≥0∞)) Fs hFs
      (by simpa [Fs] using hmem) a
    have hperm : a.toList.Perm α :=
      SobolevSpace.GraphSpace.derivIndexOfList_toList_perm α hα
    have hreg : ContDiff ℝ (a.toList.length : ℕ∞) Fs :=
      hFs.of_le (WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by
        rw [SobolevSpace.GraphSpace.DerivIndex.toList_length]; exact Nat.le_of_lt_succ a.1.2)))
    have heq := SobolevSpace.iteratedPartialDeriv_congr_perm_of_contDiff
      (n := 2) hreg hperm
    simpa [a, SobolevSpace.GraphSpace.HigherOrderReflection.coordinateAtList,
      U] using hU.trans (Filter.Eventually.of_forall (congrFun heq))
  have hbase : g =ᵐ[volume]
      (SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectListCoordinate
        (n := 2) (m := 2) U [] (by simp) : (ℝ^2) → ℝ) := by
    have hb :=
      SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectListCoordinate_apply_ae_of_ae_eq
        (n := 2) (m := 2) U [] (by simp) Fs (hsource [] (by simp))
    symm
    filter_upwards [hb] with x hx
    rw [hx]
    by_cases hneg : x 1 < 0
    · have hswap :
          radialCoordinateSwap2D (SobolevSpace.HalfSpace.reflect 2 x) =
            radialSignFlip2D (radialCoordinateSwap2D x) := by
        simpa [radialCoordinateSwap2D, radialSignFlip2D] using
          radialCoordinateSwap2D_reflect x
      simpa [g, O, Fs, hneg, PDE.Common.lastIndex, radialCoordinateSwap2D,
        radialSignFlip2D] using congrArg (fun y ↦ -A y) hswap
    · simp [g, O, Fs, hneg, PDE.Common.lastIndex, radialCoordinateSwap2D,
        radialSignFlip2D]
  have hcoord : ∀ i : Fin 2,
      (fun x ↦ (∂[i] g) x) =ᵐ[volume]
        (SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectListCoordinate
          (n := 2) (m := 2) U [i] (by simp) : (ℝ^2) → ℝ) := by
    intro i
    have hr :=
      SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectListCoordinate_apply_ae_of_ae_eq
        (n := 2) (m := 2) U [i] (by simp)
        (fun x ↦ (∂[i] Fs) x) (by
          simpa [iteratedPartialDeriv] using hsource [i] (by simp))
    filter_upwards [hr] with y hy
    rw [hy]
    fin_cases i
    · simp only at hy ⊢
      change (∂[0] (O ∘ radialCoordinateSwap2D)) y = _
      rw [partialDeriv_comp_radialCoordinateSwap2D_zero O (hO1.differentiable one_ne_zero),
        partialDeriv_oddRadialReflection_axial A hA1 haxis]
      by_cases hyneg : y 1 < 0
      · simp [hyneg, Fs, PDE.Common.lastIndex, radialCoordinateSwap2D_reflect,
          partialDeriv_comp_radialCoordinateSwap2D_zero A hAd]
      · simp [hyneg, Fs, PDE.Common.lastIndex, partialDeriv_comp_radialCoordinateSwap2D_zero A hAd]
    · simp only at hy ⊢
      change (∂[1] (O ∘ radialCoordinateSwap2D)) y = _
      rw [partialDeriv_comp_radialCoordinateSwap2D_one O (hO1.differentiable one_ne_zero),
        partialDeriv_oddRadialReflection_radial A hA1 haxis]
      by_cases hyneg : y 1 < 0
      · simp [hyneg, Fs, PDE.Common.lastIndex, abs_of_neg hyneg,
          partialDeriv_comp_radialCoordinateSwap2D_one A hAd]
      · have harg :
          EuclideanSpace.single 0 |y 1| + EuclideanSpace.single 1 (y 0) =
            radialCoordinateSwap2D y := by
          ext j
          fin_cases j <;> simp [radialCoordinateSwap2D,
            abs_of_nonneg (le_of_not_gt hyneg)]
        simpa [hyneg, Fs, PDE.Common.lastIndex, abs_of_nonneg (le_of_not_gt hyneg),
          partialDeriv_comp_radialCoordinateSwap2D_one A hAd] using congrArg (∂[0] A) harg
  let V : W^{2,2}(ℝ^2) :=
    ⟨SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectAmbient
        (n := 2) (m := 2)
        (U : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2
          (SobolevSpace.HalfSpace.upper 2)),
      oddReflectAmbient_mem_globalH2_of_contDiffOneRepresentative
        (n := 2) U g hg hbase hcoord⟩
  refine ⟨U, V, hsource, rfl, ?_⟩
  simpa only [V, SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectAmbient_apply_baseIndex]
    using hbase.symm

/-- Under the hypotheses of `oddRadialReflection_swapped_globalH2_withCoordinates`, the odd
reflection of `A` composed with `radialCoordinateSwap2D` agrees almost everywhere with the base
coordinate of some `V ∈ W^{2,2}(ℝ²)`. -/
theorem oddRadialReflection_swapped_globalH2
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 2 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (hmem : ∀ a : SobolevSpace.GraphSpace.DerivIndex 2 2,
      MemLp (iteratedPartialDeriv (n := 2) a.toList
        (A ∘ radialCoordinateSwap2D)) 2
        (SobolevSpace.domainMeasure 2 (SobolevSpace.HalfSpace.upper 2))) :
    ∃ V : W^{2,2}(ℝ^2),
      ((((V : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) =ᵐ[volume]
        ((fun x : (ℝ^2) ↦ if x 0 < 0 then -A (radialSignFlip2D x) else A x) ∘
          radialCoordinateSwap2D) := by
  obtain ⟨_U, V, _hsource, _hV, hbase⟩ :=
    oddRadialReflection_swapped_globalH2_withCoordinates A hA haxis hmem
  exact ⟨V, hbase⟩

/-- If `F` is `C²` on `ℝ²` and `∂_r F = 0` on the axis, the even reflection `F (|r|, z)` is `C²` on
`ℝ²`. The vanishing of `∂_r ∂_z F` on the axis, also needed, follows by differentiating `∂_r F = 0`
along the axis and the symmetry of second derivatives. -/
theorem contDiff_two_evenRadialReflection
    (F : (ℝ^2) → ℝ) (hF : ContDiff ℝ 2 F)
    (htrace0 : ∀ z : ℝ,
      (∂[0] F)
        (EuclideanSpace.single (1 : Fin 2) z) = 0) :
    ContDiff ℝ 2 (fun y : (ℝ^2) ↦
      F (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1))) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hA1 := PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 1) (i := 0) hF
  have hB1 := PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 1) (i := 1) hF
  -- the mixed trace: `∂₀∂₁F = ∂₁∂₀F` vanishes on the axis because `∂₀F` does
  have hBtrace (z : ℝ) :
      (∂[0] (fun y ↦ (∂[1] F) y)) (EuclideanSpace.single (1 : Fin 2) z) = 0 := by
    rw [PDE.partialDeriv_partialDeriv_comm (n := 2) (f := F) 0 1 hF]
    exact partialDeriv_axial_axis_eq_zero _ hA1 htrace0 z
  refine contDiff_succ_of_partialDeriv (n := 1)
    ((contDiff_one_evenRadialReflection F hF1 htrace0).differentiable one_ne_zero) ?_ ?_
  · simpa only [partialDeriv_evenRadialReflection_radial F hF1 htrace0, Nat.cast_one] using
      contDiff_one_oddRadialReflection _ hA1 htrace0
  · simpa only [partialDeriv_evenRadialReflection_axial F hF1 htrace0, Nat.cast_one] using
      contDiff_one_evenRadialReflection _ hB1 hBtrace

/-- If `A` is `C²` on `ℝ²` and `A` and `∂_r² A` vanish on the axis, the odd reflection of `A` is
`C²` on `ℝ²`. -/
theorem contDiff_two_oddRadialReflection
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 2 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (htrace00 : ∀ z : ℝ,
      (∂[0] (fun y ↦ (∂[0] A) y))
        (EuclideanSpace.single (1 : Fin 2) z) = 0) :
    ContDiff ℝ 2 (fun y : (ℝ^2) ↦ if y 0 < 0 then
      -A (radialSignFlip2D y) else A y) := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  refine contDiff_succ_of_partialDeriv (n := 1)
    ((contDiff_one_oddRadialReflection A hA1 haxis).differentiable one_ne_zero) ?_ ?_
  · simpa only [partialDeriv_oddRadialReflection_radial A hA1 haxis, Nat.cast_one] using
      contDiff_one_evenRadialReflection _
        (PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 1) (i := 0) hA) htrace00
  · simpa only [partialDeriv_oddRadialReflection_axial A hA1 haxis, Nat.cast_one] using
      contDiff_one_oddRadialReflection _
        (PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 1) (i := 1) hA)
        (partialDeriv_axial_axis_eq_zero A hA1 haxis)

/-- If every slice `r ↦ f r z` is `C²` and has derivative `0` at `r = 0`, every slice
`r ↦ evenReflection2D f r z` is `C²`. Continuity of the second derivative across `r = 0` needs no
further condition. -/
theorem contDiff_two_evenReflection2D_radial_slice
    (f : ℝ → ℝ → ℝ)
    (hslice : ∀ z, ContDiff ℝ 2 (fun r ↦ f r z))
    (htrace : ∀ z, deriv (fun r ↦ f r z) 0 = 0) :
    ∀ z, ContDiff ℝ 2 (fun r ↦ evenReflection2D f r z) := by
  intro z
  let d₁ : ℝ → ℝ → ℝ := fun r z ↦
    iteratedDeriv 1 (fun ρ ↦ f ρ z) r
  let d₂ : ℝ → ℝ → ℝ := fun r z ↦
    iteratedDeriv 2 (fun ρ ↦ f ρ z) r
  have hd₁ (r z : ℝ) : HasDerivAt (fun ρ ↦ f ρ z) (d₁ r z) r := by
    have hdiff := (hslice z).differentiable (by norm_num)
    simpa [d₁, iteratedDeriv_one] using hdiff.differentiableAt.hasDerivAt
  have hd₂ (r z : ℝ) : HasDerivAt (fun ρ ↦ d₁ ρ z) (d₂ r z) r := by
    have hdiff := (hslice z).differentiable_iteratedDeriv 1 (by norm_num)
    have hhas := (hdiff r).hasDerivAt
    simpa [d₁, d₂, iteratedDeriv_succ] using hhas
  have hd₁zero : ∀ z, d₁ 0 z = 0 := by
    intro ζ
    simpa [d₁, iteratedDeriv_one] using htrace ζ
  have hfirst := deriv_evenReflection2D_eq_oddReflection2D f d₁ hd₁ hd₁zero
  have hsecond := deriv_oddReflection2D_eq_evenReflection2D d₁ d₂ hd₂ hd₁zero
  -- off the axis the reflections are locally `f (|ρ|)` and `±d₁ (±ρ)`
  have hGdiff : Differentiable ℝ (fun r ↦ evenReflection2D f r z) := fun r ↦ by
    rcases eq_or_ne r 0 with rfl | hr
    · exact (hasDerivAt_evenReflection2D_axis f z
        (by simpa [hd₁zero z] using hd₁ 0 z)).differentiableAt
    · exact (hd₁ |r| z).differentiableAt.comp r (differentiableAt_abs hr)
  have hOddDiff : Differentiable ℝ (fun r ↦ oddReflection2D d₁ r z) := fun r ↦ by
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · refine ((hd₂ (-r) z).comp r (hasDerivAt_neg r)).neg.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hr] with ρ (hρ : ρ < 0)
      simp [oddReflection2D, hρ]
    · exact (hasDerivAt_oddReflection2D_axis d₁ z (d₂ 0 z)
        (hd₁zero z) (hd₂ 0 z)).differentiableAt
    · refine (hd₂ r z).differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hr] with ρ (hρ : 0 < ρ)
      simp [oddReflection2D, not_lt.mpr hρ.le]
  have heq₁ : deriv (fun r ↦ evenReflection2D f r z) = fun r ↦ oddReflection2D d₁ r z :=
    funext fun r ↦ congrFun (congrFun hfirst r) z
  have heq₂ : deriv (fun r ↦ oddReflection2D d₁ r z) = fun r ↦ evenReflection2D d₂ r z :=
    funext fun r ↦ congrFun (congrFun hsecond r) z
  refine (contDiff_nat_iff_iteratedDeriv (f := fun r ↦ evenReflection2D f r z) (n := 2)).2
    ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩
  · interval_cases m
    · simpa using hGdiff.continuous
    · simpa [iteratedDeriv_one, heq₁] using hOddDiff.continuous
    · have hcont : Continuous (fun r ↦ evenReflection2D d₂ r z) :=
        ((hslice z).continuous_iteratedDeriv 2 (by norm_num)).comp continuous_abs
      simpa [iteratedDeriv_succ, heq₁, heq₂] using hcont
  · interval_cases m
    · simpa using hGdiff
    · simpa [iteratedDeriv_one, heq₁] using hOddDiff

/-- For every `ell` and every `f`, `∂_z^ell` of the even reflection of `f` is the even reflection of
`∂_z^ell f`. -/
theorem mixedIteratedDeriv2D_zero_evenReflection
    (ell : ℕ) (f : ℝ → ℝ → ℝ) :
    mixedIteratedDeriv2D 0 ell (evenReflection2D f) =
      evenReflection2D (mixedIteratedDeriv2D 0 ell f) := by
  funext r z
  change iteratedDeriv ell (f |r|) z = iteratedDeriv ell (f |r|) z
  rfl

/-- For every `ell` and every `f`, `∂_z^ell` of the odd reflection of `f` is the odd reflection of
`∂_z^ell f`. -/
theorem mixedIteratedDeriv2D_zero_oddReflection
    (ell : ℕ) (f : ℝ → ℝ → ℝ) :
    mixedIteratedDeriv2D 0 ell (oddReflection2D f) =
      oddReflection2D (mixedIteratedDeriv2D 0 ell f) := by
  funext r z
  by_cases hr : r < 0
  · have hfun : oddReflection2D f r = -(f (-r)) := by
      funext zeta
      simp [oddReflection2D, hr]
    simp only [mixedIteratedDeriv2D, iteratedDeriv_zero]
    rw [hfun, iteratedDeriv_neg]
    simp [oddReflection2D, hr, mixedIteratedDeriv2D]
  · have hfun : oddReflection2D f r = f r := by
      funext zeta
      simp [oddReflection2D, hr]
    simp only [mixedIteratedDeriv2D, iteratedDeriv_zero]
    rw [hfun]
    simp [oddReflection2D, hr, mixedIteratedDeriv2D]

/-- `∂_r^(q+1) f (r, z)` is the derivative at `r` of `ρ ↦ ∂_r^q f (ρ, z)`. -/
theorem mixedIteratedDeriv2D_succ_zero
    (q : ℕ) (f : ℝ → ℝ → ℝ) :
    mixedIteratedDeriv2D (q + 1) 0 f =
      fun r z ↦ deriv (fun rho ↦ mixedIteratedDeriv2D q 0 f rho z) r := by
  funext r z
  simp [mixedIteratedDeriv2D, iteratedDeriv_succ]

/-- Let `d 0 = f`, let `d (s + 1) (r, z)` be the derivative of `ρ ↦ d s (ρ, z)` at every `r` for
`s < q`, and let `d s` vanish on the axis for odd `s ≤ q`. Then `∂_r^q` of the even reflection of
`f` is the even reflection of `d q` if `q` is even and the odd reflection of `d q` if `q` is odd. -/
theorem mixedIteratedDeriv2D_evenReflection_finite_radial_order
    (q : ℕ) (f : ℝ → ℝ → ℝ) (d : ℕ → ℝ → ℝ → ℝ)
    (hzero : d 0 = f)
    (hderiv : ∀ s < q, ∀ r z,
      HasDerivAt (fun rho ↦ d s rho z) (d (s + 1) r z) r)
    (htrace : ∀ s ≤ q, Odd s → ∀ z, d s 0 z = 0) :
    if Even q then
      mixedIteratedDeriv2D q 0 (evenReflection2D f) =
        evenReflection2D (d q)
    else
      mixedIteratedDeriv2D q 0 (evenReflection2D f) =
        oddReflection2D (d q) := by
  induction q with
  | zero =>
      simp only [Even.zero, ite_eq_left]
      rw [mixedIteratedDeriv2D_zero_evenReflection]
      congr 1
      rw [hzero]
      funext r z
      simp [mixedIteratedDeriv2D]
  | succ q ih =>
      have ih' := ih (fun s hs ↦ hderiv s (by omega)) (fun s hs ↦ htrace s (by omega))
      rw [mixedIteratedDeriv2D_succ_zero]
      by_cases hq : Even q
      · simp only [hq, ite_eq_left] at ih'
        simp only [Nat.not_even_iff_odd.mpr hq.add_one, ite_false, ih']
        simpa using deriv_evenReflection2D_eq_oddReflection2D (d q) (d (q + 1))
          (hderiv q (by omega)) (htrace (q + 1) (by omega) hq.add_one)
      · have hqodd : Odd q := Nat.not_even_iff_odd.mp hq
        simp only [hq, ite_false] at ih'
        simp only [hqodd.add_one, ite_eq_left, ih']
        simpa using deriv_oddReflection2D_eq_evenReflection2D (d q) (d (q + 1))
          (hderiv q (by omega)) (htrace q (by omega) hqodd)

/-- Fix `q` and `ell`. If for `s < q` the derivative of `ρ ↦ ∂_r^s ∂_z^ell f (ρ, z)` at every `r` is
`∂_r^(s+1) ∂_z^ell f (r, z)`, and `∂_r^s ∂_z^ell f` vanishes on the axis for odd `s ≤ q`, then
`∂_r^q ∂_z^ell` of the even reflection of `f` is the even reflection of `∂_r^q ∂_z^ell f` if `q` is
even and the odd reflection of `∂_r^q ∂_z^ell f` if `q` is odd. -/
theorem mixedIteratedDeriv2D_evenReflection_finite_mixed_order
    (q ell : ℕ) (f : ℝ → ℝ → ℝ)
    (hderiv : ∀ s < q, ∀ r z,
      HasDerivAt (fun rho ↦ mixedIteratedDeriv2D s ell f rho z)
        (mixedIteratedDeriv2D (s + 1) ell f r z) r)
    (htrace : ∀ s ≤ q, Odd s → ∀ z,
      mixedIteratedDeriv2D s ell f 0 z = 0) :
    if Even q then
      mixedIteratedDeriv2D q ell (evenReflection2D f) =
        evenReflection2D (mixedIteratedDeriv2D q ell f)
    else
      mixedIteratedDeriv2D q ell (evenReflection2D f) =
        oddReflection2D (mixedIteratedDeriv2D q ell f) := by
  have hall := mixedIteratedDeriv2D_evenReflection_finite_radial_order q
    (mixedIteratedDeriv2D 0 ell f)
    (fun s ↦ mixedIteratedDeriv2D s ell f) (by simp)
    hderiv htrace
  rw [← mixedIteratedDeriv2D_zero_evenReflection ell f] at hall
  have hcombine (s : ℕ) (g : ℝ → ℝ → ℝ) :
      mixedIteratedDeriv2D s 0 (mixedIteratedDeriv2D 0 ell g) =
        mixedIteratedDeriv2D s ell g := by
    funext r z
    simp [mixedIteratedDeriv2D]
  rw [hcombine] at hall
  exact hall

/-- Let `d 0 = f`, let `d (q + 1) (r, z)` be the derivative of `ρ ↦ d q (ρ, z)` at every `r` for
every `q`, and let `d q` vanish on the axis for odd `q`. Then for every `k`, `∂_r^(2k)` of the even
reflection of `f` is the even reflection of `d (2k)` and `∂_r^(2k+1)` of it is the odd reflection of
`d (2k+1)`. -/
theorem mixedIteratedDeriv2D_evenReflection_all_radial_orders
    (f : ℝ → ℝ → ℝ) (d : ℕ → ℝ → ℝ → ℝ)
    (hzero : d 0 = f)
    (hderiv : ∀ q r z,
      HasDerivAt (fun rho ↦ d q rho z) (d (q + 1) r z) r)
    (htrace : ∀ q, Odd q → ∀ z, d q 0 z = 0) :
    ∀ k : ℕ,
      mixedIteratedDeriv2D (2 * k) 0 (evenReflection2D f) =
          evenReflection2D (d (2 * k)) ∧
        mixedIteratedDeriv2D (2 * k + 1) 0 (evenReflection2D f) =
          oddReflection2D (d (2 * k + 1)) := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [mixedIteratedDeriv2D_zero_evenReflection]
        congr 1
        rw [hzero]
        funext r z
        simp [mixedIteratedDeriv2D]
      · rw [mixedIteratedDeriv2D_succ_zero]
        simpa [mixedIteratedDeriv2D, hzero] using
          deriv_evenReflection2D_eq_oddReflection2D (d 0) (d 1) (hderiv 0) (htrace 1 odd_one)
  | succ k ih =>
      have hevenNext : mixedIteratedDeriv2D (2 * (k + 1)) 0 (evenReflection2D f) =
          evenReflection2D (d (2 * (k + 1))) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, mixedIteratedDeriv2D_succ_zero, ih.2]
        exact deriv_oddReflection2D_eq_evenReflection2D _ _ (hderiv _) (htrace _ ⟨k, rfl⟩)
      refine ⟨hevenNext, ?_⟩
      rw [mixedIteratedDeriv2D_succ_zero, hevenNext]
      exact deriv_evenReflection2D_eq_oddReflection2D _ _ (hderiv _) (htrace _ ⟨k + 1, rfl⟩)

/-- Let `ell` be fixed. If every radial derivative of every order of `∂_z^ell f` exists on each line
`z = const` (`hderiv`) and those of odd order vanish at `r = 0` (`htrace`), then for every `k` the
derivative `∂_r^(2k) ∂_z^ell` of the even reflection of `f` is the even reflection of
`∂_r^(2k) ∂_z^ell f`, and `∂_r^(2k+1) ∂_z^ell` of it is the odd reflection of
`∂_r^(2k+1) ∂_z^ell f`, on the whole plane including the axis. -/
theorem mixedIteratedDeriv2D_evenReflection_all_mixed_orders
    (ell : ℕ) (f : ℝ → ℝ → ℝ)
    (hderiv : ∀ q r z,
      HasDerivAt (fun rho ↦ mixedIteratedDeriv2D q ell f rho z)
        (mixedIteratedDeriv2D (q + 1) ell f r z) r)
    (htrace : ∀ q, Odd q → ∀ z, mixedIteratedDeriv2D q ell f 0 z = 0) :
    ∀ k : ℕ,
      mixedIteratedDeriv2D (2 * k) ell (evenReflection2D f) =
          evenReflection2D (mixedIteratedDeriv2D (2 * k) ell f) ∧
        mixedIteratedDeriv2D (2 * k + 1) ell (evenReflection2D f) =
          oddReflection2D (mixedIteratedDeriv2D (2 * k + 1) ell f) := by
  intro k
  have hall :=
    mixedIteratedDeriv2D_evenReflection_all_radial_orders
      (mixedIteratedDeriv2D 0 ell f)
      (fun q ↦ mixedIteratedDeriv2D q ell f)
      (by simp) hderiv htrace k
  rw [← mixedIteratedDeriv2D_zero_evenReflection ell f] at hall
  have hcombine (s : ℕ) (g : ℝ → ℝ → ℝ) :
      mixedIteratedDeriv2D s 0 (mixedIteratedDeriv2D 0 ell g) =
        mixedIteratedDeriv2D s ell g := by
    funext r z
    simp [mixedIteratedDeriv2D]
  rw [hcombine, hcombine] at hall
  exact hall

/-- If `df (r, z)` is the derivative at `r` of `ρ ↦ f (ρ, z)` and `ddf (r, z)` that of
`ρ ↦ df (ρ, z)`, at every point, and `df = 0` on the axis, then `∂_r²` of the even reflection of `f`
is the even reflection of `ddf`. -/
theorem mixedIteratedDeriv2D_two_zero_evenReflection
    (f df ddf : ℝ → ℝ → ℝ)
    (hdf : ∀ r z, HasDerivAt (fun rho ↦ f rho z) (df r z) r)
    (hddf : ∀ r z, HasDerivAt (fun rho ↦ df rho z) (ddf r z) r)
    (htrace : ∀ z, df 0 z = 0) :
    mixedIteratedDeriv2D 2 0 (evenReflection2D f) = evenReflection2D ddf := by
  have hfirst :
      (fun r z ↦ deriv (fun rho ↦ evenReflection2D f rho z) r) =
        oddReflection2D df :=
    deriv_evenReflection2D_eq_oddReflection2D f df hdf htrace
  have hsecond :
      (fun r z ↦ deriv (fun rho ↦ oddReflection2D df rho z) r) =
        evenReflection2D ddf :=
    deriv_oddReflection2D_eq_evenReflection2D df ddf hddf htrace
  funext r z
  have hz :
      (fun rho ↦ deriv (fun sigma ↦ evenReflection2D f sigma z) rho) =
        (fun rho ↦ oddReflection2D df rho z) := by
    exact congrArg (fun g : ℝ → ℝ → ℝ ↦ fun rho ↦ g rho z) hfirst
  calc
    mixedIteratedDeriv2D 2 0 (evenReflection2D f) r z =
        deriv (fun rho ↦ deriv (fun sigma ↦ evenReflection2D f sigma z) rho) r := by
          simp [mixedIteratedDeriv2D, iteratedDeriv_succ]
    _ = deriv (fun rho ↦ oddReflection2D df rho z) r := by rw [hz]
    _ = evenReflection2D ddf r z := congrFun (congrFun hsecond r) z

/-- For every `g`, the iterated integral over the plane of the even reflection `g (|r|, z)` is twice
the iterated integral of `g` over `r > 0`; there are no hypotheses on `g`. -/
theorem integral_evenReflection_iterated (g : ℝ → ℝ → ℝ) :
    (∫ z : ℝ, ∫ r : ℝ, evenReflection2D g r z) =
      2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, g r z := by
  calc
    (∫ z : ℝ, ∫ r : ℝ, evenReflection2D g r z) =
        ∫ z : ℝ, 2 * ∫ r : ℝ in Set.Ioi 0, g r z := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa [evenReflection2D] using (integral_comp_abs (f := fun r : ℝ ↦ g r z))
    _ = 2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, g r z := by
      rw [integral_const_mul]

/-- If `g` is `σ f(-r)` for `r < 0` and `f` for `r > 0`, with `σ² = 1`, then the iterated
integral of `g² Φ(|r|)` over the plane is twice the iterated integral of `f² Φ` over the
half-plane `r > 0`. -/
private theorem integral_sq_mul_evenWeight_of_parity {g f Φ : ℝ → ℝ → ℝ} {σ : ℝ}
    (hσ : σ ^ 2 = 1) (hneg : ∀ {r z : ℝ}, r < 0 → g r z = σ * f (-r) z)
    (hpos : ∀ {r z : ℝ}, 0 < r → g r z = f r z) :
    (∫ z : ℝ, ∫ r : ℝ, g r z ^ 2 * evenReflection2D Φ r z) =
      2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, f r z ^ 2 * Φ r z := by
  calc (∫ z : ℝ, ∫ r : ℝ, g r z ^ 2 * evenReflection2D Φ r z)
      = ∫ z : ℝ, ∫ r : ℝ, evenReflection2D (fun ρ ζ ↦ f ρ ζ ^ 2 * Φ ρ ζ) r z := by
        refine integral_congr_ae (ae_of_all _ fun z ↦ integral_congr_ae ?_)
        filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
        rcases lt_or_gt_of_ne hr with hr | hr
        · rw [hneg hr, mul_pow, hσ, one_mul]
          simp [evenReflection2D, abs_of_neg hr]
        · rw [hpos hr]
          simp [evenReflection2D, abs_of_pos hr]
    _ = _ := integral_evenReflection_iterated (fun r z ↦ f r z ^ 2 * Φ r z)

/-- For all `q`, `ell`, `f` and `Φ`, the iterated integral over the plane of
`(∂_r^q ∂_z^ell Ef)² EΦ`, where `E` is the even reflection, is twice the iterated integral over
`r > 0` of `(∂_r^q ∂_z^ell f)² Φ`. No hypotheses are needed, since the identity uses only the
derivative formula off the axis, which is a null set. It does not show that `∂_r^q ∂_z^ell Ef` is a
weak derivative of `Ef`. -/
theorem integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight
    (q ell : ℕ) (f Φ : ℝ → ℝ → ℝ) :
    (∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (evenReflection2D f) r z ^ 2 *
          evenReflection2D Φ r z) =
      2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
        mixedIteratedDeriv2D q ell f r z ^ 2 * Φ r z := by
  exact integral_sq_mul_evenWeight_of_parity (by rw [pow_right_comm, neg_one_sq, one_pow])
    (mixedIteratedDeriv2D_evenReflection_neg q ell f)
    (mixedIteratedDeriv2D_evenReflection_pos q ell f)

/-- The identity `integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight` with the odd
reflection of `f` in place of the even one; the weight is still the even reflection of `Φ`. -/
theorem integral_mixedIteratedDeriv2D_oddReflection_sq_mul_evenWeight
    (q ell : ℕ) (f Φ : ℝ → ℝ → ℝ) :
    (∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (oddReflection2D f) r z ^ 2 *
          evenReflection2D Φ r z) =
      2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
        mixedIteratedDeriv2D q ell f r z ^ 2 * Φ r z := by
  exact integral_sq_mul_evenWeight_of_parity (by rw [pow_right_comm, neg_one_sq, one_pow])
    (mixedIteratedDeriv2D_oddReflection_neg q ell f)
    (mixedIteratedDeriv2D_oddReflection_pos q ell f)

/-- The square root of the iterated integral over the plane of `(∂_r^q ∂_z^ell Ef)² EΦ`, where `E`
is the even reflection, is `√2` times the square root of the iterated integral over `r > 0` of
`(∂_r^q ∂_z^ell f)² Φ`. -/
theorem sqrt_integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight
    (q ell : ℕ) (f Φ : ℝ → ℝ → ℝ) :
    Real.sqrt (∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (evenReflection2D f) r z ^ 2 *
          evenReflection2D Φ r z) =
      Real.sqrt 2 * Real.sqrt (∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
        mixedIteratedDeriv2D q ell f r z ^ 2 * Φ r z) := by
  rw [integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight]
  exact Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) _

/-- The identity `sqrt_integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight` with the odd
reflection of `f` in place of the even one. -/
theorem sqrt_integral_mixedIteratedDeriv2D_oddReflection_sq_mul_evenWeight
    (q ell : ℕ) (f Φ : ℝ → ℝ → ℝ) :
    Real.sqrt (∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (oddReflection2D f) r z ^ 2 *
          evenReflection2D Φ r z) =
      Real.sqrt 2 * Real.sqrt (∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
        mixedIteratedDeriv2D q ell f r z ^ 2 * Φ r z) := by
  rw [integral_mixedIteratedDeriv2D_oddReflection_sq_mul_evenWeight]
  exact Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) _

/-- For every `m` and `f`, the sum over `q + ell ≤ m` of the iterated integrals over the plane of
`(∂_r^q ∂_z^ell Ef)²`, where `E` is the even reflection, is twice the sum over `q + ell ≤ m` of the
iterated integrals over `r > 0` of `(∂_r^q ∂_z^ell f)²`. It does not show that the sums are finite
or that the derivatives are weak derivatives. -/
theorem sum_integral_mixedIteratedDeriv2D_evenReflection_sq
    (m : ℕ) (f : ℝ → ℝ → ℝ) :
    (∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
      ∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (evenReflection2D f) r z ^ 2) =
      2 * ∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
        ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
          mixedIteratedDeriv2D q ell f r z ^ 2 := by
  calc
    (∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
      ∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (evenReflection2D f) r z ^ 2) =
        ∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
          2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
            mixedIteratedDeriv2D q ell f r z ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro ell hell
      simpa [evenReflection2D] using
        (integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight
          q ell f (fun _ _ ↦ 1))
    _ = 2 * ∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
        ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
          mixedIteratedDeriv2D q ell f r z ^ 2 := by
      simp_rw [← Finset.mul_sum]

/-- The identity `sum_integral_mixedIteratedDeriv2D_evenReflection_sq` with the odd reflection of
`f` in place of the even one. -/
theorem sum_integral_mixedIteratedDeriv2D_oddReflection_sq
    (m : ℕ) (f : ℝ → ℝ → ℝ) :
    (∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
      ∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (oddReflection2D f) r z ^ 2) =
      2 * ∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
        ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
          mixedIteratedDeriv2D q ell f r z ^ 2 := by
  calc
    (∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
      ∫ z : ℝ, ∫ r : ℝ,
        mixedIteratedDeriv2D q ell (oddReflection2D f) r z ^ 2) =
        ∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
          2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
            mixedIteratedDeriv2D q ell f r z ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro ell hell
      simpa [evenReflection2D] using
        (integral_mixedIteratedDeriv2D_oddReflection_sq_mul_evenWeight
          q ell f (fun _ _ ↦ 1))
    _ = 2 * ∑ q ∈ Finset.range (m + 1), ∑ ell ∈ Finset.range (m + 1 - q),
        ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0,
          mixedIteratedDeriv2D q ell f r z ^ 2 := by
      simp_rw [← Finset.mul_sum]

/-- For every `f`, the iterated integral over the plane of the square of the even reflection
`f (|r|, z)` is twice the iterated integral of `f²` over `r > 0`. It is the identity of squared `L²`
norms when `f²` is integrable and Fubini's theorem applies. -/
theorem integral_evenReflection_sq_iterated (f : ℝ → ℝ → ℝ) :
    (∫ z : ℝ, ∫ r : ℝ, evenReflection2D f r z ^ 2) =
      2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, f r z ^ 2 := by
  calc
    (∫ z : ℝ, ∫ r : ℝ, evenReflection2D f r z ^ 2) =
        ∫ z : ℝ, 2 * ∫ r : ℝ in Set.Ioi 0, f r z ^ 2 := by
          apply integral_congr_ae
          filter_upwards [] with z
          simpa [evenReflection2D] using
            (integral_comp_abs (f := fun r : ℝ ↦ f r z ^ 2))
    _ = 2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, f r z ^ 2 := by
      rw [integral_const_mul]

/-- The square root of the iterated integral over the plane of the square of the even reflection of
`f` is `√2` times the square root of the iterated integral of `f²` over `r > 0`. -/
theorem sqrt_integral_evenReflection_sq_iterated
    (f : ℝ → ℝ → ℝ) :
    Real.sqrt (∫ z : ℝ, ∫ r : ℝ, evenReflection2D f r z ^ 2) =
      Real.sqrt 2 * Real.sqrt (∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, f r z ^ 2) := by
  rw [integral_evenReflection_sq_iterated]
  exact Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) _

/-- The identity `integral_evenReflection_sq_iterated` with the odd reflection of `f` in place of
the even one. -/
theorem integral_oddReflection_sq_iterated (f : ℝ → ℝ → ℝ) :
    (∫ z : ℝ, ∫ r : ℝ, oddReflection2D f r z ^ 2) =
      2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, f r z ^ 2 := by
  calc
    (∫ z : ℝ, ∫ r : ℝ, oddReflection2D f r z ^ 2) =
        ∫ z : ℝ, ∫ r : ℝ, evenReflection2D f r z ^ 2 := by
          apply integral_congr_ae
          filter_upwards [] with z
          apply integral_congr_ae
          filter_upwards [] with r
          by_cases hr : r < 0
          · simp [oddReflection2D, evenReflection2D, hr, abs_of_neg hr]
          · simp [oddReflection2D, evenReflection2D, hr, abs_of_nonneg (le_of_not_gt hr)]
    _ = 2 * ∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, f r z ^ 2 :=
      integral_evenReflection_sq_iterated f

/-- The identity `sqrt_integral_evenReflection_sq_iterated` with the odd reflection of `f` in place
of the even one. -/
theorem sqrt_integral_oddReflection_sq_iterated (f : ℝ → ℝ → ℝ) :
    Real.sqrt (∫ z : ℝ, ∫ r : ℝ,
        oddReflection2D f r z ^ 2) =
      Real.sqrt 2 * Real.sqrt (∫ z : ℝ, ∫ r : ℝ in Set.Ioi 0, f r z ^ 2) := by
  rw [integral_oddReflection_sq_iterated]
  exact Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) _

/-- The identity `(3 / (2 √π)) √2 = 3 / √(2π)` for the reflected constant `K∞` of
`PDE.Spaces.Sobolev.Weighted.PlanarReflection.Embedding`. -/
theorem reflectedKInfinity_constant_eq :
    ((3 / (2 * Real.sqrt Real.pi)) * Real.sqrt 2 : ℝ) =
      3 / Real.sqrt (2 * Real.pi) := by
  cas

end SobolevSpace.Weighted
