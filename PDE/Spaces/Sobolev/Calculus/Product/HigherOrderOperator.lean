/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.HigherOrder
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Bounded higher-order Sobolev multipliers

For every positive integer `k` and open domain `Ω ⊆ ℝ^n`, pointwise multiplication extends to
a bounded bilinear map

`W^{k,∞}(Ω) →L[ℝ] W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω)`

of norm at most `wkTopMultiplierNormBound n k`. This is the operator form of the Leibniz
formula for weak derivatives with a `W^{k,∞}` multiplier (cf. Evans, PDE, §5.2.3, Theorem 1(iv),
where the multiplier is in `C_c^∞(U)`).

The existence theorem in `Product.HigherOrder` produces a Sobolev derivative bundle for the
product. On an open domain that bundle is unique, because a `WkpSpaceOn` element is determined
by its order-zero coordinate (`WkpSpaceOn.ext_of_base_ae`). We choose that unique
product, prove it is bilinear, and use the explicit recursive estimate from
`Product.HigherOrder` to make multiplication bounded linear and bilinear maps.

## Main results

* `wkTopProduct`: the unique `W^{k,2}` realization of `A · U`, with `wkTopProduct_base_ae` and
  `norm_wkTopProduct_le`.
* `wkTopProduct_add_left`, `wkTopProduct_smul_left`, `wkTopProduct_add_right`,
  `wkTopProduct_smul_right`: bilinearity, all proved by comparing base representatives.
* `lowerOrderCLM_wkTopProduct`, `wkTopProduct_one_eq_w1TopMultiplierCLM`: compatibility with
  order truncation and with the dedicated first-order multiplier.
* `wkTopProduct_firstDeriv_apply_ae`: the first-derivative coordinates of the product are the
  Leibniz combinations `A ∂ᵢU + (∂ᵢA) U` almost everywhere.
* `wkTopMultiplierCLM`: multiplication by a fixed coefficient as a bounded endomorphism of
  `W^{k,2}(Ω)`, with `norm_wkTopMultiplierCLM_le`.
* `wkTopMultiplicationCLM`: the bounded bilinear multiplication map, with
  `norm_wkTopMultiplicationCLM_le`.

## Implementation notes

Only the base coordinate and the first-derivative coordinates of the product are described
pointwise. Higher derivative coordinates are determined by uniqueness of weak derivatives but
their Leibniz expansions are not spelled out here; `Product.WeakLeibniz` has the general
expansion for a smooth multiplier.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262, the Leibniz formula
  for a multiplier `ζ ∈ C_c^∞(U)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- The unique `W^{k,2}` realization of the pointwise product of a
`W^{k,∞}` coefficient and a `W^{k,2}` function. -/
noncomputable def wkTopProduct
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    W^{k,2}(Ω) :=
  Classical.choose
    (WkpSpaceOn.exists_mul_WkTop_WkTwo_with_norm
      (n := n) (Ω := Ω) k hk hΩopen A U)

/-- The base representative of `wkTopProduct A U` is the pointwise product
of the base representatives of `A` and `U`. -/
theorem wkTopProduct_base_ae
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    baseRepresentative
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ baseRepresentative A x * baseRepresentative U x := by
  simpa only [wkTopProduct] using
    (Classical.choose_spec
      (WkpSpaceOn.exists_mul_WkTop_WkTwo_with_norm
        (n := n) (Ω := Ω) k hk hΩopen A U)).1

/-- Explicit graph-norm estimate for the chosen higher-order product. -/
theorem norm_wkTopProduct_le
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    ‖wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U‖ ≤
      wkTopMultiplierNormBound n k * ‖A‖ * ‖U‖ := by
  exact
    (Classical.choose_spec
      (WkpSpaceOn.exists_mul_WkTop_WkTwo_with_norm
        (n := n) (Ω := Ω) k hk hΩopen A U)).2

/-- The chosen higher-order product is additive in its `W^{k,2}` input. -/
theorem wkTopProduct_add_right
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U V : W^{k,2}(Ω)) :
    wkTopProduct (n := n) (Ω := Ω) hk hΩopen A (U + V) =
      wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U +
        wkTopProduct (n := n) (Ω := Ω) hk hΩopen A V := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A (U + V))
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U +
        wkTopProduct (n := n) (Ω := Ω) hk hΩopen A V)
  filter_upwards
    [wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A (U + V),
      wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A U,
      wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A V,
      baseRepresentative_add_ae U V,
      baseRepresentative_add_ae
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A V)]
      with x hleft hU hV hinput houtput
  rw [hleft, hinput, houtput, hU, hV]
  ring

/-- The chosen higher-order product is homogeneous in its `W^{k,2}` input. -/
theorem wkTopProduct_smul_right
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (c : ℝ)
    (U : W^{k,2}(Ω)) :
    wkTopProduct (n := n) (Ω := Ω) hk hΩopen A (c • U) =
      c • wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A (c • U))
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (c • wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)
  filter_upwards
    [wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A (c • U),
      wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A U,
      baseRepresentative_smul_ae c U,
      baseRepresentative_smul_ae c
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)]
      with x hleft hU hinput houtput
  rw [hleft, hinput, houtput, hU]
  simp only [smul_eq_mul]
  ring

/-- The chosen higher-order product is additive in its coefficient. -/
theorem wkTopProduct_add_left
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A B : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    wkTopProduct (n := n) (Ω := Ω) hk hΩopen (A + B) U =
      wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U +
        wkTopProduct (n := n) (Ω := Ω) hk hΩopen B U := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen (A + B) U)
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U +
        wkTopProduct (n := n) (Ω := Ω) hk hΩopen B U)
  filter_upwards
    [wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen (A + B) U,
      wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A U,
      wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen B U,
      baseRepresentative_add_ae A B,
      baseRepresentative_add_ae
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen B U)]
      with x hleft hA hB hinput houtput
  rw [hleft, hinput, houtput, hA, hB]
  ring

/-- The chosen higher-order product is homogeneous in its coefficient. -/
theorem wkTopProduct_smul_left
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (c : ℝ) (A : W^{k,∞}(Ω))
    (U : W^{k,2}(Ω)) :
    wkTopProduct (n := n) (Ω := Ω) hk hΩopen (c • A) U =
      c • wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen (c • A) U)
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (c • wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)
  filter_upwards
    [wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen (c • A) U,
      wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A U,
      baseRepresentative_smul_ae c A,
      baseRepresentative_smul_ae c
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)]
      with x hleft hA hinput houtput
  rw [hleft, hinput, houtput, hA]
  simp only [smul_eq_mul]
  ring

/-- The base `L²` coordinate of the higher-order product is ordinary
`L∞`-by-`L²` multiplication. -/
theorem wkpBaseCoordinate_wkTopProduct
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    wkpBaseCoordinateCLM
        (n := n) (m := k) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U) =
      mulLpLeft
        (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        (wkpBaseCoordinateCLM
          (n := n) (m := k) (p := (∞ : ℝ≥0∞)) (Ω := Ω) A)
        (wkpBaseCoordinateCLM
          (n := n) (m := k) (p := (2 : ℝ≥0∞)) (Ω := Ω) U) := by
  apply MeasureTheory.Lp.ext
  exact
    (wkTopProduct_base_ae
      (n := n) (Ω := Ω) hk hΩopen A U).trans
      (mulLpLeft_apply_ae
        (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        (wkpBaseCoordinateCLM
          (n := n) (m := k) (p := (∞ : ℝ≥0∞)) (Ω := Ω) A)
        (wkpBaseCoordinateCLM
          (n := n) (m := k) (p := (2 : ℝ≥0∞)) (Ω := Ω) U)).symm

/-- Higher-order Sobolev multiplication commutes with forgetting derivative
coordinates above a positive lower order. -/
theorem lowerOrderCLM_wkTopProduct
    {r : ℕ} (hr : 0 < r) (hrk : r ≤ k) (hk : 0 < k)
    (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    lowerOrderCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hrk
        (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U) =
      wkTopProduct (n := n) (Ω := Ω) hr hΩopen
        (lowerOrderCLM
          (n := n) (p := (∞ : ℝ≥0∞)) (Ω := Ω) hrk A)
        (lowerOrderCLM
          (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hrk U) := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  have hhigh :=
    wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A U
  have hlow :=
    wkTopProduct_base_ae (n := n) (Ω := Ω) hr hΩopen
      (lowerOrderCLM
        (n := n) (p := (∞ : ℝ≥0∞)) (Ω := Ω) hrk A)
      (lowerOrderCLM
        (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hrk U)
  change
    baseRepresentative
        (lowerOrderCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hrk
          (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U)) =ᵐ[
      domainMeasure n Ω]
      baseRepresentative
        (wkTopProduct (n := n) (Ω := Ω) hr hΩopen
          (lowerOrderCLM
            (n := n) (p := (∞ : ℝ≥0∞)) (Ω := Ω) hrk A)
          (lowerOrderCLM
            (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) hrk U))
  simpa only [baseRepresentative_lowerOrderCLM] using
    hhigh.trans hlow.symm

/-- At order one, the higher-order product agrees with the dedicated
first-order multiplier. -/
theorem wkTopProduct_one_eq_w1TopMultiplierCLM
    (hΩopen : IsOpen Ω)
    (A : W^{1,∞}(Ω)) (U : W^{1,2}(Ω)) :
    wkTopProduct (n := n) (Ω := Ω) (by omega) hΩopen A U =
      w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  exact
    (wkTopProduct_base_ae
      (n := n) (Ω := Ω) (by omega) hΩopen A U).trans
      (w1TopMultiplierCLM_base_ae
        (n := n) (Ω := Ω) hΩopen A U).symm

/-- Every first-derivative coordinate of the higher-order product satisfies
the weak Leibniz formula almost everywhere. -/
theorem wkTopProduct_firstDeriv_apply_ae
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω))
    (i : Fin n) :
    ((((wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U :
          W^{k,2}(Ω)) : WkpAmbientOn n k 2 Ω)
        (firstDerivIndex n k hk i) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          (((A : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n k 2 Ω) (firstDerivIndex n k hk i) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x +
          (((A : WkpAmbientOn n k ∞ Ω) (firstDerivIndex n k hk i) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x := by
  have h1k : 1 ≤ k := by omega
  have hrestrict :
      lowerOrderCLM
          (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) h1k
          (wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U) =
        w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen
          (lowerOrderCLM
            (n := n) (p := (∞ : ℝ≥0∞)) (Ω := Ω) h1k A)
          (lowerOrderCLM
            (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) h1k U) := by
    rw [lowerOrderCLM_wkTopProduct
      (n := n) (Ω := Ω) (r := 1) (hr := by omega) (hrk := h1k) hk]
    exact wkTopProduct_one_eq_w1TopMultiplierCLM
      (n := n) (Ω := Ω) hΩopen
      (lowerOrderCLM
        (n := n) (p := (∞ : ℝ≥0∞)) (Ω := Ω) h1k A)
      (lowerOrderCLM
        (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) h1k U)
  have hcoord :=
    w1TopMultiplierCLM_singleDeriv_apply_ae
      (n := n) (Ω := Ω) hΩopen
      (lowerOrderCLM
        (n := n) (p := (∞ : ℝ≥0∞)) (Ω := Ω) h1k A)
      (lowerOrderCLM
        (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) h1k U) i
  rw [← hrestrict] at hcoord
  simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
    DerivIndex.castOrder_singleDerivIndex] using hcoord

/-- Multiplication by a fixed `W^{k,∞}` coefficient as a linear map on `W^{k,2}`,
before the continuity bound is attached. -/
noncomputable def wkTopMultiplierLinearMap
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) :
    W^{k,2}(Ω) →ₗ[ℝ] W^{k,2}(Ω) where
  toFun := wkTopProduct (n := n) (Ω := Ω) hk hΩopen A
  map_add' := wkTopProduct_add_right
    (n := n) (Ω := Ω) hk hΩopen A
  map_smul' := fun c U ↦
    wkTopProduct_smul_right
      (n := n) (Ω := Ω) hk hΩopen A c U

/-- Multiplication by a fixed `W^{k,∞}` coefficient as a continuous linear
endomorphism of `W^{k,2}`. -/
noncomputable def wkTopMultiplierCLM
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) :
    W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω) :=
  LinearMap.mkContinuous
    (wkTopMultiplierLinearMap (n := n) (Ω := Ω) hk hΩopen A)
    (wkTopMultiplierNormBound n k * ‖A‖)
    (fun U ↦ by
      change
        ‖wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U‖ ≤
          (wkTopMultiplierNormBound n k * ‖A‖) * ‖U‖
      simpa [mul_assoc] using
        norm_wkTopProduct_le
          (n := n) (Ω := Ω) hk hΩopen A U)

/-- The fixed-coefficient multiplier evaluates to the chosen Sobolev
product. -/
@[simp]
theorem wkTopMultiplierCLM_apply
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    wkTopMultiplierCLM (n := n) (Ω := Ω) hk hΩopen A U =
      wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U :=
  by
    simp [wkTopMultiplierCLM, wkTopMultiplierLinearMap]

/-- Every first-derivative coordinate of the fixed-coefficient multiplier
satisfies the weak Leibniz formula almost everywhere. -/
theorem wkTopMultiplierCLM_firstDeriv_apply_ae
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω))
    (i : Fin n) :
    ((((wkTopMultiplierCLM (n := n) (Ω := Ω) hk hΩopen A U :
          W^{k,2}(Ω)) : WkpAmbientOn n k 2 Ω)
        (firstDerivIndex n k hk i) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          (((A : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n k 2 Ω) (firstDerivIndex n k hk i) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x +
          (((A : WkpAmbientOn n k ∞ Ω) (firstDerivIndex n k hk i) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x := by
  rw [wkTopMultiplierCLM_apply]
  exact wkTopProduct_firstDeriv_apply_ae
    (n := n) (Ω := Ω) hk hΩopen A U i

/-- The fixed-coefficient multiplier satisfies the explicit graph-norm
bound. -/
theorem norm_wkTopMultiplierCLM_apply_le
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    ‖wkTopMultiplierCLM (n := n) (Ω := Ω) hk hΩopen A U‖ ≤
      wkTopMultiplierNormBound n k * ‖A‖ * ‖U‖ := by
  rw [wkTopMultiplierCLM_apply]
  exact norm_wkTopProduct_le (n := n) (Ω := Ω) hk hΩopen A U

/-- Operator-norm estimate for multiplication by a fixed coefficient. -/
theorem norm_wkTopMultiplierCLM_le
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) :
    ‖wkTopMultiplierCLM (n := n) (Ω := Ω) hk hΩopen A‖ ≤
      wkTopMultiplierNormBound n k * ‖A‖ :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (wkTopMultiplierNormBound_nonneg n k) (norm_nonneg A)) _

section HigherOrderBilinearOperator

/-- The standard normed additive group structure on bounded endomorphisms of
`W^{k,2}(Ω)`, named locally to stabilize typeclass search. -/
local instance wkEndomorphismNormedAddCommGroup :
    NormedAddCommGroup
      (W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The standard real normed-space structure on bounded endomorphisms of
`W^{k,2}(Ω)`, named locally to stabilize typeclass search. -/
local instance wkEndomorphismNormedSpace :
    NormedSpace ℝ
      (W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω)) :=
  ContinuousLinearMap.toNormedSpace

/-- The coefficient-to-multiplier assignment as a linear map into the operator
space, before the continuity bound is attached. -/
noncomputable def wkTopMultiplicationLinearMap
    (hk : 0 < k) (hΩopen : IsOpen Ω) :
    W^{k,∞}(Ω) →ₗ[ℝ]
      W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω) where
  toFun := wkTopMultiplierCLM (n := n) (Ω := Ω) hk hΩopen
  map_add' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro U
    simpa only [add_apply, wkTopMultiplierCLM_apply] using
      wkTopProduct_add_left
        (n := n) (Ω := Ω) hk hΩopen A B U
  map_smul' := by
    intro c A
    apply ContinuousLinearMap.ext
    intro U
    change
      wkTopProduct (n := n) (Ω := Ω) hk hΩopen (c • A) U =
        c • wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U
    exact wkTopProduct_smul_left
      (n := n) (Ω := Ω) hk hΩopen c A U

/-- Higher-order Sobolev multiplication as a bounded bilinear map
`W^{k,∞}(Ω) →L[ℝ] W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω)`. -/
noncomputable def wkTopMultiplicationCLM
    (hk : 0 < k) (hΩopen : IsOpen Ω) :
    W^{k,∞}(Ω) →L[ℝ]
      W^{k,2}(Ω) →L[ℝ] W^{k,2}(Ω) :=
  LinearMap.mkContinuous
    (wkTopMultiplicationLinearMap
      (n := n) (Ω := Ω) hk hΩopen)
    (wkTopMultiplierNormBound n k)
    (fun A ↦
      norm_wkTopMultiplierCLM_le
        (n := n) (Ω := Ω) hk hΩopen A)

/-- The bounded bilinear multiplier evaluates to the chosen Sobolev
product. -/
@[simp]
theorem wkTopMultiplicationCLM_apply
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    wkTopMultiplicationCLM (n := n) (Ω := Ω) hk hΩopen A U =
      wkTopProduct (n := n) (Ω := Ω) hk hΩopen A U :=
  rfl

/-- The bounded bilinear multiplier has the expected pointwise base
representative. -/
theorem wkTopMultiplicationCLM_base_ae
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    baseRepresentative
        (wkTopMultiplicationCLM
          (n := n) (Ω := Ω) hk hΩopen A U)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ baseRepresentative A x * baseRepresentative U x :=
  by
    rw [wkTopMultiplicationCLM_apply]
    exact wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen A U

/-- Every first-derivative coordinate of the bounded bilinear multiplier
satisfies the weak Leibniz formula almost everywhere. -/
theorem wkTopMultiplicationCLM_firstDeriv_apply_ae
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω))
    (i : Fin n) :
    ((((wkTopMultiplicationCLM
          (n := n) (Ω := Ω) hk hΩopen A U :
            W^{k,2}(Ω)) : WkpAmbientOn n k 2 Ω)
        (firstDerivIndex n k hk i) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          (((A : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n k 2 Ω) (firstDerivIndex n k hk i) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x +
          (((A : WkpAmbientOn n k ∞ Ω) (firstDerivIndex n k hk i) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x := by
  rw [wkTopMultiplicationCLM_apply]
  exact wkTopProduct_firstDeriv_apply_ae
    (n := n) (Ω := Ω) hk hΩopen A U i

/-- Explicit graph-norm estimate for higher-order Sobolev multiplication. -/
theorem norm_wkTopMultiplicationCLM_apply_le
    (hk : 0 < k) (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω)) (U : W^{k,2}(Ω)) :
    ‖wkTopMultiplicationCLM (n := n) (Ω := Ω) hk hΩopen A U‖ ≤
      wkTopMultiplierNormBound n k * ‖A‖ * ‖U‖ := by
  rw [wkTopMultiplicationCLM_apply]
  exact norm_wkTopProduct_le (n := n) (Ω := Ω) hk hΩopen A U

/-- Operator-norm estimate for the bounded bilinear multiplier. -/
theorem norm_wkTopMultiplicationCLM_le
    (hk : 0 < k) (hΩopen : IsOpen Ω) :
    ‖wkTopMultiplicationCLM (n := n) (Ω := Ω) hk hΩopen‖ ≤
      wkTopMultiplierNormBound n k :=
  LinearMap.mkContinuous_norm_le _
    (wkTopMultiplierNormBound_nonneg n k) _

end HigherOrderBilinearOperator

end SobolevSpace.GraphSpace
