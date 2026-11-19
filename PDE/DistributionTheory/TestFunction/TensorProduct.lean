/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.ProperPrecomposition
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# External tensor products of test functions

For scalar test functions `φ` on `E` and `ψ` on `F`, the external tensor product is

`(φ ⊗ ψ)(x, y) = φ x * ψ y`,

a test function on `E × F` with `tsupport (φ ⊗ ψ) ⊆ tsupport φ ×ˢ tsupport ψ`. Tensor products
of test functions are the elementary tests against which tensor products of distributions are
computed; see Hörmander, Chapter V.

The main analytic content is the continuity of `φ ↦ φ ⊗ ψ` (for fixed `ψ`) and of
`ψ ↦ φ ⊗ ψ` (for fixed `φ`) in the canonical LF topologies. On a fixed compact-support stage
`𝓓_K(E)` the Leibniz formula for iterated derivatives of a product gives

`‖D^k (φ ⊗ ψ)(x, y)‖ ≤ 2^k · sup_{i ≤ k} ‖D^i φ‖_∞ · sup_{i ≤ k} ‖D^i ψ‖_∞`,

which is the seminorm estimate `WithSeminorms.continuous_of_isBounded` requires, and
`TestFunction.limitCLM` assembles the stages into a continuous map on the LF space.

## Main results

* `tensorProduct`, `tsupport_tensorProduct_subset`: the tensor product and its support bound.
* `tensorProductRightCLM`, `tensorProductLeftCLM`: continuity in each factor.
* `lineDerivCLM_tensorProduct_fst`, `lineDerivCLM_tensorProduct_snd`: the derivative in
  direction `(v, 0)` acts on `φ`, and in direction `(0, w)` on `ψ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter V, "Distributions in Product Spaces".
  <https://doi.org/10.1007/978-3-642-61497-2_6>
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace TestFunction

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The external tensor product of two scalar test functions. -/
def tensorProduct
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    𝓓((⊤ : Opens (E × F)), ℝ) where
  toFun := fun p ↦ φ p.1 * ψ p.2
  contDiff' := (φ.contDiff.comp contDiff_fst).mul (ψ.contDiff.comp contDiff_snd)
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (φ.hasCompactSupport.prod ψ.hasCompactSupport)
    intro p hp
    have hφ : φ p.1 ≠ 0 := fun hzero ↦ hp (by simp [hzero])
    have hψ : ψ p.2 ≠ 0 := fun hzero ↦ hp (by simp [hzero])
    exact ⟨subset_tsupport φ hφ, subset_tsupport ψ hψ⟩
  tsupport_subset' := subset_univ _

/-- Pointwise formula for the external tensor product: `(φ ⊗ ψ)(x, y) = φ x * ψ y`. -/
@[simp]
theorem tensorProduct_apply
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ))
    (p : E × F) :
    tensorProduct φ ψ p = φ p.1 * ψ p.2 :=
  rfl

/-- The support of an external tensor product lies in the product of the factor supports. -/
theorem tsupport_tensorProduct_subset
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    tsupport (tensorProduct φ ψ) ⊆ tsupport φ ×ˢ tsupport ψ := by
  apply closure_minimal
  · intro p hp
    have hφ : φ p.1 ≠ 0 := fun hzero ↦ hp (by simp [hzero])
    have hψ : ψ p.2 ≠ 0 := fun hzero ↦ hp (by simp [hzero])
    exact ⟨subset_tsupport φ hφ, subset_tsupport ψ hψ⟩
  · exact φ.hasCompactSupport.isClosed.prod ψ.hasCompactSupport.isClosed

/-- The external tensor product with a fixed right factor on a fixed compact-support stage,
supported in the product of the stage with the support of the right factor. -/
def tensorProductRightSupported
    (ψ : 𝓓((⊤ : Opens F), ℝ))
    (K : Compacts E)
    (φ : 𝓓_{K}(E, ℝ)) :
    𝓓_{K ×ˢ tsupportCompacts ψ}(E × F, ℝ) where
  toFun := fun p ↦ φ p.1 * ψ p.2
  contDiff' := (φ.contDiff.comp contDiff_fst).mul (ψ.contDiff.comp contDiff_snd)
  zero_on_compl' := by
    intro p hp
    have hp' : p ∉
        (K : Set E) ×ˢ (tsupportCompacts ψ : Set F) := by
      simpa only [Set.mem_compl_iff, TopologicalSpace.Compacts.coe_prod] using hp
    by_cases hpK : p.1 ∈ (K : Set E)
    · have hpL : p.2 ∉ (tsupportCompacts ψ : Set F) :=
        fun hpL ↦ hp' ⟨hpK, hpL⟩
      have hψ : ψ p.2 = 0 := by
        by_contra hne
        exact hpL (subset_tsupport ψ hne)
      simp [hψ]
    · have hφ : φ p.1 = 0 :=
        φ.zero_on_compl (by simpa only [Set.mem_compl_iff])
      simp [hφ]

/-- External tensor product with a fixed right factor on a fixed compact-support stage, as a
continuous linear map between spaces of functions with prescribed support. -/
def tensorProductRightSupportedCLM
    (ψ : 𝓓((⊤ : Opens F), ℝ))
    (K : Compacts E) :
    𝓓_{K}(E, ℝ) →L[ℝ]
      𝓓_{K ×ˢ tsupportCompacts ψ}(E × F, ℝ) :=
  let Φ : 𝓓_{K}(E, ℝ) →ₗ[ℝ]
      𝓓_{K ×ˢ tsupportCompacts ψ}(E × F, ℝ) :=
    { toFun := tensorProductRightSupported ψ K
      map_add' := fun φ η ↦ ContDiffMapSupportedIn.ext fun p ↦ by
        change (φ p.1 + η p.1) * ψ p.2 =
          φ p.1 * ψ p.2 + η p.1 * ψ p.2
        ring
      map_smul' := fun c φ ↦ ContDiffMapSupportedIn.ext fun p ↦ by
        change (c * φ p.1) * ψ p.2 = c * (φ p.1 * ψ p.2)
        ring }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K)
        (ContDiffMapSupportedIn.withSeminorms ℝ (E × F) ℝ ⊤
          (K ×ˢ tsupportCompacts ψ)) _
        (.of_real fun k ↦ ?_)
      let L : Compacts F := tsupportCompacts ψ
      let ψL : 𝓓_{L}(F, ℝ) :=
        ContDiffMapSupportedIn.of_support_subset ψ.contDiff subset_closure
      let Cψ : ℝ :=
        ((Finset.Iic k).sup
          (ContDiffMapSupportedIn.seminorm ℝ F ℝ ⊤ L)) ψL
      refine ⟨Finset.Iic k, 2 ^ k * Cψ, fun φ ↦ ?_⟩
      refine ((Φ φ).seminorm_top_le_iff ℝ
        (mul_nonneg (by positivity) (apply_nonneg _ _)) k).2 ?_
      intro p hp
      have hpK : p.1 ∈ K := hp.1
      have hpL : p.2 ∈ L := hp.2
      have hfst :
          ∀ i ≤ k,
            ‖iteratedFDeriv ℝ i
                ((φ : E → ℝ) ∘ ContinuousLinearMap.fst ℝ E F) p‖ ≤
              ((Finset.Iic k).sup
                (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
        intro i hi
        rw [ContinuousLinearMap.iteratedFDeriv_comp_right
          (ContinuousLinearMap.fst ℝ E F) φ.contDiff p (mod_cast le_top)]
        apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        calc
          ‖iteratedFDeriv ℝ i (φ : E → ℝ) p.1‖ *
                ∏ _ : Fin i, ‖ContinuousLinearMap.fst ℝ E F‖
              ≤ ‖iteratedFDeriv ℝ i (φ : E → ℝ) p.1‖ * 1 := by
                gcongr
                exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
                  (fun _ _ ↦ ContinuousLinearMap.norm_fst_le ℝ E F)
          _ ≤ ((Finset.Iic k).sup
                (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
            simpa using
              (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top
                (𝕜 := ℝ) (f := φ) (x := p.1) (i := i)).trans
                (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hi))
      have hsnd :
          ∀ i ≤ k,
            ‖iteratedFDeriv ℝ i
                ((ψ : F → ℝ) ∘ ContinuousLinearMap.snd ℝ E F) p‖ ≤ Cψ := by
        intro i hi
        rw [ContinuousLinearMap.iteratedFDeriv_comp_right
          (ContinuousLinearMap.snd ℝ E F) ψ.contDiff p (mod_cast le_top)]
        apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        calc
          ‖iteratedFDeriv ℝ i (ψ : F → ℝ) p.2‖ *
                ∏ _ : Fin i, ‖ContinuousLinearMap.snd ℝ E F‖
              ≤ ‖iteratedFDeriv ℝ i (ψ : F → ℝ) p.2‖ * 1 := by
                gcongr
                exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
                  (fun _ _ ↦ ContinuousLinearMap.norm_snd_le ℝ E F)
          _ = ‖iteratedFDeriv ℝ i (ψ : F → ℝ) p.2‖ := by rw [mul_one]
          _ ≤ Cψ := by
            change ‖iteratedFDeriv ℝ i (ψL : F → ℝ) p.2‖ ≤ Cψ
            exact
              (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top
                (𝕜 := ℝ) (f := ψL) (x := p.2) (i := i)).trans
                (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hi))
      calc
        ‖iteratedFDeriv ℝ k (fun q : E × F ↦ φ q.1 * ψ q.2) p‖
            ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
                ‖iteratedFDeriv ℝ i
                  ((φ : E → ℝ) ∘ ContinuousLinearMap.fst ℝ E F) p‖ *
                ‖iteratedFDeriv ℝ (k - i)
                  ((ψ : F → ℝ) ∘ ContinuousLinearMap.snd ℝ E F) p‖ := by
              simpa only [Function.comp_apply, ContinuousLinearMap.coe_fst',
                ContinuousLinearMap.coe_snd'] using
                norm_iteratedFDeriv_mul_le
                  (φ.contDiff.comp contDiff_fst)
                  (ψ.contDiff.comp contDiff_snd) p (mod_cast le_top)
        _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
                ((Finset.Iic k).sup
                  (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ * Cψ := by
              gcongr with i hi
              · exact hfst i (Finset.mem_range_succ_iff.mp hi)
              · exact hsnd (k - i) (Nat.sub_le k i)
        _ = 2 ^ k * Cψ *
              ((Finset.Iic k).sup
                (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
              simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
              push_cast
              ring }

/-- External tensor product with a fixed right factor, as a continuous linear map. -/
def tensorProductRightCLM
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens (E × F)), ℝ) :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ tensorProduct φ ψ)
    (fun K _Ksub ↦
      TestFunction.ofSupportedInCLM ℝ (subset_univ _) ∘L
        tensorProductRightSupportedCLM ψ K)
    (by
      intro K _Ksub φ
      ext p
      rfl)

/-- The continuous linear map `φ ↦ φ ⊗ ψ` agrees with the plain tensor product `tensorProduct φ
ψ`. -/
@[simp]
theorem tensorProductRightCLM_apply
    (ψ : 𝓓((⊤ : Opens F), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    tensorProductRightCLM ψ φ = tensorProduct φ ψ := by
  ext p
  rfl

/-- External tensor product with a fixed left factor, as a continuous linear map. -/
def tensorProductLeftCLM
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    𝓓((⊤ : Opens F), ℝ) →L[ℝ] 𝓓((⊤ : Opens (E × F)), ℝ) :=
  precompProperCLM
      (ContinuousLinearEquiv.prodComm ℝ E F)
      (ContinuousLinearEquiv.prodComm ℝ E F).contDiff
      (ContinuousLinearEquiv.prodComm ℝ E F).toHomeomorph.isProperMap ∘L
    tensorProductRightCLM (E := F) (F := E) φ

/-- The continuous linear map `ψ ↦ φ ⊗ ψ` agrees with `tensorProduct φ ψ`. It is built from the
right-factor version by swapping coordinates, so the proof commutes the two scalar factors. -/
@[simp]
theorem tensorProductLeftCLM_apply
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    tensorProductLeftCLM φ ψ = tensorProduct φ ψ := by
  ext p
  change ψ p.2 * φ p.1 = φ p.1 * ψ p.2
  ring

/-- Differentiation in the first factor commutes with external tensor product. -/
theorem lineDerivCLM_tensorProduct_fst
    (v : E)
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    lineDerivCLM ℝ (v, 0) (tensorProduct φ ψ) =
      tensorProduct (lineDerivCLM ℝ v φ) ψ := by
  ext p
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun q : E × F ↦ φ q.1 * ψ q.2) p (v, 0) =
    (lineDerivCLM ℝ v φ) p.1 * ψ p.2
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun q : E × F ↦ φ q.1 * ψ q.2) p (v, 0) =
    lineDeriv ℝ (fun x : E ↦ φ x) p.1 v * ψ p.2
  have hφ : DifferentiableAt ℝ (fun x : E ↦ φ x) p.1 :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  have hψ : DifferentiableAt ℝ (fun y : F ↦ ψ y) p.2 :=
    (ψ.contDiff.differentiable (by simp)).differentiableAt
  have hφfst : DifferentiableAt ℝ (fun q : E × F ↦ φ q.1) p :=
    hφ.comp p differentiableAt_fst
  have hψsnd : DifferentiableAt ℝ (fun q : E × F ↦ ψ q.2) p :=
    hψ.comp p differentiableAt_snd
  change lineDeriv ℝ
      ((fun q : E × F ↦ φ q.1) * (fun q : E × F ↦ ψ q.2)) p (v, 0) =
    lineDeriv ℝ (fun x : E ↦ φ x) p.1 v * ψ p.2
  rw [(hφfst.mul hψsnd).lineDeriv_eq_fderiv, hφ.lineDeriv_eq_fderiv]
  rw [fderiv_mul hφfst hψsnd]
  have hφcomp :
      fderiv ℝ (fun q : E × F ↦ φ q.1) p =
        (fderiv ℝ (fun x : E ↦ φ x) p.1).comp
          (ContinuousLinearMap.fst ℝ E F) :=
    (hφ.hasFDerivAt.comp p hasFDerivAt_fst).fderiv
  have hψcomp :
      fderiv ℝ (fun q : E × F ↦ ψ q.2) p =
        (fderiv ℝ (fun y : F ↦ ψ y) p.2).comp
          (ContinuousLinearMap.snd ℝ E F) :=
    (hψ.hasFDerivAt.comp p hasFDerivAt_snd).fderiv
  rw [hφcomp, hψcomp]
  simp [mul_comm]

/-- Differentiation in the second factor commutes with external tensor product. -/
theorem lineDerivCLM_tensorProduct_snd
    (w : F)
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    lineDerivCLM ℝ (0, w) (tensorProduct φ ψ) =
      tensorProduct φ (lineDerivCLM ℝ w ψ) := by
  ext p
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun q : E × F ↦ φ q.1 * ψ q.2) p (0, w) =
    φ p.1 * (lineDerivCLM ℝ w ψ) p.2
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun q : E × F ↦ φ q.1 * ψ q.2) p (0, w) =
    φ p.1 * lineDeriv ℝ (fun y : F ↦ ψ y) p.2 w
  have hφ : DifferentiableAt ℝ (fun x : E ↦ φ x) p.1 :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  have hψ : DifferentiableAt ℝ (fun y : F ↦ ψ y) p.2 :=
    (ψ.contDiff.differentiable (by simp)).differentiableAt
  have hφfst : DifferentiableAt ℝ (fun q : E × F ↦ φ q.1) p :=
    hφ.comp p differentiableAt_fst
  have hψsnd : DifferentiableAt ℝ (fun q : E × F ↦ ψ q.2) p :=
    hψ.comp p differentiableAt_snd
  change lineDeriv ℝ
      ((fun q : E × F ↦ φ q.1) * (fun q : E × F ↦ ψ q.2)) p (0, w) =
    φ p.1 * lineDeriv ℝ (fun y : F ↦ ψ y) p.2 w
  rw [(hφfst.mul hψsnd).lineDeriv_eq_fderiv, hψ.lineDeriv_eq_fderiv]
  rw [fderiv_mul hφfst hψsnd]
  have hφcomp :
      fderiv ℝ (fun q : E × F ↦ φ q.1) p =
        (fderiv ℝ (fun x : E ↦ φ x) p.1).comp
          (ContinuousLinearMap.fst ℝ E F) :=
    (hφ.hasFDerivAt.comp p hasFDerivAt_fst).fderiv
  have hψcomp :
      fderiv ℝ (fun q : E × F ↦ ψ q.2) p =
        (fderiv ℝ (fun y : F ↦ ψ y) p.2).comp
          (ContinuousLinearMap.snd ℝ E F) :=
    (hψ.hasFDerivAt.comp p hasFDerivAt_snd).fderiv
  rw [hφcomp, hψcomp]
  simp

end TestFunction
