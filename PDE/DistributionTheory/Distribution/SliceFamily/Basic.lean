/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactCurry
public import PDE.DistributionTheory.Distribution.FixedSupport
public import PDE.DistributionTheory.TestFunction.Slice
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import PDE.Analysis.Calculus.IteratedFDerivSymmetry

/-!
# Smooth distribution-valued fiber slices

Let `Φ` be a test function on `E × F` and `T` a distribution on `F`. Applying `T` to the right
slices of `Φ` gives the function

`x ↦ ⟨T, Φ(x, ·)⟩ : E → G`,

and the basic fact behind tensor products of distributions (and hence behind their convolution)
is that this function is again a test function: it is `C^∞`, compactly supported in the first
coordinate projection of `tsupport Φ`, and its derivatives are computed by differentiating `Φ`
under `T`,

`∂ₕ ⟨T, Φ(x, ·)⟩ = ⟨T, (∂_{(h,0)} Φ)(x, ·)⟩`.

This is the differentiation-under-the-pairing lemma from the construction of tensor products of
distributions; see Hörmander, Chapter V, or Friedlander and Joshi, Chapter 4. The analytic input
is that `T`, restricted to the Fréchet space of test functions supported in the compact right
projection of `tsupport Φ`, is bounded by finitely many derivative seminorms
(`Distribution.FixedSupport`); the difference quotient of the slice family is then controlled by
a Taylor remainder of `Φ`, uniformly on compact sets, which gives differentiability, and
induction gives smoothness.

## Main results

* `iteratedFDeriv_sliceRight`: the iterated derivatives of a slice `y ↦ Φ(x, y)` are the
  restrictions of those of `Φ` to the second factor.
* `applyDistributionToSliceRight`: the slice family `x ↦ ⟨T, Φ(x, ·)⟩` as a test function in
  `𝓓((⊤ : Opens E), G)`.
* `tsupport_applyDistributionToSliceRight_subset`: its support lies in `Prod.fst '' tsupport Φ`.
* `lineDerivCLM_applyDistributionToSliceRight`: the directional derivative law displayed above.

## Implementation notes

`E` is assumed finite-dimensional, which is what makes the compact-curry and Taylor remainder
estimates in the private lemmas go through (uniformity on compact sets). The continuity of
`Φ ↦ applyDistributionToSliceRight T Φ` for the LF topologies is a separate matter, treated in
`PDE.DistributionTheory.Distribution.SliceFamily.Continuity`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter V, "Distributions in Product Spaces".
  <https://doi.org/10.1007/978-3-642-61497-2_6>
* F. G. Friedlander and M. Joshi, *Introduction to the Theory of Distributions*, 2nd ed.,
  Cambridge University Press, 1998, Chapter 4, "Tensor products".
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped CompactConvergenceCLM Distributions

noncomputable section

namespace TestFunction

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

private def rightInclusion : F →L[ℝ] E × F :=
  ContinuousLinearMap.inr ℝ E F

private def leftInclusion : E →L[ℝ] E × F :=
  ContinuousLinearMap.inl ℝ E F

private def restrictRightIterated (i : ℕ) :
    ((E × F) [×i]→L[ℝ] ℝ) →L[ℝ] F [×i]→L[ℝ] ℝ :=
  ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦
    rightInclusion (E := E) (F := F)

private theorem iteratedFDeriv_sliceRight_eq
    (i : ℕ) (x : E) (y : F)
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    iteratedFDeriv ℝ i (fun z : F ↦ Φ (x, z)) y =
      restrictRightIterated (E := E) (F := F) i
        (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p) (x, y)) := by
  let a : E × F := (x, 0)
  let g : F →L[ℝ] E × F := rightInclusion (E := E) (F := F)
  have hfun :
      (fun z : F ↦ Φ (x, z)) =
        (fun p : E × F ↦ Φ (a + p)) ∘ g := by
    funext z
    simp [a, g, rightInclusion]
  rw [hfun]
  have htranslated :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : E × F ↦ Φ (a + p)) :=
    Φ.contDiff.comp (contDiff_const.add contDiff_id)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right g htranslated y
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)]
  simp only [restrictRightIterated]
  rw [iteratedFDeriv_comp_add_left]
  simp [a, g, rightInclusion]

/-- Iterated Fréchet derivatives of a right slice are the ambient derivatives restricted to
directions tangent to the right factor. -/
theorem iteratedFDeriv_sliceRight
    (i : ℕ) (x : E) (y : F)
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    iteratedFDeriv ℝ i (fun z : F ↦ Φ (x, z)) y =
      (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p) (x, y)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ E F) := by
  rw [iteratedFDeriv_sliceRight_eq]
  rfl

private def fiberIterated
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) (y : F) :
    F [×i]→L[ℝ] ℝ :=
  restrictRightIterated (E := E) (F := F) i
    (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p) (x, y))

private def fiberIteratedFDeriv
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) (y : F) :
    E →L[ℝ] F [×i]→L[ℝ] ℝ :=
  (restrictRightIterated (E := E) (F := F) i).comp
    ((fderiv ℝ (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p)) (x, y)).comp
      (leftInclusion (E := E) (F := F)))

private theorem continuous_fiberIterated_uncurry
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    Continuous (fiberIterated i Φ).uncurry := by
  change Continuous fun p : E × F ↦
    restrictRightIterated (E := E) (F := F) i
      (iteratedFDeriv ℝ i (fun q : E × F ↦ Φ q) p)
  exact (restrictRightIterated (E := E) (F := F) i).continuous.comp
    (Φ.contDiff.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i))

private theorem continuous_fiberIteratedFDeriv_uncurry
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    Continuous (fiberIteratedFDeriv i Φ).uncurry := by
  change Continuous fun p : E × F ↦
    (restrictRightIterated (E := E) (F := F) i).comp
      ((fderiv ℝ (iteratedFDeriv ℝ i (fun q : E × F ↦ Φ q)) p).comp
        (leftInclusion (E := E) (F := F)))
  have hiter :
      ContDiff ℝ 1 (iteratedFDeriv ℝ i (fun q : E × F ↦ Φ q)) :=
    Φ.contDiff.iteratedFDeriv_right
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (1 + i))
  have hfderiv :
      Continuous
        (fderiv ℝ (iteratedFDeriv ℝ i (fun q : E × F ↦ Φ q))) :=
    hiter.continuous_fderiv one_ne_zero
  exact
    (hfderiv.clm_comp_const (leftInclusion (E := E) (F := F))).const_clm_comp
      (restrictRightIterated (E := E) (F := F) i)

private theorem hasFDerivAt_fiberIterated
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) (y : F) :
    HasFDerivAt (fun z ↦ fiberIterated i Φ z y)
      (fiberIteratedFDeriv i Φ x y) x := by
  have hbase :
      HasFDerivAt
        (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p))
        (fderiv ℝ (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p)) (x, y))
        (x, y) :=
    (Φ.contDiff.differentiable_iteratedFDeriv (m := i)
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl i)).differentiableAt.hasFDerivAt
  have hprod :
      HasFDerivAt (fun z : E ↦ (z, y)) (leftInclusion (E := E) (F := F)) x :=
    hasFDerivAt_prodMk_left x y
  have hparameter := hbase.comp x hprod
  have hout :=
    (restrictRightIterated (E := E) (F := F) i).hasFDerivAt.comp x hparameter
  simpa only [Function.comp_def, fiberIterated, fiberIteratedFDeriv] using hout

private theorem hasFDerivAt_compact_fiberIterated
    (K : Compacts F) (i : ℕ)
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    HasFDerivAt
      (BoundedContinuousFunction.compactCurry K (fiberIterated i Φ)
        (continuous_fiberIterated_uncurry i Φ))
      (BoundedContinuousFunction.compactCurryFDeriv K
        (fiberIteratedFDeriv i Φ)
        (continuous_fiberIteratedFDeriv_uncurry i Φ) x)
      x :=
  BoundedContinuousFunction.hasFDerivAt_compactCurry K
    (fiberIterated i Φ) (fiberIteratedFDeriv i Φ)
    (continuous_fiberIterated_uncurry i Φ)
    (continuous_fiberIteratedFDeriv_uncurry i Φ)
    (hasFDerivAt_fiberIterated i Φ) x

private theorem restrictRightIterated_fderiv_apply
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) (y : F) (h : E) :
    restrictRightIterated (E := E) (F := F) i
        (iteratedFDeriv ℝ i
          (fun p : E × F ↦ fderiv ℝ (fun q : E × F ↦ Φ q) p (h, 0)) (x, y)) =
      fiberIteratedFDeriv i Φ x y h := by
  ext v
  let r : Fin i → E × F := fun j ↦ rightInclusion (E := E) (F := F) (v j)
  let l : E × F := leftInclusion (E := E) (F := F) h
  have hsym :
      iteratedFDeriv ℝ (i + 1) (fun p : E × F ↦ Φ p) (x, y) (Fin.snoc r l) =
        iteratedFDeriv ℝ (i + 1) (fun p : E × F ↦ Φ p) (x, y) (Fin.cons l r) := by
    exact PDE.Analysis.iteratedFDeriv_snoc_eq_cons_of_smooth
      i (fun p : E × F ↦ Φ p) Φ.contDiff (x, y) r l
  change
    iteratedFDeriv ℝ i
        (fun p : E × F ↦ fderiv ℝ (fun q : E × F ↦ Φ q) p (h, 0)) (x, y) r =
      fderiv ℝ (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p)) (x, y) l r
  have hfderiv :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fderiv ℝ (fun p : E × F ↦ Φ p)) :=
    Φ.contDiff.fderiv_right (by simp)
  calc
    iteratedFDeriv ℝ i
        (fun p : E × F ↦ fderiv ℝ (fun q : E × F ↦ Φ q) p (h, 0)) (x, y) r =
        iteratedFDeriv ℝ i
          (fderiv ℝ (fun q : E × F ↦ Φ q)) (x, y) r l := by
      exact iteratedFDeriv_clm_apply_const_apply hfderiv
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)
    _ = iteratedFDeriv ℝ (i + 1) (fun p : E × F ↦ Φ p) (x, y)
          (Fin.snoc r l) := by
      rw [iteratedFDeriv_succ_apply_right]
      simp
    _ = iteratedFDeriv ℝ (i + 1) (fun p : E × F ↦ Φ p) (x, y)
          (Fin.cons l r) :=
      hsym
    _ = fderiv ℝ (iteratedFDeriv ℝ i (fun p : E × F ↦ Φ p)) (x, y) l r := by
      rw [iteratedFDeriv_succ_apply_left]
      simp

/-- The second-coordinate projection of the support of a product test function. -/
def rightSupport
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) : Compacts F :=
  ⟨Prod.snd '' tsupport Φ, Φ.hasCompactSupport.image continuous_snd⟩

/-- Every right slice is supported in the second-coordinate projection of the support. -/
theorem support_sliceRight_subset_rightSupport
    (x : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    support (sliceRight x Φ) ⊆ rightSupport Φ := by
  intro y hy
  have hy' : y ∈ (Prod.mk x) ⁻¹' tsupport Φ :=
    tsupport_sliceRight_subset x Φ (subset_tsupport _ hy)
  exact ⟨(x, y), hy', rfl⟩

/-- A right slice, as a smooth function supported in the projected support. -/
def sliceRightSupported
    (x : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    𝓓_{rightSupport Φ}(F, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset
    (sliceRight x Φ).contDiff
    (support_sliceRight_subset_rightSupport x Φ)

private def leftLineDeriv
    (h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    𝓓((⊤ : Opens (E × F)), ℝ) :=
  lineDerivCLM ℝ (h, 0) Φ

private theorem tsupport_leftLineDeriv_subset
    (h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    tsupport (leftLineDeriv h Φ) ⊆ tsupport Φ := by
  have hdiff : Differentiable ℝ (fun p : E × F ↦ Φ p) :=
    Φ.contDiff.differentiable (by simp)
  have heq :
      (fun p : E × F ↦ leftLineDeriv h Φ p) =
        fun p : E × F ↦
          fderiv ℝ (fun q : E × F ↦ Φ q) p (h, 0) := by
    funext p
    change (lineDerivCLM ℝ (h, 0) Φ :
      𝓓((⊤ : Opens (E × F)), ℝ)) p = _
    rw [lineDerivCLM_apply_of_le (by simp)]
    exact hdiff.differentiableAt.lineDeriv_eq_fderiv
  change tsupport (fun p : E × F ↦ leftLineDeriv h Φ p) ⊆ tsupport Φ
  rw [heq]
  exact tsupport_fderiv_apply_subset ℝ (h, 0)

private theorem support_sliceRight_leftLineDeriv_subset_rightSupport
    (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    support (sliceRight x (leftLineDeriv h Φ)) ⊆ rightSupport Φ := by
  intro y hy
  have hy' :
      y ∈ (Prod.mk x) ⁻¹' tsupport (leftLineDeriv h Φ) :=
    tsupport_sliceRight_subset x _ (subset_tsupport _ hy)
  exact ⟨(x, y), tsupport_leftLineDeriv_subset h Φ hy', rfl⟩

private def sliceRightParameterFDerivSupported
    (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    𝓓_{rightSupport Φ}(F, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset
    (sliceRight x (leftLineDeriv h Φ)).contDiff
    (support_sliceRight_leftLineDeriv_subset_rightSupport x h Φ)

@[simp]
private theorem sliceRightParameterFDerivSupported_apply
    (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (y : F) :
    sliceRightParameterFDerivSupported x h Φ y =
      fderiv ℝ (fun p : E × F ↦ Φ p) (x, y) (h, 0) := by
  change (lineDerivCLM ℝ (h, 0) Φ) (x, y) = _
  rw [lineDerivCLM_apply_of_le (by simp)]
  exact
    (Φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv

private theorem iteratedFDeriv_sliceRightParameterFDerivSupported
    (i : ℕ) (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (y : F) :
    iteratedFDeriv ℝ i
        (fun z : F ↦ sliceRightParameterFDerivSupported x h Φ z) y =
      fiberIteratedFDeriv i Φ x y h := by
  change
    iteratedFDeriv ℝ i
        (fun z : F ↦ leftLineDeriv h Φ (x, z)) y =
      fiberIteratedFDeriv i Φ x y h
  rw [iteratedFDeriv_sliceRight_eq]
  have hleft :
      (fun p : E × F ↦ leftLineDeriv h Φ p) =
        fun p : E × F ↦ fderiv ℝ (fun q : E × F ↦ Φ q) p (h, 0) := by
    funext p
    change (lineDerivCLM ℝ (h, 0) Φ) p = _
    rw [lineDerivCLM_apply_of_le (by simp)]
    exact
      (Φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
  rw [hleft]
  exact restrictRightIterated_fderiv_apply i Φ x y h

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The function obtained by applying a distribution to every right slice. -/
def applyToSliceRight
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) : G :=
  Distribution.restrictToSupportedInCLM T (rightSupport Φ)
    (sliceRightSupported x Φ)

@[simp]
private theorem applyToSliceRight_eq
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    applyToSliceRight T Φ x = T (sliceRight x Φ) := by
  rw [applyToSliceRight,
    Distribution.restrictToSupportedInCLM_apply]
  congr 1

private def applyToSliceRightFDerivLM
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) : E →ₗ[ℝ] G where
  toFun h :=
    Distribution.restrictToSupportedInCLM T (rightSupport Φ)
      (sliceRightParameterFDerivSupported x h Φ)
  map_add' h h' := by
    rw [← map_add]
    congr 1
    ext y
    simp only [sliceRightParameterFDerivSupported_apply]
    simpa using
      map_add (fderiv ℝ (fun p : E × F ↦ Φ p) (x, y)) (h, 0) (h', 0)
  map_smul' c h := by
    rw [← map_smul]
    congr 1
    ext y
    simp only [sliceRightParameterFDerivSupported_apply]
    simpa using
      map_smul (fderiv ℝ (fun p : E × F ↦ Φ p) (x, y)) c (h, 0)

private def fiberIteratedFDerivNorm
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    BoundedContinuousFunction (rightSupport Φ) ℝ :=
  letI := ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := F [×i]→L[ℝ] ℝ)
    (σ₁₂ := RingHom.id ℝ)
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun y ↦ ‖fiberIteratedFDeriv i Φ x y‖
      continuous_toFun :=
        ((continuous_fiberIteratedFDeriv_uncurry i Φ).comp
          (continuous_const.prodMk continuous_subtype_val)).norm }

@[simp]
private theorem fiberIteratedFDerivNorm_apply
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E)
    (y : rightSupport Φ) :
    fiberIteratedFDerivNorm i Φ x y =
      ‖fiberIteratedFDeriv i Φ x y‖ :=
  rfl

private theorem exists_applyToSliceRightFDerivLM_bound
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    ∃ C : ℝ, ∀ h : E, ‖applyToSliceRightFDerivLM T Φ x h‖ ≤ C * ‖h‖ := by
  obtain ⟨k, C, hC, hT⟩ :=
    Distribution.exists_norm_restrictToSupportedIn_le_supSeminorm
      T (rightSupport Φ)
  let A : ℝ :=
    ∑ i ∈ Finset.Iic k, ‖fiberIteratedFDerivNorm i Φ x‖
  refine ⟨(C : ℝ) * A, fun h ↦ ?_⟩
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg fun i _ ↦
      norm_nonneg (fiberIteratedFDerivNorm i Φ x)
  have hseminorm :
      ContDiffMapSupportedIn.supSeminorm ℝ F ℝ ⊤ (rightSupport Φ) k
          (sliceRightParameterFDerivSupported x h Φ) ≤
        A * ‖h‖ := by
    apply Seminorm.finset_sup_apply_le (mul_nonneg hA (norm_nonneg h))
    intro i hi
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ
      (mul_nonneg hA (norm_nonneg h)) i
      (sliceRightParameterFDerivSupported x h Φ)).2
    intro y hy
    rw [iteratedFDeriv_sliceRightParameterFDerivSupported]
    calc
      ‖fiberIteratedFDeriv i Φ x y h‖ ≤
          ‖fiberIteratedFDeriv i Φ x y‖ * ‖h‖ :=
        (fiberIteratedFDeriv i Φ x y).le_opNorm h
      _ ≤ ‖fiberIteratedFDerivNorm i Φ x‖ * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
        have heval :=
          BoundedContinuousFunction.norm_coe_le_norm
            (fiberIteratedFDerivNorm i Φ x) ⟨y, hy⟩
        rw [fiberIteratedFDerivNorm_apply] at heval
        rw [Real.norm_of_nonneg (norm_nonneg
          (fiberIteratedFDeriv i Φ x y))] at heval
        exact heval
      _ ≤ A * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
        exact Finset.single_le_sum
          (fun j _ ↦ norm_nonneg (fiberIteratedFDerivNorm j Φ x)) hi
  calc
    ‖applyToSliceRightFDerivLM T Φ x h‖ ≤
        (C : ℝ) *
          ContDiffMapSupportedIn.supSeminorm ℝ F ℝ ⊤
            (rightSupport Φ) k
            (sliceRightParameterFDerivSupported x h Φ) :=
      hT (sliceRightParameterFDerivSupported x h Φ)
    _ ≤ (C : ℝ) * (A * ‖h‖) :=
      mul_le_mul_of_nonneg_left hseminorm C.coe_nonneg
    _ = ((C : ℝ) * A) * ‖h‖ := by ring

private def applyToSliceRightFDerivCLM
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) : E →L[ℝ] G :=
  let hbound := exists_applyToSliceRightFDerivLM_bound T Φ x
  (applyToSliceRightFDerivLM T Φ x).mkContinuous
    hbound.choose hbound.choose_spec

@[simp]
private theorem applyToSliceRightFDerivCLM_apply
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x h : E) :
    applyToSliceRightFDerivCLM T Φ x h =
      Distribution.restrictToSupportedInCLM T (rightSupport Φ)
        (sliceRightParameterFDerivSupported x h Φ) :=
  rfl

private def sliceRightRemainderSupported
    (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    𝓓_{rightSupport Φ}(F, ℝ) :=
  sliceRightSupported (x + h) Φ - sliceRightSupported x Φ -
    sliceRightParameterFDerivSupported x h Φ

private def fiberRemainderNorm
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x h : E) : ℝ :=
  ‖BoundedContinuousFunction.compactCurry (rightSupport Φ)
        (fiberIterated i Φ) (continuous_fiberIterated_uncurry i Φ) (x + h) -
      BoundedContinuousFunction.compactCurry (rightSupport Φ)
        (fiberIterated i Φ) (continuous_fiberIterated_uncurry i Φ) x -
      BoundedContinuousFunction.compactCurryFDeriv (rightSupport Φ)
        (fiberIteratedFDeriv i Φ)
        (continuous_fiberIteratedFDeriv_uncurry i Φ) x h‖

private theorem fiberRemainderNorm_isLittleO
    (i : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    (fun h ↦ fiberRemainderNorm i Φ x h) =o[nhds 0] fun h : E ↦ h := by
  have hderiv := hasFDerivAt_compact_fiberIterated
    (rightSupport Φ) i Φ x
  have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hderiv).norm_left
  simpa only [fiberRemainderNorm] using ho

private theorem iteratedFDeriv_sliceRightRemainderSupported
    (i : ℕ) (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (y : F) :
    iteratedFDeriv ℝ i
        (fun z : F ↦ sliceRightRemainderSupported x h Φ z) y =
      fiberIterated i Φ (x + h) y - fiberIterated i Φ x y -
        fiberIteratedFDeriv i Φ x y h := by
  change
    iteratedFDeriv ℝ i
        ((fun z : F ↦ sliceRightSupported (x + h) Φ z) -
          (fun z : F ↦ sliceRightSupported x Φ z) -
          (fun z : F ↦ sliceRightParameterFDerivSupported x h Φ z)) y = _
  have hleft :
      ContDiff ℝ (i : ℕ∞)
        ((fun z : F ↦ sliceRightSupported (x + h) Φ z) -
          fun z : F ↦ sliceRightSupported x Φ z) :=
    ((sliceRightSupported (x + h) Φ).contDiff.of_le (mod_cast le_top)).sub
      ((sliceRightSupported x Φ).contDiff.of_le (mod_cast le_top))
  have hright :
      ContDiff ℝ (i : ℕ∞)
        (fun z : F ↦ sliceRightParameterFDerivSupported x h Φ z) :=
    (sliceRightParameterFDerivSupported x h Φ).contDiff.of_le
      (mod_cast le_top)
  have hfirst :
      iteratedFDeriv ℝ i
          (fun z : F ↦ sliceRightSupported (x + h) Φ z) y =
        fiberIterated i Φ (x + h) y := by
    change iteratedFDeriv ℝ i (fun z : F ↦ Φ (x + h, z)) y = _
    exact iteratedFDeriv_sliceRight_eq i (x + h) y Φ
  have hsecond :
      iteratedFDeriv ℝ i
          (fun z : F ↦ sliceRightSupported x Φ z) y =
        fiberIterated i Φ x y := by
    change iteratedFDeriv ℝ i (fun z : F ↦ Φ (x, z)) y = _
    exact iteratedFDeriv_sliceRight_eq i x y Φ
  have hthird :
      iteratedFDeriv ℝ i
          (fun z : F ↦ sliceRightParameterFDerivSupported x h Φ z) y =
        fiberIteratedFDeriv i Φ x y h :=
    iteratedFDeriv_sliceRightParameterFDerivSupported i x h Φ y
  rw [iteratedFDeriv_sub hleft hright]
  rw [iteratedFDeriv_sub
    ((sliceRightSupported (x + h) Φ).contDiff.of_le (mod_cast le_top))
    ((sliceRightSupported x Φ).contDiff.of_le (mod_cast le_top))]
  simp only [Pi.sub_apply, hfirst, hsecond, hthird]

private theorem norm_iteratedFDeriv_sliceRightRemainderSupported_le
    (i : ℕ) (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ))
    (y : F) (hy : y ∈ rightSupport Φ) :
    ‖iteratedFDeriv ℝ i
        (fun z : F ↦ sliceRightRemainderSupported x h Φ z) y‖ ≤
      fiberRemainderNorm i Φ x h := by
  rw [iteratedFDeriv_sliceRightRemainderSupported]
  have heval :=
    BoundedContinuousFunction.norm_coe_le_norm
      (BoundedContinuousFunction.compactCurry (rightSupport Φ)
          (fiberIterated i Φ) (continuous_fiberIterated_uncurry i Φ) (x + h) -
        BoundedContinuousFunction.compactCurry (rightSupport Φ)
          (fiberIterated i Φ) (continuous_fiberIterated_uncurry i Φ) x -
        BoundedContinuousFunction.compactCurryFDeriv (rightSupport Φ)
          (fiberIteratedFDeriv i Φ)
          (continuous_fiberIteratedFDeriv_uncurry i Φ) x h)
      ⟨y, hy⟩
  simpa only [BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.compactCurry_apply,
    BoundedContinuousFunction.compactCurryFDeriv_apply,
    fiberRemainderNorm] using heval

private theorem supSeminorm_sliceRightRemainderSupported_le
    (k : ℕ) (x h : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    ContDiffMapSupportedIn.supSeminorm ℝ F ℝ ⊤ (rightSupport Φ) k
        (sliceRightRemainderSupported x h Φ) ≤
      ∑ i ∈ Finset.Iic k, fiberRemainderNorm i Φ x h := by
  have hsum_nonneg :
      0 ≤ ∑ i ∈ Finset.Iic k, fiberRemainderNorm i Φ x h :=
    Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  apply Seminorm.finset_sup_apply_le hsum_nonneg
  intro i hi
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hsum_nonneg i
    (sliceRightRemainderSupported x h Φ)).2
  intro y hy
  have hnonneg (j : ℕ) : 0 ≤ fiberRemainderNorm j Φ x h := by
    unfold fiberRemainderNorm
    exact norm_nonneg _
  exact (norm_iteratedFDeriv_sliceRightRemainderSupported_le
    i x h Φ y hy).trans
      (Finset.single_le_sum (fun j _ ↦ hnonneg j) hi)

private theorem norm_applyToSliceRight_remainder_le
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x h : E)
    (k : ℕ) (C : NNReal)
    (hT : ∀ φ : 𝓓_{rightSupport Φ}(F, ℝ),
      ‖Distribution.restrictToSupportedInCLM T (rightSupport Φ) φ‖ ≤
        C * ContDiffMapSupportedIn.supSeminorm ℝ F ℝ ⊤
          (rightSupport Φ) k φ) :
    ‖applyToSliceRight T Φ (x + h) - applyToSliceRight T Φ x -
        applyToSliceRightFDerivCLM T Φ x h‖ ≤
      (C : ℝ) * ∑ i ∈ Finset.Iic k, fiberRemainderNorm i Φ x h := by
  have heq :
      applyToSliceRight T Φ (x + h) - applyToSliceRight T Φ x -
          applyToSliceRightFDerivCLM T Φ x h =
        Distribution.restrictToSupportedInCLM T (rightSupport Φ)
          (sliceRightRemainderSupported x h Φ) := by
    simp only [applyToSliceRight, applyToSliceRightFDerivCLM_apply,
      sliceRightRemainderSupported, map_sub]
  rw [heq]
  exact (hT (sliceRightRemainderSupported x h Φ)).trans
    (mul_le_mul_of_nonneg_left
      (supSeminorm_sliceRightRemainderSupported_le k x h Φ)
      C.coe_nonneg)

private theorem sum_fiberRemainderNorm_isLittleO
    (k : ℕ) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    (fun h ↦ ∑ i ∈ Finset.Iic k, fiberRemainderNorm i Φ x h) =o[nhds 0]
      fun h : E ↦ h := by
  have hsum :=
    Asymptotics.IsLittleO.sum fun i (_hi : i ∈ Finset.Iic k) ↦
      fiberRemainderNorm_isLittleO i Φ x
  exact hsum.congr'
    (Filter.Eventually.of_forall fun h ↦ by simp)
    (Filter.Eventually.of_forall fun _ ↦ rfl)

private theorem hasFDerivAt_applyToSliceRight
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    HasFDerivAt (applyToSliceRight T Φ)
      (applyToSliceRightFDerivCLM T Φ x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  obtain ⟨k, C, _hC, hT⟩ :=
    Distribution.exists_norm_restrictToSupportedIn_le_supSeminorm
      T (rightSupport Φ)
  apply Asymptotics.isLittleO_iff.2
  intro ε hε
  let δ : ℝ := ε / ((C : ℝ) + 1)
  have hC1 : 0 < (C : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hC1
  have hsmall :=
    Asymptotics.isLittleO_iff.1
      (sum_fiberRemainderNorm_isLittleO k Φ x) hδ
  filter_upwards [hsmall] with h hh
  have hsum_nonneg :
      0 ≤ ∑ i ∈ Finset.Iic k, fiberRemainderNorm i Φ x h :=
    Finset.sum_nonneg fun i _ ↦ by
      unfold fiberRemainderNorm
      exact norm_nonneg _
  have hh' :
      ∑ i ∈ Finset.Iic k, fiberRemainderNorm i Φ x h ≤
        δ * ‖h‖ := by
    rw [Real.norm_of_nonneg hsum_nonneg] at hh
    exact hh
  calc
    ‖applyToSliceRight T Φ (x + h) - applyToSliceRight T Φ x -
        applyToSliceRightFDerivCLM T Φ x h‖ ≤
        (C : ℝ) * ∑ i ∈ Finset.Iic k, fiberRemainderNorm i Φ x h :=
      norm_applyToSliceRight_remainder_le T Φ x h k C hT
    _ ≤ (C : ℝ) * (δ * ‖h‖) :=
      mul_le_mul_of_nonneg_left hh' C.coe_nonneg
    _ ≤ ((C : ℝ) + 1) * (δ * ‖h‖) := by
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one)
        (mul_nonneg hδ.le (norm_nonneg h))
    _ = ε * ‖h‖ := by
      dsimp only [δ]
      field_simp [ne_of_gt hC1]

private theorem applyToSliceRightFDerivCLM_apply_eq
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x h : E) :
    applyToSliceRightFDerivCLM T Φ x h =
      applyToSliceRight T (leftLineDeriv h Φ) x := by
  rw [applyToSliceRightFDerivCLM_apply, applyToSliceRight_eq,
    Distribution.restrictToSupportedInCLM_apply]
  congr 1

private theorem contDiff_applyToSliceRight_nat
    [FiniteDimensional ℝ E]
    (n : ℕ) (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    ContDiff ℝ n (applyToSliceRight T Φ) := by
  induction n generalizing Φ with
  | zero =>
      change ContDiff ℝ 0 (applyToSliceRight T Φ)
      rw [contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x ↦
        (hasFDerivAt_applyToSliceRight T Φ x).continuousAt
  | succ n ih =>
      apply contDiff_succ_iff_hasFDerivAt.2
      refine ⟨applyToSliceRightFDerivCLM T Φ, ?_, fun x ↦
        hasFDerivAt_applyToSliceRight T Φ x⟩
      rw [contDiff_clm_apply_iff]
      intro h
      have heq :
          (fun x ↦ applyToSliceRightFDerivCLM T Φ x h) =
            applyToSliceRight T (leftLineDeriv h Φ) := by
        funext x
        exact applyToSliceRightFDerivCLM_apply_eq T Φ x h
      rw [heq]
      exact ih (leftLineDeriv h Φ)

/-- Applying a distribution to the right slices gives a smooth function of the parameter. If
`E` is infinite-dimensional, the compactly supported test function is zero (Riesz), and so is
the slice-applied distribution. -/
theorem contDiff_applyToSliceRight
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (applyToSliceRight T Φ) := by
  by_cases hE : FiniteDimensional ℝ E
  · exact contDiff_infty.2 fun n ↦ contDiff_applyToSliceRight_nat n T Φ
  have hΦ : ⇑Φ = 0 := by
    rcases Φ.hasCompactSupport.eq_zero_or_finiteDimensional (𝕜 := ℝ) Φ.contDiff.continuous with
      h | h
    · exact h
    · exact absurd (Module.Finite.of_surjective (LinearMap.fst ℝ E F) LinearMap.fst_surjective) hE
  have h0 : applyToSliceRight T Φ = fun _ ↦ 0 := by
    funext x
    have hslice : sliceRight x Φ = 0 := by
      ext y
      by_contra hxy
      exact hxy (congrFun hΦ (x, y))
    simp only [applyToSliceRight_eq, hslice, map_zero]
  rw [h0]
  exact contDiff_const

/-- The first-coordinate projection of the support of a product test function. -/
def leftSupport
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) : Compacts E :=
  ⟨Prod.fst '' tsupport Φ, Φ.hasCompactSupport.image continuous_fst⟩

/-- The slice-applied distribution vanishes outside the projected support. -/
theorem support_applyToSliceRight_subset_leftSupport
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    support (applyToSliceRight T Φ) ⊆ leftSupport Φ := by
  intro x hx
  by_contra hxleft
  have hslice : sliceRight x Φ = 0 := by
    ext y
    by_contra hxy
    exact hxleft ⟨(x, y), subset_tsupport Φ hxy, rfl⟩
  exact hx (by simp only [applyToSliceRight_eq, hslice, map_zero])

/-- Apply a distribution in the second variable of a product test function. -/
def applyDistributionToSliceRight
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    𝓓((⊤ : Opens E), G) where
  toFun := applyToSliceRight T Φ
  contDiff' := contDiff_applyToSliceRight T Φ
  hasCompactSupport' :=
    HasCompactSupport.of_support_subset_isCompact (leftSupport Φ).2
      (support_applyToSliceRight_subset_leftSupport T Φ)
  tsupport_subset' := subset_univ _

/-- Pointwise formula: at `x` the slice family is `⟨T, Φ(x, ·)⟩`, the distribution `T` applied
to the right slice `sliceRight x Φ`. -/
@[simp]
theorem applyDistributionToSliceRight_apply
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    applyDistributionToSliceRight T Φ x = T (sliceRight x Φ) :=
  applyToSliceRight_eq T Φ x

/-- Applying a distribution to the right slices does not enlarge support beyond the first
coordinate projection of the original test-function support. -/
theorem tsupport_applyDistributionToSliceRight_subset
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    tsupport (applyDistributionToSliceRight T Φ) ⊆
      Prod.fst '' tsupport Φ := by
  apply closure_minimal
  · exact support_applyToSliceRight_subset_leftSupport T Φ
  · exact (leftSupport Φ).2.isClosed

/-- Differentiating the distribution-applied slice family in the parameter differentiates the
product test function in the same coordinate. -/
theorem lineDerivCLM_applyDistributionToSliceRight
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (h : E) :
    lineDerivCLM ℝ h (applyDistributionToSliceRight T Φ) =
      applyDistributionToSliceRight T (lineDerivCLM ℝ (h, 0) Φ) := by
  ext x
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (applyToSliceRight T Φ) x h =
    applyToSliceRight T (leftLineDeriv h Φ) x
  have hderiv := hasFDerivAt_applyToSliceRight T Φ x
  rw [hderiv.differentiableAt.lineDeriv_eq_fderiv, hderiv.fderiv]
  exact applyToSliceRightFDerivCLM_apply_eq T Φ x h

end TestFunction
