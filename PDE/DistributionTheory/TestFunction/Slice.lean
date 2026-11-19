/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.TensorProduct

/-!
# Fixed-coordinate slices of test functions

A scalar test function on a product restricts to a scalar test function on every coordinate
fiber. These restrictions are continuous linear maps between the canonical LF test-function
spaces, supported in the corresponding fiber of the original support, and compatible with
coordinate derivatives and external tensor products.
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace TestFunction

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Fixing the first coordinate is a proper map into the product. -/
theorem isProperMap_prodMk_right (x : E) :
    IsProperMap (Prod.mk x : F → E × F) := by
  refine Topology.IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight x, ?_⟩
  have : range (Prod.mk x : F → E × F) = ({x} ×ˢ univ) := by
    simp [Set.singleton_prod]
  rw [this]
  exact isClosed_singleton.prod isClosed_univ

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Fixing the second coordinate is a proper map into the product. -/
theorem isProperMap_prodMk_left (y : F) :
    IsProperMap (fun x : E ↦ (x, y)) := by
  refine Topology.IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkLeft y, ?_⟩
  have : range (fun x : E ↦ (x, y)) = (univ ×ˢ {y}) := by
    simp [Set.prod_singleton]
  rw [this]
  exact isClosed_univ.prod isClosed_singleton

/-- Fix the first coordinate of a test function on a product. -/
def sliceRight
    (x : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    𝓓((⊤ : Opens F), ℝ) :=
  precompProper (Prod.mk x) (contDiff_prodMk_right x)
    (isProperMap_prodMk_right x) Φ

/-- The right slice at `x` is the function `y ↦ Φ (x, y)`. -/
@[simp]
theorem sliceRight_apply
    (x : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (y : F) :
    sliceRight x Φ y = Φ (x, y) :=
  rfl

/-- Fix the first coordinate, as a continuous linear map of LF test-function spaces. -/
def sliceRightCLM (x : E) :
    𝓓((⊤ : Opens (E × F)), ℝ) →L[ℝ] 𝓓((⊤ : Opens F), ℝ) :=
  precompProperCLM (Prod.mk x) (contDiff_prodMk_right x)
    (isProperMap_prodMk_right x)

/-- The continuous linear slice map agrees with `sliceRight`; it is `precompProperCLM` along the
closed embedding `y ↦ (x, y)`. -/
@[simp]
theorem sliceRightCLM_apply
    (x : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    sliceRightCLM x Φ = sliceRight x Φ := by
  ext y
  rfl

/-- Fix the second coordinate of a test function on a product. -/
def sliceLeft
    (y : F) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    𝓓((⊤ : Opens E), ℝ) :=
  precompProper (fun x : E ↦ (x, y)) (contDiff_prodMk_left y)
    (isProperMap_prodMk_left y) Φ

/-- The left slice at `y` is the function `x ↦ Φ (x, y)`. -/
@[simp]
theorem sliceLeft_apply
    (y : F) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    sliceLeft y Φ x = Φ (x, y) :=
  rfl

/-- Fix the second coordinate, as a continuous linear map of LF test-function spaces. -/
def sliceLeftCLM (y : F) :
    𝓓((⊤ : Opens (E × F)), ℝ) →L[ℝ] 𝓓((⊤ : Opens E), ℝ) :=
  precompProperCLM (fun x : E ↦ (x, y)) (contDiff_prodMk_left y)
    (isProperMap_prodMk_left y)

/-- The continuous linear slice map agrees with `sliceLeft`; it is `precompProperCLM` along the
closed embedding `x ↦ (x, y)`. -/
@[simp]
theorem sliceLeftCLM_apply
    (y : F) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    sliceLeftCLM y Φ = sliceLeft y Φ := by
  ext x
  rfl

/-- A right slice is supported in the corresponding fiber of the original support. -/
theorem tsupport_sliceRight_subset
    (x : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    tsupport (sliceRight x Φ) ⊆ (Prod.mk x) ⁻¹' tsupport Φ := by
  intro y hy
  change y ∈ tsupport (⇑Φ ∘ Prod.mk x) at hy
  exact tsupport_comp_subset_preimage Φ (Continuous.prodMk_right x) hy

/-- A left slice is supported in the corresponding fiber of the original support. -/
theorem tsupport_sliceLeft_subset
    (y : F) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    tsupport (sliceLeft y Φ) ⊆ (fun x : E ↦ (x, y)) ⁻¹' tsupport Φ := by
  intro x hx
  change x ∈ tsupport (⇑Φ ∘ fun x : E ↦ (x, y)) at hx
  exact tsupport_comp_subset_preimage Φ (Continuous.prodMk_left y) hx

/-- Slicing an external tensor product evaluates its left factor. -/
theorem sliceRight_tensorProduct
    (x : E)
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    sliceRight x (tensorProduct φ ψ) = φ x • ψ := by
  ext y
  simp

/-- Slicing an external tensor product evaluates its right factor. -/
theorem sliceLeft_tensorProduct
    (y : F)
    (φ : 𝓓((⊤ : Opens E), ℝ))
    (ψ : 𝓓((⊤ : Opens F), ℝ)) :
    sliceLeft y (tensorProduct φ ψ) = ψ y • φ := by
  ext x
  simp [mul_comm]

/-- A directional derivative in the retained right coordinate commutes with slicing. -/
theorem lineDerivCLM_sliceRight
    (x : E) (w : F) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    lineDerivCLM ℝ w (sliceRight x Φ) =
      sliceRight x (lineDerivCLM ℝ (0, w) Φ) := by
  ext y
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun z : F ↦ Φ (x, z)) y w =
    (lineDerivCLM ℝ (0, w) Φ) (x, y)
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun z : F ↦ Φ (x, z)) y w =
    lineDeriv ℝ (fun p : E × F ↦ Φ p) (x, y) (0, w)
  have hΦ : DifferentiableAt ℝ (fun p : E × F ↦ Φ p) (x, y) :=
    (Φ.contDiff.differentiable (by simp)).differentiableAt
  have hslice : DifferentiableAt ℝ (fun z : F ↦ Φ (x, z)) y :=
    hΦ.comp y (hasFDerivAt_prodMk_right x y).differentiableAt
  rw [hslice.lineDeriv_eq_fderiv, hΦ.lineDeriv_eq_fderiv]
  change (fderiv ℝ (⇑Φ ∘ Prod.mk x) y) w =
    (fderiv ℝ (fun p : E × F ↦ Φ p) (x, y)) (0, w)
  rw [(hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).fderiv]
  simp

/-- A directional derivative in the retained left coordinate commutes with slicing. -/
theorem lineDerivCLM_sliceLeft
    (y : F) (v : E) (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    lineDerivCLM ℝ v (sliceLeft y Φ) =
      sliceLeft y (lineDerivCLM ℝ (v, 0) Φ) := by
  ext x
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun z : E ↦ Φ (z, y)) x v =
    (lineDerivCLM ℝ (v, 0) Φ) (x, y)
  rw [lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun z : E ↦ Φ (z, y)) x v =
    lineDeriv ℝ (fun p : E × F ↦ Φ p) (x, y) (v, 0)
  have hΦ : DifferentiableAt ℝ (fun p : E × F ↦ Φ p) (x, y) :=
    (Φ.contDiff.differentiable (by simp)).differentiableAt
  have hslice : DifferentiableAt ℝ (fun z : E ↦ Φ (z, y)) x :=
    hΦ.comp x (hasFDerivAt_prodMk_left x y).differentiableAt
  rw [hslice.lineDeriv_eq_fderiv, hΦ.lineDeriv_eq_fderiv]
  change (fderiv ℝ (⇑Φ ∘ fun z : E ↦ (z, y)) x) v =
    (fderiv ℝ (fun p : E × F ↦ Φ p) (x, y)) (v, 0)
  rw [(hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)).fderiv]
  simp

end TestFunction
