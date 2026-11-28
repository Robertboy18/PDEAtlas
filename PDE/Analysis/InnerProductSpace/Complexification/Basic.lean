/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The complexification of a real inner product space

For a real inner product space `H`, the product `H × H` carries the complex structure
`J (x, y) = (-y, x)`. Writing the pair `(x, y)` as `x + i y`, complex scalars act by
`(a + b i) (x + i y) = (a x - b y) + i (a y + b x)` and the inner product is

```text
⟪x + i y, x' + i y'⟫ = ⟪x, x'⟫ + ⟪y, y'⟫ + i (⟪x, y'⟫ - ⟪y, x'⟫).
```

This makes `Complexification H` a complex inner product space with
`‖x + i y‖² = ‖x‖² + ‖y‖²`. Its real coordinates identify it isometrically with the `L²`
product `WithLp 2 (H × H)`, so the complexification of a complete space is complete, and the
complexification of a finite-dimensional space has complex dimension `dim H`. The
inclusion `x ↦ x + i 0` is a real linear isometry, and conjugation `x + i y ↦ x - i y` is a
conjugate-linear isometric involution.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace PDE.Analysis

/-- The complexification of a real inner product space `H`. The pair `(x, y)` stands for
`x + i y`, and multiplication by `i` is the complex structure `J (x, y) = (-y, x)`. The type
only uses `H × H`; the instance arguments say that it is meant for inner product spaces. -/
@[nolint unusedArguments]
def Complexification (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] := H × H

namespace Complexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The vector `x + i y` of the complexification. -/
def mk (x y : H) : Complexification H := (x, y)

/-- The real part `x` of `x + i y`. -/
def re (z : Complexification H) : H := Prod.fst (α := H) (β := H) z

/-- The imaginary part `y` of `x + i y`. -/
def im (z : Complexification H) : H := Prod.snd (α := H) (β := H) z

/-- The real part of `mk x y` is `x`. -/
@[simp]
theorem re_mk (x y : H) : (mk x y).re = x := rfl

/-- The imaginary part of `mk x y` is `y`. -/
@[simp]
theorem im_mk (x y : H) : (mk x y).im = y := rfl

/-- Every vector `z` is `mk` of its real and imaginary parts: `mk z.re z.im = z`. -/
@[simp]
theorem mk_re_im (z : Complexification H) : mk z.re z.im = z := rfl

/-- Two vectors of the complexification agree when their real and imaginary parts agree. -/
@[ext]
theorem ext {z w : Complexification H} (hre : z.re = w.re) (him : z.im = w.im) : z = w :=
  Prod.ext hre him

/-- `Complexification H` is an additive commutative group, with the componentwise operations of
`H × H`. -/
instance : AddCommGroup (Complexification H) := inferInstanceAs (AddCommGroup (H × H))

/-- The real part of the zero vector of `Complexification H` is `0`. -/
@[simp]
theorem re_zero : (0 : Complexification H).re = 0 := rfl

/-- The imaginary part of the zero vector of `Complexification H` is `0`. -/
@[simp]
theorem im_zero : (0 : Complexification H).im = 0 := rfl

/-- The real part of `z + w` is `z.re + w.re`. -/
@[simp]
theorem re_add (z w : Complexification H) : (z + w).re = z.re + w.re := rfl

/-- The imaginary part of `z + w` is `z.im + w.im`. -/
@[simp]
theorem im_add (z w : Complexification H) : (z + w).im = z.im + w.im := rfl

/-- The real part of `-z` is `-z.re`. -/
@[simp]
theorem re_neg (z : Complexification H) : (-z).re = -z.re := rfl

/-- The imaginary part of `-z` is `-z.im`. -/
@[simp]
theorem im_neg (z : Complexification H) : (-z).im = -z.im := rfl

/-- The real part of `z - w` is `z.re - w.re`. -/
@[simp]
theorem re_sub (z w : Complexification H) : (z - w).re = z.re - w.re := rfl

/-- The imaginary part of `z - w` is `z.im - w.im`. -/
@[simp]
theorem im_sub (z w : Complexification H) : (z - w).im = z.im - w.im := rfl

/-- Complex scalars act by `(a + b i) (x + i y) = (a x - b y) + i (a y + b x)`. -/
instance : SMul ℂ (Complexification H) where
  smul c z := mk (c.re • z.re - c.im • z.im) (c.re • z.im + c.im • z.re)

/-- For a complex scalar `c`, the real part of `c • z` is `c.re • z.re - c.im • z.im`. -/
@[simp]
theorem re_smul (c : ℂ) (z : Complexification H) : (c • z).re = c.re • z.re - c.im • z.im :=
  rfl

/-- For a complex scalar `c`, the imaginary part of `c • z` is `c.re • z.im + c.im • z.re`. -/
@[simp]
theorem im_smul (c : ℂ) (z : Complexification H) : (c • z).im = c.re • z.im + c.im • z.re :=
  rfl

/-- `Complexification H` is a complex vector space under the scalar action
`(a + b i) (x + i y) = (a x - b y) + i (a y + b x)`. -/
instance : Module ℂ (Complexification H) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by ext <;> simp <;> module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp <;> module
  add_smul c d z := by ext <;> simp <;> module
  zero_smul z := by ext <;> simp

/-- Real scalars act on the real part. -/
@[simp]
theorem re_real_smul (r : ℝ) (z : Complexification H) : (r • z).re = r • z.re := by
  rw [← Complex.coe_smul, re_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

/-- Real scalars act on the imaginary part. -/
@[simp]
theorem im_real_smul (r : ℝ) (z : Complexification H) : (r • z).im = r • z.im := by
  rw [← Complex.coe_smul, im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-- Multiplication by `i` is the complex structure `J (x, y) = (-y, x)`. -/
theorem I_smul (z : Complexification H) : Complex.I • z = mk (-z.im) z.re := by
  ext <;> simp

/-- The inner product `⟪x, x'⟫ + ⟪y, y'⟫ + i (⟪x, y'⟫ - ⟪y, x'⟫)` of `x + i y` and
`x' + i y'` satisfies the axioms of a complex inner product. -/
@[instance_reducible]
def innerProductCore : InnerProductSpace.Core ℂ (Complexification H) where
  inner z w := ⟨⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ, ⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ⟩
  conj_inner_symm z w := by
    apply Complex.ext <;> simp [real_inner_comm]
  re_inner_nonneg z := add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left z w u := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring
  smul_left z w c := by
    apply Complex.ext <;> simp [inner_add_left, inner_sub_left, real_inner_smul_left] <;> ring
  definite z hz := by
    have h := congrArg Complex.re hz
    simp only [Complex.zero_re] at h
    have hre : ⟪z.re, z.re⟫_ℝ = 0 := le_antisymm (by
      linarith [real_inner_self_nonneg (x := z.im)]) real_inner_self_nonneg
    have him : ⟪z.im, z.im⟫_ℝ = 0 := le_antisymm (by
      linarith [real_inner_self_nonneg (x := z.re)]) real_inner_self_nonneg
    ext
    · exact inner_self_eq_zero.mp hre
    · exact inner_self_eq_zero.mp him

/-- `Complexification H` is a normed additive commutative group, with the norm induced by the
inner product of `innerProductCore`. -/
instance : NormedAddCommGroup (Complexification H) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ innerProductCore

/-- `Complexification H` is a complex inner product space, with the inner product of
`innerProductCore`. -/
instance : InnerProductSpace ℂ (Complexification H) :=
  InnerProductSpace.ofCore innerProductCore.toCore

/-- The inner product `⟪z, w⟫_ℂ` is the complex number with real part
`⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ` and imaginary part `⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ`. -/
theorem inner_def (z w : Complexification H) :
    ⟪z, w⟫_ℂ = ⟨⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ, ⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ⟩ :=
  rfl

/-- The real part of `⟪z, w⟫_ℂ` is `⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ`. -/
@[simp]
theorem re_inner (z w : Complexification H) :
    (⟪z, w⟫_ℂ).re = ⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ :=
  rfl

/-- The imaginary part of `⟪z, w⟫_ℂ` is `⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ`. -/
@[simp]
theorem im_inner (z w : Complexification H) :
    (⟪z, w⟫_ℂ).im = ⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ :=
  rfl

/-- The squared norm of `x + i y` is `‖x‖² + ‖y‖²`. -/
theorem norm_sq_eq (z : Complexification H) : ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex, re_inner, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

/-- The norm of `z` is `√(‖z.re‖ ^ 2 + ‖z.im‖ ^ 2)`. -/
theorem norm_eq (z : Complexification H) : ‖z‖ = √(‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) := by
  rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg z)]

/-- The norm of `mk x y` is `√(‖x‖ ^ 2 + ‖y‖ ^ 2)`. -/
@[simp]
theorem norm_mk (x y : H) : ‖mk x y‖ = √(‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  norm_eq (mk x y)

/-- The norm of the real part `z.re` is at most the norm of `z`. -/
theorem norm_re_le (z : Complexification H) : ‖z.re‖ ≤ ‖z‖ := by
  rw [norm_eq]
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

/-- The norm of the imaginary part `z.im` is at most the norm of `z`. -/
theorem norm_im_le (z : Complexification H) : ‖z.im‖ ≤ ‖z‖ := by
  rw [norm_eq]
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))

/-- The inclusion `x ↦ x + i 0`. -/
def ofReal (x : H) : Complexification H := mk x 0

/-- The real part of `ofReal x` is `x`. -/
@[simp]
theorem re_ofReal (x : H) : (ofReal x).re = x := rfl

/-- The imaginary part of `ofReal x` is `0`. -/
@[simp]
theorem im_ofReal (x : H) : (ofReal x).im = 0 := rfl

/-- The inclusion preserves the norm: `‖ofReal x‖ = ‖x‖`. -/
@[simp]
theorem norm_ofReal (x : H) : ‖ofReal x‖ = ‖x‖ := by
  simp [ofReal, Real.sqrt_sq (norm_nonneg x)]

/-- The inclusion `ofReal : H → Complexification H` is injective. -/
theorem ofReal_injective : Function.Injective (ofReal : H → Complexification H) :=
  fun _ _ h ↦ congrArg re h

/-- Every vector is `x + i y` for its real and imaginary parts. -/
theorem ofReal_re_add_I_smul_ofReal_im (z : Complexification H) :
    ofReal z.re + Complex.I • ofReal z.im = z := by
  ext <;> simp

/-- The inclusion `x ↦ x + i 0` as a real linear isometry. -/
def ofRealLI : H →ₗᵢ[ℝ] Complexification H where
  toFun := ofReal
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  norm_map' := norm_ofReal

/-- The inclusion `x ↦ x + i 0` as a continuous real linear map. -/
def ofRealCLM : H →L[ℝ] Complexification H := ofRealLI.toContinuousLinearMap

/-- The linear isometry `ofRealLI` sends `x` to `ofReal x`. -/
@[simp]
theorem ofRealLI_apply (x : H) : ofRealLI x = ofReal x := rfl

/-- The continuous linear map `ofRealCLM` sends `x` to `ofReal x`. -/
@[simp]
theorem ofRealCLM_apply (x : H) : ofRealCLM x = ofReal x := rfl

/-- The inclusion sends the zero vector of `H` to the zero vector of `Complexification H`. -/
@[simp]
theorem ofReal_zero : ofReal (0 : H) = 0 := rfl

/-- The inclusion preserves sums: `ofReal (x + y) = ofReal x + ofReal y`. -/
@[simp]
theorem ofReal_add (x y : H) : ofReal (x + y) = ofReal x + ofReal y := ofRealLI.map_add x y

/-- The inclusion preserves negation: `ofReal (-x) = -ofReal x`. -/
@[simp]
theorem ofReal_neg (x : H) : ofReal (-x) = -ofReal x := ofRealLI.map_neg x

/-- The inclusion preserves differences: `ofReal (x - y) = ofReal x - ofReal y`. -/
@[simp]
theorem ofReal_sub (x y : H) : ofReal (x - y) = ofReal x - ofReal y := ofRealLI.map_sub x y

/-- The inclusion commutes with real scalars: `ofReal (r • x) = r • ofReal x`. -/
@[simp]
theorem ofReal_smul (r : ℝ) (x : H) : ofReal (r • x) = r • ofReal x := by
  ext <;> simp

/-- The real part as a continuous real linear map. -/
def reCLM : Complexification H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := re_add
      map_smul' r z := re_real_smul r z } 1 fun z ↦ by simpa using norm_re_le z

/-- The imaginary part as a continuous real linear map. -/
def imCLM : Complexification H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := im
      map_add' := im_add
      map_smul' r z := im_real_smul r z } 1 fun z ↦ by simpa using norm_im_le z

/-- The map `reCLM` sends `z` to its real part `z.re`. -/
@[simp]
theorem reCLM_apply (z : Complexification H) : reCLM z = z.re := rfl

/-- The map `imCLM` sends `z` to its imaginary part `z.im`. -/
@[simp]
theorem imCLM_apply (z : Complexification H) : imCLM z = z.im := rfl

/-- The real coordinates `(re z, im z)` identify the complexification with the `L²` product
as a real linear isometric equivalence. -/
def equivProdL2 : Complexification H ≃ₗᵢ[ℝ] WithLp 2 (H × H) where
  toFun z := WithLp.toLp 2 (z.re, z.im)
  invFun p := mk p.fst p.snd
  left_inv z := rfl
  right_inv p := rfl
  map_add' z w := rfl
  map_smul' r z := by
    change WithLp.toLp 2 ((r • z).re, (r • z).im) = r • WithLp.toLp 2 (z.re, z.im)
    rw [← WithLp.toLp_smul, re_real_smul, im_real_smul, Prod.smul_mk]
  norm_map' z := by
    rw [WithLp.prod_norm_eq_of_L2, norm_eq]
    rfl

/-- The equivalence `equivProdL2` sends `z` to the pair `WithLp.toLp 2 (z.re, z.im)`. -/
@[simp]
theorem equivProdL2_apply (z : Complexification H) :
    equivProdL2 z = WithLp.toLp 2 (z.re, z.im) := rfl

/-- If `H` is complete, then `Complexification H` is a complete space. -/
instance [CompleteSpace H] : CompleteSpace (Complexification H) :=
  equivProdL2.toIsometryEquiv.completeSpace

/-- If `H` is finite-dimensional over `ℝ`, then `Complexification H` is finite-dimensional over
`ℂ`. -/
instance [FiniteDimensional ℝ H] : FiniteDimensional ℂ (Complexification H) :=
  have : FiniteDimensional ℝ (Complexification H) :=
    LinearEquiv.finiteDimensional equivProdL2.toLinearEquiv.symm
  Module.Finite.of_restrictScalars_finite ℝ ℂ _

/-- The complex dimension of the complexification is the real dimension of `H`. -/
theorem finrank_complexification [FiniteDimensional ℝ H] :
    Module.finrank ℂ (Complexification H) = Module.finrank ℝ H := by
  have h := finrank_real_of_complex (Complexification H)
  rw [equivProdL2.toLinearEquiv.finrank_eq, WithLp.linearEquiv 2 ℝ (H × H) |>.finrank_eq,
    Module.finrank_prod, ← two_mul] at h
  omega

/-- Complex conjugation `x + i y ↦ x - i y` as a conjugate-linear isometric equivalence. -/
def conjLIE : Complexification H ≃ₗᵢ⋆[ℂ] Complexification H where
  toFun z := mk z.re (-z.im)
  invFun z := mk z.re (-z.im)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp [add_comm]
  map_smul' c z := by ext <;> simp [add_comm]
  norm_map' z := by simp [norm_eq]

/-- The real part of `conjLIE z` is `z.re`. -/
@[simp]
theorem re_conjLIE (z : Complexification H) : (conjLIE z).re = z.re := rfl

/-- The imaginary part of `conjLIE z` is `-z.im`. -/
@[simp]
theorem im_conjLIE (z : Complexification H) : (conjLIE z).im = -z.im := rfl

/-- Conjugating twice gives the original vector: `conjLIE (conjLIE z) = z`. -/
@[simp]
theorem conjLIE_conjLIE (z : Complexification H) : conjLIE (conjLIE z) = z := by
  ext <;> simp

/-- The inverse of the conjugation `conjLIE` is `conjLIE` itself. -/
@[simp]
theorem conjLIE_symm : (conjLIE : Complexification H ≃ₗᵢ⋆[ℂ] Complexification H).symm =
    conjLIE := rfl

/-- Conjugation fixes the image of the inclusion: `conjLIE (ofReal x) = ofReal x`. -/
@[simp]
theorem conjLIE_ofReal (x : H) : conjLIE (ofReal x) = ofReal x := by
  ext <;> simp

/-- A vector fixed by conjugation is real. -/
theorem eq_ofReal_re_of_conjLIE_eq {z : Complexification H} (hz : conjLIE z = z) :
    z = ofReal z.re := by
  have him : -z.im = z.im := congrArg im hz
  have h2 : (2 : ℝ) • z.im = 0 := by
    rw [two_smul]
    nth_rw 1 [← him]
    exact neg_add_cancel z.im
  ext
  · rfl
  · exact ((smul_eq_zero.mp h2).resolve_left two_ne_zero).trans (im_ofReal z.re).symm

end Complexification

end PDE.Analysis
