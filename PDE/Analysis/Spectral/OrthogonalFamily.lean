/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Expansions in orthogonal families

Let `v` be a family in a real inner product space with `⟪v i, v j⟫ = c i` for `i = j` and `0`
otherwise, where every `c i` is positive. Dividing each `v i` by its norm `√(c i)` gives an
orthonormal family, and a Hilbert basis when the space is complete and the span of `v` is dense.
Every element `f` is then the sum of its expansion `∑ (⟪v i, f⟫ / c i) • v i` and satisfies
Parseval's identity `‖f‖² = ∑ ⟪v i, f⟫² / c i`. Conversely, the coefficients of any convergent
expansion `f = ∑ a i • v i` are `a i = ⟪v i, f⟫ / c i`, and an element orthogonal to every member
of a family with dense span is zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Spectral

open Set
open scoped RealInnerProductSpace

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : ι → E}

/-- An element orthogonal to every member of a family with dense span is zero. -/
theorem eq_zero_of_forall_inner_eq_zero_of_dense
    (hv : (Submodule.span ℝ (range v)).topologicalClosure = ⊤) {f : E}
    (h : ∀ i, ⟪v i, f⟫ = 0) : f = 0 := by
  have hle : Submodule.span ℝ (range v) ≤ (ℝ ∙ f)ᗮ :=
    Submodule.span_le.mpr <| range_subset_iff.mpr fun i ↦
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (h i)
  exact (Submodule.dense_iff_topologicalClosure_eq_top.mpr hv).eq_zero_of_inner_right ℝ
    fun w hw ↦ Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hw)

variable [DecidableEq ι] {c : ι → ℝ}

/-- An orthogonal family with positive squared norms is orthonormal after division by the
norms. -/
theorem orthonormal_inv_sqrt_smul (hc : ∀ i, 0 < c i)
    (hv : ∀ i j, ⟪v i, v j⟫ = if i = j then c i else 0) :
    Orthonormal ℝ fun i ↦ (Real.sqrt (c i))⁻¹ • v i := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [real_inner_smul_left, real_inner_smul_right, hv]
  split_ifs with h
  · subst h
    have hs : Real.sqrt (c i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hc i)
    have h2 : Real.sqrt (c i) ^ 2 = c i := Real.sq_sqrt (hc i).le
    field_simp
    linarith
  · simp

/-- The coefficients of a convergent expansion in an orthogonal family are determined by the
inner products: if `f = ∑ a i • v i`, then `⟪v j, f⟫ = a j * c j`. -/
theorem inner_eq_mul_of_hasSum_orthogonal
    (hv : ∀ i j, ⟪v i, v j⟫ = if i = j then c i else 0) {a : ι → ℝ} {f : E}
    (hf : HasSum (fun i ↦ a i • v i) f) (j : ι) : ⟪v j, f⟫ = a j * c j := by
  have h := hf.mapL (innerSL ℝ (v j))
  simp only [innerSL_apply_apply, real_inner_smul_right, hv] at h
  refine h.unique ?_
  convert hasSum_ite_eq j (a j * c j) using 1
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

variable [CompleteSpace E]

/-- The normalized Hilbert basis of an orthogonal family with positive squared norms `c i` and
dense span. -/
def hilbertBasisOfOrthogonal (hc : ∀ i, 0 < c i)
    (hv : ∀ i j, ⟪v i, v j⟫ = if i = j then c i else 0)
    (hd : (Submodule.span ℝ (range v)).topologicalClosure = ⊤) : HilbertBasis ι ℝ E :=
  HilbertBasis.mk (orthonormal_inv_sqrt_smul hc hv) <| by
    rw [← hd]
    refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    have hs : Real.sqrt (c i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hc i)
    have hvi : v i = Real.sqrt (c i) • (Real.sqrt (c i))⁻¹ • v i := by
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    rw [hvi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The elements of the normalized Hilbert basis. -/
@[simp]
theorem hilbertBasisOfOrthogonal_apply (hc : ∀ i, 0 < c i)
    (hv : ∀ i j, ⟪v i, v j⟫ = if i = j then c i else 0)
    (hd : (Submodule.span ℝ (range v)).topologicalClosure = ⊤) (i : ι) :
    hilbertBasisOfOrthogonal hc hv hd i = (Real.sqrt (c i))⁻¹ • v i := by
  rw [hilbertBasisOfOrthogonal, HilbertBasis.coe_mk]

/-- Every element is the sum of its orthogonal expansion `∑ (⟪v i, f⟫ / c i) • v i`. -/
theorem hasSum_inner_div_smul_of_orthogonal (hc : ∀ i, 0 < c i)
    (hv : ∀ i j, ⟪v i, v j⟫ = if i = j then c i else 0)
    (hd : (Submodule.span ℝ (range v)).topologicalClosure = ⊤) (f : E) :
    HasSum (fun i ↦ (⟪v i, f⟫ / c i) • v i) f := by
  convert (hilbertBasisOfOrthogonal hc hv hd).hasSum_repr f using 1
  funext i
  rw [HilbertBasis.repr_apply_apply, hilbertBasisOfOrthogonal_apply, real_inner_smul_left,
    smul_smul]
  congr 1
  have hs : Real.sqrt (c i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hc i)
  have h2 : Real.sqrt (c i) ^ 2 = c i := Real.sq_sqrt (hc i).le
  field_simp
  rw [h2, mul_div_cancel_right₀ _ (hc i).ne']

/-- Parseval's identity for an orthogonal family with dense span:
`‖f‖² = ∑ ⟪v i, f⟫² / c i`. -/
theorem hasSum_inner_sq_div_of_orthogonal (hc : ∀ i, 0 < c i)
    (hv : ∀ i j, ⟪v i, v j⟫ = if i = j then c i else 0)
    (hd : (Submodule.span ℝ (range v)).topologicalClosure = ⊤) (f : E) :
    HasSum (fun i ↦ ⟪v i, f⟫ ^ 2 / c i) (‖f‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq]
  convert (hilbertBasisOfOrthogonal hc hv hd).hasSum_inner_mul_inner f f using 1
  funext i
  rw [hilbertBasisOfOrthogonal_apply, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm f]
  have hs : Real.sqrt (c i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hc i)
  have h2 : Real.sqrt (c i) ^ 2 = c i := Real.sq_sqrt (hc i).le
  field_simp
  rw [h2, mul_div_cancel_right₀ _ (hc i).ne']

end PDE.Analysis.Spectral
