/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Operator.Schur
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Schur assembly for matrices of operators

Each entry may act between different Banach spaces. A nonnegative scalar
matrix bounds the entry norms. Its row and column masses control the operator
on the Hilbert sums of the source and target spaces.

The operator is constructed from the convergent row series. Square
summability of the output follows from the scalar Schur estimate on counting
measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace lp

private theorem memLp_count_two_iff {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (f : ι → ℝ) :
    MemLp f 2 Measure.count ↔ Memℓp f 2 := by
  rw [memLp_two_iff_integrable_sq_norm
    (measurable_of_countable f).aestronglyMeasurable,
    integrable_count_iff, memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_pow, norm_norm]

private theorem lpNorm_count_two_eq_norm {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (f : lp (fun _ : ι ↦ ℝ) 2) :
    lpNorm f 2 Measure.count = ‖f‖ := by
  have hf : MemLp f 2 Measure.count := (memLp_count_two_iff f).2 (lp.memℓp f)
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
    hf.aestronglyMeasurable,
    lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]
  rw [integral_countable hf.norm.integrable_sq]
  simp only [count_real_singleton, one_smul]

private theorem lintegral_count_norm_le {ι : Type*}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {w : ι → ℝ} {A : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (hA : ∑' i, w i ≤ A) :
    (∫⁻ i, ENNReal.ofReal ‖w i‖ ∂Measure.count) ≤ ENNReal.ofReal A := by
  have hnorm (i : ι) : ‖w i‖ = w i := Real.norm_of_nonneg (hw i)
  simp only [hnorm, lintegral_count]
  rw [← ENNReal.ofReal_tsum_of_nonneg hw hs]
  exact ENNReal.ofReal_le_ofReal hA

/-- A matrix of continuous linear maps acts on the Hilbert sums of its
Banach-space fibers when a nonnegative majorant has summable rows and columns.
The norm is at most the square root of the product of their uniform masses.
Every output coordinate is the sum of the matrix row. -/
theorem exists_blockMatrix_of_schur
    {ι κ : Type*} [Countable ι] [Countable κ]
    {E : κ → Type*} {F : ι → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, CompleteSpace (F i)]
    (B : ∀ i j, E j →L[ℝ] F i) (w : ι → κ → ℝ) {A D : ℝ}
    (hw : ∀ i j, 0 ≤ w i j) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hrow : ∀ i, Summable (w i) ∧ ∑' j, w i j ≤ A)
    (hcolumn : ∀ j, Summable (fun i ↦ w i j) ∧ ∑' i, w i j ≤ D)
    (hB : ∀ i j, ‖B i j‖ ≤ w i j) :
    ∃ T : lp E 2 →L[ℝ] lp F 2,
      ‖T‖ ≤ √(A * D) ∧
        ∀ x i, HasSum (fun j ↦ B i j (x j)) (T x i) := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSpace κ := ⊤
  have hpoint (x : lp E 2) (i : ι) (j : κ) :
      ‖B i j (x j)‖ ≤ w i j * ‖x j‖ :=
    (B i j).le_of_opNorm_le (hB i j) (x j)
  have hscalar (x : lp E 2) (i : ι) :
      Summable (fun j ↦ w i j * ‖x j‖) :=
    ((hrow i).1.mul_right ‖x‖).of_norm_bounded fun j ↦ by
      rw [Real.norm_of_nonneg (mul_nonneg (hw i j) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm two_ne_zero x j) (hw i j)
  have hseries (x : lp E 2) (i : ι) : Summable (fun j ↦ B i j (x j)) :=
    (hscalar x i).of_norm_bounded (hpoint x i)
  have hK : AEStronglyMeasurable (fun z : ι × κ ↦ w z.1 z.2)
      ((Measure.count : Measure ι).prod (Measure.count : Measure κ)) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hrow' : ∀ᵐ i ∂(Measure.count : Measure ι),
      (∫⁻ j, ENNReal.ofReal ‖w i j‖ ∂(Measure.count : Measure κ)) ≤
        ENNReal.ofReal A :=
    Filter.Eventually.of_forall fun i ↦
      lintegral_count_norm_le (hw i) (hrow i).1 (hrow i).2
  have hcolumn' : ∀ᵐ j ∂(Measure.count : Measure κ),
      (∫⁻ i, ENNReal.ofReal ‖w i j‖ ∂(Measure.count : Measure ι)) ≤
        ENNReal.ofReal D :=
    Filter.Eventually.of_forall fun j ↦
      lintegral_count_norm_le (fun i ↦ hw i j) (hcolumn j).1 (hcolumn j).2
  have hout (x : lp E 2) :
      ∃ hx : Memℓp (fun i ↦ ∑' j, B i j (x j)) 2,
        ‖(⟨fun i ↦ ∑' j, B i j (x j), hx⟩ : lp F 2)‖ ≤
          √(A * D) * ‖x‖ := by
    let g : ι → ℝ := fun i ↦ ∫ j, w i j • ‖x j‖ ∂Measure.count
    have hx : MemLp (fun j ↦ ‖x j‖) 2 Measure.count :=
      (memLp_count_two_iff _).2 (lp.memℓp x).norm
    have hg : MemLp g 2 Measure.count :=
      MemLp.integral_kernel_smul_of_schur hK hx hA hD hrow' hcolumn'
    have hsum (i : ι) : g i = ∑' j, w i j * ‖x j‖ := by
      have hi : Integrable (fun j ↦ w i j * ‖x j‖) Measure.count :=
        integrable_count_iff.mpr <| by
          simpa only [Real.norm_of_nonneg (mul_nonneg (hw i _) (norm_nonneg _))] using hscalar x i
      change (∫ j, w i j * ‖x j‖ ∂Measure.count) = _
      rw [integral_countable hi]
      simp only [count_real_singleton, one_smul]
    have hdom (i : ι) : ‖∑' j, B i j (x j)‖ ≤ g i :=
      (tsum_of_norm_bounded (hscalar x i).hasSum (hpoint x i)).trans_eq (hsum i).symm
    have hg' : Memℓp g 2 := (memLp_count_two_iff g).1 hg
    refine ⟨hg'.mono hdom, ?_⟩
    let y : lp (fun _ : ι ↦ ℝ) 2 := ⟨g, hg'⟩
    calc
      ‖(⟨fun i ↦ ∑' j, B i j (x j), hg'.mono hdom⟩ : lp F 2)‖ ≤ ‖y‖ :=
        lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) fun i ↦
          (hdom i).trans (Real.le_norm_self (g i))
      _ = lpNorm g 2 Measure.count := (lpNorm_count_two_eq_norm y).symm
      _ ≤ √(A * D) * lpNorm (fun j ↦ ‖x j‖) 2 Measure.count :=
        lpNorm_integral_kernel_smul_le_of_schur hK hx hA hD hrow' hcolumn'
      _ = √(A * D) * ‖x‖ :=
        congrArg (√(A * D) * ·) ((lpNorm_count_two_eq_norm (lp.toNorm x)).trans lp.norm_toNorm)
  let T : lp E 2 →ₗ[ℝ] lp F 2 :=
    { toFun := fun x ↦ ⟨fun i ↦ ∑' j, B i j (x j), (hout x).choose⟩
      map_add' := fun x y ↦ lp.ext <| funext fun i ↦ by
        change (∑' j, B i j (x j + y j)) = (∑' j, B i j (x j)) + ∑' j, B i j (y j)
        simpa only [map_add] using (hseries x i).tsum_add (hseries y i)
      map_smul' := fun c x ↦ lp.ext <| funext fun i ↦ by
        change (∑' j, B i j (c • x j)) = c • ∑' j, B i j (x j)
        simpa only [map_smul] using (hseries x i).tsum_const_smul c }
  have hbound (x : lp E 2) : ‖T x‖ ≤ √(A * D) * ‖x‖ := (hout x).choose_spec
  exact ⟨T.mkContinuous (√(A * D)) hbound, T.mkContinuous_norm_le (Real.sqrt_nonneg _) hbound,
    fun x i ↦ (hseries x i).hasSum⟩

end lp
