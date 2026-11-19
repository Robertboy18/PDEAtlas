/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.MatrixSymbol.Multiplier
public import PDE.Analysis.Fourier.L1Reconstruction.Parametric

/-!
# Joint regularity of a matrix-symbol Fourier evolution

The polynomial bound consumes `m - 1` frequency moments, and either a spatial
or time derivative consumes one more. Thus moments through order `m` suffice
for a single jointly `C¹` inverse Fourier integral, including time zero.
The empty target dimension is handled directly.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators Matrix.Norms.L2Operator

namespace PDE.Analysis.Fourier

variable {n m : ℕ}

/-- Acting by the continuous matrix multiplier preserves strong measurability
of the frequency datum. -/
theorem aestronglyMeasurable_symbolMultiplier_apply
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    {g : ℝ^n → EuclideanSpace ℂ (Fin m)}
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun ξ ↦ symbolMultiplier A t ξ (g ξ)) volume :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (((continuous_symbolMultiplier A).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable.prodMk hg)

/-- Polynomial multiplier bounds produce integrable majorants for the value,
its first spatial moment, and its time derivative. -/
theorem exists_symbolEvolution_majorants
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    (g : Lp (EuclideanSpace ℂ (Fin m)) 1
      (volume : Measure (ℝ^n)))
    (hmom : ∀ k ≤ m, Integrable (fun ξ : ℝ^n ↦
      ‖ξ‖ ^ k * ‖g ξ‖)) (hmpos : 1 ≤ m) {T : ℝ} :
    ∃ b c : ℝ^n → ℝ,
      Integrable b ∧ Integrable (fun ξ ↦ ‖ξ‖ * b ξ) ∧ Integrable c ∧
        ∀ t : ℝ, |t| ≤ T → ∀ ξ,
          ‖symbolMultiplier A t ξ (g ξ)‖ ≤ b ξ ∧
          ‖symbolGenerator A ξ (symbolMultiplier A t ξ (g ξ))‖ ≤ c ξ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_symbolMultiplier_le A hA (T := T)
  let b (ξ : ℝ^n) :=
    C * (1 + ‖ξ‖ ^ (m - 1)) * ‖g ξ‖
  let L : ℝ := 2 * Real.pi * ∑ j, ‖A j‖
  have hL : 0 ≤ L := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)
  have hb : Integrable b := by
    convert ((L1.integrable_coeFn g).norm.add
      (hmom (m - 1) (Nat.sub_le m 1))).const_mul C using 1
    funext ξ
    dsimp only [b, Pi.add_apply]
    ring
  have hxb : Integrable (fun ξ ↦ ‖ξ‖ * b ξ) := by
    convert ((hmom 1 hmpos).add (hmom m le_rfl)).const_mul C using 1
    funext ξ
    dsimp only [b, Pi.add_apply]
    have hp : ‖ξ‖ ^ m = ‖ξ‖ ^ (m - 1) * ‖ξ‖ := by
      rw [← pow_succ, Nat.sub_add_cancel hmpos]
    rw [pow_one, hp]
    ring
  refine ⟨b, fun ξ ↦ L * (‖ξ‖ * b ξ), hb, hxb, hxb.const_mul L,
    fun t ht ξ ↦ ?_⟩
  have hvbound : ‖symbolMultiplier A t ξ (g ξ)‖ ≤ b ξ :=
    ((symbolMultiplier A t ξ).le_opNorm (g ξ)).trans
      (mul_le_mul_of_nonneg_right (hbound t ht ξ) (norm_nonneg _))
  refine ⟨hvbound, ?_⟩
  calc
    ‖symbolGenerator A ξ (symbolMultiplier A t ξ (g ξ))‖ ≤
        ‖symbolGenerator A ξ‖ * ‖symbolMultiplier A t ξ (g ξ)‖ :=
      (symbolGenerator A ξ).le_opNorm _
    _ ≤ (L * ‖ξ‖) * b ξ :=
      mul_le_mul (norm_symbolGenerator_le A ξ) hvbound (norm_nonneg _) (by positivity)
    _ = L * (‖ξ‖ * b ξ) := mul_assoc _ _ _


private theorem contDiff_one_symbolEvolution_of_pos
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    (g : Lp (EuclideanSpace ℂ (Fin m)) 1
      (volume : Measure (ℝ^n)))
    (hmom : ∀ k ≤ m, Integrable (fun ξ : ℝ^n ↦
      ‖ξ‖ ^ k * ‖g ξ‖)) (hmpos : 1 ≤ m) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ^n ↦
      𝓕⁻ (fun ξ ↦ symbolMultiplier A p.1 ξ (g ξ)) p.2) ∧
      ∀ p : ℝ × ℝ^n,
        Integrable (fun ξ ↦ inverseKernelDerivative ξ p (symbolMultiplier A p.1 ξ (g ξ))
          (symbolGenerator A ξ (symbolMultiplier A p.1 ξ (g ξ)))) ∧
          HasFDerivAt (fun q : ℝ × ℝ^n ↦
            𝓕⁻ (fun ξ ↦ symbolMultiplier A q.1 ξ (g ξ)) q.2)
            (∫ ξ, inverseKernelDerivative ξ p (symbolMultiplier A p.1 ξ (g ξ))
              (symbolGenerator A ξ (symbolMultiplier A p.1 ξ (g ξ)))) p := by
  let v (t : ℝ) (ξ : ℝ^n) :=
    symbolMultiplier A t ξ (g ξ)
  let d (t : ℝ) (ξ : ℝ^n) := symbolGenerator A ξ (v t ξ)
  have hv (t : ℝ) : AEStronglyMeasurable (v t) volume :=
    aestronglyMeasurable_symbolMultiplier_apply A t (Lp.aestronglyMeasurable g)
  have hd (t : ℝ) : AEStronglyMeasurable (d t) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((continuous_symbolGenerator A).aestronglyMeasurable.prodMk (hv t))
  have hder (ξ : ℝ^n) (t : ℝ) :
      HasDerivAt (fun u ↦ v u ξ) (d t ξ) t :=
    hasDerivAt_symbolMultiplier_apply A ξ (g ξ) t
  have hc (ξ : ℝ^n) : Continuous (fun t ↦ d t ξ) :=
    (symbolGenerator A ξ).continuous.comp
      (continuous_iff_continuousAt.mpr fun t ↦ (hder ξ t).continuousAt)
  have hb (T : ℝ) (_ : 0 ≤ T) :
      ∃ b c : ℝ^n → ℝ,
        Integrable b ∧ Integrable (fun ξ ↦ ‖ξ‖ * b ξ) ∧ Integrable c ∧
          ∀ t : ℝ, |t| ≤ T → ∀ ξ, ‖v t ξ‖ ≤ b ξ ∧ ‖d t ξ‖ ≤ c ξ :=
    exists_symbolEvolution_majorants A hA g hmom hmpos
  exact contDiff_one_fourierInv_family v d hv hd hder hc hb

/-- The matrix-symbol inverse Fourier integral has a continuous joint
derivative whenever the datum has the required finite frequency moments. -/
theorem contDiff_one_symbolEvolution
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    (g : Lp (EuclideanSpace ℂ (Fin m)) 1
      (volume : Measure (ℝ^n)))
    (hmom : ∀ k ≤ m, Integrable (fun ξ : ℝ^n ↦
      ‖ξ‖ ^ k * ‖g ξ‖)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ^n ↦
      𝓕⁻ (fun ξ ↦ symbolMultiplier A p.1 ξ (g ξ)) p.2) ∧
      ∀ p : ℝ × ℝ^n,
        Integrable (fun ξ ↦ inverseKernelDerivative ξ p (symbolMultiplier A p.1 ξ (g ξ))
          (symbolGenerator A ξ (symbolMultiplier A p.1 ξ (g ξ)))) ∧
          HasFDerivAt (fun q : ℝ × ℝ^n ↦
            𝓕⁻ (fun ξ ↦ symbolMultiplier A q.1 ξ (g ξ)) q.2)
            (∫ ξ, inverseKernelDerivative ξ p (symbolMultiplier A p.1 ξ (g ξ))
              (symbolGenerator A ξ (symbolMultiplier A p.1 ξ (g ξ)))) p := by
  by_cases hm : m = 0
  · subst m
    refine ⟨contDiff_of_subsingleton, fun p ↦ ?_⟩
    have hK : (fun ξ ↦ inverseKernelDerivative ξ p (symbolMultiplier A p.1 ξ (g ξ))
        (symbolGenerator A ξ (symbolMultiplier A p.1 ξ (g ξ)))) =
        fun _ : ℝ^n ↦
          (0 : (ℝ × ℝ^n) →L[ℝ] EuclideanSpace ℂ (Fin 0)) :=
      funext fun _ ↦ Subsingleton.elim _ _
    refine ⟨?_, ?_⟩
    · rw [hK]
      exact integrable_zero (ℝ^n)
        ((ℝ × ℝ^n) →L[ℝ] EuclideanSpace ℂ (Fin 0)) volume
    have hf : (fun q : ℝ × ℝ^n ↦
        𝓕⁻ (fun ξ ↦ symbolMultiplier A q.1 ξ (g ξ)) q.2) =
        fun _ ↦ (0 : EuclideanSpace ℂ (Fin 0)) :=
      funext fun _ ↦ Subsingleton.elim _ _
    have hd : (∫ ξ, inverseKernelDerivative ξ p (symbolMultiplier A p.1 ξ (g ξ))
        (symbolGenerator A ξ (symbolMultiplier A p.1 ξ (g ξ)))) =
        (0 : (ℝ × ℝ^n) →L[ℝ] EuclideanSpace ℂ (Fin 0)) :=
      Subsingleton.elim _ _
    rw [hf, hd]
    exact hasFDerivAt_const (𝕜 := ℝ) (0 : EuclideanSpace ℂ (Fin 0)) p
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  exact contDiff_one_symbolEvolution_of_pos A hA g hmom hmpos

end PDE.Analysis.Fourier
