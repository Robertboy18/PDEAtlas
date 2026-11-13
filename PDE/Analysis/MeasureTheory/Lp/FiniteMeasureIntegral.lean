/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Integrating a uniformly bounded family of L2 functions

A jointly measurable real family, uniformly bounded in spatial L2, has a
pointwise integral in L2 over any finite parameter measure. Its norm is at most
the mass of that measure times the uniform bound. The proof uses square
integrability on the product, Cauchy–Schwarz in the parameter, and Fubini.

The statement concerns scalar representatives and gives both membership and the
norm bound.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Filter
open scoped ENNReal

/-- Integrating a jointly measurable, uniformly L2-bounded real family over a
finite parameter measure produces an L2 function, with norm bounded by the
parameter mass times the common bound. The spatial measure need only be
s-finite. -/
theorem memLp_integral_of_uniform_bound
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (η : Measure T) [IsFiniteMeasure η] (ν : Measure X) [SFinite ν]
    (F : T × X → ℝ) (hF : AEStronglyMeasurable F (η.prod ν))
    {B : ℝ} (hB : 0 ≤ B)
    (hmem : ∀ t, MemLp (fun x ↦ F (t, x)) 2 ν)
    (hbound : ∀ t, lpNorm (fun x ↦ F (t, x)) 2 ν ≤ B) :
    MemLp (fun x ↦ ∫ t, F (t, x) ∂η) 2 ν ∧
      lpNorm (fun x ↦ ∫ t, F (t, x) ∂η) 2 ν ≤ η.real Set.univ * B := by
  have hsq : Integrable (fun p ↦ F p ^ 2) (η.prod ν) := by
    apply (integrable_prod_iff (hF.pow 2)).2
    refine ⟨Eventually.of_forall (fun t ↦ (hmem t).integrable_sq), ?_⟩
    apply (integrable_const (B ^ 2)).mono' ((hF.pow 2).norm.integral_prod_right')
    filter_upwards with t
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _),
      (hmem t).integral_sq_eq_lpNorm_sq] using
        pow_le_pow_left₀ lpNorm_nonneg (hbound t) 2
  let I : X → ℝ := fun x ↦ ∫ t, F (t, x) ∂η
  let G : X → ℝ := fun x ↦ ∫ t, F (t, x) ^ 2 ∂η
  have hI : AEStronglyMeasurable I ν := hF.prod_swap.integral_prod_right'
  have hG : Integrable G ν := hsq.integral_prod_right
  have hdom : ∀ᵐ x ∂ν, I x ^ 2 ≤ η.real Set.univ * G x := by
    filter_upwards [hsq.prod_left_ae, hF.prodMk_right] with x hx hxm
    have ht : MemLp (fun t ↦ F (t, x)) 2 η :=
      (memLp_two_iff_integrable_sq hxm).2 hx
    have h1 : MemLp (fun _ : T ↦ (1 : ℝ)) 2 η := memLp_const 1
    have hcs : |I x| ≤
        lpNorm (fun t ↦ F (t, x)) 2 η * lpNorm (fun _ : T ↦ (1 : ℝ)) 2 η := by
      simpa only [I, mul_one] using
        abs_integral_mul_le_lpNorm_two_mul_lpNorm_two ht h1
    calc
      I x ^ 2 = |I x| ^ 2 := (sq_abs _).symm
      _ ≤ (lpNorm (fun t ↦ F (t, x)) 2 η *
          lpNorm (fun _ : T ↦ (1 : ℝ)) 2 η) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = η.real Set.univ * G x := by
        rw [mul_pow, ← ht.integral_sq_eq_lpNorm_sq, ← h1.integral_sq_eq_lpNorm_sq]
        simp only [one_pow, integral_const, smul_eq_mul, mul_one, G]
        exact mul_comm _ _
  have hIint : Integrable (fun x ↦ I x ^ 2) ν := by
    apply (hG.const_mul (η.real Set.univ)).mono' (hI.pow 2)
    filter_upwards [hdom] with x hx
    simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using hx
  have hImem : MemLp I 2 ν := (memLp_two_iff_integrable_sq hI).2 hIint
  have hmass : 0 ≤ η.real Set.univ := ENNReal.toReal_nonneg
  have hGbound : (∫ x, G x ∂ν) ≤ η.real Set.univ * B ^ 2 := by
    calc
      (∫ x, G x ∂ν) = ∫ t, ∫ x, F (t, x) ^ 2 ∂ν ∂η :=
        (integral_integral_swap hsq).symm
      _ ≤ ∫ _ : T, B ^ 2 ∂η := by
        apply integral_mono_ae hsq.integral_prod_left (integrable_const _)
        filter_upwards with t
        rw [(hmem t).integral_sq_eq_lpNorm_sq]
        exact pow_le_pow_left₀ lpNorm_nonneg (hbound t) 2
      _ = η.real Set.univ * B ^ 2 := by rw [integral_const, smul_eq_mul]
  refine ⟨hImem, ?_⟩
  have hnormsq : lpNorm I 2 ν ^ 2 ≤ (η.real Set.univ * B) ^ 2 := by
    calc
      lpNorm I 2 ν ^ 2 = ∫ x, I x ^ 2 ∂ν := hImem.integral_sq_eq_lpNorm_sq.symm
      _ ≤ ∫ x, η.real Set.univ * G x ∂ν :=
        integral_mono_ae hIint (hG.const_mul _) hdom
      _ = η.real Set.univ * ∫ x, G x ∂ν := integral_const_mul _ _
      _ ≤ η.real Set.univ * (η.real Set.univ * B ^ 2) :=
        mul_le_mul_of_nonneg_left hGbound hmass
      _ = (η.real Set.univ * B) ^ 2 := by ring
  exact (sq_le_sq₀ lpNorm_nonneg (mul_nonneg hmass hB)).1 hnormsq

end MeasureTheory
