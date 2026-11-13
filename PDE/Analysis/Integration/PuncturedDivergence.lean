/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Divergence integrals with isolated derivative exceptions

The box divergence theorem permits a countable exceptional set for differentiability.
A continuous compactly supported vector field therefore has zero integral divergence
when its divergence is integrable, even if it is not differentiable at isolated points.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory Set
open scoped BigOperators

/-- A continuous compactly supported field has zero integral divergence when its
classical derivative exists off a countable set and its divergence is integrable. -/
theorem integral_divergence_eq_zero_of_continuous_off_countable {n : ℕ}
    {F : ℝ^(n + 1) → ℝ^(n + 1)} {s : Set (ℝ^(n + 1))}
    (hF : Continuous F) (hcompact : HasCompactSupport F) (hs : s.Countable)
    (hdiff : ∀ x ∉ s, DifferentiableAt ℝ F x)
    (hint : Integrable (PDE.divergence F)) :
    (∫ x, PDE.divergence F x) = 0 := by
  let : Preorder (ℝ^(n + 1)) := Preorder.lift (fun x : ℝ^(n + 1) ↦ x.ofLp)
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  let a : ℝ^(n + 1) := WithLp.toLp 2 (fun _ ↦ -(R + 1))
  let b : ℝ^(n + 1) := WithLp.toLp 2 (fun _ ↦ R + 1)
  have hcoord (x : ℝ^(n + 1)) (hx : x ∈ tsupport F) (i : Fin (n + 1)) :
      |x i| ≤ R := (PiLp.norm_apply_le x i).trans (hbound x hx)
  have hsbox : tsupport F ⊆ Icc a b := by
    intro x hx
    constructor <;> intro i
    · have h := (abs_le.mp (hcoord x hx i)).1
      dsimp [a]
      linarith
    · have h := (abs_le.mp (hcoord x hx i)).2
      dsimp [b]
      linarith
  have hzero (x : ℝ^(n + 1)) (i : Fin (n + 1))
      (hx : x i = R + 1 ∨ x i = -(R + 1)) : F x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hb := hcoord x hmem i
    rcases hx with hx | hx
    · rw [hx, abs_of_pos (by linarith)] at hb
      linarith
    · rw [hx, abs_neg, abs_of_pos (by linarith)] at hb
      linarith
  let eL : ℝ^(n + 1) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    EuclideanSpace.equiv (Fin (n + 1)) ℝ
  have hmain := integral_divergence_of_hasFDerivAt_off_countable_of_equiv
    (n := n) (eL := eL) (he_ord := fun _ _ ↦ Iff.rfl)
    (he_vol := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1)))
    (f := fun i x ↦ F x i) (f' := fun i x ↦ fderiv ℝ (fun y ↦ F y i) x)
    (s := s) (hs := hs) (a := a) (b := b)
    (hle := fun _ ↦ by dsimp [a, b]; linarith)
    (Hc := fun i ↦ ((EuclideanSpace.proj i).continuous.comp hF).continuousOn)
    (Hd := by
      intro x hx i
      exact ((EuclideanSpace.proj i : ℝ^(n + 1) →L[ℝ] ℝ).differentiableAt.comp x
        (hdiff x hx.2)).hasFDerivAt)
    (DF := PDE.divergence F) (hDF := fun _ ↦ rfl) (Hi := hint.integrableOn)
  have hflux :
      (∑ i : Fin (n + 1),
        ((∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            F (eL.symm (i.insertNth (eL b i) x)) i) -
          ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            F (eL.symm (i.insertNth (eL a i) x)) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hfront (x : Fin n → ℝ) : F (eL.symm (i.insertNth (eL b i) x)) = 0 := by
      apply hzero _ i
      left
      simp [eL, b]
    have hback (x : Fin n → ℝ) : F (eL.symm (i.insertNth (eL a i) x)) = 0 := by
      apply hzero _ i
      right
      simp [eL, a]
    simp only [hfront, hback, PiLp.zero_apply, integral_zero, sub_zero]
  rw [hflux] at hmain
  rw [← hmain]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have houtside : x ∉ tsupport F := fun h ↦ hx (hsbox h)
  unfold PDE.divergence
  apply Finset.sum_eq_zero
  intro i _
  have houtsidei : x ∉ tsupport (fun y ↦ F y i) := by
    exact fun h ↦ houtside (tsupport_comp_subset (g := fun z : ℝ^(n + 1) ↦ z i) (by rfl) F h)
  simp [PDE.partialDeriv, fderiv_of_notMem_tsupport ℝ houtsidei]

end PDE.Analysis
