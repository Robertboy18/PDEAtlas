/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.CompactByParts
public import PDE.FDeriv.Operators
public import PDE.FDeriv.PartialDeriv.Support
public import PDE.FDeriv.PartialDeriv.Regularity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Coordinate integration by parts for smooth fields

For smooth functions on `ℝⁿ` with one compactly supported factor: the dilation identity
`∫ g (x·∇f) = -∫ (x·∇g) f - n ∫ g f` and the transport identity
`∑ⱼ ∫ a bⱼ ∂ⱼψ = -∫ (b·∇a) ψ` for a divergence-free field `b`. The components of the Fréchet
derivative of a vector field are `(DW(x) v)ᵢ = ∑ⱼ vⱼ ∂ⱼWᵢ(x)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PDE.Analysis

variable {n : ℕ}

theorem integrable_mul_of_hasCompactSupport_right {f g : ℝ^n → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun x ↦ f x * g x) volume :=
  (hf.mul hg).integrable_of_hasCompactSupport (hc.mul_left (f := f))

theorem integrable_mul_of_hasCompactSupport_left {f g : ℝ^n → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ f x * g x) volume :=
  (hf.mul hg).integrable_of_hasCompactSupport (hc.mul_right (f' := g))

/-- Integration by parts for the dilation field: `∫ g (x·∇f) = -∫ (x·∇g) f - n ∫ g f` for
smooth `f, g` with `f` compactly supported. -/
theorem integral_mul_sum_coord_mul_partialDeriv {f g : ℝ^n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport f) :
    ∫ x, g x * ∑ j, x j * (∂[j] f) x =
      -(∫ x, (∑ j, x j * (∂[j] g) x) * f x) - n * ∫ x, g x * f x := by
  have hcoord : ∀ j : Fin n, ContDiff ℝ ∞ (fun x : ℝ^n ↦ x j) := fun j ↦
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).contDiff
  have hfj : ∀ j : Fin n, ContDiff ℝ ∞ (fun y ↦ (∂[j] f) y) := fun j ↦
    contDiff_top_partialDeriv hf
  have hgj : ∀ j : Fin n, ContDiff ℝ ∞ (fun y ↦ (∂[j] g) y) := fun j ↦
    contDiff_top_partialDeriv hg
  have hper : ∀ j : Fin n, ∫ x, g x * (x j * (∂[j] f) x) =
      -(∫ x, x j * (∂[j] g) x * f x) - ∫ x, g x * f x := by
    intro j
    set F : ℝ^n → ℝ := fun x ↦ x j * f x
    have hF : ContDiff ℝ ∞ F := (hcoord j).mul hf
    have hFc : HasCompactSupport F := hc.mul_left
    have hdF : ∀ x, (∂[j] F) x = f x + x j * (∂[j] f) x := by
      intro x
      have h := partialDeriv_mul (i := j) (x := x)
        ((hcoord j).differentiable (by simp) x) (hf.differentiable (by simp) x)
      simp only [F] at h ⊢
      rw [h, partialDeriv_coord]
      simp
    have e := integral_mul_partialDeriv_eq_neg (𝕜 := ℝ) j (f := F) (g := g)
      (hF.of_le (by simp)) (hg.of_le (by simp)) hFc
    simp only [hdF] at e
    have hi1 : Integrable (fun x ↦ f x * g x) volume :=
      integrable_mul_of_hasCompactSupport_left hf.continuous hg.continuous hc
    have hi2 : Integrable (fun x ↦ x j * (∂[j] f) x * g x) volume :=
      integrable_mul_of_hasCompactSupport_left ((hcoord j).continuous.mul (hfj j).continuous)
        hg.continuous ((hc.partialDeriv j).mul_left)
    have e2 : ∫ x, (f x + x j * (∂[j] f) x) * g x =
        (∫ x, f x * g x) + ∫ x, x j * (∂[j] f) x * g x := by
      rw [← integral_add hi1 hi2]
      congr 1; funext x; ring
    rw [e2] at e
    calc ∫ x, g x * (x j * (∂[j] f) x) = ∫ x, x j * (∂[j] f) x * g x := by
          congr 1; funext x; ring
      _ = -(∫ x, F x * (∂[j] g) x) - ∫ x, f x * g x := by linarith
      _ = _ := by
          congr 2
          · congr 1; funext x; simp only [F]; ring
          · funext x; ring
  have hint1 : ∀ j : Fin n, Integrable (fun x ↦ g x * (x j * (∂[j] f) x)) volume := fun j ↦
    integrable_mul_of_hasCompactSupport_right hg.continuous
      ((hcoord j).continuous.mul (hfj j).continuous) ((hc.partialDeriv j).mul_left)
  have hint2 : ∀ j : Fin n, Integrable (fun x ↦ x j * (∂[j] g) x * f x) volume := fun j ↦
    integrable_mul_of_hasCompactSupport_right ((hcoord j).continuous.mul (hgj j).continuous)
      hf.continuous hc
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ ↦ hint1 j, integral_finsetSum _ fun j _ ↦ hint2 j]
  simp only [hper, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Integration by parts for a transport term: for smooth `a`, a smooth divergence-free field
`b` and a smooth compactly supported `ψ`, `∑ⱼ ∫ a bⱼ ∂ⱼψ = -∫ (b·∇a) ψ`. -/
theorem sum_integral_mul_mul_partialDeriv_eq_neg {a ψ : ℝ^n → ℝ} {b : ℝ^n → ℝ^n}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hdiv : ∀ x, PDE.divergence b x = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∑ j, ∫ x, a x * b x j * (∂[j] ψ) x = -∫ x, (∑ j, b x j * (∂[j] a) x) * ψ x := by
  have hbj : ∀ j : Fin n, ContDiff ℝ ∞ (fun x ↦ b x j) := fun j ↦
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).contDiff.comp hb
  have hper : ∀ j : Fin n, ∫ x, a x * b x j * (∂[j] ψ) x =
      -∫ x, ψ x * ((∂[j] a) x * b x j + a x * (∂[j] (fun y ↦ b y j)) x) := by
    intro j
    have e := integral_mul_partialDeriv_eq_neg (𝕜 := ℝ) j (f := ψ)
      (g := fun x ↦ a x * b x j) (hψ.of_le (by simp)) ((ha.mul (hbj j)).of_le (by simp)) hc
    have hd : ∀ x, (∂[j] (fun y ↦ a y * b y j)) x =
        (∂[j] a) x * b x j + a x * (∂[j] (fun y ↦ b y j)) x := fun x ↦
      partialDeriv_mul (ha.differentiable (by simp) x) ((hbj j).differentiable (by simp) x)
    simp only [hd] at e
    rw [e, neg_neg]
    congr 1; funext x; ring
  have hint : ∀ j : Fin n, Integrable (fun x ↦ ψ x * ((∂[j] a) x * b x j +
      a x * (∂[j] (fun y ↦ b y j)) x)) volume := fun j ↦
    integrable_mul_of_hasCompactSupport_left hψ.continuous
      (((contDiff_top_partialDeriv ha).continuous.mul (hbj j).continuous).add
        (ha.continuous.mul (contDiff_top_partialDeriv (hbj j)).continuous)) hc
  simp only [hper]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ ↦ hint j]
  congr 1
  congr 1
  funext x
  have hdx := hdiv x
  simp only [PDE.divergence] at hdx
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul]
  rw [hdx, mul_zero, mul_zero, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Fréchet derivative of a differentiable field in coordinates. -/
theorem fderiv_apply_component {W : ℝ^n → ℝ^n} {x : ℝ^n} (hW : DifferentiableAt ℝ W x)
    (v : ℝ^n) (i : Fin n) :
    fderiv ℝ W x v i = ∑ j, v j * (∂[j] (fun y ↦ W y i)) x := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [PiLp.smul_apply, smul_eq_mul, partialDeriv_apply j i hW]

end PDE.Analysis
