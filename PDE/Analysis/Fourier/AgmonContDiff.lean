/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.FDeriv.Calculus
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder
public import PDE.Analysis.Fourier.Agmon
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Agmon's inequality for `C²` functions with compact support

Agmon's inequality on `ℝ³`, `ae_norm_sq_le_of_hasComplexWeakDerivativeOn`, is stated for `L²`
classes with weak derivatives, and it holds almost everywhere. This module reads it for a
classical `C²` function `w` with compact support: at every point, with the `L²` norms of the
Fréchet derivatives `Dw` and `D²w`, and for values in any real normed space. The constant here
is `1`. With the gradient and the Laplacian in place of `Dw` and `D²w` the sharp constant is
`1/(2π)`. Bounding the Laplacian by `3 ‖D²w‖` costs a factor `3`, and `3 ≤ 2π`. The same
reading of `sum_norm_sq_le_of_hasComplexWeakDerivativeOn` gives `‖Dw‖₂² ≤ n ‖w‖₂ ‖D²w‖₂` in
every dimension `n`. Agmon's inequality on an annulus applies both results to an extension of a
function from the annulus.

## Main results

* `norm_sq_le_of_contDiff_two`: `‖w x‖² ≤ ‖Dw‖₂ ‖D²w‖₂` for every `C²` function `w : ℝ³ → F`
  with compact support, `F` a real normed space, and every point `x`.
* `lpNorm_fderiv_sq_le`: `‖Dw‖₂² ≤ n ‖w‖₂ ‖D²w‖₂` for every real `C²` function `w` on `ℝⁿ` with
  compact support.
* `lpNorm_comp_le_of_norm_le_one`: a functional of norm at most one does not increase the `L²`
  norms of a `C²` function and of its first two derivatives, for every measure under which
  these norms are finite.

## How it works

A `C²` function with compact support and its classical derivatives are square integrable, and
the classical derivatives are the weak ones
(`SobolevSpace.hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn`). So the inequality for
classes applies to a real `w` and gives `|w(x)|² ≤ ‖Dw‖₂ ‖D²w‖₂` for almost every `x`. The set
where this fails is open, because `w` is continuous and the right side is a constant, and an
open null set is empty. The gradient has the norm of `Dw` at every point, and each pure second
derivative `∂ₖ∂ₖw` is at most `‖D²w‖`. A function with values in a normed space is reduced to
the real case by a functional of norm one that attains the norm of `w(x)` (Hahn–Banach).
-/

@[expose] public noncomputable section

open MeasureTheory Real Filter Set
open scoped ENNReal NNReal

namespace PDE.Analysis.Fourier

/-- The `L²` classes of a real `C²` function with compact support, of its coordinate derivatives
and of its pure second derivatives, with their norms. -/
private theorem exists_classes_of_contDiff_two {n : ℕ} {w : ℝ^n → ℝ} (hw : ContDiff ℝ 2 w)
    (hc : HasCompactSupport w) :
    ∃ (u : Lp ℂ 2 (volume : Measure (ℝ^n))) (d l : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n))),
      (∀ i, SobolevSpace.HasComplexWeakDerivativeOn univ [i] u (d i)) ∧
      (∀ k, SobolevSpace.HasComplexWeakDerivativeOn univ [k, k] u (l k)) ∧
      ((u : ℝ^n → ℂ) =ᵐ[volume] fun y ↦ ((w y : ℝ) : ℂ)) ∧
      ‖u‖ = lpNorm w 2 volume ∧
      ∑ i, ‖d i‖ ^ 2 = lpNorm (fderiv ℝ w) 2 volume ^ 2 ∧
      ∀ k, ‖l k‖ ≤ lpNorm (fderiv ℝ (fderiv ℝ w)) 2 volume := by
  have hw1 : ContDiff ℝ 1 (fderiv ℝ w) := hw.fderiv_right (by norm_num)
  have hm0 : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hc
  have hm1 : MemLp (fderiv ℝ w) 2 volume :=
    hw1.continuous.memLp_of_hasCompactSupport (hc.fderiv ℝ)
  have hm2 : MemLp (fderiv ℝ (fderiv ℝ w)) 2 volume :=
    (hw1.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport ((hc.fderiv ℝ).fderiv ℝ)
  -- the coordinate derivatives and their bounds by the Fréchet derivatives
  have hb1 (i : Fin n) (y : ℝ^n) : ‖PDE.iteratedPartialDeriv [i] w y‖ ≤ ‖fderiv ℝ w y‖ :=
    PDE.norm_partialDeriv_le_norm_fderiv i w y
  have hb2 (k : Fin n) (y : ℝ^n) :
      ‖PDE.iteratedPartialDeriv [k, k] w y‖ ≤ ‖fderiv ℝ (fderiv ℝ w) y‖ := by
    have h : PDE.iteratedPartialDeriv [k, k] w y = fderiv ℝ (fderiv ℝ w) y
        (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ)) :=
      PDE.secondPartialDeriv_eq_fderiv k k (hw1.differentiable one_ne_zero y)
    rw [h]
    simpa using (fderiv ℝ (fderiv ℝ w) y).le_opNorm₂ (EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single k (1 : ℝ))
  have hc1 (i : Fin n) : Continuous (PDE.iteratedPartialDeriv [i] w) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le (k := 2) (by exact_mod_cast hw) [i]
      (by simp)).continuous
  have hc2 (k : Fin n) : Continuous (PDE.iteratedPartialDeriv [k, k] w) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le (k := 2) (by exact_mod_cast hw) [k, k]
      (by simp)).continuous
  have hg1 (i : Fin n) : MemLp (PDE.iteratedPartialDeriv [i] w) 2 volume :=
    hm1.of_le (hc1 i).aestronglyMeasurable (Eventually.of_forall (hb1 i))
  have hg2 (k : Fin n) : MemLp (PDE.iteratedPartialDeriv [k, k] w) 2 volume :=
    MemLp.of_le (F := ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ) hm2 (hc2 k).aestronglyMeasurable
      (Eventually.of_forall (hb2 k))
  -- the classes in `L²` and their weak derivatives
  let u : Lp ℂ 2 (volume : Measure (ℝ^n)) := hm0.ofReal.toLp (fun y ↦ ((w y : ℝ) : ℂ))
  let d : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)) := fun i ↦
    (hg1 i).ofReal.toLp (fun y ↦ ((PDE.iteratedPartialDeriv [i] w y : ℝ) : ℂ))
  let l : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)) := fun k ↦
    (hg2 k).ofReal.toLp (fun y ↦ ((PDE.iteratedPartialDeriv [k, k] w y : ℝ) : ℂ))
  have hweak (α : List (Fin n)) (hα : α.length ≤ 2) (hg : MemLp (PDE.iteratedPartialDeriv α w) 2
      volume) : SobolevSpace.HasComplexWeakDerivativeOn univ α u
        (hg.ofReal.toLp (fun y ↦ ((PDE.iteratedPartialDeriv α w y : ℝ) : ℂ))) := by
    have hfun : SobolevSpace.HasComplexWeakDerivativeOn univ α (fun y ↦ ((w y : ℝ) : ℂ))
        (fun y ↦ ((PDE.iteratedPartialDeriv α w y : ℝ) : ℂ)) :=
      ⟨SobolevSpace.hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn (k := 2) isOpen_univ
        (by exact_mod_cast hw.contDiffOn) α hα,
        by simpa only [Complex.ofReal_im] using SobolevSpace.hasWeakDerivativeOn_zero univ α⟩
    refine hfun.congr_ae ?_ ?_
    · simpa [SobolevSpace.domainMeasure] using (MemLp.coeFn_toLp _).symm
    · simpa [SobolevSpace.domainMeasure] using (MemLp.coeFn_toLp _).symm
  have hu : (u : ℝ^n → ℂ) =ᵐ[volume] fun y ↦ ((w y : ℝ) : ℂ) := MemLp.coeFn_toLp _
  refine ⟨u, d, l, fun i ↦ hweak [i] (by simp) (hg1 i), fun k ↦ hweak [k, k] (by simp) (hg2 k),
    hu, ?_, ?_, fun k ↦ ?_⟩
  · -- the norm of the class of `w`
    rw [Lp.norm_toLp]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae
      (Complex.continuous_ofReal.comp hw.continuous).aestronglyMeasurable
      hw.continuous.aestronglyMeasurable (Eventually.of_forall fun y ↦ Complex.norm_real _))
  · -- the gradient energy
    have hd (i : Fin n) : ‖d i‖ ^ 2 = ∫ y, (∂[i] w) y ^ 2 := by
      rw [Lp.norm_sq_eq_integral_norm_sq]
      refine integral_congr_ae ?_
      have hdi : (d i : ℝ^n → ℂ) =ᵐ[volume]
          fun y ↦ ((PDE.iteratedPartialDeriv [i] w y : ℝ) : ℂ) := MemLp.coeFn_toLp _
      filter_upwards [hdi] with y hy
      rw [hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rfl
    have hint (i : Fin n) : Integrable (fun y ↦ (∂[i] w) y ^ 2) := (hg1 i).integrable_sq
    calc ∑ i, ‖d i‖ ^ 2 = ∫ y, ∑ i, (∂[i] w) y ^ 2 := by
          rw [integral_finsetSum _ fun i _ ↦ hint i]
          exact Finset.sum_congr rfl fun i _ ↦ hd i
      _ = ∫ y, ‖fderiv ℝ w y‖ ^ 2 := by
          refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
          exact (PDE.norm_fderiv_sq_eq_sum_partialDeriv_sq
            (hw.differentiable (by norm_num) y)).symm
      _ = lpNorm (fderiv ℝ w) 2 volume ^ 2 := by
          rw [MemLp.integral_sq_eq_lpNorm_sq hm1.norm,
            lpNorm_norm hm1.aestronglyMeasurable]
  · -- the pure second derivatives
    rw [Lp.norm_toLp]
    refine ENNReal.toReal_mono hm2.eLpNorm_ne_top (eLpNorm_mono (G := ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ)
      (Complex.continuous_ofReal.comp (hc2 k)).aestronglyMeasurable fun y ↦ ?_)
    rw [Complex.norm_real]
    exact hb2 k y

/-- A sum of `n` vectors of norm at most `N` has norm at most `n N`. It bounds the class of the
Laplacian by `n ‖D²w‖₂`. -/
private theorem norm_sum_le_card_mul {n : ℕ} {G : Type*} [SeminormedAddCommGroup G]
    (l : Fin n → G) {N : ℝ} (hl : ∀ k, ‖l k‖ ≤ N) : ‖∑ k, l k‖ ≤ n * N := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∑ k : Fin n, ‖l k‖ ≤ ∑ _k : Fin n, N := Finset.sum_le_sum fun k _ ↦ hl k
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

/-- **The gradient of a `C²` function with compact support is controlled by the function and its
second derivative.** For every real `C²` function `w` on `ℝⁿ` with compact support,
`‖Dw‖₂² ≤ n ‖w‖₂ ‖D²w‖₂`. This is `sum_norm_sq_le_of_hasComplexWeakDerivativeOn` read for
classical derivatives; the factor `n` bounds the Laplacian by the operator norm of `D²w`. -/
theorem lpNorm_fderiv_sq_le {n : ℕ} {w : ℝ^n → ℝ} (hw : ContDiff ℝ 2 w)
    (hc : HasCompactSupport w) :
    lpNorm (fderiv ℝ w) 2 volume ^ 2 ≤
      n * (lpNorm w 2 volume * lpNorm (fderiv ℝ (fderiv ℝ w)) 2 volume) := by
  obtain ⟨u, d, l, hd, hl, -, hu, hsum, hl2⟩ := exists_classes_of_contDiff_two hw hc
  have h := sum_norm_sq_le_of_hasComplexWeakDerivativeOn u d l hd hl
  rw [hsum, hu] at h
  refine h.trans ?_
  have h2 := mul_le_mul_of_nonneg_left (norm_sum_le_card_mul l hl2) (lpNorm_nonneg (f := w)
    (p := 2) (μ := volume))
  linarith

/-- Agmon's inequality for real `C²` functions with compact support, with the `L²` norms of the
first and second Fréchet derivatives. -/
private theorem sq_le_of_contDiff_two_real {w : ℝ^3 → ℝ} (hw : ContDiff ℝ 2 w)
    (hc : HasCompactSupport w) (x : ℝ^3) :
    w x ^ 2 ≤ lpNorm (fderiv ℝ w) 2 volume * lpNorm (fderiv ℝ (fderiv ℝ w)) 2 volume := by
  obtain ⟨u, d, l, hd, hl, hu, -, hsum, hl2⟩ := exists_classes_of_contDiff_two hw hc
  have hae := ae_norm_sq_le_of_hasComplexWeakDerivativeOn u d l hd hl
  set N₁ := lpNorm (fderiv ℝ w) 2 volume with hN₁
  set N₂ := lpNorm (fderiv ℝ (fderiv ℝ w)) 2 volume with hN₂
  have hN₁0 : 0 ≤ N₁ := lpNorm_nonneg
  have hN₂0 : 0 ≤ N₂ := lpNorm_nonneg
  have hsum2 : ‖∑ k, l k‖ ≤ 3 * N₂ := by simpa using norm_sum_le_card_mul l hl2
  have hB : √(∑ i, ‖d i‖ ^ 2) * ‖∑ k, l k‖ / (2 * π) ≤ N₁ * N₂ := by
    rw [hsum, Real.sqrt_sq hN₁0, div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left hsum2 hN₁0
    nlinarith [Real.pi_gt_three, mul_nonneg hN₁0 hN₂0]
  -- almost everywhere, then everywhere by continuity
  have hae' : ∀ᵐ y, w y ^ 2 ≤ N₁ * N₂ := by
    filter_upwards [hae, hu] with y hy hy'
    have hy'' : ‖u y‖ = |w y| := by
      rw [show u y = ((w y : ℝ) : ℂ) from hy', Complex.norm_real, Real.norm_eq_abs]
    rw [hy'', sq_abs] at hy
    exact hy.trans hB
  have hopen : IsOpen {y | N₁ * N₂ < w y ^ 2} :=
    isOpen_lt continuous_const (hw.continuous.pow 2)
  have hnull : volume {y | N₁ * N₂ < w y ^ 2} = 0 := by
    simpa only [not_le] using ae_iff.1 hae'
  have hempty := (hopen.measure_eq_zero_iff volume).1 hnull
  by_contra h
  have hx : x ∈ {y | N₁ * N₂ < w y ^ 2} := not_le.1 h
  rw [hempty] at hx
  exact hx

/-- A functional of norm at most one does not increase the `L²` norms of a function and of its
first two derivatives, with respect to any measure for which these norms are finite. -/
theorem lpNorm_comp_le_of_norm_le_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {φ : F →L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) {w : E → F} (hw : ContDiff ℝ 2 w)
    {ν : Measure E} (hm0 : MemLp w 2 ν) (hm1 : MemLp (fderiv ℝ w) 2 ν)
    (hm2 : MemLp (fderiv ℝ (fderiv ℝ w)) 2 ν) :
    lpNorm (φ ∘ w) 2 ν ≤ lpNorm w 2 ν ∧
      lpNorm (fderiv ℝ (φ ∘ w)) 2 ν ≤ lpNorm (fderiv ℝ w) 2 ν ∧
      lpNorm (fderiv ℝ (fderiv ℝ (φ ∘ w))) 2 ν ≤ lpNorm (fderiv ℝ (fderiv ℝ w)) 2 ν := by
  have hφw : ContDiff ℝ 2 (φ ∘ w) := φ.contDiff.comp hw
  have hφw1 : ContDiff ℝ 1 (fderiv ℝ (φ ∘ w)) := hφw.fderiv_right (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · refine ENNReal.toReal_mono hm0.eLpNorm_ne_top
      (eLpNorm_mono hφw.continuous.aestronglyMeasurable fun y ↦ ?_)
    exact (φ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hφ)
  · refine ENNReal.toReal_mono hm1.eLpNorm_ne_top
      (eLpNorm_mono hφw1.continuous.aestronglyMeasurable fun y ↦ ?_)
    rw [← norm_iteratedFDeriv_one, ← norm_iteratedFDeriv_one (f := w)]
    refine (φ.norm_iteratedFDeriv_comp_left hw.contDiffAt (by norm_num)).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) hφ
  · refine ENNReal.toReal_mono hm2.eLpNorm_ne_top
      (eLpNorm_mono (hφw1.continuous_fderiv one_ne_zero).aestronglyMeasurable fun y ↦ ?_)
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv,
      ← norm_iteratedFDeriv_one (f := fderiv ℝ w), norm_iteratedFDeriv_fderiv]
    refine (φ.norm_iteratedFDeriv_comp_left hw.contDiffAt (by norm_num)).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) hφ

/-- **Agmon's inequality for `C²` functions with compact support on `ℝ³`.** For every `C²`
function `w : ℝ³ → F` with compact support and every point `x`,
`|w(x)|² ≤ ‖Dw‖₂ ‖D²w‖₂`, with the operator norms of the Fréchet derivatives. Compared with the
inequality for classes, the statement holds at every point and asks for no weak derivative. The
proof applies `ae_norm_sq_le_of_hasComplexWeakDerivativeOn` to `φ ∘ w` for a functional `φ` of
norm at most one with `φ (w x) = |w x|`, and removes the null set by continuity. -/
theorem norm_sq_le_of_contDiff_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : ℝ^3 → F} (hw : ContDiff ℝ 2 w) (hc : HasCompactSupport w) (x : ℝ^3) :
    ‖w x‖ ^ 2 ≤ lpNorm (fderiv ℝ w) 2 volume * lpNorm (fderiv ℝ (fderiv ℝ w)) 2 volume := by
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ (w x)
  have hreal := sq_le_of_contDiff_two_real (φ.contDiff.comp hw) (hc.comp_left (map_zero φ)) x
  have hw1 : ContDiff ℝ 1 (fderiv ℝ w) := hw.fderiv_right (by norm_num)
  obtain ⟨-, h1, h2⟩ := lpNorm_comp_le_of_norm_le_one (ν := volume) hφ hw
    (hw.continuous.memLp_of_hasCompactSupport hc)
    (hw1.continuous.memLp_of_hasCompactSupport (hc.fderiv ℝ))
    ((hw1.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport ((hc.fderiv ℝ).fderiv ℝ))
  have hval : (φ ∘ w) x = ‖w x‖ := by simpa using hφx
  rw [← hval]
  exact hreal.trans (mul_le_mul h1 h2 lpNorm_nonneg lpNorm_nonneg)

end PDE.Analysis.Fourier
