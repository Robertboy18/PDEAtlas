/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Deriv.Curried
public import PDE.Analysis.Integration.Primitive.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Spatially smooth families with continuous traces

A family `f : ℝ → ℝ → ℝ` (space, then time) is spatially smooth on `[0, T]` if each slice
`f (·, t)`, `t ∈ [0, T]`, is `C^∞` and every spatial derivative `∂ₓᵏ f` is jointly continuous on
`ℝ × [0, T]`. Such families are closed under sums, products, spatial differentiation (`derivX`)
and the spatial primitive from `0` (`primitiveX`); the spatial Hilbert transform is in
`PDE.Analysis.Fourier.HilbertTransform.Parametric.Smooth`.

## Main results

* `IsSpatiallySmooth`, `HasBoundedSupport`: the class of families and a support bound uniform
  in time.
* `IsSpatiallySmooth.add`, `.mul`, `.derivX`, `.primitiveX`: closure.
* `IsSpatiallySmooth.exists_bounds`: uniform value and Lipschitz bounds of each spatial
  derivative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff NNReal

namespace PDE.Analysis

/-- Smooth slices on `[0, T]` whose spatial derivatives of every order are jointly continuous on
`ℝ × [0, T]`. -/
structure IsSpatiallySmooth (T : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  /-- Every slice on `[0, T]` is `C^∞`. -/
  contDiff : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun x ↦ f x t)
  /-- Every spatial derivative is jointly continuous on `ℝ × [0, T]`. -/
  continuous : ∀ k : ℕ,
    Continuous (fun z : ℝ × Icc (0 : ℝ) T ↦ deriv^[k] (fun y ↦ f y z.2) z.1)

/-- The family vanishes outside one bounded interval at every time of `[0, T]`. -/
def HasBoundedSupport (T : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ L, ∀ t ∈ Icc (0 : ℝ) T, ∀ x, L ≤ |x| → f x t = 0

/-- The primitive of a family in its first variable, `∫₀ˣ f (y, t) dy`. -/
def primitiveX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ := primitive (fun y ↦ f y t) x

namespace HasBoundedSupport

variable {T : ℝ} {f g : ℝ → ℝ → ℝ}

/-- Products with a family of bounded support have bounded support. -/
theorem mul_right (hf : HasBoundedSupport T f) (g : ℝ → ℝ → ℝ) :
    HasBoundedSupport T (fun x t ↦ f x t * g x t) := by
  obtain ⟨L, hL⟩ := hf
  exact ⟨L, fun t ht x hx ↦ by dsimp only; rw [hL t ht x hx, zero_mul]⟩

/-- Products with a family of bounded support have bounded support. -/
theorem mul_left (hg : HasBoundedSupport T g) (f : ℝ → ℝ → ℝ) :
    HasBoundedSupport T (fun x t ↦ f x t * g x t) := by
  obtain ⟨L, hL⟩ := hg
  exact ⟨L, fun t ht x hx ↦ by dsimp only; rw [hL t ht x hx, mul_zero]⟩

/-- Sums of families of bounded support have bounded support. -/
theorem add (hf : HasBoundedSupport T f) (hg : HasBoundedSupport T g) :
    HasBoundedSupport T (fun x t ↦ f x t + g x t) := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  refine ⟨max L M, fun t ht x hx ↦ ?_⟩
  dsimp only
  rw [hL t ht x ((le_max_left _ _).trans hx), hM t ht x ((le_max_right _ _).trans hx), add_zero]

/-- Spatial derivatives of a family of bounded support have bounded support. -/
theorem iterate_deriv (hf : HasBoundedSupport T f) :
    ∃ L, ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x, L ≤ |x| → deriv^[k] (fun y ↦ f y t) x = 0 := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L + 1, fun k t ht x hx ↦ ?_⟩
  have h : EqOn (fun y ↦ f y t) 0 {y | L < |y|} := fun y hy ↦ hL t ht y (le_of_lt hy)
  rw [← iteratedDeriv_eq_iterate, h.iteratedDeriv_of_isOpen
    (isOpen_lt continuous_const continuous_abs) k (show L < |x| by linarith),
    iteratedDeriv_const_zero]

/-- The spatial derivative of a family of bounded support has bounded support. -/
theorem derivX (hf : HasBoundedSupport T f) : HasBoundedSupport T (derivX f) := by
  obtain ⟨L, hL⟩ := hf.iterate_deriv
  exact ⟨L, fun t ht x hx ↦ hL 1 t ht x hx⟩

/-- At each time a family of bounded support has compactly supported slices. -/
theorem hasCompactSupport (hf : HasBoundedSupport T f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasCompactSupport (fun x ↦ f x t) := by
  obtain ⟨L, hL⟩ := hf
  apply HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc
  intro x hx
  exact hL t ht x (le_of_not_ge fun h ↦ hx (abs_le.mp h))

end HasBoundedSupport

namespace IsSpatiallySmooth

variable {T : ℝ} {f g : ℝ → ℝ → ℝ}

/-- Along a fixed point, the spatially smooth family is continuous in time on `[0, T]`. -/
theorem continuousOn_time (hf : IsSpatiallySmooth T f)
    (x : ℝ) : ContinuousOn (f x) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h := (hf.continuous 0).comp ((continuous_const (y := x)).prodMk continuous_id)
  exact h

/-- The spatial derivative is spatially smooth. -/
theorem derivX (h : IsSpatiallySmooth T f) : IsSpatiallySmooth T (derivX f) where
  contDiff t ht := (h.contDiff t ht).iterate_deriv 1
  continuous k := by
    simpa only [PDE.Analysis.derivX, ← Function.iterate_succ_apply] using h.continuous (k + 1)

/-- Sums of spatially smooth families are spatially smooth. -/
theorem add (hf : IsSpatiallySmooth T f) (hg : IsSpatiallySmooth T g) :
    IsSpatiallySmooth T (fun x t ↦ f x t + g x t) where
  contDiff t ht := (hf.contDiff t ht).add (hg.contDiff t ht)
  continuous k := by
    have heq : (fun z : ℝ × Icc (0 : ℝ) T ↦ deriv^[k] (fun y ↦ f y z.2 + g y z.2) z.1) =
        fun z ↦ deriv^[k] (fun y ↦ f y z.2) z.1 + deriv^[k] (fun y ↦ g y z.2) z.1 := by
      funext z
      simp only [← iteratedDeriv_eq_iterate]
      exact iteratedDeriv_fun_add (contDiff_infty.mp (hf.contDiff z.2 z.2.property) k).contDiffAt
        (contDiff_infty.mp (hg.contDiff z.2 z.2.property) k).contDiffAt
    rw [heq]
    exact (hf.continuous k).add (hg.continuous k)

/-- Constants are spatially smooth. -/
theorem const (T a : ℝ) : IsSpatiallySmooth T (fun _ _ ↦ a) where
  contDiff _ _ := contDiff_const
  continuous k := by
    simp only [← iteratedDeriv_eq_iterate, iteratedDeriv_const]
    exact continuous_const

/-- Products of spatially smooth families are spatially smooth. -/
theorem mul (hf : IsSpatiallySmooth T f) (hg : IsSpatiallySmooth T g) :
    IsSpatiallySmooth T (fun x t ↦ f x t * g x t) where
  contDiff t ht := (hf.contDiff t ht).mul (hg.contDiff t ht)
  continuous k := by
    induction k generalizing f g with
    | zero => exact (hf.continuous 0).mul (hg.continuous 0)
    | succ k ih =>
      have heq : (fun z : ℝ × Icc (0 : ℝ) T ↦ deriv^[k + 1] (fun y ↦ f y z.2 * g y z.2) z.1) =
          fun z ↦ deriv^[k] (fun y ↦ PDE.Analysis.derivX f y z.2 * g y z.2) z.1 +
            deriv^[k] (fun y ↦ f y z.2 * PDE.Analysis.derivX g y z.2) z.1 := by
        funext z
        have hfz := hf.contDiff z.2 z.2.property
        have hgz := hg.contDiff z.2 z.2.property
        have hd : deriv (fun y ↦ f y z.2 * g y z.2) = fun y ↦
            PDE.Analysis.derivX f y z.2 * g y z.2 + f y z.2 * PDE.Analysis.derivX g y z.2 := by
          funext y
          exact deriv_mul (hfz.differentiable (by simp) y) (hgz.differentiable (by simp) y)
        have hf' : ContDiff ℝ ∞ (fun y ↦ PDE.Analysis.derivX f y z.2) :=
          (contDiff_infty_iff_deriv.mp hfz).2
        have hg' : ContDiff ℝ ∞ (fun y ↦ PDE.Analysis.derivX g y z.2) :=
          (contDiff_infty_iff_deriv.mp hgz).2
        rw [Function.iterate_succ_apply, hd]
        simp only [← iteratedDeriv_eq_iterate]
        exact iteratedDeriv_fun_add (contDiff_infty.mp (hf'.mul hgz) k).contDiffAt
          (contDiff_infty.mp (hfz.mul hg') k).contDiffAt
      rw [heq]
      exact (ih hf.derivX hg).add (ih hf hg.derivX)

/-- A spatially smooth family of bounded support has, for each order, uniform value and Lipschitz
bounds for its spatial derivative on `[0, T]`. -/
theorem exists_bounds (hf : IsSpatiallySmooth T f) (hs : HasBoundedSupport T f) (k : ℕ) :
    ∃ (L B : ℝ) (K : ℝ≥0), 0 ≤ L ∧ ∀ t : Icc (0 : ℝ) T,
      LipschitzWith K (deriv^[k] (fun y ↦ f y t)) ∧
      (∀ y, ‖deriv^[k] (fun y ↦ f y t) y‖ ≤ B) ∧
      ∀ y, L ≤ |y| → deriv^[k] (fun y ↦ f y t) y = 0 := by
  obtain ⟨L₀, hL₀⟩ := hs.iterate_deriv
  set L := max L₀ 0 with hL
  have hc : IsCompact (Icc (-L) L ×ˢ (univ : Set (Icc (0 : ℝ) T))) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (hf.continuous k).continuousOn
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuousOn (hf.continuous (k + 1)).continuousOn
  have hzero (j : ℕ) (t : Icc (0 : ℝ) T) (y : ℝ) (hy : ¬ y ∈ Icc (-L) L) :
      deriv^[j] (fun y ↦ f y t) y = 0 := by
    apply hL₀ j t t.property y
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy | hy
    · rw [abs_of_neg (by linarith [le_max_right L₀ 0])]
      linarith [le_max_left L₀ 0]
    · rw [abs_of_pos (by linarith [le_max_right L₀ 0])]
      linarith [le_max_left L₀ 0]
  have hbound (j : ℕ) (C : ℝ) (hC : ∀ z ∈ Icc (-L) L ×ˢ (univ : Set (Icc (0 : ℝ) T)),
      ‖deriv^[j] (fun y ↦ f y z.2) z.1‖ ≤ C) (t : Icc (0 : ℝ) T) (y : ℝ) :
      ‖deriv^[j] (fun y ↦ f y t) y‖ ≤ max C 0 := by
    by_cases hy : y ∈ Icc (-L) L
    · exact (hC (y, t) ⟨hy, mem_univ _⟩).trans (le_max_left _ _)
    · rw [hzero j t y hy, norm_zero]
      exact le_max_right _ _
  refine ⟨L, max B 0, ⟨max K 0, le_max_right _ _⟩, le_max_right _ _, fun t ↦ ⟨?_, hbound k B hB t,
    fun y hy ↦ ?_⟩⟩
  · have hdiff : Differentiable ℝ (deriv^[k] (fun y ↦ f y t)) :=
      ((hf.contDiff t t.property).iterate_deriv k).differentiable (by simp)
    apply lipschitzWith_of_nnnorm_deriv_le hdiff
    intro y
    change ‖deriv (deriv^[k] (fun y ↦ f y t)) y‖ ≤ max K 0
    have := hbound (k + 1) K hK t y
    rwa [Function.iterate_succ_apply'] at this
  · exact hL₀ k t t.property y ((le_max_left _ _).trans hy)

/-- The spatial primitive of a spatially smooth family is spatially smooth. -/
theorem primitiveX (hf : IsSpatiallySmooth T f) : IsSpatiallySmooth T (primitiveX f) where
  contDiff t ht := by
    have hd (x : ℝ) : HasDerivAt (fun x ↦ PDE.Analysis.primitiveX f x t) (f x t) x :=
      ((hf.contDiff t ht).continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
    rw [show deriv (fun x ↦ PDE.Analysis.primitiveX f x t) = fun x ↦ f x t from
      funext fun x ↦ (hd x).deriv]
    exact hf.contDiff t ht
  continuous k := by
    rcases k with _ | k
    · have hc : Continuous (fun p : (ℝ × Icc (0 : ℝ) T) × ℝ ↦ f p.2 p.1.2) :=
        (hf.continuous 0).comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (z : ℝ × Icc (0 : ℝ) T) (y : ℝ) ↦ f y z.2) (a₀ := 0) hc continuous_fst
    · have heq : (fun z : ℝ × Icc (0 : ℝ) T ↦
          deriv^[k + 1] (fun y ↦ PDE.Analysis.primitiveX f y z.2) z.1) =
          fun z ↦ deriv^[k] (fun y ↦ f y z.2) z.1 := by
        funext z
        have hd : deriv (fun x ↦ PDE.Analysis.primitiveX f x z.2) = fun x ↦ f x z.2 :=
          funext fun x ↦ (((hf.contDiff z.2 z.2.property).continuous.integral_hasStrictDerivAt
            0 x).hasDerivAt).deriv
        rw [Function.iterate_succ_apply, hd]
      rw [heq]
      exact hf.continuous k

end IsSpatiallySmooth

end PDE.Analysis
