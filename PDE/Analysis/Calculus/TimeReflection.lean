/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# First-order reflection of a time-dependent field across time zero

A classical solution on `[0, T)` is regular up to `t = 0` only from the right. The reflection

```text
f̃(x, τ) = f(x, τ) for τ ≥ 0,     f̃(x, τ) = 2 f(x, 0) - f(x, -τ) for τ < 0
```

agrees with `f` for `τ ≥ 0`, and if `f` is differentiable within `E × [0, ∞)` at `(x, 0)` with
derivative `L`, then `f̃` is differentiable at `(x, 0)` with the same derivative `L`: the
derivative of `2 f(x, 0) - f(x, -τ)` within `E × (-∞, 0]` is `2 L(v, 0) - L(v, -s) = L(v, s)`.
So a field that is `C¹` within `E × [0, ∞)` has, after reflection, an ordinary joint derivative
at every point `(x, τ)` with `τ ≥ 0`, and its time derivatives at `τ ≥ 0` are those of `f`
(at `τ = 0` the right derivative). This turns one-sided regularity at the initial time into the
two-sided derivatives used by classical solution predicates on `[0, T)`.

## Main results

* `hasFDerivAt_reflectTimeZero`: the derivative at a point of the initial slice.
* `differentiableAt_reflectTimeZero`, `contDiffOn_reflectTimeZero`, `deriv_reflectTimeZero`, and
  `differentiableAt_reflectTimeZero_of_Ico`, `deriv_reflectTimeZero_of_Ico` for fields given on a
  finite interval of times `[0, q)`.
-/

@[expose] public section

open Set Function
open scoped Topology

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The first-order reflection of `f` across `τ = 0`: `f x τ` for `τ ≥ 0` and
`2 f x 0 - f x (-τ)` for `τ < 0`. -/
noncomputable def reflectTimeZero (f : E → ℝ → F) (x : E) (τ : ℝ) : F :=
  if 0 ≤ τ then f x τ else (2 : ℝ) • f x 0 - f x (-τ)

variable {f : E → ℝ → F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The reflection agrees with `f` at nonnegative times. -/
theorem reflectTimeZero_of_nonneg (f : E → ℝ → F) {x : E} {τ : ℝ} (hτ : 0 ≤ τ) :
    reflectTimeZero f x τ = f x τ := by
  simp [reflectTimeZero, hτ]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- At nonpositive times the reflection is `2 f x 0 - f x (-τ)`. -/
theorem reflectTimeZero_of_nonpos (f : E → ℝ → F) {x : E} {τ : ℝ} (hτ : τ ≤ 0) :
    reflectTimeZero f x τ = (2 : ℝ) • f x 0 - f x (-τ) := by
  rcases hτ.lt_or_eq with hτ | rfl
  · simp [reflectTimeZero, not_le.2 hτ]
  · rw [reflectTimeZero_of_nonneg f le_rfl, neg_zero, two_smul, add_sub_cancel_right]

/-- If `f` has derivative `L` at `(x, 0)` within `E × [0, ∞)`, its reflection has the ordinary
derivative `L` at `(x, 0)`. -/
theorem hasFDerivAt_reflectTimeZero {L : E × ℝ →L[ℝ] F} {x : E}
    (hf : HasFDerivWithinAt (uncurry f) L (univ ×ˢ Ici 0) (x, 0)) :
    HasFDerivAt (uncurry (reflectTimeZero f)) L (x, 0) := by
  have hup : HasFDerivWithinAt (uncurry (reflectTimeZero f)) L (univ ×ˢ Ici 0) (x, 0) :=
    hf.congr (fun p hp ↦ reflectTimeZero_of_nonneg f hp.2) (reflectTimeZero_of_nonneg f le_rfl)
  let P : E × ℝ →L[ℝ] E × ℝ := (ContinuousLinearMap.fst ℝ E ℝ).prod 0
  let M : E × ℝ →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).prod (-ContinuousLinearMap.snd ℝ E ℝ)
  have hP : MapsTo P (univ ×ˢ Iic 0) (univ ×ˢ Ici 0) := fun p _ ↦ by simp [P]
  have hM : MapsTo M (univ ×ˢ Iic 0) (univ ×ˢ Ici 0) := fun p hp ↦ by
    simpa [M] using hp.2
  have hP0 : P (x, 0) = (x, 0) := by simp [P]
  have hM0 : M (x, 0) = (x, 0) := by simp [M]
  have h₁ : HasFDerivWithinAt (fun p ↦ uncurry f (P p)) (L.comp P) (univ ×ˢ Iic 0) (x, 0) :=
    (hP0 ▸ hf).comp (x, 0) P.hasFDerivWithinAt hP
  have h₂ : HasFDerivWithinAt (fun p ↦ uncurry f (M p)) (L.comp M) (univ ×ˢ Iic 0) (x, 0) :=
    (hM0 ▸ hf).comp (x, 0) M.hasFDerivWithinAt hM
  have hdown : HasFDerivWithinAt (uncurry (reflectTimeZero f)) L (univ ×ˢ Iic 0) (x, 0) := by
    have h := (h₁.const_smul (2 : ℝ)).sub h₂
    have hL : (2 : ℝ) • L.comp P - L.comp M = L := by
      refine ContinuousLinearMap.ext fun p ↦ ?_
      simp only [sub_apply, smul_apply,
        ContinuousLinearMap.comp_apply]
      rw [← map_smul, ← map_sub]
      congr 1
      ext <;> simp [P, M, two_smul]
    rw [hL] at h
    refine h.congr (fun p hp ↦ ?_) ?_
    · simp only [uncurry, reflectTimeZero_of_nonpos f hp.2]
      simp [P, M]
    · simp only [uncurry, reflectTimeZero_of_nonneg f le_rfl]
      simp [P, M, two_smul]
  have hunion : univ ×ˢ Ici (0 : ℝ) ∪ univ ×ˢ Iic 0 = (univ : Set (E × ℝ)) := by
    ext p
    simp [le_total]
  have h := hup.union hdown
  rw [hunion] at h
  exact h.hasFDerivAt Filter.univ_mem

/-- A field differentiable within `E × [0, ∞)` has a reflection that is differentiable at every
point with nonnegative time. -/
theorem differentiableAt_reflectTimeZero (hf : DifferentiableOn ℝ (uncurry f) (univ ×ˢ Ici 0))
    {x : E} {τ : ℝ} (hτ : 0 ≤ τ) : DifferentiableAt ℝ (uncurry (reflectTimeZero f)) (x, τ) := by
  rcases hτ.eq_or_lt with rfl | hτ
  · exact (hasFDerivAt_reflectTimeZero
      (hf (x, 0) ⟨mem_univ x, le_rfl⟩).hasFDerivWithinAt).differentiableAt
  · have hmem : univ ×ˢ Ioi (0 : ℝ) ∈ 𝓝 (x, τ) :=
      (isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨mem_univ x, hτ⟩
    have hd : DifferentiableAt ℝ (uncurry f) (x, τ) :=
      hf.differentiableAt (Filter.mem_of_superset hmem (prod_mono le_rfl Ioi_subset_Ici_self))
    refine hd.congr_of_eventuallyEq (Filter.mem_of_superset hmem fun p hp ↦ ?_)
    exact reflectTimeZero_of_nonneg f (le_of_lt hp.2)

/-- The reflection keeps the regularity of `f` within `E × [0, ∞)`. -/
theorem contDiffOn_reflectTimeZero {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (univ ×ˢ Ici 0)) :
    ContDiffOn ℝ n (uncurry (reflectTimeZero f)) (univ ×ˢ Ici 0) :=
  hf.congr fun _ hp ↦ reflectTimeZero_of_nonneg f hp.2

/-- At nonnegative times the time derivatives of the reflection are those of `f`. -/
theorem deriv_reflectTimeZero (hf : DifferentiableOn ℝ (uncurry f) (univ ×ˢ Ici 0)) {x : E}
    {τ : ℝ} (hτ : 0 ≤ τ) (hx : DifferentiableAt ℝ (f x) τ) :
    deriv (reflectTimeZero f x) τ = deriv (f x) τ := by
  have hslice : DifferentiableAt ℝ (reflectTimeZero f x) τ := by
    have h := differentiableAt_reflectTimeZero hf (x := x) hτ
    have hpath : DifferentiableAt ℝ (fun s : ℝ ↦ (x, s)) τ :=
      (differentiableAt_const x).prodMk differentiableAt_id
    exact h.comp τ hpath
  have h₁ := hslice.hasDerivAt.hasDerivWithinAt (s := Ici τ)
  have h₂ : HasDerivWithinAt (reflectTimeZero f x) (deriv (f x) τ) (Ici τ) τ :=
    hx.hasDerivAt.hasDerivWithinAt.congr_of_mem
      (fun s hs ↦ reflectTimeZero_of_nonneg f (hτ.trans hs)) self_mem_Ici
  exact (uniqueDiffWithinAt_Ici τ).eq_deriv _ h₁ h₂

/-- A field differentiable within `E × [0, q)` has a reflection that is differentiable at every
point with time in `[0, q)`. -/
theorem differentiableAt_reflectTimeZero_of_Ico {q : ℝ}
    (hf : DifferentiableOn ℝ (uncurry f) (univ ×ˢ Ico 0 q)) {x : E} {τ : ℝ}
    (hτ : τ ∈ Ico 0 q) : DifferentiableAt ℝ (uncurry (reflectTimeZero f)) (x, τ) := by
  rcases hτ.1.eq_or_lt with rfl | hτ0
  · have hmem : univ ×ˢ Ico 0 q ∈ 𝓝[univ ×ˢ Ici 0] ((x, 0) : E × ℝ) := by
      refine mem_nhdsWithin.2 ⟨univ ×ˢ Iio q, isOpen_univ.prod isOpen_Iio,
        ⟨mem_univ _, hτ.2⟩, fun p hp ↦ ⟨mem_univ _, hp.2.2, hp.1.2⟩⟩
    exact (hasFDerivAt_reflectTimeZero ((hf (x, 0) ⟨mem_univ x, hτ⟩).hasFDerivWithinAt
      |>.mono_of_mem_nhdsWithin hmem)).differentiableAt
  · have hmem : univ ×ˢ Ioo (0 : ℝ) q ∈ 𝓝 (x, τ) :=
      (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, hτ0, hτ.2⟩
    have hd : DifferentiableAt ℝ (uncurry f) (x, τ) :=
      hf.differentiableAt (Filter.mem_of_superset hmem (prod_mono le_rfl Ioo_subset_Ico_self))
    refine hd.congr_of_eventuallyEq (Filter.mem_of_superset hmem fun p hp ↦ ?_)
    exact reflectTimeZero_of_nonneg f (le_of_lt hp.2.1)

/-- At times of `[0, q)` the time derivatives of the reflection of a field differentiable within
`E × [0, q)` are those of the field. -/
theorem deriv_reflectTimeZero_of_Ico {q : ℝ}
    (hf : DifferentiableOn ℝ (uncurry f) (univ ×ˢ Ico 0 q)) {x : E} {τ : ℝ} (hτ : τ ∈ Ico 0 q)
    (hx : DifferentiableAt ℝ (f x) τ) :
    deriv (reflectTimeZero f x) τ = deriv (f x) τ := by
  have hslice : DifferentiableAt ℝ (reflectTimeZero f x) τ := by
    have h := differentiableAt_reflectTimeZero_of_Ico hf (x := x) hτ
    have hpath : DifferentiableAt ℝ (fun s : ℝ ↦ (x, s)) τ :=
      (differentiableAt_const x).prodMk differentiableAt_id
    exact h.comp τ hpath
  have h₁ := hslice.hasDerivAt.hasDerivWithinAt (s := Ici τ)
  have h₂ : HasDerivWithinAt (reflectTimeZero f x) (deriv (f x) τ) (Ici τ) τ :=
    hx.hasDerivAt.hasDerivWithinAt.congr_of_mem
      (fun s hs ↦ reflectTimeZero_of_nonneg f (hτ.1.trans hs)) self_mem_Ici
  exact (uniqueDiffWithinAt_Ici τ).eq_deriv _ h₁ h₂

end PDE.Analysis
