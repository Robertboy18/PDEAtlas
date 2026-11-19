/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.FaaDiBrunoBounds
public import PDE.Analysis.Calculus.HolderInterpolation
import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# `C^{n,α}` bounds on the closed half-plane and compositions

A map `f` on the plane has `C^{n,α}` bounds on the closed upper half-plane `H̄ = {y | 0 ≤ y 1}`
(`HasHolderBounds n f α M H N K`) if it is `C^n` within `H̄`, its derivatives within `H̄` of the
orders `1 ≤ j < n` are bounded by `M` and `α`-Hölder there with constant `H`, and its derivative
of order `n` is bounded by `N` and `α`-Hölder with constant `K`.

For `g ∘ f`, with `f` preserving `H̄` and `Lf`-Lipschitz there, the constants of the orders below
`n` depend only on those of `g` and `f` below `n`, and the two top-order constants are linear in
the top-order constants `N, K` of `g` and of `f`. The directional derivative `z ↦ Dθ(z) e` of a
map with bounds of order `n + 1` has bounds of order `n`.

## Main definitions

* `HasHolderBounds`: the `C^{n,α}` bounds `M, H` below the top order and `N, K` at order `n` on
  `H̄`.
* `compBound`, `compHolder`: the bound and the Hölder constant of the derivatives of a
  composition of the orders below `n`.
* `compTopBound`, `compTopHolder`: the bound and the Hölder constant of the derivative of order
  `n` of a composition.

## Main results

* `HasHolderBounds.comp`: for `n ≥ 2`, `g ∘ f` has `C^{n,α}` bounds with the constants
  `compBound`, `compHolder`, `compTopBound` and `compTopHolder`.
* `HasHolderBounds.fderivWithin_apply`: if `θ` has bounds of order `n + 1`, then `z ↦ Dθ(z) e` has
  bounds of order `n`.
* `HasHolderBounds.of_contDiff`: bounds of a `C^n` map of the plane from bounds of its
  derivatives at the points of `H̄`.
* `HasHolderBounds.of_lt`: bounds of order `n` give bounds of every order `1 ≤ j < n`.
* `compTopBound_inner_affine`: the top-order bound of a composition is affine in the top-order
  bound of the inner map.
* `compTopHolder_inner_affine`: the top-order Hölder constant of a composition is affine in the
  top-order constants of the inner map.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `C^{n,α}` bounds on the closed upper half-plane: `f` is `C^n` within `H̄`, its derivatives
within `H̄` of the orders `1 ≤ j < n` are bounded by `M` and `α`-Hölder with constant `H` on
`H̄`, and its derivative of order `n` is bounded by `N` and `α`-Hölder with constant `K`. -/
structure HasHolderBounds (n : ℕ) (f : ℝ^2 → F) (α M H N K : ℝ) : Prop where
  /-- `C^n` regularity within the closed half-plane. -/
  contDiffOn : ContDiffOn ℝ n f H̄
  /-- The bound of the derivatives of the orders below `n`. -/
  norm_le : ∀ j, 1 ≤ j → j < n → ∀ z : ℝ^2, 0 ≤ z 1 → ‖iteratedFDerivWithin ℝ j f H̄ z‖ ≤ M
  /-- The Hölder constant of the derivatives of the orders below `n`. -/
  holder : ∀ j, 1 ≤ j → j < n → ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
    ‖iteratedFDerivWithin ℝ j f H̄ z - iteratedFDerivWithin ℝ j f H̄ z'‖ ≤ H * ‖z - z'‖ ^ α
  /-- The bound of the derivative of order `n`. -/
  norm_top_le : ∀ z : ℝ^2, 0 ≤ z 1 → ‖iteratedFDerivWithin ℝ n f H̄ z‖ ≤ N
  /-- The Hölder constant of the derivative of order `n`. -/
  holder_top : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
    ‖iteratedFDerivWithin ℝ n f H̄ z - iteratedFDerivWithin ℝ n f H̄ z'‖ ≤ K * ‖z - z'‖ ^ α

/-- The sum `∑_{j < n} #(OrderedFinpartition j)`, a common bound of the numbers of ordered
finpartitions of the orders below `n`. -/
def finpartitionSum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (Fintype.card (OrderedFinpartition j) : ℝ)

/-- The bound of the derivatives of the orders below `n` of a composition. -/
def compBound (n : ℕ) (Mg Mf : ℝ) : ℝ :=
  Mg * Mf + Mg * max 1 Mf ^ n + finpartitionSum n * (Mg * max 1 Mf ^ n)

/-- The Hölder constant of the derivatives of the orders below `n` of a composition. -/
def compHolder (n : ℕ) (α Mg Hg Mf Hf Lf : ℝ) : ℝ :=
  Mg * Hf + Hg * Lf ^ α * Mf + (Mg * n * max 1 Mf ^ n * Hf + Hg * Lf ^ α * max 1 Mf ^ n) +
    finpartitionSum n * ((Mg * n * Hf + Hg * Lf ^ α) * max 1 Mf ^ n)

/-- The bound of the derivative of order `n` of a composition, linear in `Ng` and `Nf`. -/
def compTopBound (n : ℕ) (Mg Ng Mf Nf : ℝ) : ℝ :=
  Mg * Nf + Ng * Mf ^ n + Fintype.card (OrderedFinpartition n) * (Mg * max 1 Mf ^ n)

/-- The Hölder constant of the derivative of order `n` of a composition, linear in
`Ng, Kg, Nf, Kf`. -/
def compTopHolder (n : ℕ) (α Mg Hg Ng Kg Mf Hf Nf Kf Lf : ℝ) : ℝ :=
  Mg * Kf + Hg * Lf ^ α * Nf + (Ng * n * Mf ^ (n - 1) * Hf + Kg * Lf ^ α * Mf ^ n) +
    Fintype.card (OrderedFinpartition n) * ((Mg * n * Hf + Hg * Lf ^ α) * max 1 Mf ^ n)

/-- The top-order bound of a composition is affine in the top-order bound of the inner map. -/
theorem compTopBound_inner_affine (n : ℕ) (Mg Ng Mf a b Ψ : ℝ) :
    compTopBound n Mg Ng Mf (a + b * Ψ) = compTopBound n Mg Ng Mf a + Mg * b * Ψ := by
  unfold compTopBound; ring

/-- The top-order bound of a composition is affine in the top-order bound of the outer map. -/
theorem compTopBound_outer_affine (n : ℕ) (Mg Mf Nf a b Ψ : ℝ) :
    compTopBound n Mg (a + b * Ψ) Mf Nf = compTopBound n Mg a Mf Nf + b * Mf ^ n * Ψ := by
  unfold compTopBound; ring

/-- The top-order Hölder constant of a composition is affine in the top-order constants of the
inner map. -/
theorem compTopHolder_inner_affine (n : ℕ) (α Mg Hg Ng Kg Mf Hf Lf a b c d Ψ : ℝ) :
    compTopHolder n α Mg Hg Ng Kg Mf Hf (a + b * Ψ) (c + d * Ψ) Lf =
      compTopHolder n α Mg Hg Ng Kg Mf Hf a c Lf + (Mg * d + Hg * Lf ^ α * b) * Ψ := by
  unfold compTopHolder; ring

/-- The top-order Hölder constant of a composition is affine in the top-order constants of the
outer map. -/
theorem compTopHolder_outer_affine (n : ℕ) (α Mg Hg Mf Hf Nf Kf Lf a b c d Ψ : ℝ) :
    compTopHolder n α Mg Hg (a + b * Ψ) (c + d * Ψ) Mf Hf Nf Kf Lf =
      compTopHolder n α Mg Hg a c Mf Hf Nf Kf Lf +
        (b * n * Mf ^ (n - 1) * Hf + d * Lf ^ α * Mf ^ n) * Ψ := by
  unfold compTopHolder; ring

/-- The count `finpartitionSum n` is nonnegative. -/
theorem finpartitionSum_nonneg (n : ℕ) : 0 ≤ finpartitionSum n :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- For `j < n` the number of ordered finpartitions of `j` is at most `finpartitionSum n`. -/
theorem card_le_finpartitionSum {j n : ℕ} (hj : j < n) :
    (Fintype.card (OrderedFinpartition j) : ℝ) ≤ finpartitionSum n :=
  Finset.single_le_sum (f := fun i ↦ (Fintype.card (OrderedFinpartition i) : ℝ))
    (fun _ _ ↦ Nat.cast_nonneg _) (Finset.mem_range.mpr hj)

/-- For `0 ≤ M` and `i ≤ n`, `M ^ i ≤ max 1 M ^ n`. -/
theorem pow_le_max_one_pow {M : ℝ} (hM : 0 ≤ M) {i n : ℕ} (hin : i ≤ n) :
    M ^ i ≤ max 1 M ^ n :=
  (pow_le_pow_left₀ hM (le_max_right 1 M) i).trans (pow_le_pow_right₀ (le_max_left 1 M) hin)

/-- For `i ≤ n`, `max 1 M ^ i ≤ max 1 M ^ n`. -/
theorem max_one_pow_le {M : ℝ} {i n : ℕ} (hin : i ≤ n) : max 1 M ^ i ≤ max 1 M ^ n :=
  pow_le_pow_right₀ (le_max_left 1 M) hin

/-- On the closed half-plane the derivatives within it of a `C^n` map of the plane are its
derivatives. -/
theorem iteratedFDerivWithin_closedUpper_eq {f : ℝ^2 → F} {n : ℕ} (hf : ContDiff ℝ n f) {j : ℕ}
    (hj : j ≤ n) {z : ℝ^2} (hz : 0 ≤ z 1) :
    iteratedFDerivWithin ℝ j f H̄ z = iteratedFDeriv ℝ j f z :=
  iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_coordinateHalfSpace 1)
    ((hf.of_le (by exact_mod_cast hj)).contDiffAt) hz

/-- The unit normal `e₁` lies in the closed half-plane `H̄`. -/
private theorem single_mem : (0 : ℝ) ≤ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ^2) 1 := by
  simp

/-- `‖0 - e₁‖ ^ α = 1` for every exponent `α`. -/
private theorem norm_zero_sub_single_rpow (α : ℝ) :
    ‖(0 : ℝ^2) - EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ ^ α = 1 := by
  have h : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  rw [zero_sub, norm_neg, h, Real.one_rpow]

namespace HasHolderBounds

variable {n : ℕ} {f : ℝ^2 → F} {α M H N K : ℝ}

/-- For `n ≥ 2` the bound `M` of the derivatives of the orders below `n` is nonnegative. -/
theorem bound_nonneg (h : HasHolderBounds n f α M H N K) (hn : 2 ≤ n) : 0 ≤ M :=
  (norm_nonneg _).trans (h.norm_le 1 le_rfl (by omega) 0 (by simp))

/-- For `n ≥ 2` the Hölder constant `H` of the derivatives of the orders below `n` is
nonnegative. -/
theorem holder_nonneg (h : HasHolderBounds n f α M H N K) (hn : 2 ≤ n) : 0 ≤ H := by
  have h1 := h.holder 1 le_rfl (by omega) 0 _ (by simp) single_mem
  rw [norm_zero_sub_single_rpow, mul_one] at h1
  exact (norm_nonneg _).trans h1

/-- The bound `N` of the derivative of order `n` is nonnegative. -/
theorem top_nonneg (h : HasHolderBounds n f α M H N K) : 0 ≤ N :=
  (norm_nonneg _).trans (h.norm_top_le 0 (by simp))

/-- The Hölder constant `K` of the derivative of order `n` is nonnegative. -/
theorem holder_top_nonneg (h : HasHolderBounds n f α M H N K) : 0 ≤ K := by
  have h1 := h.holder_top 0 _ (by simp) single_mem
  rw [norm_zero_sub_single_rpow, mul_one] at h1
  exact (norm_nonneg _).trans h1

/-- Larger constants. -/
theorem mono (h : HasHolderBounds n f α M H N K) {M' H' N' K' : ℝ} (hM : M ≤ M') (hH : H ≤ H')
    (hN : N ≤ N') (hK : K ≤ K') : HasHolderBounds n f α M' H' N' K' where
  contDiffOn := h.contDiffOn
  norm_le j hj hjn z hz := (h.norm_le j hj hjn z hz).trans hM
  holder j hj hjn z z' hz hz' := (h.holder j hj hjn z z' hz hz').trans
    (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg _) α))
  norm_top_le z hz := (h.norm_top_le z hz).trans hN
  holder_top z z' hz hz' := (h.holder_top z z' hz hz').trans
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (norm_nonneg _) α))

/-- Bounds of order `n` give bounds of every order `1 ≤ j < n`. -/
theorem of_lt (h : HasHolderBounds n f α M H N K) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    HasHolderBounds j f α M H M H where
  contDiffOn := h.contDiffOn.of_le (by exact_mod_cast hjn.le)
  norm_le i hi hij := h.norm_le i hi (hij.trans hjn)
  holder i hi hij := h.holder i hi (hij.trans hjn)
  norm_top_le := h.norm_le j hj hjn
  holder_top := h.holder j hj hjn

/-- The bounds depend only on the values on the closed half-plane. -/
theorem congr (h : HasHolderBounds n f α M H N K) {g : ℝ^2 → F} (hfg : EqOn g f H̄) :
    HasHolderBounds n g α M H N K where
  contDiffOn := h.contDiffOn.congr fun y hy ↦ hfg hy
  norm_le j hj hjn z hz := by
    rw [iteratedFDerivWithin_congr hfg hz]; exact h.norm_le j hj hjn z hz
  holder j hj hjn z z' hz hz' := by
    rw [iteratedFDerivWithin_congr hfg hz, iteratedFDerivWithin_congr hfg hz']
    exact h.holder j hj hjn z z' hz hz'
  norm_top_le z hz := by rw [iteratedFDerivWithin_congr hfg hz]; exact h.norm_top_le z hz
  holder_top z z' hz hz' := by
    rw [iteratedFDerivWithin_congr hfg hz, iteratedFDerivWithin_congr hfg hz']
    exact h.holder_top z z' hz hz'

/-- Bounds of a `C^n` map of the plane from bounds of its derivatives at the points of the
closed half-plane. -/
theorem of_contDiff (hf : ContDiff ℝ n f)
    (hM : ∀ j, 1 ≤ j → j < n → ∀ z : ℝ^2, 0 ≤ z 1 → ‖iteratedFDeriv ℝ j f z‖ ≤ M)
    (hH : ∀ j, 1 ≤ j → j < n → ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDeriv ℝ j f z - iteratedFDeriv ℝ j f z'‖ ≤ H * ‖z - z'‖ ^ α)
    (hN : ∀ z : ℝ^2, 0 ≤ z 1 → ‖iteratedFDeriv ℝ n f z‖ ≤ N)
    (hK : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f z'‖ ≤ K * ‖z - z'‖ ^ α) :
    HasHolderBounds n f α M H N K where
  contDiffOn := hf.contDiffOn
  norm_le j hj hjn z hz := by
    rw [iteratedFDerivWithin_closedUpper_eq hf hjn.le hz]; exact hM j hj hjn z hz
  holder j hj hjn z z' hz hz' := by
    rw [iteratedFDerivWithin_closedUpper_eq hf hjn.le hz,
      iteratedFDerivWithin_closedUpper_eq hf hjn.le hz']
    exact hH j hj hjn z z' hz hz'
  norm_top_le z hz := by
    rw [iteratedFDerivWithin_closedUpper_eq hf le_rfl hz]; exact hN z hz
  holder_top z z' hz hz' := by
    rw [iteratedFDerivWithin_closedUpper_eq hf le_rfl hz,
      iteratedFDerivWithin_closedUpper_eq hf le_rfl hz']
    exact hK z z' hz hz'

/-- For `n ≥ 2` the derivative within `H̄` is bounded by `M` on `H̄`. -/
private theorem norm_fderivWithin_le (h : HasHolderBounds n f α M H N K) (hn : 2 ≤ n)
    {z : ℝ^2} (hz : 0 ≤ z 1) : ‖fderivWithin ℝ f H̄ z‖ ≤ M := by
  rw [← norm_iteratedFDerivWithin_one _ (uniqueDiffOn_coordinateHalfSpace 1 z hz)]
  exact h.norm_le 1 le_rfl (by omega) z hz

/-- For `n ≥ 2` the derivative within `H̄` is `α`-Hölder with constant `H` on `H̄`. -/
private theorem norm_fderivWithin_sub_le (h : HasHolderBounds n f α M H N K) (hn : 2 ≤ n)
    {z z' : ℝ^2} (hz : 0 ≤ z 1) (hz' : 0 ≤ z' 1) :
    ‖fderivWithin ℝ f H̄ z - fderivWithin ℝ f H̄ z'‖ ≤ H * ‖z - z'‖ ^ α := by
  rw [← norm_iteratedFDerivWithin_one_sub (uniqueDiffOn_coordinateHalfSpace 1 z hz)
    (uniqueDiffOn_coordinateHalfSpace 1 z' hz')]
  exact h.holder 1 le_rfl (by omega) z z' hz hz'

/-- For `n ≥ 2` the map is `M`-Lipschitz on the closed half-plane. -/
theorem norm_sub_le (h : HasHolderBounds n f α M H N K) (hn : 2 ≤ n) {z z' : ℝ^2}
    (hz : 0 ≤ z 1) (hz' : 0 ≤ z' 1) : ‖f z - f z'‖ ≤ M * ‖z - z'‖ :=
  convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderivWithin_le
    (h.contDiffOn.differentiableOn (by exact_mod_cast (show n ≠ 0 by omega)))
    (fun _ hy ↦ h.norm_fderivWithin_le hn hy) hz' hz

section Comp

variable {g : ℝ^2 → F} {f : ℝ^2 → ℝ^2} {Mg Hg Ng Kg Mf Hf Nf Kf Lf : ℝ}

/-- For `n ≥ 2` and `f` mapping `H̄` into itself, the derivative of order `n` within `H̄` of
`g ∘ f` is bounded on `H̄` by `compTopBound n Mg Ng Mf Nf`. -/
private theorem norm_top_comp_le (hg : HasHolderBounds n g α Mg Hg Ng Kg)
    (hf : HasHolderBounds n f α Mf Hf Nf Kf) (hmaps : MapsTo f H̄ H̄) (hn : 2 ≤ n) {z : ℝ^2}
    (hz : 0 ≤ z 1) : ‖iteratedFDerivWithin ℝ n (g ∘ f) H̄ z‖ ≤ compTopBound n Mg Ng Mf Nf := by
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  have hfz : 0 ≤ f z 1 := hmaps hz
  have hMg := hg.bound_nonneg hn
  have hMf := hf.bound_nonneg hn
  refine (norm_iteratedFDerivWithin_comp_le_add hg.contDiffOn hf.contDiffOn hU hU hmaps hz hn hMg
    (fun i hi hin ↦ hg.norm_le i (by omega) hin _ hfz)
    (fun j hj hjn ↦ hf.norm_le j hj hjn z hz)).trans ?_
  have h1 := hg.norm_fderivWithin_le hn hfz
  have h2 := hf.norm_fderivWithin_le hn hz
  unfold compTopBound
  gcongr
  · exact hf.norm_top_le z hz
  · exact hg.top_nonneg
  · exact hg.norm_top_le _ hfz

/-- **The bounds of a composition.** For `n ≥ 2`, if `g` and `f` have `C^{n,α}` bounds on the
closed half-plane, `f` preserves it and is `Lf`-Lipschitz there, then `g ∘ f` has `C^{n,α}`
bounds with the constants `compBound`, `compHolder` below the top order and `compTopBound`,
`compTopHolder` at the top order. -/
theorem comp (hg : HasHolderBounds n g α Mg Hg Ng Kg) (hf : HasHolderBounds n f α Mf Hf Nf Kf)
    (hmaps : MapsTo f H̄ H̄) (hLf : 0 ≤ Lf)
    (hfL : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 → ‖f z - f z'‖ ≤ Lf * ‖z - z'‖) (hn : 2 ≤ n)
    (hα : 0 ≤ α) :
    HasHolderBounds n (g ∘ f) α (compBound n Mg Mf) (compHolder n α Mg Hg Mf Hf Lf)
      (compTopBound n Mg Ng Mf Nf) (compTopHolder n α Mg Hg Ng Kg Mf Hf Nf Kf Lf) := by
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  have hMg := hg.bound_nonneg hn
  have hMf := hf.bound_nonneg hn
  have hHg := hg.holder_nonneg hn
  have hHf := hf.holder_nonneg hn
  have hS := finpartitionSum_nonneg n
  have hQ : 0 ≤ Mg * max 1 Mf ^ n := mul_nonneg hMg (pow_nonneg (by positivity) n)
  have hD (z : ℝ^2) (hz : 0 ≤ z 1) : fderivWithin ℝ (g ∘ f) H̄ z =
      (fderivWithin ℝ g H̄ (f z)).comp (fderivWithin ℝ f H̄ z) := by
    have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact fderivWithin_comp z (hg.contDiffOn.differentiableOn hn0 _ (hmaps hz))
      (hf.contDiffOn.differentiableOn hn0 z hz) hmaps (hU z hz)
  refine ⟨hg.contDiffOn.comp hf.contDiffOn hmaps, fun j hj hjn z hz ↦ ?_,
    fun j hj hjn z z' hz hz' ↦ ?_, fun z hz ↦ norm_top_comp_le hg hf hmaps hn hz,
    fun z z' hz hz' ↦ ?_⟩
  · rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
    · rw [norm_iteratedFDerivWithin_one _ (hU z hz), hD z hz]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
        (mul_le_mul (hg.norm_fderivWithin_le hn (hmaps hz)) (hf.norm_fderivWithin_le hn hz)
          (norm_nonneg _) hMg).trans ?_
      unfold compBound
      linarith [mul_nonneg hS hQ]
    · refine (norm_top_comp_le (hg.of_lt hj hjn) (hf.of_lt hj hjn) hmaps hj2 hz).trans ?_
      unfold compTopBound compBound
      gcongr
      · exact pow_le_max_one_pow hMf hjn.le
      · exact card_le_finpartitionSum hjn
      · exact le_max_left _ _
  · rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
    · rw [norm_iteratedFDerivWithin_one_sub (hU z hz) (hU z' hz'), hD z hz, hD z' hz']
      have hsplit : (fderivWithin ℝ g H̄ (f z)).comp (fderivWithin ℝ f H̄ z) -
          (fderivWithin ℝ g H̄ (f z')).comp (fderivWithin ℝ f H̄ z') =
          (fderivWithin ℝ g H̄ (f z)).comp (fderivWithin ℝ f H̄ z - fderivWithin ℝ f H̄ z') +
            (fderivWithin ℝ g H̄ (f z) - fderivWithin ℝ g H̄ (f z')).comp
              (fderivWithin ℝ f H̄ z') := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
        abel
      have h2 : ‖fderivWithin ℝ g H̄ (f z) - fderivWithin ℝ g H̄ (f z')‖ ≤
          Hg * Lf ^ α * ‖z - z'‖ ^ α := by
        refine (hg.norm_fderivWithin_sub_le hn (hmaps hz) (hmaps hz')).trans ?_
        rw [mul_assoc, ← Real.mul_rpow hLf (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
          (hfL z z' hz hz') hα) hHg
      have hd : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
      have h3 : 0 ≤ Mg * n * max 1 Mf ^ n * Hf + Hg * Lf ^ α * max 1 Mf ^ n := by positivity
      have h4 : 0 ≤ finpartitionSum n * ((Mg * n * Hf + Hg * Lf ^ α) * max 1 Mf ^ n) := by
        positivity
      rw [hsplit]
      refine (norm_add_le_of_le ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hg.norm_fderivWithin_le hn (hmaps hz)) (hf.norm_fderivWithin_sub_le hn hz hz')
          (norm_nonneg _) hMg)) ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul h2 (hf.norm_fderivWithin_le hn hz') (norm_nonneg _) (by positivity)))).trans ?_
      unfold compHolder
      linarith [mul_nonneg h3 hd, mul_nonneg h4 hd]
    · refine (norm_iteratedFDerivWithin_comp_sub_le_rpow_of_closedUpper
        (hg.of_lt hj hjn).contDiffOn (hf.of_lt hj hjn).contDiffOn hmaps hj2 hα hMg hHg hMg hHg hMf
        hHf hLf (fun i hi hij ↦ hg.norm_le i hi (hij.trans hjn))
        (fun i hi hij ↦ hg.holder i hi (hij.trans hjn)) (hg.norm_le j hj hjn)
        (hg.holder j hj hjn) (fun i hi hij ↦ hf.norm_le i hi (hij.trans hjn))
        (fun i hi hij ↦ hf.holder i hi (hij.trans hjn)) (hf.norm_le j hj hjn)
        (hf.holder j hj hjn) hfL hz hz').trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α)
      have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn.le
      unfold compHolder
      gcongr
      · exact pow_le_max_one_pow hMf (by omega)
      · exact pow_le_max_one_pow hMf hjn.le
      · exact card_le_finpartitionSum hjn
      · exact le_max_left _ _
  · exact norm_iteratedFDerivWithin_comp_sub_le_rpow_of_closedUpper hg.contDiffOn hf.contDiffOn
      hmaps hn hα hMg hHg hg.top_nonneg hg.holder_top_nonneg hMf hHf hLf hg.norm_le hg.holder
      hg.norm_top_le hg.holder_top hf.norm_le hf.holder hf.norm_top_le hf.holder_top hfL hz hz'

end Comp

/-- **The directional derivative.** If `θ` has `C^{n+1,α}` bounds on the closed half-plane, the
map `z ↦ Dθ(z) e`, with the derivative within the closed half-plane, has `C^{n,α}` bounds with
the constants multiplied by `‖e‖`. -/
theorem fderivWithin_apply {θ : ℝ^2 → F} (h : HasHolderBounds (n + 1) θ α M H N K) (e : ℝ^2) :
    HasHolderBounds n (fun z ↦ fderivWithin ℝ θ H̄ z e) α (‖e‖ * M) (‖e‖ * H) (‖e‖ * N)
      (‖e‖ * K) := by
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  set L : (ℝ^2 →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F e
  have hL : ‖L‖ ≤ ‖e‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg e) fun A ↦ by
    simpa [L, mul_comm] using A.le_opNorm e
  have hfun : (fun z ↦ fderivWithin ℝ θ H̄ z e) = L ∘ fderivWithin ℝ θ H̄ := by
    funext z; simp [L]
  have hd : ContDiffOn ℝ n (fderivWithin ℝ θ H̄) H̄ :=
    h.contDiffOn.fderivWithin hU (by push_cast; exact le_rfl)
  have heq (j : ℕ) (hj : j ≤ n) (z : ℝ^2) (hz : 0 ≤ z 1) :
      iteratedFDerivWithin ℝ j (fun z ↦ fderivWithin ℝ θ H̄ z e) H̄ z =
        L.compContinuousMultilinearMap (iteratedFDerivWithin ℝ j (fderivWithin ℝ θ H̄) H̄ z) := by
    rw [hfun]
    exact L.iteratedFDerivWithin_comp_left (hd z hz) hU hz (by exact_mod_cast hj)
  have hnorm (j : ℕ) (hj : j ≤ n) (z : ℝ^2) (hz : 0 ≤ z 1) :
      ‖iteratedFDerivWithin ℝ j (fun z ↦ fderivWithin ℝ θ H̄ z e) H̄ z‖ ≤
        ‖e‖ * ‖iteratedFDerivWithin ℝ (j + 1) θ H̄ z‖ := by
    rw [heq j hj z hz, ← norm_iteratedFDerivWithin_fderivWithin hU hz]
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have hsub (j : ℕ) (hj : j ≤ n) (z z' : ℝ^2) (hz : 0 ≤ z 1) (hz' : 0 ≤ z' 1) :
      ‖iteratedFDerivWithin ℝ j (fun z ↦ fderivWithin ℝ θ H̄ z e) H̄ z -
          iteratedFDerivWithin ℝ j (fun z ↦ fderivWithin ℝ θ H̄ z e) H̄ z'‖ ≤
        ‖e‖ * ‖iteratedFDerivWithin ℝ (j + 1) θ H̄ z - iteratedFDerivWithin ℝ (j + 1) θ H̄ z'‖ := by
    rw [heq j hj z hz, heq j hj z' hz', ← norm_iteratedFDerivWithin_fderivWithin_sub hU hz hz']
    have e' : L.compContinuousMultilinearMap
          (iteratedFDerivWithin ℝ j (fderivWithin ℝ θ H̄) H̄ z) -
        L.compContinuousMultilinearMap (iteratedFDerivWithin ℝ j (fderivWithin ℝ θ H̄) H̄ z') =
        L.compContinuousMultilinearMap (iteratedFDerivWithin ℝ j (fderivWithin ℝ θ H̄) H̄ z -
          iteratedFDerivWithin ℝ j (fderivWithin ℝ θ H̄) H̄ z') := by
      ext v; simp
    rw [e']
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have he := norm_nonneg e
  refine ⟨hfun ▸ L.contDiff.comp_contDiffOn hd, fun j hj hjn z hz ↦ ?_,
    fun j hj hjn z z' hz hz' ↦ ?_, fun z hz ↦ ?_, fun z z' hz hz' ↦ ?_⟩
  · exact (hnorm j hjn.le z hz).trans
      (mul_le_mul_of_nonneg_left (h.norm_le (j + 1) (by omega) (by omega) z hz) he)
  · exact (hsub j hjn.le z z' hz hz').trans ((mul_le_mul_of_nonneg_left
      (h.holder (j + 1) (by omega) (by omega) z z' hz hz') he).trans_eq (mul_assoc _ _ _).symm)
  · exact (hnorm n le_rfl z hz).trans (mul_le_mul_of_nonneg_left (h.norm_top_le z hz) he)
  · exact (hsub n le_rfl z z' hz hz').trans ((mul_le_mul_of_nonneg_left
      (h.holder_top z z' hz hz') he).trans_eq (mul_assoc _ _ _).symm)

end HasHolderBounds

end PDE.Analysis
