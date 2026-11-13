/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Module.Normalize
public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import PDE.Analysis.Calculus.CompositionBounds

/-!
# Derivative decay of symbol type at infinity

A function `f` on a real normed space has symbol decay of order `d ∈ ℤ` if it is smooth away
from the origin and, for every `k`, its `k`th derivative is bounded by a multiple of
`‖x‖ ^ (d - k)` outside the open unit ball. Each derivative gains one power of decay, as for
a function homogeneous of degree `d`.

Functions homogeneous of degree `d` and smooth away from the origin have symbol decay of order
`d`; in particular `‖x‖⁻¹`, the normalization `x / ‖x‖` and the identity. Sums, continuous linear
images and bilinear products (the orders add) preserve the class, a derivative lowers the order
by one, and a smooth map applied to a function of order zero with values in a compact set has
order zero. A function smooth away from the origin that agrees with one of order `d` outside a
ball has order `d`. A function homogeneous of degree `d` satisfies Euler's identity
`Df(x) x = d f(x)` wherever it is differentiable.
-/

@[expose] public section

open Set Filter
open scoped ContDiff Topology

namespace PDE.Analysis

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Symbol decay of order `d`: `f` is smooth away from the origin, and for every `k` its `k`th
derivative is bounded by a multiple of `‖x‖ ^ (d - k)` where `1 ≤ ‖x‖`. -/
structure HasSymbolDecay (d : ℤ) (f : E → F) : Prop where
  /-- The function is smooth away from the origin. -/
  contDiffOn : ContDiffOn ℝ ∞ f {0}ᶜ
  /-- Each derivative gains one power of decay outside the open unit ball. -/
  bound : ∀ k : ℕ, ∃ C, ∀ x : E, 1 ≤ ‖x‖ → ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖x‖ ^ (d - k)

namespace HasSymbolDecay

variable {d e : ℤ} {f g : E → F}

/-- A function with symbol decay is smooth at every point other than the origin. -/
theorem contDiffAt (hf : HasSymbolDecay d f) {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ f x :=
  hf.contDiffOn.contDiffAt (isOpen_compl_singleton.mem_nhds hx)

/-- The constants of the derivative bounds can be chosen nonnegative, for all orders at once. -/
theorem exists_bound_nonneg (hf : HasSymbolDecay d f) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ k (x : E), 1 ≤ ‖x‖ → ‖iteratedFDeriv ℝ k f x‖ ≤ C k * ‖x‖ ^ (d - k) := by
  choose C hC using hf.bound
  refine ⟨fun k ↦ max (C k) 0, fun k ↦ le_max_right _ _, fun k x hx ↦ (hC k x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg (norm_nonneg _) _)

/-- For a negative order `-m`, the derivative bounds read `‖D^k f x‖ ≤ C ‖x‖⁻¹ ^ (m + k)`. -/
theorem bound_inv_pow {m : ℕ} (hf : HasSymbolDecay (-(m : ℤ)) f) (k : ℕ) :
    ∃ C, ∀ x : E, 1 ≤ ‖x‖ → ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖x‖⁻¹ ^ (m + k) := by
  obtain ⟨C, hC⟩ := hf.bound k
  refine ⟨C, fun x hx ↦ ?_⟩
  have h : ‖x‖ ^ (-(m : ℤ) - k) = ‖x‖⁻¹ ^ (m + k) := by
    rw [show -(m : ℤ) - k = -((m + k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      inv_pow]
  rw [← h]
  exact hC x hx

/-- The order of symbol decay can be raised. -/
theorem mono (hf : HasSymbolDecay d f) (hde : d ≤ e) : HasSymbolDecay e f := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound_nonneg
  refine ⟨hf.contDiffOn, fun k ↦ ⟨C k, fun x hx ↦ (hC k x hx).trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hx (by omega)) (hC0 k)

/-- Symbol decay depends only on the values away from the origin. -/
theorem congr (hf : HasSymbolDecay d f) (hfg : ∀ x, x ≠ 0 → f x = g x) :
    HasSymbolDecay d g := by
  refine ⟨hf.contDiffOn.congr fun x hx ↦ (hfg x hx).symm, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hf.bound k
  refine ⟨C, fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have hev : f =ᶠ[𝓝 x] g := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx0] with y hy
    exact hfg y hy
  rw [← (hev.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hC x hx

/-- Sums preserve symbol decay. -/
theorem add (hf : HasSymbolDecay d f) (hg : HasSymbolDecay d g) :
    HasSymbolDecay d (fun x ↦ f x + g x) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun k ↦ ?_⟩
  obtain ⟨C₁, hC₁⟩ := hf.bound k
  obtain ⟨C₂, hC₂⟩ := hg.bound k
  refine ⟨C₁ + C₂, fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  change ‖iteratedFDeriv ℝ k (f + g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply ((hf.contDiffAt hx0).of_le (by simp))
    ((hg.contDiffAt hx0).of_le (by simp)), add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ x hx) (hC₂ x hx))

/-- Negation preserves symbol decay. -/
theorem neg (hf : HasSymbolDecay d f) : HasSymbolDecay d (fun x ↦ -f x) := by
  refine ⟨hf.contDiffOn.neg, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hf.bound k
  refine ⟨C, fun x hx ↦ ?_⟩
  change ‖iteratedFDeriv ℝ k (-f) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hC x hx

/-- Differences preserve symbol decay. -/
theorem sub (hf : HasSymbolDecay d f) (hg : HasSymbolDecay d g) :
    HasSymbolDecay d (fun x ↦ f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Finite sums preserve symbol decay. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, HasSymbolDecay d (f i)) : HasSymbolDecay d (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨contDiffOn_const, fun k ↦ ⟨0, fun x _ ↦ ?_⟩⟩
    simp only [Finset.sum_empty, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, zero_mul,
      le_refl]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A continuous linear image of a function with symbol decay has the same decay. -/
theorem clm_comp (L : F →L[ℝ] G) (hf : HasSymbolDecay d f) :
    HasSymbolDecay d (fun x ↦ L (f x)) := by
  refine ⟨L.contDiff.comp_contDiffOn hf.contDiffOn, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hf.bound k
  refine ⟨‖L‖ * C, fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have h := L.norm_iteratedFDeriv_comp_left (hf.contDiffAt hx0) (n := k) (by simp)
  rw [mul_assoc]
  exact h.trans (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg L))

/-- Constant multiples preserve symbol decay. -/
theorem const_smul (c : ℝ) (hf : HasSymbolDecay d f) : HasSymbolDecay d (fun x ↦ c • f x) :=
  hf.clm_comp (c • ContinuousLinearMap.id ℝ F)

/-- A bilinear product of functions with symbol decay of orders `d` and `e` has symbol decay of
order `d + e`. -/
theorem bilinear (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} (hf : HasSymbolDecay d f)
    (hg : HasSymbolDecay e g) : HasSymbolDecay (d + e) (fun x ↦ B (f x) (g x)) := by
  refine ⟨(B.contDiff.comp_contDiffOn hf.contDiffOn).clm_apply hg.contDiffOn, fun n ↦ ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := hf.exists_bound_nonneg
  obtain ⟨C₂, hC₂0, hC₂⟩ := hg.exists_bound_nonneg
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C₁ i * C₂ (n - i),
    fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have hxs : x ∈ ({0}ᶜ : Set E) := hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hB := B.norm_iteratedFDerivWithin_le_of_bilinear hf.contDiffOn hg.contDiffOn
    hopen.uniqueDiffOn hxs (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hopen hxs] at hB
  refine hB.trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦ ?_) (norm_nonneg B)
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : ‖x‖ ^ (d - (i : ℤ)) * ‖x‖ ^ (e - ((n - i : ℕ) : ℤ)) = ‖x‖ ^ (d + e - n) := by
    rw [← zpow_add₀ hpos.ne']
    congr 1
    push_cast [Nat.cast_sub hin]
    ring
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
      ≤ (n.choose i : ℝ) * (C₁ i * ‖x‖ ^ (d - (i : ℤ))) *
          (C₂ (n - i) * ‖x‖ ^ (e - ((n - i : ℕ) : ℤ))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hC₁ i x hx) (Nat.cast_nonneg _))
          (hC₂ (n - i) x hx) (norm_nonneg _) ?_
        exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC₁0 i) (zpow_nonneg (norm_nonneg _) _))
    _ = (n.choose i : ℝ) * C₁ i * C₂ (n - i) * ‖x‖ ^ (d + e - n) := by
        rw [← hpow]
        ring

/-- A scalar function of order `d` times a vector function of order `e` has order `d + e`. -/
theorem smul {a : E → ℝ} {g : E → G} (ha : HasSymbolDecay d a) (hg : HasSymbolDecay e g) :
    HasSymbolDecay (d + e) (fun x ↦ a x • g x) :=
  ha.bilinear (ContinuousLinearMap.lsmul ℝ ℝ) hg

/-- A product of scalar functions of orders `d` and `e` has order `d + e`. -/
theorem mul {a b : E → ℝ} (ha : HasSymbolDecay d a) (hb : HasSymbolDecay e b) :
    HasSymbolDecay (d + e) (fun x ↦ a x * b x) :=
  ha.bilinear (ContinuousLinearMap.mul ℝ ℝ) hb

/-- Applying a function with values in continuous linear maps to one with values in their
domain multiplies symbol decay. -/
theorem clm_apply {A : E → F →L[ℝ] G} {g : E → F} (hA : HasSymbolDecay d A)
    (hg : HasSymbolDecay e g) : HasSymbolDecay (d + e) (fun x ↦ A x (g x)) :=
  hA.bilinear (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) hg

/-- Differentiation lowers the order of symbol decay by one. -/
theorem fderiv (hf : HasSymbolDecay d f) : HasSymbolDecay (d - 1) (fderiv ℝ f) := by
  refine ⟨hf.contDiffOn.fderiv_of_isOpen isOpen_compl_singleton
    (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp), fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hf.bound (k + 1)
  refine ⟨C, fun x hx ↦ ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  convert hC x hx using 3
  push_cast
  ring

/-- A smooth function of a function of order zero with values in a compact set has order zero
outside the unit ball. -/
theorem comp {g : E → F} {Φ : F → G} (hΦ : ContDiff ℝ ∞ Φ) (hg : HasSymbolDecay 0 g)
    {K : Set F} (hK : IsCompact K) (hgK : ∀ x, 1 ≤ ‖x‖ → g x ∈ K) :
    HasSymbolDecay 0 (fun x ↦ Φ (g x)) := by
  refine ⟨hΦ.comp_contDiffOn hg.contDiffOn, fun n ↦ ?_⟩
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_nonneg
  have hcont : ContinuousOn
      (fun y ↦ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i Φ y‖) K :=
    (continuous_finsetSum _ fun i _ ↦
      (hΦ.continuous_iteratedFDeriv (by simp)).norm).continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  set D₀ : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), C i with hD₀
  have hD₀1 : 1 ≤ D₀ := by
    rw [hD₀]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range (n + 1)) ↦ hC0 i]
  refine ⟨n.factorial * B * D₀ ^ n, fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hbound := norm_iteratedFDeriv_comp_le_of_contDiffAt (𝕜 := ℝ) (n := n)
    (B := B) (D := D₀ * ‖x‖⁻¹)
    ((hg.contDiffAt hx0).of_le (by simp)) (hΦ.contDiffAt.of_le (by simp))
    (fun i hi ↦ by
      have hsum := hB (g x) (hgK x hx)
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at hsum
      exact (Finset.single_le_sum (f := fun i ↦ ‖iteratedFDeriv ℝ i Φ (g x)‖)
        (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans hsum)
    (fun i hi hin ↦ by
      refine (hC i x hx).trans ?_
      have hCi : C i ≤ D₀ := by
        rw [hD₀]
        have := Finset.single_le_sum (f := C) (fun j _ ↦ hC0 j)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
        linarith
      rw [mul_pow, zero_sub, zpow_neg, zpow_natCast, inv_pow]
      exact mul_le_mul_of_nonneg_right (hCi.trans (le_self_pow₀ hD₀1 (by omega)))
        (by positivity))
  refine hbound.trans (le_of_eq ?_)
  rw [mul_pow, zero_sub, zpow_neg, zpow_natCast, inv_pow]
  ring

/-- A function smooth away from the origin that agrees with a function of symbol decay of
order `d` outside a ball has symbol decay of order `d`. -/
theorem of_eqOn_far [FiniteDimensional ℝ E] (hg : HasSymbolDecay d g)
    (hf : ContDiffOn ℝ ∞ f {0}ᶜ) {R : ℝ} (hfg : ∀ x, R < ‖x‖ → f x = g x) :
    HasSymbolDecay d f := by
  refine ⟨hf, fun k ↦ ?_⟩
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_nonneg
  set ρ : ℝ := max R 1 + 1 with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ]; linarith [le_max_right R 1]
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) ({0}ᶜ : Set E) :=
    (hf.continuousOn_iteratedFDerivWithin (by simp) hopen.uniqueDiffOn).congr
      fun x hx ↦ (iteratedFDerivWithin_of_isOpen k hopen hx).symm
  set K : Set E := Metric.closedBall 0 ρ ∩ {x | 1 ≤ ‖x‖} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 ρ).inter_right (isClosed_le continuous_const continuous_norm)
  have hKs : K ⊆ ({0}ᶜ : Set E) := fun x hx h0 ↦ by
    rw [Set.mem_singleton_iff] at h0
    have := hx.2
    simp only [Set.mem_ofPred_eq, h0, norm_zero] at this
    linarith
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKs)
  set e : ℤ := d - k
  set m : ℝ := (ρ ^ e.natAbs)⁻¹ with hm
  have hmpos : 0 < m := by positivity
  refine ⟨max (C k) (max B 0 / m), fun x hx ↦ ?_⟩
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx
  by_cases hxρ : ‖x‖ ≤ ρ
  · have hxK : x ∈ K := ⟨by rwa [Metric.mem_closedBall, dist_zero_right], hx⟩
    have hlow : m ≤ ‖x‖ ^ e := by
      calc m ≤ (‖x‖ ^ e.natAbs)⁻¹ :=
            inv_anti₀ (pow_pos hx0 _) (pow_le_pow_left₀ hx0.le hxρ _)
        _ = ‖x‖ ^ (-(e.natAbs : ℤ)) := by rw [zpow_neg, zpow_natCast]
        _ ≤ ‖x‖ ^ e := zpow_le_zpow_right₀ hx (by omega)
    calc ‖iteratedFDeriv ℝ k f x‖ ≤ max B 0 := (hB x hxK).trans (le_max_left _ _)
      _ = max B 0 / m * m := by field_simp
      _ ≤ max B 0 / m * ‖x‖ ^ e :=
          mul_le_mul_of_nonneg_left hlow (div_nonneg (le_max_right _ _) hmpos.le)
      _ ≤ max (C k) (max B 0 / m) * ‖x‖ ^ e :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_nonneg (norm_nonneg _) _)
  · have hRx : R < ‖x‖ := by
      rw [not_le, hρ] at hxρ
      linarith [le_max_left R 1]
    have hev : f =ᶠ[𝓝 x] g := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hRx] with y hy
      exact hfg y hy
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hC k x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg (norm_nonneg _) _))

end HasSymbolDecay

/-- A coordinate partial derivative lowers the order of symbol decay by one. -/
theorem HasSymbolDecay.partialDeriv {n : ℕ} {d : ℤ} {f : ℝ^n → F} (hf : HasSymbolDecay d f)
    (i : Fin n) : HasSymbolDecay (d - 1) (∂[i] f) :=
  hf.fderiv.clm_comp (ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i (1 : ℝ)))

/-- The coordinate Laplacian lowers the order of symbol decay by two. -/
theorem HasSymbolDecay.laplacian {n : ℕ} {d : ℤ} {f : ℝ^n → F} (hf : HasSymbolDecay d f) :
    HasSymbolDecay (d - 2) (PDE.laplacian f) := by
  have h := HasSymbolDecay.sum Finset.univ fun i _ ↦ (hf.partialDeriv i).partialDeriv i
  exact (h.mono (by omega)).congr fun x _ ↦ rfl

/-- A function homogeneous of degree `d`, `f (c • x) = c ^ d • f x` for `c > 0`, and smooth away
from the origin of a finite-dimensional space has symbol decay of order `d`. -/
theorem hasSymbolDecay_of_homogeneous [FiniteDimensional ℝ E] {d : ℤ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f {0}ᶜ) (hhom : ∀ x (c : ℝ), 0 < c → f (c • x) = c ^ d • f x) :
    HasSymbolDecay d f := by
  refine ⟨hf, fun k ↦ ?_⟩
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) ({0}ᶜ : Set E) :=
    (hf.continuousOn_iteratedFDerivWithin (by simp) hopen.uniqueDiffOn).congr
      fun x hx ↦ (iteratedFDerivWithin_of_isOpen k hopen hx).symm
  have hsub : Metric.sphere (0 : E) 1 ⊆ ({0}ᶜ : Set E) := fun y hy h0 ↦ by
    rw [Set.mem_singleton_iff] at h0
    simp [h0] at hy
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨C, fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  set c : ℝ := ‖x‖ with hc
  have hcpos : 0 < c := norm_pos_iff.mpr hx0
  set y : E := c⁻¹ • x with hy
  have hyx : c • y = x := by rw [hy, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
  have hy1 : y ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, hy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hcpos.le),
      ← hc, inv_mul_cancel₀ hcpos.ne']
  have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hy1
  let u : ℝˣ := Units.mk0 c hcpos.ne'
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft u
  have hL : ∀ z, L z = c • z := fun z ↦ rfl
  have hcomp : f ∘ L = fun z ↦ c ^ d • f z := funext fun z ↦ by
    simp only [Function.comp_apply, hL, hhom z c hcpos]
  have hright : iteratedFDeriv ℝ k (f ∘ L) y =
      (iteratedFDeriv ℝ k f (L y)).compContinuousLinearMap fun _ ↦ (L : E →L[ℝ] E) := by
    simpa only [iteratedFDerivWithin_univ, Set.preimage_univ] using
      L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (L y)) k
  have hscale : (iteratedFDeriv ℝ k f (L y)).compContinuousLinearMap
      (fun _ ↦ (L : E →L[ℝ] E)) = c ^ k • iteratedFDeriv ℝ k f (L y) := by
    ext v
    have hmul := (iteratedFDeriv ℝ k f (L y)).map_smul_univ (fun _ ↦ c) v
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmul
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, hL] at hmul ⊢
    rw [hmul]
    rfl
  have hleft : iteratedFDeriv ℝ k (fun z ↦ c ^ d • f z) y =
      c ^ d • iteratedFDeriv ℝ k f y :=
    iteratedFDeriv_const_smul_apply' ((hf.contDiffAt (hopen.mem_nhds hy0)).of_le (by simp))
  have hkey : c ^ k • iteratedFDeriv ℝ k f x = c ^ d • iteratedFDeriv ℝ k f y := by
    rw [← hleft, ← hcomp, hright, hscale, hL, hyx]
  have hnorm : ‖iteratedFDeriv ℝ k f x‖ = c ^ (d - k) * ‖iteratedFDeriv ℝ k f y‖ := by
    have h := congrArg norm hkey
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg hcpos.le _),
      Real.norm_of_nonneg (zpow_nonneg hcpos.le _)] at h
    rw [zpow_sub₀ hcpos.ne', zpow_natCast, div_mul_eq_mul_div, ← h]
    field_simp
  rw [hnorm, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC y hy1) (zpow_nonneg hcpos.le _)

/-- Euler's identity: a function homogeneous of degree `d` satisfies `Df(x) x = d f(x)` at every
point where it is differentiable. -/
theorem fderiv_apply_self_of_homogeneous {d : ℤ} {f : E → F}
    (hhom : ∀ x (c : ℝ), 0 < c → f (c • x) = c ^ d • f x) {x : E}
    (hx : DifferentiableAt ℝ f x) : fderiv ℝ f x x = (d : ℝ) • f x := by
  have h := hx.hasFDerivAt.apply_self_eq_smul_of_eventuallyEq
    (by simpa using hasDerivAt_zpow d (1 : ℝ) (Or.inl one_ne_zero))
    (by filter_upwards [Ioi_mem_nhds one_pos] with c hc using hhom x c hc)
  simpa using h

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The inverse norm has symbol decay of order `-1`. -/
theorem hasSymbolDecay_inv_norm : HasSymbolDecay (-1) (fun x : V ↦ ‖x‖⁻¹) := by
  refine hasSymbolDecay_of_homogeneous (fun x hx ↦ ?_) fun x c hc ↦ ?_
  · exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).contDiffWithinAt
  · rw [norm_smul, Real.norm_of_nonneg hc.le, mul_inv, zpow_neg_one, smul_eq_mul]

/-- The normalization `x / ‖x‖` has symbol decay of order zero. -/
theorem hasSymbolDecay_normalize : HasSymbolDecay 0 (NormedSpace.normalize : V → V) := by
  refine hasSymbolDecay_of_homogeneous (fun x hx ↦ ?_) fun x c hc ↦ ?_
  · exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul
      contDiffAt_id).contDiffWithinAt
  · rw [NormedSpace.normalize_smul_of_pos hc, zpow_zero, one_smul]

/-- A smooth function of the inverse norm has symbol decay of order zero. -/
theorem hasSymbolDecay_comp_inv_norm {Φ : ℝ → F} (hΦ : ContDiff ℝ ∞ Φ) :
    HasSymbolDecay 0 (fun x : V ↦ Φ ‖x‖⁻¹) :=
  HasSymbolDecay.comp hΦ (hasSymbolDecay_inv_norm.mono (by norm_num)) isCompact_Icc
    (K := Icc 0 1) fun x hx ↦ ⟨inv_nonneg.mpr (norm_nonneg x), inv_le_one_of_one_le₀ hx⟩

/-- A smooth function of the normalized point has symbol decay of order zero. -/
theorem hasSymbolDecay_comp_normalize {K : V → F} (hK : ContDiff ℝ ∞ K) :
    HasSymbolDecay 0 (fun x : V ↦ K (NormedSpace.normalize x)) := by
  refine HasSymbolDecay.comp hK hasSymbolDecay_normalize (isCompact_closedBall (0 : V) 1)
    fun x hx ↦ ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  rw [Metric.mem_closedBall, dist_zero_right, NormedSpace.norm_normalize hx0]

end InnerProduct

/-- The identity has symbol decay of order one. -/
theorem hasSymbolDecay_id [FiniteDimensional ℝ E] : HasSymbolDecay 1 (fun x : E ↦ x) :=
  hasSymbolDecay_of_homogeneous contDiffOn_id fun x c _ ↦ by rw [zpow_one]

/-- Constants have symbol decay of order zero. -/
theorem hasSymbolDecay_const [FiniteDimensional ℝ E] (v : F) :
    HasSymbolDecay 0 (fun _ : E ↦ v) :=
  hasSymbolDecay_of_homogeneous contDiffOn_const fun _ _ _ ↦ by rw [zpow_zero, one_smul]

end PDE.Analysis
