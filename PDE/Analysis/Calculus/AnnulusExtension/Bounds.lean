/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import PDE.Analysis.Calculus.AnnulusExtension.Basic
public import PDE.Analysis.MeasureTheory.LeftInverseChange

/-!
# Bounds for the extension from the annulus

The extension `annulusExtension v` of a `C²` function `v` is controlled order by order: for
`k ≤ 2`, the `L²` norm over the whole space of its `k`-th derivative is at most a constant times
the `L²` norms over the open annulus `1 < |y| < 2` of the derivatives of `v` of order at most `k`.
So the bound for the first derivatives does not involve the second derivatives of `v`, which is
what Agmon's inequality on the annulus needs (it applies the bound with `k = 1` and `k = 2`). The
constant is not explicit: the derivatives of the reflection maps are bounded by compactness.

## Main results

* `exists_lintegral_iteratedFDeriv_annulusExtension_le`: on every finite-dimensional real inner
  product space and for every `k ≤ 2` there is `C` such that, for every `C²` function `v`,
  `∫ |Dᵏ (annulusExtension v)|² ≤ C ∑_{i ≤ k} ∫_{1 < |y| < 2} |Dⁱ v|²`.
* `exists_lintegral_collar_le`: the same bound on a collar of one of the two spheres
  (`IsReflectionCollar`), for the cut-off reflection across that sphere.

## How it works

In the annulus the extension is `v`. In the collar `3/4 < |y| < 1` it is a cutoff times a
combination of `v ∘ Φⱼ`, where `Φⱼ(y) = y + tⱼ q(y)` maps the collar into the annulus. The chain
rule and the Leibniz rule bound its `k`-th derivative at `y` by the derivatives of `v` of order
at most `k` at the three points `Φⱼ(y)` (`norm_iteratedFDeriv_smul_reflectionSum_le`). Each `Φⱼ`
has a smooth left inverse, the reflection with the node `tⱼ/(tⱼ - 1)`, so `∫ g ∘ Φⱼ` over the
collar is at most a constant times `∫ g` over the annulus (`lintegral_comp_le_of_leftInverse`).
The outer collar `2 < |y| < 9/4` is treated the same way, and outside the two collars the
extension vanishes. The four spheres between the regions are null sets.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology ContDiff ENNReal NNReal Nat

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The open annulus `1 < |y| < 2`. -/
def unitAnnulus (E : Type*) [NormedAddCommGroup E] : Set E := {y | 1 < ‖y‖ ∧ ‖y‖ < 2}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The annulus `1 < |y| < 2` is open. -/
theorem isOpen_unitAnnulus : IsOpen (unitAnnulus E) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-! ## The reflection maps on a collar -/

/-- The three nodes lie in `(1, 4]`. -/
theorem reflNode_bounds (j : Fin 3) : 1 < reflNode j ∧ reflNode j ≤ 4 := by
  fin_cases j <;> simp [reflNode] <;> norm_num

/-- The three coefficients are at most `8` in absolute value. -/
theorem abs_reflCoeff_le (j : Fin 3) : |reflCoeff j| ≤ 8 := by
  fin_cases j <;> simp [reflCoeff] <;> norm_num

/-- The norm of a shifted point, away from the origin. -/
theorem norm_add_smul_sphereShift {R t : ℝ} {y : E} (hy : 1 / 2 ≤ ‖y‖)
    (ht : 0 ≤ (1 - t) * ‖y‖ + t * R) :
    ‖y + t • sphereShift R y‖ = (1 - t) * ‖y‖ + t * R := by
  have hy0 : 0 < ‖y‖ := by linarith
  have ha : (1 - t) + t * R * ‖y‖⁻¹ = ((1 - t) * ‖y‖ + t * R) / ‖y‖ := by field_simp
  rw [add_smul_sphereShift t hy, norm_smul, Real.norm_eq_abs, ha,
    abs_of_nonneg (div_nonneg ht hy0.le), div_mul_cancel₀ _ hy0.ne']

/-- The reflection with the node `t/(t - 1)` undoes the reflection with the node `t`. -/
theorem add_smul_sphereShift_leftInverse {R t : ℝ} (ht : 1 < t) {y : E} (hy : 1 / 2 ≤ ‖y‖)
    (hρ : 1 / 2 ≤ (1 - t) * ‖y‖ + t * R) :
    (y + t • sphereShift R y) + (t / (t - 1)) • sphereShift R (y + t • sphereShift R y) = y := by
  have hy0 : 0 < ‖y‖ := by linarith
  have hnorm := norm_add_smul_sphereShift hy (by linarith : 0 ≤ (1 - t) * ‖y‖ + t * R)
  have hρ0 : (1 - t) * ‖y‖ + t * R ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hs : ((1 - t / (t - 1)) + t / (t - 1) * R * ((1 - t) * ‖y‖ + t * R)⁻¹) *
      ((1 - t) + t * R * ‖y‖⁻¹) = 1 := by
    field_simp
    ring
  rw [add_smul_sphereShift (t / (t - 1)) (hnorm ▸ hρ), hnorm, add_smul_sphereShift t hy, smul_smul,
    hs, one_smul]

/-- A collar of the sphere of radius `R`: an open set away from the origin and inside the ball
of radius three, whose points are sent into the open annulus by the three reflections. -/
structure IsReflectionCollar (R : ℝ) (K : Set E) : Prop where
  /-- The collar is open. -/
  isOpen : IsOpen K
  /-- The collar lies in the ball of radius three. -/
  subset_closedBall : K ⊆ closedBall 0 3
  /-- The collar stays away from the origin. -/
  le_norm : ∀ y ∈ K, 1 / 2 ≤ ‖y‖
  /-- The norm of each reflected point, `(1 - tⱼ) |y| + tⱼ R`, lies in `(1, 2)`. -/
  mem_Ioo : ∀ y ∈ K, ∀ j, (1 - reflNode j) * ‖y‖ + reflNode j * R ∈ Ioo (1 : ℝ) 2

/-- The three reflections send a collar into the open annulus. -/
theorem IsReflectionCollar.mem_unitAnnulus {R : ℝ} {K : Set E} (hK : IsReflectionCollar R K)
    {y : E} (hy : y ∈ K) (j : Fin 3) : y + reflNode j • sphereShift R y ∈ unitAnnulus E := by
  have h := hK.mem_Ioo y hy j
  rw [unitAnnulus, mem_ofPred_eq, norm_add_smul_sphereShift (hK.le_norm y hy) (by linarith [h.1])]
  exact h

/-- On a collar, the reflection with the node `tⱼ/(tⱼ - 1)` undoes the reflection with the node
`tⱼ`. -/
theorem IsReflectionCollar.leftInverse {R : ℝ} {K : Set E} (hK : IsReflectionCollar R K)
    {y : E} (hy : y ∈ K) (j : Fin 3) :
    (y + reflNode j • sphereShift R y) + (reflNode j / (reflNode j - 1)) •
      sphereShift R (y + reflNode j • sphereShift R y) = y :=
  add_smul_sphereShift_leftInverse (reflNode_bounds j).1 (hK.le_norm y hy)
    (by linarith [(hK.mem_Ioo y hy j).1])

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The collar `3/4 < |y| < 1` of the unit sphere. -/
theorem isReflectionCollar_inner :
    IsReflectionCollar 1 {y : E | 3 / 4 < ‖y‖ ∧ ‖y‖ < 1} where
  isOpen := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  subset_closedBall y hy := mem_closedBall_zero_iff.2 (by linarith [hy.2])
  le_norm y hy := by linarith [hy.1]
  mem_Ioo y hy j := by
    obtain ⟨h1, h4⟩ := reflNode_bounds j
    obtain ⟨hy1, hy2⟩ := hy
    constructor <;> nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The collar `2 < |y| < 9/4` of the sphere of radius two. -/
theorem isReflectionCollar_outer :
    IsReflectionCollar 2 {y : E | 2 < ‖y‖ ∧ ‖y‖ < 9 / 4} where
  isOpen := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  subset_closedBall y hy := mem_closedBall_zero_iff.2 (by linarith [hy.2])
  le_norm y hy := by linarith [hy.1]
  mem_Ioo y hy j := by
    obtain ⟨h1, h4⟩ := reflNode_bounds j
    obtain ⟨hy1, hy2⟩ := hy
    constructor <;> nlinarith

/-! ## Bounds by compactness -/

/-- The first and second derivatives of finitely many shift maps `z ↦ z + τⱼ q_R(z)` are bounded
on the ball of radius three. -/
theorem exists_bound_iteratedFDeriv_shiftMap (R : ℝ) (τ : Fin 3 → ℝ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ j, ∀ y ∈ closedBall (0 : E) 3, ∀ i, 1 ≤ i → i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fun z ↦ z + τ j • sphereShift R z) y‖ ≤ D := by
  have hΦ (j : Fin 3) : ContDiff ℝ ∞ (fun z : E ↦ z + τ j • sphereShift R z) :=
    contDiff_id.add ((contDiff_sphereShift R).const_smul (τ j))
  have hcont : Continuous fun y : E ↦ ∑ j, ∑ i ∈ Finset.Icc 1 2,
      ‖iteratedFDeriv ℝ i (fun z ↦ z + τ j • sphereShift R z) y‖ :=
    continuous_finsetSum _ fun j _ ↦ continuous_finsetSum _ fun i _ ↦
      ((hΦ j).continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) 3).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 1 B, le_max_left _ _, fun j y hy i hi1 hi2 ↦ le_trans ?_ (le_max_right _ _)⟩
  refine le_trans ?_ ((le_abs_self _).trans (hB y hy))
  refine le_trans ?_ (Finset.single_le_sum (f := fun j ↦ ∑ i ∈ Finset.Icc 1 2,
    ‖iteratedFDeriv ℝ i (fun z ↦ z + τ j • sphereShift R z) y‖)
    (fun j _ ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _) (Finset.mem_univ j))
  exact Finset.single_le_sum (f := fun i ↦
    ‖iteratedFDeriv ℝ i (fun z ↦ z + τ j • sphereShift R z) y‖) (fun i _ ↦ norm_nonneg _)
    (Finset.mem_Icc.2 ⟨hi1, hi2⟩)

/-- The derivatives of order at most two of the annular cutoff are bounded. -/
theorem exists_bound_iteratedFDeriv_annulusCut :
    ∃ C : ℝ, ∀ i ≤ 2, ∀ y : E, ‖iteratedFDeriv ℝ i (annulusCut (E := E)) y‖ ≤ C := by
  have h (i : ℕ) : ∃ C : ℝ, ∀ y : E, ‖iteratedFDeriv ℝ i (annulusCut (E := E)) y‖ ≤ C :=
    (contDiff_annulusCut.continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support
      (hasCompactSupport_annulusCut.iteratedFDeriv i)
  choose C hC using h
  refine ⟨|C 0| + |C 1| + |C 2|, fun i hi y ↦ ?_⟩
  have h0 := abs_nonneg (C 0)
  have h1 := abs_nonneg (C 1)
  have h2 := abs_nonneg (C 2)
  interval_cases i
  · exact (hC 0 y).trans (by linarith [le_abs_self (C 0)])
  · exact (hC 1 y).trans (by linarith [le_abs_self (C 1)])
  · exact (hC 2 y).trans (by linarith [le_abs_self (C 2)])

/-! ## The pointwise bound in a collar -/

omit [FiniteDimensional ℝ E] in
/-- The Leibniz rule and the chain rule for a cutoff times a reflection sum: the `k`-th derivative
at `y`, `k ≤ 2`, is bounded by the derivatives of `v` of order at most `k` at the reflected
points. -/
theorem norm_iteratedFDeriv_smul_reflectionSum_le {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) {Cψ : ℝ}
    (hCψ : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ Cψ) {q : E → E} (hq : ContDiff ℝ 2 q)
    {D : ℝ} (hD1 : 1 ≤ D) {y : E}
    (hD : ∀ j : Fin 3, ∀ i, 1 ≤ i → i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fun z ↦ z + reflNode j • q z) y‖ ≤ D)
    {v : E → F} (hv : ContDiff ℝ 2 v) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun z ↦ ψ z • reflectionSum Finset.univ reflCoeff reflNode q v z) y‖ ≤
      192 * Cψ * D ^ 2 * ∑ j : Fin 3, ∑ i ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖ := by
  set S : ℝ := ∑ j : Fin 3, ∑ i ∈ Finset.range (k + 1),
    ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0 (by norm_num) y)
  have hΦ (j : Fin 3) : ContDiff ℝ 2 (fun z : E ↦ z + reflNode j • q z) :=
    contDiff_id.add (hq.const_smul (reflNode j))
  have hcomp (j : Fin 3) : ContDiff ℝ 2 (fun z : E ↦ v (z + reflNode j • q z)) := hv.comp (hΦ j)
  have hrefl : ContDiff ℝ 2 (reflectionSum Finset.univ reflCoeff reflNode q v) := by
    change ContDiff ℝ 2 (fun z : E ↦ ∑ j, reflCoeff j • v (z + reflNode j • q z))
    exact ContDiff.sum fun j _ ↦ (hcomp j).const_smul (reflCoeff j)
  -- the chain rule, for each derivative of the reflection sum of order at most `k`
  have hm (m : ℕ) (hmk : m ≤ k) :
      ‖iteratedFDeriv ℝ m (reflectionSum Finset.univ reflCoeff reflNode q v) y‖ ≤
        16 * D ^ 2 * S := by
    have hm2 : (m : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hmk.trans hk
    have e : iteratedFDeriv ℝ m (reflectionSum Finset.univ reflCoeff reflNode q v) y =
        ∑ j, iteratedFDeriv ℝ m (fun z ↦ reflCoeff j • v (z + reflNode j • q z)) y :=
      iteratedFDeriv_fun_sum_apply fun j _ ↦ (((hcomp j).const_smul (reflCoeff j)).of_le
        hm2).contDiffAt
    rw [e]
    refine (norm_sum_le _ _).trans ?_
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hc := norm_iteratedFDeriv_comp_le hv (hΦ j) hm2 y
      (C := ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖) (D := D)
      (fun i hi ↦ Finset.single_le_sum (f := fun i ↦
        ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_range.2 (by omega)))
      (fun i hi1 hi2 ↦ (hD j i hi1 (hi2.trans (hmk.trans hk))).trans
        (le_self_pow₀ hD1 (by omega)))
    have hfac : (m ! : ℝ) ≤ 2 := by
      have := Nat.factorial_le (hmk.trans hk)
      exact_mod_cast this
    have hpow : D ^ m ≤ D ^ 2 := pow_le_pow_right₀ hD1 (hmk.trans hk)
    have hC0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖ :=
      Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    rw [iteratedFDeriv_const_smul_apply' ((hcomp j).of_le hm2).contDiffAt, norm_smul,
      Real.norm_eq_abs]
    calc |reflCoeff j| * ‖iteratedFDeriv ℝ m (fun z ↦ v (z + reflNode j • q z)) y‖
        ≤ 8 * (m ! * (∑ i ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖) * D ^ m) :=
          mul_le_mul (abs_reflCoeff_le j) hc (norm_nonneg _) (by norm_num)
      _ ≤ 8 * (2 * (∑ i ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖) * D ^ 2) := by gcongr
      _ = 16 * D ^ 2 * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ i v (y + reflNode j • q y)‖ := by ring
  -- the Leibniz rule
  refine (norm_iteratedFDeriv_smul_le hψ hrefl y (n := k) (by exact_mod_cast hk)).trans ?_
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ *
        ‖iteratedFDeriv ℝ (k - i) (reflectionSum Finset.univ reflCoeff reflNode q v) y‖ ≤
      4 * Cψ * (16 * D ^ 2 * S) := by
    have hik : i ≤ k := by
      have := Finset.mem_range.1 hi
      omega
    have hch : (k.choose i : ℝ) ≤ 4 := by
      have h1 := Nat.choose_le_two_pow k i
      have h2 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
      exact_mod_cast h1.trans h2
    have h3 := hCψ i (hik.trans hk) y
    have h4 := hm (k - i) (Nat.sub_le k i)
    have h5 : (0 : ℝ) ≤ 16 * D ^ 2 * S := by positivity
    have h6 : (0 : ℝ) ≤ 4 * Cψ := by positivity
    exact mul_le_mul (mul_le_mul hch h3 (norm_nonneg _) (by norm_num)) h4 (norm_nonneg _) h6
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hk3 : ((k + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.succ_le_succ hk
  have hnn : (0 : ℝ) ≤ 4 * Cψ * (16 * D ^ 2 * S) := by positivity
  have hfin := mul_le_mul_of_nonneg_right hk3 hnn
  refine hsum.trans (hfin.trans_eq ?_)
  ring

/-! ## The integral bound in a collar -/

variable [MeasurableSpace E] [BorelSpace E]

/-- A bound for the square of a norm, read in `[0, ∞]`. -/
private theorem eNorm_sq_le_ofReal {G : Type*} [NormedAddCommGroup G] {X : G} {a : ℝ}
    (h : ‖X‖ ^ 2 ≤ a) : ‖X‖ₑ ^ 2 ≤ ENNReal.ofReal a := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

/-- The energy density of order at most `k`: `∑_{i ≤ k} |Dⁱ v|²`. -/
def jetEnergy (k : ℕ) (v : E → F) (x : E) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i v x‖ₑ ^ 2

omit [FiniteDimensional ℝ E] in
/-- The energy density of a `C²` function is measurable, for orders `k ≤ 2`. -/
theorem measurable_jetEnergy {k : ℕ} (hk : k ≤ 2) {v : E → F} (hv : ContDiff ℝ 2 v) :
    Measurable (jetEnergy k v) := by
  refine Finset.measurable_fun_sum _ fun i hi ↦ ?_
  have hi2 : (i : WithTop ℕ∞) ≤ 2 := by
    have := Finset.mem_range.1 hi
    exact_mod_cast (by omega : i ≤ 2)
  exact (hv.continuous_iteratedFDeriv hi2).eNorm.measurable.pow_const 2

/-- **The bound in a collar.** For a collar `K` of the sphere of radius `R` and `k ≤ 2` there is
a constant such that, for every `C²` function `v`, the `k`-th derivative of the cut-off
reflection of `v` across the sphere is bounded in `L²(K)` by the derivatives of `v` of order at
most `k` in `L²` of the annulus. -/
theorem exists_lintegral_collar_le {R : ℝ} {K : Set E} (hK : IsReflectionCollar R K) {k : ℕ}
    (hk : k ≤ 2) :
    ∃ C : ℝ≥0, ∀ v : E → F, ContDiff ℝ 2 v →
      ∫⁻ y in K, ‖iteratedFDeriv ℝ k (fun z ↦ annulusCut z • sphereReflection R v z) y‖ₑ ^ 2 ≤
        C * ∫⁻ x in unitAnnulus E, jetEnergy k v x := by
  obtain ⟨Cψ, hCψ⟩ := exists_bound_iteratedFDeriv_annulusCut (E := E)
  obtain ⟨D, hD1, hD⟩ := exists_bound_iteratedFDeriv_shiftMap (E := E) R reflNode
  obtain ⟨L, hL1, hL⟩ := exists_bound_iteratedFDeriv_shiftMap (E := E) R
    (fun j ↦ reflNode j / (reflNode j - 1))
  have hq : ContDiff ℝ 2 (sphereShift (E := E) R) := (contDiff_sphereShift R).of_le (by simp)
  set M : ℝ := (192 * Cψ * D ^ 2) ^ 2 * 9 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨(ENNReal.ofReal M * (3 * ENNReal.ofReal (L ^ Module.finrank ℝ E))).toNNReal,
    fun v hv ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))]
  -- pointwise in the collar
  have hpt (y : E) (hy : y ∈ K) :
      ‖iteratedFDeriv ℝ k (fun z ↦ annulusCut z • sphereReflection R v z) y‖ₑ ^ 2 ≤
        ENNReal.ofReal M * ∑ j : Fin 3, jetEnergy k v (y + reflNode j • sphereShift R y) := by
    have h := norm_iteratedFDeriv_smul_reflectionSum_le (contDiff_annulusCut.of_le (by simp)) hCψ
      hq hD1 (fun j i hi1 hi2 ↦ hD j y (hK.subset_closedBall hy) i hi1 hi2) hv hk (y := y)
    set t : Fin 3 × ℕ → ℝ := fun p ↦
      ‖iteratedFDeriv ℝ p.2 v (y + reflNode p.1 • sphereShift R y)‖ with ht
    have hsum : ∑ j : Fin 3, ∑ i ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ i v (y + reflNode j • sphereShift R y)‖ =
        ∑ p ∈ Finset.univ ×ˢ Finset.range (k + 1), t p := (Finset.sum_product' _ _ _).symm
    have hsum2 : ∑ j : Fin 3, ∑ i ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ i v (y + reflNode j • sphereShift R y)‖ ^ 2 =
        ∑ p ∈ Finset.univ ×ˢ Finset.range (k + 1), t p ^ 2 := (Finset.sum_product' _ _ _).symm
    have hcard : ((Finset.univ ×ˢ Finset.range (k + 1) : Finset (Fin 3 × ℕ)).card : ℝ) ≤ 9 := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_range]
      exact_mod_cast (by omega : 3 * (k + 1) ≤ 9)
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ ×ˢ Finset.range (k + 1)) (f := t)
    have hreal : ‖iteratedFDeriv ℝ k (fun z ↦ annulusCut z • sphereReflection R v z) y‖ ^ 2 ≤
        M * ∑ j : Fin 3, ∑ i ∈ Finset.range (k + 1),
          ‖iteratedFDeriv ℝ i v (y + reflNode j • sphereShift R y)‖ ^ 2 := by
      have hS0 : 0 ≤ ∑ p ∈ Finset.univ ×ˢ Finset.range (k + 1), t p ^ 2 :=
        Finset.sum_nonneg fun p _ ↦ sq_nonneg _
      calc ‖iteratedFDeriv ℝ k (fun z ↦ annulusCut z • sphereReflection R v z) y‖ ^ 2
          ≤ (192 * Cψ * D ^ 2 * ∑ p ∈ Finset.univ ×ˢ Finset.range (k + 1), t p) ^ 2 := by
            rw [← hsum]
            exact pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = (192 * Cψ * D ^ 2) ^ 2 * (∑ p ∈ Finset.univ ×ˢ Finset.range (k + 1), t p) ^ 2 :=
            mul_pow _ _ _
        _ ≤ (192 * Cψ * D ^ 2) ^ 2 * (9 * ∑ p ∈ Finset.univ ×ˢ Finset.range (k + 1), t p ^ 2) :=
            mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_right hcard hS0))
              (sq_nonneg _)
        _ = M * ∑ j : Fin 3, ∑ i ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ i v (y + reflNode j • sphereShift R y)‖ ^ 2 := by
            rw [hsum2, hM]
            ring
    refine (eNorm_sq_le_ofReal hreal).trans_eq ?_
    rw [ENNReal.ofReal_mul hM0, ENNReal.ofReal_sum_of_nonneg fun j _ ↦
      Finset.sum_nonneg fun i _ ↦ sq_nonneg _]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [jetEnergy, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  -- integrate, and change variables in each of the three terms
  have hmeasK : MeasurableSet K := hK.isOpen.measurableSet
  have hΦc (j : Fin 3) : Continuous (fun y : E ↦ y + reflNode j • sphereShift R y) :=
    continuous_id.add ((contDiff_sphereShift R).continuous.const_smul _)
  have hjm (j : Fin 3) : Measurable fun y : E ↦ jetEnergy k v (y + reflNode j • sphereShift R y) :=
    (measurable_jetEnergy hk hv).comp (hΦc j).measurable
  have hcov (j : Fin 3) : ∫⁻ y in K, jetEnergy k v (y + reflNode j • sphereShift R y) ≤
      ENNReal.ofReal (L ^ Module.finrank ℝ E) * ∫⁻ x in unitAnnulus E, jetEnergy k v x := by
    have hΨd (x : E) : HasFDerivAt
        (fun z : E ↦ z + (reflNode j / (reflNode j - 1)) • sphereShift R z)
        (fderiv ℝ (fun z : E ↦ z + (reflNode j / (reflNode j - 1)) • sphereShift R z) x) x :=
      ((contDiff_id.add ((contDiff_sphereShift R).const_smul _)).differentiable (by simp)
        x).hasFDerivAt
    have himg : (fun y : E ↦ y + reflNode j • sphereShift R y) '' K ⊆ unitAnnulus E := by
      rintro _ ⟨y, hy, rfl⟩
      exact hK.mem_unitAnnulus hy j
    refine (lintegral_comp_le_of_leftInverse hmeasK (hΦc j).continuousOn
      (fun y hy ↦ hK.leftInverse hy j) (fun x _ ↦ hΨd x) (L := L) (fun x hx ↦ ?_)
      (jetEnergy k v)).trans (mul_le_mul' le_rfl (lintegral_mono_set himg))
    rw [← norm_iteratedFDeriv_one]
    refine hL j x ?_ 1 le_rfl one_le_two
    have := himg hx
    exact mem_closedBall_zero_iff.2 (by linarith [this.2])
  calc ∫⁻ y in K, ‖iteratedFDeriv ℝ k (fun z ↦ annulusCut z • sphereReflection R v z) y‖ₑ ^ 2
      ≤ ∫⁻ y in K, ENNReal.ofReal M *
          ∑ j : Fin 3, jetEnergy k v (y + reflNode j • sphereShift R y) :=
        setLIntegral_mono' hmeasK hpt
    _ = ENNReal.ofReal M *
          ∑ j : Fin 3, ∫⁻ y in K, jetEnergy k v (y + reflNode j • sphereShift R y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum _ fun j _ ↦ hjm j]
    _ ≤ ENNReal.ofReal M * ∑ _j : Fin 3,
          ENNReal.ofReal (L ^ Module.finrank ℝ E) * ∫⁻ x in unitAnnulus E, jetEnergy k v x :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ ↦ hcov j)
    _ = ENNReal.ofReal M * (3 * ENNReal.ofReal (L ^ Module.finrank ℝ E)) *
          ∫⁻ x in unitAnnulus E, jetEnergy k v x := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## The bound on the whole space -/

/-- **The extension is bounded order by order.** For `k ≤ 2` there is a constant `C` such that,
for every `C²` function `v`, `∫ |Dᵏ (annulusExtension v)|² ≤ C ∑_{i ≤ k} ∫_{1 < |y| < 2} |Dⁱ v|²`.
The integral over the whole space splits into the annulus, where the extension is `v`, the two
collars, and the rest, where it vanishes; the spheres between them are null. -/
theorem exists_lintegral_iteratedFDeriv_annulusExtension_le {k : ℕ} (hk : k ≤ 2) :
    ∃ C : ℝ≥0, ∀ v : E → F, ContDiff ℝ 2 v →
      ∫⁻ y, ‖iteratedFDeriv ℝ k (annulusExtension v) y‖ₑ ^ 2 ≤
        C * ∫⁻ x in unitAnnulus E, jetEnergy k v x := by
  obtain ⟨C₁, hC₁⟩ := exists_lintegral_collar_le (F := F) (isReflectionCollar_inner (E := E)) hk
  obtain ⟨C₂, hC₂⟩ := exists_lintegral_collar_le (F := F) (isReflectionCollar_outer (E := E)) hk
  refine ⟨C₁ + 1 + C₂, fun v hv ↦ ?_⟩
  set Kin : Set E := {y | 3 / 4 < ‖y‖ ∧ ‖y‖ < 1} with hKin
  set Kout : Set E := {y | 2 < ‖y‖ ∧ ‖y‖ < 9 / 4} with hKout
  set fin : E → ℝ≥0∞ := fun y ↦
    ‖iteratedFDeriv ℝ k (fun z ↦ annulusCut z • sphereReflection 1 v z) y‖ₑ ^ 2 with hfin
  set fout : E → ℝ≥0∞ := fun y ↦
    ‖iteratedFDeriv ℝ k (fun z ↦ annulusCut z • sphereReflection 2 v z) y‖ₑ ^ 2 with hfout
  set fmid : E → ℝ≥0∞ := fun y ↦ ‖iteratedFDeriv ℝ k v y‖ₑ ^ 2 with hfmid
  have hk2 : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  have hmKin : MeasurableSet Kin := (isReflectionCollar_inner (E := E)).isOpen.measurableSet
  have hmKout : MeasurableSet Kout := (isReflectionCollar_outer (E := E)).isOpen.measurableSet
  have hmA : MeasurableSet (unitAnnulus E) := isOpen_unitAnnulus.measurableSet
  have hcut : ContDiff ℝ 2 (annulusCut (E := E)) := contDiff_annulusCut.of_le (by simp)
  have hmin : Measurable fin :=
    ((hcut.smul (contDiff_sphereReflection hv 1)).continuous_iteratedFDeriv
      hk2).eNorm.measurable.pow_const 2
  have hmmid : Measurable fmid := (hv.continuous_iteratedFDeriv hk2).eNorm.measurable.pow_const 2
  have hmAB : Measurable fun y ↦ Kin.indicator fin y + (unitAnnulus E).indicator fmid y :=
    (hmin.indicator hmKin).add (hmmid.indicator hmA)
  -- almost every point is off the four spheres
  have hsph (r : ℝ) (hr : r ≠ 0) : ∀ᵐ y : E, ‖y‖ ≠ r := by
    have h0 : (volume : Measure E) (sphere 0 r) = 0 := Measure.addHaar_sphere_of_ne_zero _ _ hr
    filter_upwards [compl_mem_ae_iff.2 h0] with y hy
    exact fun h ↦ hy (mem_sphere_zero_iff_norm.2 h)
  have hae : ∀ᵐ y : E, ‖iteratedFDeriv ℝ k (annulusExtension v) y‖ₑ ^ 2 ≤
      Kin.indicator fin y + (unitAnnulus E).indicator fmid y + Kout.indicator fout y := by
    filter_upwards [hsph (3 / 4) (by norm_num), hsph 1 one_ne_zero, hsph 2 two_ne_zero,
      hsph (9 / 4) (by norm_num)] with y h34 h1 h2 h94
    rcases lt_or_gt_of_ne h34 with ha | ha
    · -- `|y| < 3/4`: the extension vanishes near `y`
      have hz : ‖iteratedFDeriv ℝ k (annulusExtension v) y‖ₑ ^ 2 = 0 := by
        rw [((annulusExtension_eventuallyEq_zero v (Or.inl ha)).iteratedFDeriv ℝ k).eq_of_nhds,
          ← ofReal_norm]
        simp
      rw [hz]
      exact zero_le
    rcases lt_or_gt_of_ne h1 with hb | hb
    · -- the inner collar
      rw [((annulusExtension_eventuallyEq_inner v hb).iteratedFDeriv ℝ k).eq_of_nhds,
        indicator_of_mem (show y ∈ Kin from ⟨ha, hb⟩)]
      exact le_add_right (le_add_right le_rfl)
    rcases lt_or_gt_of_ne h2 with hc | hc
    · -- the annulus
      rw [((annulusExtension_eventuallyEq_mid v hb hc).iteratedFDeriv ℝ k).eq_of_nhds,
        indicator_of_mem (show y ∈ unitAnnulus E from ⟨hb, hc⟩)]
      exact le_add_right (le_add_left le_rfl)
    rcases lt_or_gt_of_ne h94 with hd | hd
    · -- the outer collar
      rw [((annulusExtension_eventuallyEq_outer v hc).iteratedFDeriv ℝ k).eq_of_nhds,
        indicator_of_mem (show y ∈ Kout from ⟨hc, hd⟩)]
      exact le_add_left le_rfl
    · have hz : ‖iteratedFDeriv ℝ k (annulusExtension v) y‖ₑ ^ 2 = 0 := by
        rw [((annulusExtension_eventuallyEq_zero v (Or.inr hd)).iteratedFDeriv ℝ k).eq_of_nhds,
          ← ofReal_norm]
        simp
      rw [hz]
      exact zero_le
  have hmidle : ∫⁻ x in unitAnnulus E, fmid x ≤ ∫⁻ x in unitAnnulus E, jetEnergy k v x :=
    lintegral_mono fun x ↦ Finset.single_le_sum (f := fun i ↦ ‖iteratedFDeriv ℝ i v x‖ₑ ^ 2)
      (fun _ _ ↦ zero_le) (Finset.mem_range.2 (Nat.lt_succ_self k))
  calc ∫⁻ y, ‖iteratedFDeriv ℝ k (annulusExtension v) y‖ₑ ^ 2
      ≤ ∫⁻ y, (Kin.indicator fin y + (unitAnnulus E).indicator fmid y + Kout.indicator fout y) :=
        lintegral_mono_ae hae
    _ = (∫⁻ y in Kin, fin y) + (∫⁻ y in unitAnnulus E, fmid y) + ∫⁻ y in Kout, fout y := by
        rw [lintegral_add_left hmAB, lintegral_add_left (hmin.indicator hmKin),
          lintegral_indicator hmKin, lintegral_indicator hmA, lintegral_indicator hmKout]
    _ ≤ C₁ * (∫⁻ x in unitAnnulus E, jetEnergy k v x) + (∫⁻ x in unitAnnulus E, jetEnergy k v x) +
          C₂ * ∫⁻ x in unitAnnulus E, jetEnergy k v x :=
        add_le_add (add_le_add (hC₁ v hv) hmidle) (hC₂ v hv)
    _ = ((C₁ + 1 + C₂ : ℝ≥0) : ℝ≥0∞) * ∫⁻ x in unitAnnulus E, jetEnergy k v x := by
        push_cast
        ring

end PDE.Analysis
