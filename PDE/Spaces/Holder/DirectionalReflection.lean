/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.Directional
public import PDE.Common.Euclidean.CoordinateReflection
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Directional Hölder seminorms of reflected functions

Let `σ` be the reflection in the coordinate hyperplane `{x_i = 0}` and let `D` be a
`σ`-invariant set. For a function that is odd or even under `σ`, the directional seminorms on
`D` are controlled by data on the half `D ∩ {x_i > 0}` (or `D ∩ {x_i ≥ 0}`).

* Across the hyperplane, in the direction `i` itself, an odd function needs the weighted bound
  `|f x| ≤ M |x_i|^α`: with `a = |x_i|`, `b = |z_i|` on opposite sides,
  `|f x - f z| ≤ M (a^α + b^α) ≤ 2^{1-α} M (a + b)^α` by concavity of `t^α`. Hence
  `[f]_{C^α_{x_i}(D)} ≤ max([f]_{C^α_{x_i}(D⁺)}, 2^{1-α} sup_{D⁺} |f| |x_i|^{-α})`. At `α = 1/2`
  the constant is `√2`: this is the estimate (5.30) of Chen and Hou (Part I, Section 5.3.4)
  behind (5.26).
* An even function needs nothing: `|f x - f z| = |f(σx) - f z|` and `|x_i + z_i| ≤ |x_i - z_i|`
  when `x_i, z_i` have opposite signs.
* In a direction `j ≠ i` the reflection maps coordinate lines to coordinate lines, so the
  seminorm on `D` equals that on the half, for odd and even functions.

## Main results

* `enorm_le_iSup_mul_of_odd`: the bound `|f x| ≤ M |x_i|^α` on `D` from the half.
* `directionalSeminorm_le_max_of_odd`
* `directionalSeminorm_eq_of_even`
* `directionalSeminorm_eq_of_odd_of_ne`, `directionalSeminorm_eq_of_even_of_ne`
* `directionalSeminorm_eq_of_even_of_continuousOn`: the open-half form for continuous even
  functions on domains invariant under translations along `e_i`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.3.2, (5.26), and
  Section 5.3.4, (5.30).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set Filter PDE.Common
open scoped ENNReal NNReal Topology

namespace HolderSpace

/-- Concavity of `t ↦ t^α` for `α ∈ [0, 1]`: `a^α + b^α ≤ 2^{1-α} (a + b)^α` for `a, b ≥ 0`. -/
theorem rpow_add_rpow_le_two_rpow_mul {a b α : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) : a ^ α + b ^ α ≤ 2 ^ (1 - α) * (a + b) ^ α := by
  have h := (Real.concaveOn_rpow hα₀ hα₁).2 (mem_Ici.2 ha) (mem_Ici.2 hb)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have hmid : 1 / 2 * a + 1 / 2 * b = (a + b) / 2 := by ring
  rw [hmid, Real.div_rpow (add_nonneg ha hb) zero_le_two] at h
  have h2 : (0 : ℝ) < 2 ^ α := Real.rpow_pos_of_pos two_pos α
  rw [Real.rpow_sub two_pos, Real.rpow_one]
  rw [le_div_iff₀ h2] at h
  calc a ^ α + b ^ α = 2 * (1 / 2 * a ^ α + 1 / 2 * b ^ α) := by ring
    _ ≤ 2 * ((a + b) ^ α / 2 ^ α) := by
        gcongr
        rw [le_div_iff₀ h2]
        linarith
    _ = 2 / 2 ^ α * (a + b) ^ α := by ring

/-- The constant `2^{1-α}` as an extended real. -/
theorem two_rpow_eq_ofReal (a : ℝ) : (2 : ℝ≥0∞) ^ a = ENNReal.ofReal (2 ^ a) := by
  rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]

variable {n : ℕ} {i j : Fin n} {α : ℝ≥0} {D : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- Reflection keeps the relation "the coordinates other than `j` agree". -/
private theorem reflection_line {x z : ℝ^n} (h : ∀ k ≠ j, x k = z k) :
    ∀ k ≠ j, coordinateReflection i x k = coordinateReflection i z k := by
  intro k hk
  by_cases hki : k = i
  · subst hki
    simp [h k hk]
  · simp [coordinateReflection_apply_of_ne i k hki, h k hk]

/-- An odd function vanishes on the reflecting hyperplane. -/
private theorem odd_apply_eq_zero (hf : IsOddUnderCoordinateReflection i f) {x : ℝ^n}
    (hx : x i = 0) : f x = 0 := by
  have hσ : coordinateReflection i x = x := by
    ext k
    by_cases hki : k = i
    · subst hki
      simp [hx]
    · simp [coordinateReflection_apply_of_ne i k hki]
  have := hf x
  rw [hσ] at this
  linarith

/-- The weighted bound `|f x| ≤ M |x_i|^α` on all of `D` for an odd function, where `M` is the
supremum of `|f| |x_i|^{-α}` over `D ∩ {x_i > 0}`. -/
theorem enorm_le_iSup_mul_of_odd (hD : ∀ x ∈ D, coordinateReflection i x ∈ D)
    (hf : IsOddUnderCoordinateReflection i f) {x : ℝ^n} (hx : x ∈ D) :
    ‖f x‖ₑ ≤ (⨆ y ∈ D ∩ {y | 0 < y i}, ‖f y‖ₑ / ‖y i‖ₑ ^ (α : ℝ)) * ‖x i‖ₑ ^ (α : ℝ) := by
  have key : ∀ y ∈ D ∩ {y | 0 < y i},
      ‖f y‖ₑ ≤ (⨆ y ∈ D ∩ {y | 0 < y i}, ‖f y‖ₑ / ‖y i‖ₑ ^ (α : ℝ)) * ‖y i‖ₑ ^ (α : ℝ) := by
    intro y hy
    have hpos : ‖y i‖ₑ ^ (α : ℝ) ≠ 0 := by
      rcases eq_or_ne (α : ℝ) 0 with hα | hα
      · simp [hα]
      · exact (ENNReal.rpow_pos (enorm_pos.2 hy.2.ne') enorm_ne_top).ne'
    have htop : ‖y i‖ₑ ^ (α : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg α.2 enorm_ne_top
    exact (ENNReal.div_le_iff hpos htop).1
      (le_iSup₂ (f := fun y _ ↦ ‖f y‖ₑ / ‖y i‖ₑ ^ (α : ℝ)) y hy)
  rcases lt_trichotomy (x i) 0 with hneg | hzero | hpos
  · have hσ : coordinateReflection i x ∈ D ∩ {y | 0 < y i} :=
      ⟨hD x hx, by simpa using hneg⟩
    have := key _ hσ
    rwa [hf x, enorm_neg, coordinateReflection_apply_same, enorm_neg] at this
  · simp [odd_apply_eq_zero hf hzero]
  · exact key x ⟨hx, hpos⟩

/-- Odd reflection across `{x_i = 0}` in the direction `i`: for `α ≤ 1`,
`[f]_{C^α_{x_i}(D)} ≤ max([f]_{C^α_{x_i}(D⁺)}, 2^{1-α} sup_{D⁺} |f| |x_i|^{-α})` with
`D⁺ = D ∩ {x_i > 0}`. At `α = 1/2` this is the bound
`[f]_{C^{1/2}_x(ℝ²₊)} ≤ max([f]_{C^{1/2}_x(ℝ²₊₊)}, √2 sup_{ℝ²₊₊} |f| |x_1|^{-1/2})` of Chen and Hou
(Part I, (5.30)), with a pointwise supremum. -/
theorem directionalSeminorm_le_max_of_odd (hD : ∀ x ∈ D, coordinateReflection i x ∈ D)
    (hf : IsOddUnderCoordinateReflection i f) (hα : α ≤ 1) :
    directionalSeminorm i α D f ≤
      max (directionalSeminorm i α (D ∩ {x | 0 < x i}) f)
        (2 ^ (1 - (α : ℝ)) * ⨆ x ∈ D ∩ {x | 0 < x i}, ‖f x‖ₑ / ‖x i‖ₑ ^ (α : ℝ)) := by
  set M := ⨆ x ∈ D ∩ {x | 0 < x i}, ‖f x‖ₑ / ‖x i‖ₑ ^ (α : ℝ)
  set S := directionalSeminorm i α (D ∩ {x | 0 < x i}) f
  have hα₁ : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  -- pairs on opposite sides of the hyperplane
  have cross : ∀ x ∈ D, ∀ z ∈ D, x i ≤ 0 → 0 ≤ z i →
      edist (f x) (f z) ≤ 2 ^ (1 - (α : ℝ)) * M * edist (x i) (z i) ^ (α : ℝ) := by
    intro x hx z hz hxi hzi
    have hsum : ‖x i‖ₑ ^ (α : ℝ) + ‖z i‖ₑ ^ (α : ℝ) ≤
        2 ^ (1 - (α : ℝ)) * edist (x i) (z i) ^ (α : ℝ) := by
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, edist_dist, Real.dist_eq,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (NNReal.coe_nonneg α),
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (NNReal.coe_nonneg α),
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (NNReal.coe_nonneg α),
        ← ENNReal.ofReal_add (Real.rpow_nonneg (abs_nonneg _) _)
          (Real.rpow_nonneg (abs_nonneg _) _),
        two_rpow_eq_ofReal, ← ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have habs : |x i - z i| = |x i| + |z i| := by
        rw [abs_of_nonpos hxi, abs_of_nonneg hzi, abs_of_nonpos (by linarith)]
        ring
      rw [habs]
      exact rpow_add_rpow_le_two_rpow_mul (abs_nonneg _) (abs_nonneg _) (NNReal.coe_nonneg α) hα₁
    calc edist (f x) (f z) ≤ ‖f x‖ₑ + ‖f z‖ₑ := by
          rw [edist_eq_enorm_sub]
          exact enorm_sub_le
      _ ≤ M * ‖x i‖ₑ ^ (α : ℝ) + M * ‖z i‖ₑ ^ (α : ℝ) :=
          add_le_add (enorm_le_iSup_mul_of_odd hD hf hx) (enorm_le_iSup_mul_of_odd hD hf hz)
      _ = M * (‖x i‖ₑ ^ (α : ℝ) + ‖z i‖ₑ ^ (α : ℝ)) := by ring
      _ ≤ M * (2 ^ (1 - (α : ℝ)) * edist (x i) (z i) ^ (α : ℝ)) := by gcongr
      _ = 2 ^ (1 - (α : ℝ)) * M * edist (x i) (z i) ^ (α : ℝ) := by ring
  have right : 2 ^ (1 - (α : ℝ)) * M ≤ max S (2 ^ (1 - (α : ℝ)) * M) := le_max_right _ _
  refine directionalSeminorm_le_iff.2 fun x hx z hz h ↦ ?_
  rcases lt_or_ge (x i) 0 with hxi | hxi <;> rcases lt_or_ge (z i) 0 with hzi | hzi
  · -- both on the negative side: reflect the pair
    have hσx : coordinateReflection i x ∈ D ∩ {y | 0 < y i} := ⟨hD x hx, by simpa using hxi⟩
    have hσz : coordinateReflection i z ∈ D ∩ {y | 0 < y i} := ⟨hD z hz, by simpa using hzi⟩
    have := edist_le_directionalSeminorm_mul (α := α) hσx hσz (reflection_line (i := i) h)
      (f := f)
    rw [hf x, hf z, edist_neg_neg, coordinateReflection_apply_same,
      coordinateReflection_apply_same, edist_neg_neg] at this
    exact this.trans (by gcongr; exact le_max_left _ _)
  · exact (cross x hx z hz hxi.le hzi).trans (by gcongr)
  · rw [edist_comm, edist_comm (x i)]
    exact (cross z hz x hx hzi.le hxi).trans (by gcongr)
  · rcases eq_or_lt_of_le hxi with hx0 | hx0
    · exact (cross x hx z hz hx0.ge hzi).trans (by gcongr)
    rcases eq_or_lt_of_le hzi with hz0 | hz0
    · rw [edist_comm, edist_comm (x i)]
      exact (cross z hz x hx hz0.ge hxi).trans (by gcongr)
    exact (edist_le_directionalSeminorm_mul (D := D ∩ {y | 0 < y i}) ⟨hx, hx0⟩ ⟨hz, hz0⟩ h).trans
      (by gcongr; exact le_max_left _ _)

/-- Folding a point into the closed half `{x_i ≥ 0}` by the reflection. -/
private def fold (i : Fin n) (y : ℝ^n) : ℝ^n :=
  if 0 ≤ y i then y else coordinateReflection i y

/-- If `D` is invariant under the reflection in the `i`-th coordinate, folding maps `D` into itself.
-/
private theorem fold_mem (hD : ∀ x ∈ D, coordinateReflection i x ∈ D) {y : ℝ^n} (hy : y ∈ D) :
    fold i y ∈ D := by
  unfold fold
  split_ifs
  · exact hy
  · exact hD y hy

/-- The `i`-th coordinate of the folded point is `|y i|`. -/
private theorem fold_apply_same (y : ℝ^n) : fold i y i = |y i| := by
  unfold fold
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · simp [abs_of_neg (not_le.1 h)]

/-- Folding leaves every coordinate other than the `i`-th unchanged. -/
private theorem fold_apply_of_ne {k : Fin n} (hk : k ≠ i) (y : ℝ^n) : fold i y k = y k := by
  unfold fold
  split_ifs
  · rfl
  · exact coordinateReflection_apply_of_ne i k hk y

/-- A function even under the reflection in the `i`-th coordinate takes the same value at `y` and at
its fold. -/
private theorem even_fold (hf : IsEvenUnderCoordinateReflection i f) (y : ℝ^n) :
    f (fold i y) = f y := by
  unfold fold
  split_ifs
  · rfl
  · exact hf y

/-- Even reflection across `{x_i = 0}`, direction `i`: the seminorm on `D` equals the seminorm
on `D ∩ {x_i ≥ 0}`, since `|f x - f z| = |f(σx) - f(σz)|` and `||x_i| - |z_i|| ≤ |x_i - z_i|`. -/
theorem directionalSeminorm_eq_of_even (hD : ∀ x ∈ D, coordinateReflection i x ∈ D)
    (hf : IsEvenUnderCoordinateReflection i f) :
    directionalSeminorm i α D f = directionalSeminorm i α (D ∩ {x | 0 ≤ x i}) f := by
  refine le_antisymm (directionalSeminorm_le_iff.2 fun x hx z hz h ↦ ?_)
    (directionalSeminorm_mono inter_subset_left)
  have hmem : ∀ y ∈ D, fold i y ∈ D ∩ {x | 0 ≤ x i} := fun y hy ↦
    ⟨fold_mem hD hy, by simp [fold_apply_same]⟩
  have hline : ∀ k ≠ i, fold i x k = fold i z k := fun k hk ↦ by
    rw [fold_apply_of_ne hk, fold_apply_of_ne hk, h k hk]
  have := edist_le_directionalSeminorm_mul (α := α) (hmem x hx) (hmem z hz) hline (f := f)
  rw [even_fold hf, even_fold hf, fold_apply_same, fold_apply_same] at this
  refine this.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (NNReal.coe_nonneg α)))
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub _ _)

/-- Even reflection across `{x_i = 0}`, direction `j ≠ i`: the seminorm on `D` equals the
seminorm on `D ∩ {x_i ≥ 0}`. -/
theorem directionalSeminorm_eq_of_even_of_ne (hji : j ≠ i)
    (hD : ∀ x ∈ D, coordinateReflection i x ∈ D) (hf : IsEvenUnderCoordinateReflection i f) :
    directionalSeminorm j α D f = directionalSeminorm j α (D ∩ {x | 0 ≤ x i}) f := by
  refine le_antisymm (directionalSeminorm_le_iff.2 fun x hx z hz h ↦ ?_)
    (directionalSeminorm_mono inter_subset_left)
  have hmem : ∀ y ∈ D, fold i y ∈ D ∩ {x | 0 ≤ x i} := fun y hy ↦
    ⟨fold_mem hD hy, by simp [fold_apply_same]⟩
  have hline : ∀ k ≠ j, fold i x k = fold i z k := fun k hk ↦ by
    by_cases hki : k = i
    · subst hki
      rw [fold_apply_same, fold_apply_same, h k hk]
    · rw [fold_apply_of_ne hki, fold_apply_of_ne hki, h k hk]
  have := edist_le_directionalSeminorm_mul (α := α) (hmem x hx) (hmem z hz) hline (f := f)
  rwa [even_fold hf, even_fold hf, fold_apply_of_ne hji, fold_apply_of_ne hji] at this

/-- Odd reflection across `{x_i = 0}`, direction `j ≠ i`: the seminorm on `D` equals the
seminorm on `D ∩ {x_i > 0}`. Pairs on the hyperplane contribute nothing, since `f` vanishes
there. -/
theorem directionalSeminorm_eq_of_odd_of_ne (hji : j ≠ i)
    (hD : ∀ x ∈ D, coordinateReflection i x ∈ D) (hf : IsOddUnderCoordinateReflection i f) :
    directionalSeminorm j α D f = directionalSeminorm j α (D ∩ {x | 0 < x i}) f := by
  refine le_antisymm (directionalSeminorm_le_iff.2 fun x hx z hz h ↦ ?_)
    (directionalSeminorm_mono inter_subset_left)
  have hxz : x i = z i := h i hji.symm
  rcases lt_trichotomy (x i) 0 with hneg | hzero | hpos
  · have hσx : coordinateReflection i x ∈ D ∩ {y | 0 < y i} := ⟨hD x hx, by simpa using hneg⟩
    have hσz : coordinateReflection i z ∈ D ∩ {y | 0 < y i} :=
      ⟨hD z hz, by simpa [← hxz] using hneg⟩
    have := edist_le_directionalSeminorm_mul (α := α) hσx hσz (reflection_line (i := i) h)
      (f := f)
    rwa [hf x, hf z, edist_neg_neg, coordinateReflection_apply_of_ne i j hji,
      coordinateReflection_apply_of_ne i j hji] at this
  · simp [odd_apply_eq_zero hf hzero, odd_apply_eq_zero hf (hxz ▸ hzero)]
  · exact edist_le_directionalSeminorm_mul (D := D ∩ {y | 0 < y i}) ⟨hx, hpos⟩
      ⟨hz, show 0 < z i from hxz ▸ hpos⟩ h

/-- Moving the closed half to the open half for a continuous function. If `D` is invariant under
translations along `e_i` and `f` is continuous on `D`, the directional seminorms on
`D ∩ {x_i ≥ 0}` and on `D ∩ {x_i > 0}` agree: a pair touching the hyperplane is the limit of the
pair translated by `ε e_i`, which stays on the same coordinate line. -/
theorem directionalSeminorm_nonneg_eq_pos
    (hDt : ∀ x ∈ D, ∀ t : ℝ, x + t • EuclideanSpace.single i (1 : ℝ) ∈ D)
    (hc : ContinuousOn f D) (j : Fin n) :
    directionalSeminorm j α (D ∩ {x | 0 ≤ x i}) f =
      directionalSeminorm j α (D ∩ {x | 0 < x i}) f := by
  refine le_antisymm (directionalSeminorm_le_iff.2 fun x hx z hz h ↦ ?_)
    (directionalSeminorm_mono fun x hx ↦ ⟨hx.1, le_of_lt (show 0 < x i from hx.2)⟩)
  set e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  have hshift : ∀ y ∈ D, Tendsto (fun t : ℝ ↦ f (y + t • e)) (𝓝[>] 0) (𝓝 (f y)) := by
    intro y hy
    have h₁ : Tendsto (fun t : ℝ ↦ y + t • e) (𝓝[>] 0) (𝓝[D] y) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t ↦ hDt y hy t⟩
      have : Tendsto (fun t : ℝ ↦ y + t • e) (𝓝 0) (𝓝 (y + (0 : ℝ) • e)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (hc y hy).tendsto.comp h₁
  have hlim := (hshift x hx.1).edist (hshift z hz.1)
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hx0 : 0 ≤ x i := hx.2
  have hz0 : 0 ≤ z i := hz.2
  have hxt : x + t • e ∈ D ∩ {y | 0 < y i} :=
    ⟨hDt x hx.1 t, by simp only [e, mem_ofPred_eq]; simp; linarith⟩
  have hzt : z + t • e ∈ D ∩ {y | 0 < y i} :=
    ⟨hDt z hz.1 t, by simp only [e, mem_ofPred_eq]; simp; linarith⟩
  have hline : ∀ k ≠ j, (x + t • e) k = (z + t • e) k := fun k hk ↦ by
    simp [h k hk]
  have := edist_le_directionalSeminorm_mul (α := α) (f := f) hxt hzt hline
  simpa using this

/-- Even reflection across `{x_i = 0}` onto the open half for a continuous function: on a
reflection-invariant `D` that is invariant under translations along `e_i`, every directional
seminorm of an even function continuous on `D` equals the seminorm on `D ∩ {x_i > 0}`. This is the
open-quadrant form used for the even component `ξ₁` in Chen and Hou (Part I, Section 5.3.4). -/
theorem directionalSeminorm_eq_of_even_of_continuousOn
    (hD : ∀ x ∈ D, coordinateReflection i x ∈ D)
    (hDt : ∀ x ∈ D, ∀ t : ℝ, x + t • EuclideanSpace.single i (1 : ℝ) ∈ D)
    (hf : IsEvenUnderCoordinateReflection i f) (hc : ContinuousOn f D) (j : Fin n) :
    directionalSeminorm j α D f = directionalSeminorm j α (D ∩ {x | 0 < x i}) f := by
  rw [← directionalSeminorm_nonneg_eq_pos hDt hc j]
  rcases eq_or_ne j i with rfl | hji
  · exact directionalSeminorm_eq_of_even hD hf
  · exact directionalSeminorm_eq_of_even_of_ne hji hD hf

end HolderSpace
