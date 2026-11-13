/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Directional and weighted Hölder seminorms

For `f : ℝ^n → E`, a set `D` and an exponent `α`, the directional Hölder seminorm along the
coordinate `i` is

`[f]_{C^α_{x_i}(D)} = sup |f x - f z| / |x_i - z_i|^α`

over pairs `x, z ∈ D` that differ only in the coordinate `i`. For a weight `g` on differences,
the weighted Hölder seminorm is

`[f]_{C_g(D)} = sup |f x - f z| g(x - z)`

over all pairs `x, z ∈ D`. When `g` is positive and `(-α)`-homogeneous this is a `C^α` seminorm
adapted to the anisotropy of `g`; `g(h) = |h|^{-α}` gives the usual one. Both seminorms are
`ℝ≥0∞`-valued suprema: they are finite exactly when the corresponding Hölder bound holds, and
they need no continuity, boundedness or measurability of `f`.

Pairs with `x = z` contribute zero to both suprema (with `0 / 0 = 0` in `ℝ≥0∞`), so the
definitions do not exclude them.

## Main declarations

* `directionalSeminorm i α D f`: the seminorm `[f]_{C^α_{x_i}(D)}` of Chen and Hou (2.81).
* `weightedSeminorm g D f`: the seminorm `[f]_{C_g(D)}` of Chen and Hou (2.82).
* `directionalSeminorm_le_iff`, `weightedSeminorm_le_iff`: the seminorms as least constants.
* `directionalSeminorm_le_of_holderOnWith`: a Hölder function on `D` has every directional
  seminorm at most its Hölder constant.
* `ofReal_mul_directionalSeminorm_le`: for a `(-α)`-homogeneous weight,
  `g(e_i) [f]_{C^α_{x_i}} ≤ [f]_{C_g}`.
* `weightedSeminorm_le_of_directional`: the rectangular path estimate in the plane,
  `[f]_{C_g} ≤ A₀ [f]_{C^α_{x_1}} + A₁ [f]_{C^α_{x_2}}` when `g(h) |h_i|^α ≤ A_i`.
* `holderOnWith_slice_zero`, `holderOnWith_slice_one`: slices along the axes are `α`-Hölder
  with any constant above the directional seminorm.
* `directionalSeminorm_mul_le`, `weightedSeminorm_mul_le`: product rules with pointwise suprema.

## How it works

Bounds for either seminorm reduce to bounds for single pairs through `directionalSeminorm_le_iff`
and `weightedSeminorm_le_iff`. If `x` and `z` differ only in the coordinate `i` and `z i < x i`,
then `x - z = (x i - z i) • e_i` with `e_i = EuclideanSpace.single i 1` (`sub_eq_smul_single`), and
`(-α)`-homogeneity gives `g (x - z) = (x i - z i) ^ (-α) * g e_i`. So `g e_i` times the directional
quotient of the pair is its weighted term; swapping the pair covers `x i < z i`, which proves
`ofReal_mul_directionalSeminorm_le`. For `weightedSeminorm_le_of_directional` we go from `x` to `z`
through the corner `w = !₂[z 0, x 1]`, which differs from `x` only in the first coordinate and from
`z` only in the second. The triangle inequality and `edist_le_directionalSeminorm_mul` on the two
legs bound `edist (f x) (f z)` by `[f]_{C^α_{x_1}} |x_1 - z_1|^α + [f]_{C^α_{x_2}} |x_2 - z_2|^α`,
and multiplying by `g (x - z)` and using the bounds on `g(h) |h_i|^α` at `h = x - z` gives the
estimate. This is the rectangular path argument behind (5.40) of Chen and Hou, stated for the
seminorms on a set `D` that contains these corners.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.11, (2.81)-(2.82);
  Section 5.3.2, (5.26); Section 5.4.1, (5.40).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set
open scoped ENNReal NNReal

namespace HolderSpace

section Line

variable {n : ℕ} {i : Fin n} {x z : ℝ^n}

/-- Two points whose coordinates other than `i` agree, and whose `i`-th coordinates agree, are
equal. -/
theorem eq_of_forall_ne_eq (h : ∀ j ≠ i, x j = z j) (hi : x i = z i) : x = z := by
  ext j
  by_cases hj : j = i
  · subst hj
    exact hi
  · exact h j hj

/-- The difference of two points on a line parallel to the `i`-th axis is a multiple of the
`i`-th coordinate vector. -/
theorem sub_eq_smul_single (h : ∀ j ≠ i, x j = z j) :
    x - z = (x i - z i) • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj, h j hj]

/-- On a line parallel to the `i`-th axis the Euclidean distance is the distance of the
`i`-th coordinates. -/
theorem dist_eq_dist_apply (h : ∀ j ≠ i, x j = z j) : dist x z = dist (x i) (z i) := by
  rw [EuclideanSpace.dist_eq, Finset.sum_eq_single i (fun j _ hj ↦ by simp [h j hj])
    (by simp), Real.sqrt_sq dist_nonneg]

/-- On a line parallel to the `i`-th axis the extended distance is that of the `i`-th
coordinates. -/
theorem edist_eq_edist_apply (h : ∀ j ≠ i, x j = z j) : edist x z = edist (x i) (z i) := by
  rw [edist_dist, edist_dist, dist_eq_dist_apply h]

end Line

section Directional

variable {n : ℕ} {E : Type*} [PseudoEMetricSpace E]

/-- The directional Hölder seminorm `[f]_{C^α_{x_i}(D)}` of Chen and Hou (2.81): the supremum
of `edist (f x) (f z) / |x_i - z_i|^α` over points `x, z ∈ D` whose coordinates other than `i`
agree. -/
def directionalSeminorm (i : Fin n) (α : ℝ≥0) (D : Set (ℝ^n)) (f : ℝ^n → E) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ z ∈ D, ⨆ (_ : ∀ j ≠ i, x j = z j),
    edist (f x) (f z) / edist (x i) (z i) ^ (α : ℝ)

variable {i : Fin n} {α : ℝ≥0} {D D' : Set (ℝ^n)} {f : ℝ^n → E}

/-- The directional seminorm is the least constant in the directional Hölder bound. -/
theorem directionalSeminorm_le_iff {C : ℝ≥0∞} :
    directionalSeminorm i α D f ≤ C ↔
      ∀ x ∈ D, ∀ z ∈ D, (∀ j ≠ i, x j = z j) →
        edist (f x) (f z) ≤ C * edist (x i) (z i) ^ (α : ℝ) := by
  simp only [directionalSeminorm, iSup_le_iff]
  refine forall₂_congr fun x _ ↦ forall₂_congr fun z _ ↦ forall_congr' fun h ↦ ?_
  by_cases hxz : x i = z i
  · obtain rfl := eq_of_forall_ne_eq h hxz
    simp
  · have h0 : edist (x i) (z i) ^ (α : ℝ) ≠ 0 := by
      rcases eq_or_ne (α : ℝ) 0 with hα | hα
      · simp [hα]
      · exact (ENNReal.rpow_pos (edist_pos.2 hxz) (edist_ne_top _ _)).ne'
    have ht : edist (x i) (z i) ^ (α : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg α.2 (edist_ne_top _ _)
    exact ENNReal.div_le_iff h0 ht

/-- The directional Hölder bound with the seminorm as constant. -/
theorem edist_le_directionalSeminorm_mul {x z : ℝ^n} (hx : x ∈ D) (hz : z ∈ D)
    (h : ∀ j ≠ i, x j = z j) :
    edist (f x) (f z) ≤ directionalSeminorm i α D f * edist (x i) (z i) ^ (α : ℝ) :=
  directionalSeminorm_le_iff.1 le_rfl x hx z hz h

/-- The directional seminorm increases with the domain. -/
theorem directionalSeminorm_mono (h : D ⊆ D') :
    directionalSeminorm i α D f ≤ directionalSeminorm i α D' f :=
  directionalSeminorm_le_iff.2 fun _ hx _ hz hl ↦
    edist_le_directionalSeminorm_mul (h hx) (h hz) hl

/-- A Hölder function on `D` has every directional seminorm at most its Hölder constant. -/
theorem directionalSeminorm_le_of_holderOnWith {C : ℝ≥0} (hf : HolderOnWith C α f D) :
    directionalSeminorm i α D f ≤ C :=
  directionalSeminorm_le_iff.2 fun _ hx _ hz hl ↦ by
    rw [← edist_eq_edist_apply hl]
    exact hf.edist_le hx hz

/-- The directional seminorm of a constant function vanishes. -/
@[simp]
theorem directionalSeminorm_const (c : E) :
    directionalSeminorm i α D (fun _ ↦ c) = 0 :=
  le_antisymm (directionalSeminorm_le_iff.2 fun _ _ _ _ _ ↦ by simp) bot_le

/-- The directional seminorm depends only on the values on `D`. -/
theorem directionalSeminorm_congr {g : ℝ^n → E} (h : EqOn f g D) :
    directionalSeminorm i α D f = directionalSeminorm i α D g := by
  simp only [directionalSeminorm]
  refine iSup_congr fun x ↦ iSup_congr fun hx ↦ iSup_congr fun z ↦ iSup_congr fun hz ↦ ?_
  rw [h hx, h hz]

/-- The directional Hölder bound in real form, for a finite seminorm. -/
theorem dist_le_directionalSeminorm_mul {F : Type*} [PseudoMetricSpace F] {f : ℝ^n → F}
    (hf : directionalSeminorm i α D f ≠ ∞) {x z : ℝ^n} (hx : x ∈ D) (hz : z ∈ D)
    (h : ∀ j ≠ i, x j = z j) :
    dist (f x) (f z) ≤ (directionalSeminorm i α D f).toReal * |x i - z i| ^ (α : ℝ) := by
  have hle := edist_le_directionalSeminorm_mul (α := α) hx hz h (f := f)
  have hrt : edist (x i) (z i) ^ (α : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg α.2 (edist_ne_top _ _)
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top hf hrt) hle
  rwa [← dist_edist, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← dist_edist,
    Real.dist_eq] at this

end Directional

section DirectionalNormed

variable {n : ℕ} {F : Type*} [SeminormedAddCommGroup F]
  {i : Fin n} {α : ℝ≥0} {D : Set (ℝ^n)} {f g : ℝ^n → F}

/-- The directional seminorm is subadditive. -/
theorem directionalSeminorm_add_le :
    directionalSeminorm i α D (f + g) ≤
      directionalSeminorm i α D f + directionalSeminorm i α D g :=
  directionalSeminorm_le_iff.2 fun _ hx _ hz hl ↦ by
    rw [add_mul]
    exact (edist_add_add_le _ _ _ _).trans
      (add_le_add (edist_le_directionalSeminorm_mul hx hz hl)
        (edist_le_directionalSeminorm_mul hx hz hl))

/-- The directional seminorm is invariant under negation. -/
@[simp]
theorem directionalSeminorm_neg :
    directionalSeminorm i α D (-f) = directionalSeminorm i α D f := by
  simp [directionalSeminorm]

/-- Scaling a function by `c` multiplies its directional seminorm by at most `‖c‖`. -/
theorem directionalSeminorm_smul_le {𝕜 : Type*} [SeminormedRing 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] (c : 𝕜) :
    directionalSeminorm i α D (c • f) ≤ ‖c‖₊ * directionalSeminorm i α D f :=
  directionalSeminorm_le_iff.2 fun _ hx _ hz hl ↦ by
    simp only [Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul, mul_assoc]
    gcongr
    exact edist_le_directionalSeminorm_mul hx hz hl

end DirectionalNormed

section Weighted

variable {V E : Type*} [Sub V] [PseudoEMetricSpace E]

/-- The weighted Hölder seminorm `[f]_{C_g(D)}` of Chen and Hou (2.82): the supremum of
`edist (f x) (f z) * g (x - z)` over points `x, z ∈ D`. Negative values of `g` count as zero. -/
def weightedSeminorm (g : V → ℝ) (D : Set V) (f : V → E) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ z ∈ D, edist (f x) (f z) * ENNReal.ofReal (g (x - z))

variable {g g' : V → ℝ} {D D' : Set V} {f : V → E}

/-- The weighted seminorm is the least constant in the weighted Hölder bound. -/
theorem weightedSeminorm_le_iff {C : ℝ≥0∞} :
    weightedSeminorm g D f ≤ C ↔
      ∀ x ∈ D, ∀ z ∈ D, edist (f x) (f z) * ENNReal.ofReal (g (x - z)) ≤ C := by
  simp only [weightedSeminorm, iSup_le_iff]

/-- The weighted Hölder bound with the seminorm as constant. -/
theorem edist_mul_le_weightedSeminorm {x z : V} (hx : x ∈ D) (hz : z ∈ D) :
    edist (f x) (f z) * ENNReal.ofReal (g (x - z)) ≤ weightedSeminorm g D f :=
  weightedSeminorm_le_iff.1 le_rfl x hx z hz

/-- The weighted seminorm increases with the domain. -/
theorem weightedSeminorm_mono (h : D ⊆ D') :
    weightedSeminorm g D f ≤ weightedSeminorm g D' f :=
  weightedSeminorm_le_iff.2 fun _ hx _ hz ↦ edist_mul_le_weightedSeminorm (h hx) (h hz)

/-- The weighted seminorm increases with the weight. -/
theorem weightedSeminorm_mono_weight (h : ∀ x ∈ D, ∀ z ∈ D, g (x - z) ≤ g' (x - z)) :
    weightedSeminorm g D f ≤ weightedSeminorm g' D f :=
  weightedSeminorm_le_iff.2 fun _ hx _ hz ↦
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (h _ hx _ hz))).trans
      (edist_mul_le_weightedSeminorm hx hz)

/-- The weighted seminorm of a constant function vanishes. -/
@[simp]
theorem weightedSeminorm_const (c : E) : weightedSeminorm g D (fun _ ↦ c) = 0 :=
  le_antisymm (weightedSeminorm_le_iff.2 fun _ _ _ _ ↦ by simp) bot_le

/-- The weighted seminorm depends only on the values on `D`. -/
theorem weightedSeminorm_congr {f' : V → E} (h : EqOn f f' D) :
    weightedSeminorm g D f = weightedSeminorm g D f' := by
  simp only [weightedSeminorm]
  refine iSup_congr fun x ↦ iSup_congr fun hx ↦ iSup_congr fun z ↦ iSup_congr fun hz ↦ ?_
  rw [h hx, h hz]

/-- The weighted Hölder bound in real form, for a finite seminorm. -/
theorem dist_mul_le_weightedSeminorm {F : Type*} [PseudoMetricSpace F] {f : V → F}
    (hf : weightedSeminorm g D f ≠ ∞) {x z : V} (hx : x ∈ D) (hz : z ∈ D) :
    dist (f x) (f z) * g (x - z) ≤ (weightedSeminorm g D f).toReal := by
  rcases le_or_gt (g (x - z)) 0 with hg | hg
  · exact (mul_nonpos_of_nonneg_of_nonpos dist_nonneg hg).trans ENNReal.toReal_nonneg
  · have hle := edist_mul_le_weightedSeminorm (f := f) (g := g) hx hz
    rw [edist_dist, ← ENNReal.ofReal_mul dist_nonneg] at hle
    exact (ENNReal.ofReal_le_iff_le_toReal hf).1 hle

end Weighted

section WeightedNormed

variable {V F : Type*} [Sub V] [SeminormedAddCommGroup F] {g : V → ℝ} {D : Set V} {f f' : V → F}

/-- The weighted seminorm is subadditive. -/
theorem weightedSeminorm_add_le :
    weightedSeminorm g D (f + f') ≤ weightedSeminorm g D f + weightedSeminorm g D f' :=
  weightedSeminorm_le_iff.2 fun _ hx _ hz ↦
    (mul_le_mul' (edist_add_add_le _ _ _ _) le_rfl).trans <| by
      rw [add_mul]
      exact add_le_add (edist_mul_le_weightedSeminorm hx hz)
        (edist_mul_le_weightedSeminorm hx hz)

/-- The weighted seminorm is invariant under negation. -/
@[simp]
theorem weightedSeminorm_neg : weightedSeminorm g D (-f) = weightedSeminorm g D f := by
  simp [weightedSeminorm]

/-- Scaling a function by `c` multiplies its weighted seminorm by at most `‖c‖`. -/
theorem weightedSeminorm_smul_le {𝕜 : Type*} [SeminormedRing 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] (c : 𝕜) :
    weightedSeminorm g D (c • f) ≤ ‖c‖₊ * weightedSeminorm g D f :=
  weightedSeminorm_le_iff.2 fun _ hx _ hz ↦ by
    simp only [Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul, mul_assoc]
    gcongr
    exact edist_mul_le_weightedSeminorm hx hz

end WeightedNormed

section Homogeneous

variable {n : ℕ} {E : Type*} [PseudoEMetricSpace E] {α : ℝ≥0} {D : Set (ℝ^n)}
  {f : ℝ^n → E} {g : ℝ^n → ℝ}

/-- For pairs on a coordinate line, ordered so that `z_i < x_i`, a `(-α)`-homogeneous weight
turns the weighted quotient into the directional one. -/
private theorem weighted_term_eq {i : Fin n} {x z : ℝ^n}
    (hg : ∀ t : ℝ, 0 < t → ∀ h, g (t • h) = t ^ (-(α : ℝ)) * g h)
    (h : ∀ j ≠ i, x j = z j) (hlt : z i < x i) :
    ENNReal.ofReal (g (EuclideanSpace.single i 1)) *
        (edist (f x) (f z) / edist (x i) (z i) ^ (α : ℝ)) =
      edist (f x) (f z) * ENNReal.ofReal (g (x - z)) := by
  have ht : 0 < x i - z i := sub_pos.2 hlt
  rw [sub_eq_smul_single h, hg _ ht, edist_dist, Real.dist_eq, abs_of_pos ht,
    ENNReal.ofReal_rpow_of_nonneg ht.le (NNReal.coe_nonneg α), div_eq_mul_inv,
    ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_neg ht.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  ring

/-- A `(-α)`-homogeneous weight dominates the directional seminorms:
`g(e_i) [f]_{C^α_{x_i}(D)} ≤ [f]_{C_g(D)}`. Chen and Hou use it with
`g₁(0, h₂) = g₁(0, 1) |h₂|^{-1/2}` for the second inequality in (5.26). -/
theorem ofReal_mul_directionalSeminorm_le (i : Fin n)
    (hg : ∀ t : ℝ, 0 < t → ∀ h, g (t • h) = t ^ (-(α : ℝ)) * g h) :
    ENNReal.ofReal (g (EuclideanSpace.single i 1)) * directionalSeminorm i α D f ≤
      weightedSeminorm g D f := by
  simp only [directionalSeminorm, ENNReal.mul_iSup, iSup_le_iff]
  intro x hx z hz h
  rcases lt_trichotomy (z i) (x i) with hlt | heq | hgt
  · rw [weighted_term_eq hg h hlt]
    exact edist_mul_le_weightedSeminorm hx hz
  · obtain rfl := eq_of_forall_ne_eq h heq.symm
    simp
  · rw [edist_comm (f x), edist_comm (x i),
      weighted_term_eq hg (fun j hj ↦ (h j hj).symm) hgt]
    exact edist_mul_le_weightedSeminorm hz hx

/-- The weighted seminorm of `g ∘ neg` equals that of `g`, since the supremum runs over
ordered pairs. -/
theorem weightedSeminorm_comp_neg :
    weightedSeminorm (fun h ↦ g (-h)) D f = weightedSeminorm g D f := by
  refine le_antisymm (weightedSeminorm_le_iff.2 fun x hx z hz ↦ ?_)
    (weightedSeminorm_le_iff.2 fun x hx z hz ↦ ?_)
  · rw [neg_sub, edist_comm]
    exact edist_mul_le_weightedSeminorm hz hx
  · have := edist_mul_le_weightedSeminorm (g := fun h ↦ g (-h)) (f := f) hz hx
    rwa [neg_sub, edist_comm] at this

/-- The reflected form of `ofReal_mul_directionalSeminorm_le`:
`g(-e_i) [f]_{C^α_{x_i}(D)} ≤ [f]_{C_g(D)}`. -/
theorem ofReal_neg_mul_directionalSeminorm_le (i : Fin n)
    (hg : ∀ t : ℝ, 0 < t → ∀ h, g (t • h) = t ^ (-(α : ℝ)) * g h) :
    ENNReal.ofReal (g (-EuclideanSpace.single i 1)) * directionalSeminorm i α D f ≤
      weightedSeminorm g D f := by
  rw [← weightedSeminorm_comp_neg]
  exact ofReal_mul_directionalSeminorm_le (g := fun h ↦ g (-h)) i
    fun t ht h ↦ by rw [← smul_neg, hg t ht]

end Homogeneous

section Path

variable {E : Type*} [PseudoEMetricSpace E] {α : ℝ≥0} {D : Set (ℝ^2)} {f : ℝ^2 → E}
  {g : ℝ^2 → ℝ}

/-- The rectangular path estimate of Chen and Hou (5.40) in seminorm form. If `D` contains the
corner `(z₁, x₂)` of every pair `x, z ∈ D`, and the `0`-homogeneous quantities `g(h) |h_i|^α`
are bounded by `A_i`, then `[f]_{C_g(D)} ≤ A₀ [f]_{C^α_{x_1}(D)} + A₁ [f]_{C^α_{x_2}(D)}`. -/
theorem weightedSeminorm_le_of_directional {A₀ A₁ : ℝ≥0∞}
    (hD : ∀ x ∈ D, ∀ z ∈ D, !₂[z 0, x 1] ∈ D)
    (hA₀ : ∀ h : ℝ^2, ENNReal.ofReal (g h) * ‖h 0‖ₑ ^ (α : ℝ) ≤ A₀)
    (hA₁ : ∀ h : ℝ^2, ENNReal.ofReal (g h) * ‖h 1‖ₑ ^ (α : ℝ) ≤ A₁) :
    weightedSeminorm g D f ≤ A₀ * directionalSeminorm 0 α D f +
      A₁ * directionalSeminorm 1 α D f := by
  refine weightedSeminorm_le_iff.2 fun x hx z hz ↦ ?_
  set w : ℝ^2 := !₂[z 0, x 1]
  have hw := hD x hx z hz
  have h₀ : ∀ j ≠ (0 : Fin 2), x j = w j := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · simp [w]
  have h₁ : ∀ j ≠ (1 : Fin 2), w j = z j := by
    intro j hj
    fin_cases j
    · simp [w]
    · exact absurd rfl hj
  have hx₀ : edist (x 0) (w 0) = ‖(x - z) 0‖ₑ := by
    simp [w, edist_eq_enorm_sub]
  have hx₁ : edist (w 1) (z 1) = ‖(x - z) 1‖ₑ := by
    simp [w, edist_eq_enorm_sub]
  calc edist (f x) (f z) * ENNReal.ofReal (g (x - z))
      ≤ (directionalSeminorm 0 α D f * ‖(x - z) 0‖ₑ ^ (α : ℝ) +
          directionalSeminorm 1 α D f * ‖(x - z) 1‖ₑ ^ (α : ℝ)) *
          ENNReal.ofReal (g (x - z)) := by
        gcongr
        refine (edist_triangle _ (f w) _).trans (add_le_add ?_ ?_)
        · rw [← hx₀]
          exact edist_le_directionalSeminorm_mul hx hw h₀
        · rw [← hx₁]
          exact edist_le_directionalSeminorm_mul hw hz h₁
    _ = directionalSeminorm 0 α D f * (ENNReal.ofReal (g (x - z)) * ‖(x - z) 0‖ₑ ^ (α : ℝ)) +
          directionalSeminorm 1 α D f *
            (ENNReal.ofReal (g (x - z)) * ‖(x - z) 1‖ₑ ^ (α : ℝ)) := by ring
    _ ≤ directionalSeminorm 0 α D f * A₀ + directionalSeminorm 1 α D f * A₁ := by
        gcongr
        · exact hA₀ _
        · exact hA₁ _
    _ = A₀ * directionalSeminorm 0 α D f + A₁ * directionalSeminorm 1 α D f := by ring

end Path

section Slice

variable {E : Type*} [PseudoEMetricSpace E] {α : ℝ≥0} {D : Set (ℝ^2)} {f : ℝ^2 → E}

/-- A horizontal slice `t ↦ f(t, a)` is `α`-Hölder with any constant `C ≥ [f]_{C^α_{x_1}(D)}`
on the set of `t` with `(t, a) ∈ D`. This feeds one-dimensional estimates on horizontal lines. -/
theorem holderOnWith_slice_zero {C : ℝ≥0} (hf : directionalSeminorm 0 α D f ≤ C) (a : ℝ) :
    HolderOnWith C α (fun t ↦ f !₂[t, a]) {t | !₂[t, a] ∈ D} := by
  intro s hs t ht
  have h : ∀ j ≠ (0 : Fin 2), (!₂[s, a] : ℝ^2) j = (!₂[t, a] : ℝ^2) j := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · simp
  have := edist_le_directionalSeminorm_mul (α := α) (f := f) (D := D)
    (show !₂[s, a] ∈ D from hs) (show !₂[t, a] ∈ D from ht) h
  simpa using this.trans (mul_le_mul' hf le_rfl)

/-- A vertical slice `t ↦ f(a, t)` is `α`-Hölder with any constant `C ≥ [f]_{C^α_{x_2}(D)}` on
the set of `t` with `(a, t) ∈ D`. -/
theorem holderOnWith_slice_one {C : ℝ≥0} (hf : directionalSeminorm 1 α D f ≤ C) (a : ℝ) :
    HolderOnWith C α (fun t ↦ f !₂[a, t]) {t | !₂[a, t] ∈ D} := by
  intro s hs t ht
  have h : ∀ j ≠ (1 : Fin 2), (!₂[a, s] : ℝ^2) j = (!₂[a, t] : ℝ^2) j := by
    intro j hj
    fin_cases j
    · simp
    · exact absurd rfl hj
  have := edist_le_directionalSeminorm_mul (α := α) (f := f) (D := D)
    (show !₂[a, s] ∈ D from hs) (show !₂[a, t] ∈ D from ht) h
  simpa using this.trans (mul_le_mul' hf le_rfl)

end Slice

section Product

/-- The product difference `ab - cd = (a - c) b + c (b - d)` in extended form. -/
theorem edist_mul_mul_le (a b c d : ℝ) :
    edist (a * b) (c * d) ≤ edist a c * ‖b‖ₑ + ‖c‖ₑ * edist b d := by
  simp only [edist_eq_enorm_sub]
  calc ‖a * b - c * d‖ₑ = ‖(a - c) * b + c * (b - d)‖ₑ := by ring_nf
    _ ≤ ‖(a - c) * b‖ₑ + ‖c * (b - d)‖ₑ := enorm_add_le _ _
    _ = ‖a - c‖ₑ * ‖b‖ₑ + ‖c‖ₑ * ‖b - d‖ₑ := by rw [enorm_mul, enorm_mul]

variable {n : ℕ} {i : Fin n} {α : ℝ≥0} {D : Set (ℝ^n)} {f g : ℝ^n → ℝ}

/-- Product rule for the directional seminorm:
`[fg]_{C^α_{x_i}} ≤ [f]_{C^α_{x_i}} sup_D |g| + sup_D |f| [g]_{C^α_{x_i}}`, with pointwise
suprema over `D`. -/
theorem directionalSeminorm_mul_le :
    directionalSeminorm i α D (f * g) ≤
      directionalSeminorm i α D f * (⨆ x ∈ D, ‖g x‖ₑ) +
        (⨆ x ∈ D, ‖f x‖ₑ) * directionalSeminorm i α D g :=
  directionalSeminorm_le_iff.2 fun x hx z hz hl ↦ by
    calc edist ((f * g) x) ((f * g) z)
        ≤ edist (f x) (f z) * ‖g x‖ₑ + ‖f z‖ₑ * edist (g x) (g z) := edist_mul_mul_le _ _ _ _
      _ ≤ directionalSeminorm i α D f * edist (x i) (z i) ^ (α : ℝ) * (⨆ x ∈ D, ‖g x‖ₑ) +
            (⨆ x ∈ D, ‖f x‖ₑ) *
              (directionalSeminorm i α D g * edist (x i) (z i) ^ (α : ℝ)) :=
          add_le_add
            (mul_le_mul' (edist_le_directionalSeminorm_mul hx hz hl)
              (le_iSup₂ (f := fun x _ ↦ ‖g x‖ₑ) x hx))
            (mul_le_mul' (le_iSup₂ (f := fun x _ ↦ ‖f x‖ₑ) z hz)
              (edist_le_directionalSeminorm_mul hx hz hl))
      _ = _ := by ring

variable {V : Type*} [Sub V] {w : V → ℝ} {S : Set V} {u v : V → ℝ}

/-- Product rule for the weighted seminorm:
`[uv]_{C_w} ≤ [u]_{C_w} sup_S |v| + sup_S |u| [v]_{C_w}`, with pointwise suprema over `S`. -/
theorem weightedSeminorm_mul_le :
    weightedSeminorm w S (u * v) ≤
      weightedSeminorm w S u * (⨆ x ∈ S, ‖v x‖ₑ) + (⨆ x ∈ S, ‖u x‖ₑ) * weightedSeminorm w S v :=
  weightedSeminorm_le_iff.2 fun x hx z hz ↦ by
    calc edist ((u * v) x) ((u * v) z) * ENNReal.ofReal (w (x - z))
        ≤ (edist (u x) (u z) * ‖v x‖ₑ + ‖u z‖ₑ * edist (v x) (v z)) *
            ENNReal.ofReal (w (x - z)) := mul_le_mul' (edist_mul_mul_le _ _ _ _) le_rfl
      _ = edist (u x) (u z) * ENNReal.ofReal (w (x - z)) * ‖v x‖ₑ +
            ‖u z‖ₑ * (edist (v x) (v z) * ENNReal.ofReal (w (x - z))) := by ring
      _ ≤ _ :=
          add_le_add
            (mul_le_mul' (edist_mul_le_weightedSeminorm hx hz)
              (le_iSup₂ (f := fun x _ ↦ ‖v x‖ₑ) x hx))
            (mul_le_mul' (le_iSup₂ (f := fun x _ ↦ ‖u x‖ₑ) z hz)
              (edist_mul_le_weightedSeminorm hx hz))

end Product

end HolderSpace
