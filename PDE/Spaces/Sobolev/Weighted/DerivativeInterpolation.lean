/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.DerivativeInterpolation.Basic

import CAS.ExactTactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite families of weighted adjacent-derivative estimates

We sum the adjacent-derivative estimates of
`PDE.Spaces.Sobolev.Weighted.DerivativeInterpolation.Basic` over finite families of rows, and we
prove the row estimate without compact support. Let `ιmid` be finite, `β : ιmid → ιprev` and
`γ : ιmid → ιnext` with `γ` injective, `M i ≥ 0`, `A0, A1 ≥ 0`, `η > 0` and `0 < θ < 1`. If
`M i ≤ A0 √(P (β i)) √(N (γ i)) + A1 √(P (β i)) √(M i)` for every `i`, then

  `(∑ i, √(M i))² ≤ η (∑ i, √(N i))² +
    weightedInterpolationStepConstant (card ιmid) A0 A1 η θ * (∑ i, √(P i))²`.

We apply this to finite families of compactly supported `C²` rows on the line, on the half line
`r > 0` and for `∂_r` and `∂_z` on the half plane `r > 0`; the rows on the half line and the `∂_r`
rows vanish at `r = 0`. Write `‖g‖_Φ = (∫ g² Φ)^(1/2)`. For functions of two variables we also prove
`∫ du² Φmid ≤ A0 ‖u‖_Φprev ‖ddu‖_Φnext + A1 ‖u‖_Φprev ‖du‖_Φmid` without compact support, when
`u du Φmid` tends to `0` at both ends of almost every line.

## Main results

* `weightedInterpolation_mixedIndex_row_aggregation`: the bound above.
  `weightedInterpolation_finite_row_aggregation` is the case `β = γ = id`.
* `weightedInterpolation_finite_family_integral_real`,
  `weightedInterpolation_finite_family_integral_Ioi`: for compactly supported `C²` functions `u i`
  and nonnegative `C¹` weights with `|Φmid| ≤ A0 √(Φprev Φnext)` and `|Φmid'| ≤ A1 √(Φprev Φmid)`,
  the bound above with `β = γ = id`, `M i = ‖(u i)'‖_Φmid²`, `N i = ‖(u i)''‖_Φnext²` and
  `P i = ‖u i‖_Φprev²`, on `ℝ`, and on `(0, ∞)` when `u i 0 = 0`.
* `weightedInterpolation_finite_family_integral_halfPlane_radial`,
  `weightedInterpolation_finite_family_integral_halfPlane_axial`: the same for `∂_r`, when
  `u i 0 z = 0`, and for `∂_z` on the half plane, with the integrability and measurability of the
  weighted terms as hypotheses.
* `interpolation_row_axial_of_tendsto`, `interpolation_row_radial_of_tendsto`: the row estimate for
  `∂_z` with respect to `μ.prod volume` and for `∂_r` with respect to
  `(volume.restrict (Ioi 0)).prod μ`, for an s-finite measure `μ`. The `_of_ae` versions assume the
  weight comparisons only almost everywhere.

## How it works

The aggregation is the summation (180) in the proof of Proposition 3 of Duruisseaux, Ganeshram,
George and Anandkumar, with `card ιmid` in place of the number `j + 1` of derivatives of order `j`
in two variables; the predecessor and successor maps are ours. We sum the row bounds, bound each
`√(P (β i))` by `∑ i, √(P i)` and, since `γ` is injective, `∑ i, √(N (γ i))` by `∑ i, √(N i)`.
Mathlib's `sq_sum_le_card_mul_sum_sq` gives `(∑ i, √(M i))² ≤ card ιmid * ∑ i, M i`, and
`weightedInterpolationStep_from_base` does the Young steps (181)-(182). For the rows without compact
support we prove `∫ du² Φmid = -∫ u ddu Φmid - ∫ u du dΦ` on almost every line with Mathlib's
`MeasureTheory.integral_of_hasDerivAt_of_tendsto` on `ℝ` and
`MeasureTheory.integral_Ioi_deriv_mul_eq_sub` on `(0, ∞)`, integrate it over the other variable with
`MeasureTheory.integral_prod`, and conclude with
`weightedInterpolation_row_base_integral_measure_of_ae`. The limits of `u du Φmid` are our form of
the boundary-flux assumption of Proposition 3. The derivatives of `u du` and `u du Φmid` are
computed by the `cas` tactic of SymLean, our verified computer algebra system.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix A, Proposition 3,
  (174)-(182), pp. 38-39, for the estimate (176) from the row bounds (177)-(179) by the summation
  (180), with the factor `j + 1`, and the Young steps (181)-(182).
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology

namespace SobolevSpace.Weighted

/-- Let `β : ιmid → ιprev` and `γ : ιmid → ιnext` with `γ` injective, `M i ≥ 0` for every `i`,
`A0, A1 ≥ 0`, `η > 0` and `0 < θ < 1`. If `M i ≤ A0 √(P (β i)) √(N (γ i)) + A1 √(P (β i)) √(M i)`
for every `i`, then `(∑ i, √(M i))² ≤ η (∑ i, √(N i))² + C * (∑ i, √(P i))²` with
`C = weightedInterpolationStepConstant (card ιmid) A0 A1 η θ`. -/
theorem weightedInterpolation_mixedIndex_row_aggregation
    {ιprev ιmid ιnext : Type*}
    [Fintype ιprev] [Fintype ιmid] [Fintype ιnext]
    (β : ιmid → ιprev) (γ : ιmid → ιnext) (hγ : Function.Injective γ)
    (P : ιprev → ℝ) (M : ιmid → ℝ) (N : ιnext → ℝ)
    {A0 A1 η θ : ℝ}
    (hM : ∀ i, 0 ≤ M i)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hrow : ∀ i,
      M i ≤
        A0 * √(P (β i)) * √(N (γ i)) +
          A1 * √(P (β i)) * √(M i)) :
    (∑ i, √(M i)) ^ 2 ≤
      η * (∑ i, √(N i)) ^ 2 +
        weightedInterpolationStepConstant (Fintype.card ιmid : ℝ)
          A0 A1 η θ * (∑ i, √(P i)) ^ 2 := by
  classical
  set XP := ∑ i, √(P i)
  set XM := ∑ i, √(M i)
  set XN := ∑ i, √(N i)
  have hXP : 0 ≤ XP := Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg (P i)
  have hP : ∀ i, √(P i) ≤ XP := fun i ↦
    Finset.single_le_sum (fun j _ ↦ Real.sqrt_nonneg (P j)) (Finset.mem_univ i)
  have hN : ∑ i, √(N (γ i)) ≤ XN := (Finset.sum_image hγ.injOn).symm.trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ ↦
      Real.sqrt_nonneg (N k))
  have hrows : ∑ i, M i ≤ A0 * XP * XN + A1 * XP * XM := calc
    ∑ i, M i ≤ ∑ i, (A0 * XP * √(N (γ i)) + A1 * XP * √(M i)) :=
      Finset.sum_le_sum fun i _ ↦ (hrow i).trans (by have hPβ := hP (β i); gcongr)
    _ = A0 * XP * ∑ i, √(N (γ i)) + A1 * XP * XM := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by gcongr
  have hcard := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ √(M i))
  refine weightedInterpolationStep_from_base hη hθ0 hθ1 ?_
  calc XM ^ 2 ≤ (Fintype.card ιmid : ℝ) * ∑ i, M i := by
        simpa [XM, Real.sq_sqrt (hM _)] using hcard
    _ ≤ (Fintype.card ιmid : ℝ) * (A0 * XP * XN + A1 * XP * XM) := by gcongr
    _ = _ := by ring

/-- Let `M i ≥ 0` for every `i`, `A0, A1 ≥ 0`, `η > 0` and `0 < θ < 1`. If
`M i ≤ A0 √(P i) √(N i) + A1 √(P i) √(M i)` for every `i`, then
`(∑ i, √(M i))² ≤ η (∑ i, √(N i))² + C * (∑ i, √(P i))²` with
`C = weightedInterpolationStepConstant (card ι) A0 A1 η θ`. -/
theorem weightedInterpolation_finite_row_aggregation
    {ι : Type*} [Fintype ι]
    (P M N : ι → ℝ) {A0 A1 η θ : ℝ}
    (hM : ∀ i, 0 ≤ M i)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hrow : ∀ i,
      M i ≤
        A0 * √(P i) * √(N i) +
          A1 * √(P i) * √(M i)) :
    (∑ i, √(M i)) ^ 2 ≤
      η * (∑ i, √(N i)) ^ 2 +
        weightedInterpolationStepConstant (Fintype.card ι : ℝ) A0 A1 η θ *
          (∑ i, √(P i)) ^ 2 :=
  weightedInterpolation_mixedIndex_row_aggregation id id Function.injective_id P M N hM hA0 hA1
    hη hθ0 hθ1 hrow

/-- Let each `u i : ℝ → ℝ` be `C²` with compact support, and let `Φprev`, `Φmid` and `Φnext` be
nonnegative and `C¹` with `|Φmid| ≤ A0 √Φprev √Φnext` and `|Φmid'| ≤ A1 √Φprev √Φmid`, where
`A0, A1 ≥ 0`. Then for `η > 0` and `0 < θ < 1`,
`(∑ i, ‖(u i)'‖_Φmid)² ≤ η (∑ i, ‖(u i)''‖_Φnext)² + C * (∑ i, ‖u i‖_Φprev)²`, where
`C = weightedInterpolationStepConstant (card ι) A0 A1 η θ` and `‖g‖_Φ = (∫ g² Φ)^(1/2)` over `ℝ`.
Each row is paired with its own derivatives; the two-dimensional statement, where rows of order `j`
are paired with rows of orders `j - 1` and `j + 1`, is
`weightedInterpolation_twoDimensional_from_coordinate_rows`. -/
theorem weightedInterpolation_finite_family_integral_real
    {ι : Type*} [Fintype ι]
    (u : ι → ℝ → ℝ) {Φprev Φmid Φnext : ℝ → ℝ} {A0 A1 η θ : ℝ}
    (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hcu : ∀ i, HasCompactSupport (u i))
    (hΦprev : ContDiff ℝ 1 Φprev)
    (hΦmid : ContDiff ℝ 1 Φmid)
    (hΦnext : ContDiff ℝ 1 Φnext)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ x,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ x,
      |deriv Φmid x| ≤ A1 * √(Φprev x) * √(Φmid x)) :
    (∑ i, √(∫ x : ℝ, deriv (u i) x ^ 2 * Φmid x)) ^ 2 ≤
      η * (∑ i,
        √(∫ x : ℝ, deriv (deriv (u i)) x ^ 2 * Φnext x)) ^ 2 +
      weightedInterpolationStepConstant (Fintype.card ι : ℝ) A0 A1 η θ *
        (∑ i, √(∫ x : ℝ, u i x ^ 2 * Φprev x)) ^ 2 := by
  refine weightedInterpolation_finite_row_aggregation _ _ _ (fun i ↦ ?_) hA0 hA1 hη hθ0 hθ1
    fun i ↦ ?_
  · exact integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (hmid_nonneg x)
  · exact weightedInterpolation_row_base_integral_real (hu i) hΦprev hΦmid hΦnext (hcu i) hA0
      hA1 hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1

/-- Let each `u i : ℝ → ℝ` be `C²` with compact support and `u i 0 = 0`, and let `Φprev`, `Φmid` and
`Φnext` be nonnegative and `C¹` with `|Φmid| ≤ A0 √Φprev √Φnext` and `|Φmid'| ≤ A1 √Φprev √Φmid`,
where `A0, A1 ≥ 0`. Then for `η > 0` and `0 < θ < 1`,
`(∑ i, ‖(u i)'‖_Φmid)² ≤ η (∑ i, ‖(u i)''‖_Φnext)² + C * (∑ i, ‖u i‖_Φprev)²`, where
`C = weightedInterpolationStepConstant (card ι) A0 A1 η θ` and `‖g‖_Φ = (∫ g² Φ)^(1/2)` over
`(0, ∞)`. -/
theorem weightedInterpolation_finite_family_integral_Ioi
    {ι : Type*} [Fintype ι]
    (u : ι → ℝ → ℝ) {Φprev Φmid Φnext : ℝ → ℝ} {A0 A1 η θ : ℝ}
    (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hcu : ∀ i, HasCompactSupport (u i))
    (hu0 : ∀ i, u i 0 = 0)
    (hΦprev : ContDiff ℝ 1 Φprev)
    (hΦmid : ContDiff ℝ 1 Φmid)
    (hΦnext : ContDiff ℝ 1 Φnext)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ x,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ x,
      |deriv Φmid x| ≤ A1 * √(Φprev x) * √(Φmid x)) :
    (∑ i, √(∫ x in Set.Ioi (0 : ℝ), deriv (u i) x ^ 2 * Φmid x)) ^ 2 ≤
      η * (∑ i, √(∫ x in Set.Ioi (0 : ℝ),
          deriv (deriv (u i)) x ^ 2 * Φnext x)) ^ 2 +
      weightedInterpolationStepConstant (Fintype.card ι : ℝ) A0 A1 η θ *
        (∑ i, √(∫ x in Set.Ioi (0 : ℝ), u i x ^ 2 * Φprev x)) ^ 2 := by
  refine weightedInterpolation_finite_row_aggregation _ _ _ (fun i ↦ ?_) hA0 hA1 hη hθ0 hθ1
    fun i ↦ ?_
  · exact integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (hmid_nonneg x)
  · exact weightedInterpolation_row_base_integral_Ioi (hu i) hΦprev hΦmid hΦnext (hcu i) (hu0 i)
      hA0 hA1 hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1

/-- Let each `u i r z` be `C²` with compact support in `r` for every `z`, with `u i 0 z = 0`, and
let the weights be nonnegative with `r ↦ Φmid r z` of class `C¹`, `|Φmid| ≤ A0 √Φprev √Φnext` and
`|∂_r Φmid| ≤ A1 √Φprev √Φmid`, where `A0, A1 ≥ 0`. Suppose that for every `i`, with `u = u i`, the
functions `u² Φprev`, `(∂_r u)² Φmid`, `(∂_r² u)² Φnext`, `u ∂_r² u Φmid` and `u ∂_r u ∂_r Φmid` are
integrable and `u √Φprev`, `∂_r u √Φmid` and `∂_r² u √Φnext` are a.e. strongly measurable for
`dz dr` on `ℝ × (0, ∞)`. Then for `η > 0` and `0 < θ < 1`,
`(∑ i, ‖∂_r u i‖_Φmid)² ≤ η (∑ i, ‖∂_r² u i‖_Φnext)² + C * (∑ i, ‖u i‖_Φprev)²`, where
`C = weightedInterpolationStepConstant (card ι) A0 A1 η θ` and the weighted norms are for `dz dr` on
`ℝ × (0, ∞)`. -/
theorem weightedInterpolation_finite_family_integral_halfPlane_radial
    {ι : Type*} [Fintype ι]
    (u : ι → ℝ → ℝ → ℝ)
    {Φprev Φmid Φnext : ℝ → ℝ → ℝ} {A0 A1 η θ : ℝ}
    (hu : ∀ i z, ContDiff ℝ 2 (fun r ↦ u i r z))
    (hcu : ∀ i z, HasCompactSupport (fun r ↦ u i r z))
    (hu0 : ∀ i z, u i 0 z = 0)
    (hΦmid : ∀ z, ContDiff ℝ 1 (fun r ↦ Φmid r z))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * √(Φprev r z) * √(Φnext r z))
    (hcompare1 : ∀ r z,
      |deriv (fun s ↦ Φmid s z) r| ≤
        A1 * √(Φprev r z) * √(Φmid r z))
    (hprev_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦ u i p.2 p.1 ^ 2 * Φprev p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hmid_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        deriv (fun r ↦ u i r p.1) p.2 ^ 2 * Φmid p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hnext_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun r ↦ u i r p.1)) p.2 ^ 2 * Φnext p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hterm0_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        u i p.2 p.1 * deriv (deriv (fun r ↦ u i r p.1)) p.2 * Φmid p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hterm1_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        u i p.2 p.1 * deriv (fun r ↦ u i r p.1) p.2 *
          deriv (fun r ↦ Φmid r p.1) p.2)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hprev_meas : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u i p.2 p.1 * √(Φprev p.2 p.1))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hmid_meas : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (fun r ↦ u i r p.1) p.2 * √(Φmid p.2 p.1))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hnext_meas : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun r ↦ u i r p.1)) p.2 * √(Φnext p.2 p.1))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) :
    (∑ i, √(∫ p : ℝ × ℝ,
        deriv (fun r ↦ u i r p.1) p.2 ^ 2 * Φmid p.2 p.1
          ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))) ^ 2 ≤
      η * (∑ i, √(∫ p : ℝ × ℝ,
          deriv (deriv (fun r ↦ u i r p.1)) p.2 ^ 2 * Φnext p.2 p.1
            ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))) ^ 2 +
      weightedInterpolationStepConstant (Fintype.card ι : ℝ) A0 A1 η θ *
        (∑ i, √(∫ p : ℝ × ℝ, u i p.2 p.1 ^ 2 * Φprev p.2 p.1
            ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))) ^ 2 := by
  refine weightedInterpolation_finite_row_aggregation _ _ _ (fun i ↦ ?_) hA0 hA1 hη hθ0 hθ1
    fun i ↦ ?_
  · exact integral_nonneg fun p ↦ mul_nonneg (sq_nonneg _) (hmid_nonneg p.2 p.1)
  · exact weightedInterpolation_row_base_integral_halfPlane_radial (hu i) hΦmid (hcu i) (hu0 i)
      hA0 hA1 hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1 (hprev_int i)
      (hmid_int i) (hnext_int i) (hterm0_int i) (hterm1_int i) (hprev_meas i) (hmid_meas i)
      (hnext_meas i)

/-- Let each `u i r z` be `C²` with compact support in `z` for every `r`, and let the weights be
nonnegative with `z ↦ Φmid r z` of class `C¹`, `|Φmid| ≤ A0 √Φprev √Φnext` and
`|∂_z Φmid| ≤ A1 √Φprev √Φmid`, where `A0, A1 ≥ 0`. Suppose that for every `i`, with `u = u i`, the
functions `u² Φprev`, `(∂_z u)² Φmid`, `(∂_z² u)² Φnext`, `u ∂_z² u Φmid` and `u ∂_z u ∂_z Φmid` are
integrable and `u √Φprev`, `∂_z u √Φmid` and `∂_z² u √Φnext` are a.e. strongly measurable for
`dr dz` on `(0, ∞) × ℝ`. Then for `η > 0` and `0 < θ < 1`,
`(∑ i, ‖∂_z u i‖_Φmid)² ≤ η (∑ i, ‖∂_z² u i‖_Φnext)² + C * (∑ i, ‖u i‖_Φprev)²`, where
`C = weightedInterpolationStepConstant (card ι) A0 A1 η θ` and the weighted norms are for `dr dz` on
`(0, ∞) × ℝ`. -/
theorem weightedInterpolation_finite_family_integral_halfPlane_axial
    {ι : Type*} [Fintype ι]
    (u : ι → ℝ → ℝ → ℝ)
    {Φprev Φmid Φnext : ℝ → ℝ → ℝ} {A0 A1 η θ : ℝ}
    (hu : ∀ i r, ContDiff ℝ 2 (fun z ↦ u i r z))
    (hcu : ∀ i r, HasCompactSupport (fun z ↦ u i r z))
    (hΦmid : ∀ r, ContDiff ℝ 1 (fun z ↦ Φmid r z))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * √(Φprev r z) * √(Φnext r z))
    (hcompare1 : ∀ r z,
      |deriv (fun s ↦ Φmid r s) z| ≤
        A1 * √(Φprev r z) * √(Φmid r z))
    (hprev_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦ u i p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        deriv (fun z ↦ u i p.1 z) p.2 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun z ↦ u i p.1 z)) p.2 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm0_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        u i p.1 p.2 * deriv (deriv (fun z ↦ u i p.1 z)) p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm1_int : ∀ i, Integrable
      (fun p : ℝ × ℝ ↦
        u i p.1 p.2 * deriv (fun z ↦ u i p.1 z) p.2 *
          deriv (fun z ↦ Φmid p.1 z) p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hprev_meas : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u i p.1 p.2 * √(Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_meas : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (fun z ↦ u i p.1 z) p.2 * √(Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_meas : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun z ↦ u i p.1 z)) p.2 * √(Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∑ i, √(∫ p : ℝ × ℝ,
        deriv (fun z ↦ u i p.1 z) p.2 ^ 2 * Φmid p.1 p.2
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))) ^ 2 ≤
      η * (∑ i, √(∫ p : ℝ × ℝ,
          deriv (deriv (fun z ↦ u i p.1 z)) p.2 ^ 2 * Φnext p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))) ^ 2 +
      weightedInterpolationStepConstant (Fintype.card ι : ℝ) A0 A1 η θ *
        (∑ i, √(∫ p : ℝ × ℝ, u i p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))) ^ 2 := by
  refine weightedInterpolation_finite_row_aggregation _ _ _ (fun i ↦ ?_) hA0 hA1 hη hθ0 hθ1
    fun i ↦ ?_
  · exact integral_nonneg fun p ↦ mul_nonneg (sq_nonneg _) (hmid_nonneg p.1 p.2)
  · exact weightedInterpolation_row_base_integral_halfPlane_axial (hu i) hΦmid (hcu i) hA0 hA1
      hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1 (hprev_int i) (hmid_int i)
      (hnext_int i) (hterm0_int i) (hterm1_int i) (hprev_meas i) (hmid_meas i) (hnext_meas i)

/-- Let `μ` be s-finite, `A0, A1 ≥ 0` and `ν = μ.prod volume`, for pairs `(r, z)`. Suppose that for
`μ`-almost every `r`, `z ↦ u r z`, `z ↦ du r z` and `z ↦ Φmid r z` have derivatives `du r z`,
`ddu r z` and `dΦ r z` at every `z`, and `u r z * du r z * Φmid r z` tends to `0` as `z → ±∞`. Let
the weights be nonnegative, with `|Φmid| ≤ A0 √Φprev √Φnext` and `|dΦ| ≤ A1 √Φprev √Φmid` `ν`-almost
everywhere, let `u² Φprev`, `du² Φmid`, `ddu² Φnext`, `u ddu Φmid` and `u du dΦ` be `ν`-integrable
and `u √Φprev`, `du √Φmid` and `ddu √Φnext` `ν`-a.e. strongly measurable. Then
`∫ du² Φmid dν ≤ A0 ‖u‖_Φprev ‖ddu‖_Φnext + A1 ‖u‖_Φprev ‖du‖_Φmid`, where
`‖g‖_Φ = (∫ g² Φ dν)^(1/2)`. -/
theorem interpolation_row_axial_of_tendsto_of_ae
    {μ : Measure ℝ} [SFinite μ]
    {u du ddu Φprev Φmid Φnext dΦ : ℝ → ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ∀ᵐ r ∂μ, ∀ z, HasDerivAt (u r) (du r z) z)
    (hdu : ∀ᵐ r ∂μ, ∀ z, HasDerivAt (du r) (ddu r z) z)
    (hΦ : ∀ᵐ r ∂μ, ∀ z, HasDerivAt (Φmid r) (dΦ r z) z)
    (hbot : ∀ᵐ r ∂μ,
      Tendsto (fun z ↦ u r z * du r z * Φmid r z) atBot (𝓝 0))
    (htop : ∀ᵐ r ∂μ,
      Tendsto (fun z ↦ u r z * du r z * Φmid r z) atTop (𝓝 0))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ᵐ p : ℝ × ℝ ∂(μ.prod volume),
      |Φmid p.1 p.2| ≤ A0 * √(Φprev p.1 p.2) * √(Φnext p.1 p.2))
    (hcompare1 : ∀ᵐ p : ℝ × ℝ ∂(μ.prod volume),
      |dΦ p.1 p.2| ≤ A1 * √(Φprev p.1 p.2) * √(Φmid p.1 p.2))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 ^ 2 * Φprev p.1 p.2) (μ.prod volume))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 ^ 2 * Φmid p.1 p.2) (μ.prod volume))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 ^ 2 * Φnext p.1 p.2) (μ.prod volume))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * ddu p.1 p.2 * Φmid p.1 p.2) (μ.prod volume))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * du p.1 p.2 * dΦ p.1 p.2) (μ.prod volume))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * √(Φprev p.1 p.2)) (μ.prod volume))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 * √(Φmid p.1 p.2)) (μ.prod volume))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 * √(Φnext p.1 p.2)) (μ.prod volume)) :
    (∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2 ∂μ.prod volume) ≤
      A0 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2 ∂μ.prod volume) *
        √(∫ p : ℝ × ℝ, ddu p.1 p.2 ^ 2 * Φnext p.1 p.2 ∂μ.prod volume) +
      A1 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2 ∂μ.prod volume) *
        √(∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2 ∂μ.prod volume) := by
  have hslice : ∀ᵐ r ∂μ,
      (∫ z : ℝ, du r z ^ 2 * Φmid r z) =
        -(∫ z : ℝ, u r z * ddu r z * Φmid r z) -
          (∫ z : ℝ, u r z * du r z * dΦ r z) := by
    filter_upwards [hu, hdu, hΦ, hbot, htop,
      hmid_int.prod_right_ae, hterm0_int.prod_right_ae, hterm1_int.prod_right_ae]
      with r hur hdur hΦr hbotr htopr hmidr hterm0r hterm1r
    have hflux : ∀ z, HasDerivAt (fun s ↦ u r s * du r s * Φmid r s)
        (du r z ^ 2 * Φmid r z +
          u r z * ddu r z * Φmid r z + u r z * du r z * dΦ r z) z := fun z ↦
      (((hur z).mul (hdur z)).mul (hΦr z)).congr_deriv (by cas)
    have hftc := integral_of_hasDerivAt_of_tendsto hflux
      ((hmidr.add hterm0r).add hterm1r) hbotr htopr
    have hadd := integral_add (hmidr.add hterm0r) hterm1r
    have hadd0 := integral_add hmidr hterm0r
    simp only [Pi.add_apply] at hadd hadd0
    linarith
  have hid :
      (∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2 ∂μ.prod volume) =
        -(∫ p : ℝ × ℝ, u p.1 p.2 * ddu p.1 p.2 * Φmid p.1 p.2 ∂μ.prod volume) -
          (∫ p : ℝ × ℝ, u p.1 p.2 * du p.1 p.2 * dΦ p.1 p.2 ∂μ.prod volume) := by
    have hsub := integral_sub hterm0_int.integral_prod_left.neg hterm1_int.integral_prod_left
    simp only [Pi.neg_apply] at hsub
    rw [integral_prod _ hmid_int, integral_prod _ hterm0_int, integral_prod _ hterm1_int,
      integral_congr_ae hslice, hsub, integral_neg]
  exact weightedInterpolation_row_base_integral_measure_of_ae hA0 hA1
    (fun p ↦ hprev_nonneg p.1 p.2) (fun p ↦ hmid_nonneg p.1 p.2) (fun p ↦ hnext_nonneg p.1 p.2)
    hcompare0 hcompare1 hprev_int hmid_int hnext_int hterm0_int hterm1_int hprev_meas hmid_meas
    hnext_meas hid

/-- Let `μ` be s-finite, `A0, A1 ≥ 0` and `ν = μ.prod volume`, for pairs `(r, z)`. Suppose that for
`μ`-almost every `r`, `z ↦ u r z`, `z ↦ du r z` and `z ↦ Φmid r z` have derivatives `du r z`,
`ddu r z` and `dΦ r z` at every `z`, and `u r z * du r z * Φmid r z` tends to `0` as `z → ±∞`. Let
the weights be nonnegative, with `|Φmid| ≤ A0 √Φprev √Φnext` and `|dΦ| ≤ A1 √Φprev √Φmid`
everywhere, let `u² Φprev`, `du² Φmid`, `ddu² Φnext`, `u ddu Φmid` and `u du dΦ` be `ν`-integrable
and `u √Φprev`, `du √Φmid` and `ddu √Φnext` `ν`-a.e. strongly measurable. Then
`∫ du² Φmid dν ≤ A0 ‖u‖_Φprev ‖ddu‖_Φnext + A1 ‖u‖_Φprev ‖du‖_Φmid`, where
`‖g‖_Φ = (∫ g² Φ dν)^(1/2)`. No compact support is assumed, and `u du Φmid` need not be integrable.
-/
theorem interpolation_row_axial_of_tendsto
    {μ : Measure ℝ} [SFinite μ]
    {u du ddu Φprev Φmid Φnext dΦ : ℝ → ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ∀ᵐ r ∂μ, ∀ z, HasDerivAt (u r) (du r z) z)
    (hdu : ∀ᵐ r ∂μ, ∀ z, HasDerivAt (du r) (ddu r z) z)
    (hΦ : ∀ᵐ r ∂μ, ∀ z, HasDerivAt (Φmid r) (dΦ r z) z)
    (hbot : ∀ᵐ r ∂μ,
      Tendsto (fun z ↦ u r z * du r z * Φmid r z) atBot (𝓝 0))
    (htop : ∀ᵐ r ∂μ,
      Tendsto (fun z ↦ u r z * du r z * Φmid r z) atTop (𝓝 0))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤ A0 * √(Φprev r z) * √(Φnext r z))
    (hcompare1 : ∀ r z,
      |dΦ r z| ≤ A1 * √(Φprev r z) * √(Φmid r z))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 ^ 2 * Φprev p.1 p.2) (μ.prod volume))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 ^ 2 * Φmid p.1 p.2) (μ.prod volume))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 ^ 2 * Φnext p.1 p.2) (μ.prod volume))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * ddu p.1 p.2 * Φmid p.1 p.2) (μ.prod volume))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * du p.1 p.2 * dΦ p.1 p.2) (μ.prod volume))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * √(Φprev p.1 p.2)) (μ.prod volume))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 * √(Φmid p.1 p.2)) (μ.prod volume))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 * √(Φnext p.1 p.2)) (μ.prod volume)) :
    (∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2 ∂μ.prod volume) ≤
      A0 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2 ∂μ.prod volume) *
        √(∫ p : ℝ × ℝ, ddu p.1 p.2 ^ 2 * Φnext p.1 p.2 ∂μ.prod volume) +
      A1 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2 ∂μ.prod volume) *
        √(∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2 ∂μ.prod volume) :=
  interpolation_row_axial_of_tendsto_of_ae hu hdu hΦ hbot htop hA0 hA1 hprev_nonneg hmid_nonneg
    hnext_nonneg (ae_of_all _ fun p ↦ hcompare0 p.1 p.2) (ae_of_all _ fun p ↦ hcompare1 p.1 p.2)
    hprev_int hmid_int hnext_int hterm0_int hterm1_int hprev_meas hmid_meas hnext_meas

/-- Let `μ` be s-finite, `A0, A1 ≥ 0` and `ν = (volume.restrict (Ioi 0)).prod μ`, for pairs
`(r, z)`. Suppose that for `μ`-almost every `z`, `r ↦ u r z`, `r ↦ du r z` and `r ↦ Φmid r z` have
derivatives `du r z`, `ddu r z` and `dΦ r z` at every `r > 0`, and `u r z * du r z * Φmid r z` tends
to `0` as `r → 0+` and as `r → ∞`. Let the weights be nonnegative, with `|Φmid| ≤ A0 √Φprev √Φnext`
and `|dΦ| ≤ A1 √Φprev √Φmid` `ν`-almost everywhere, let `u² Φprev`, `du² Φmid`, `ddu² Φnext`,
`u ddu Φmid` and `u du dΦ` be `ν`-integrable and `u √Φprev`, `du √Φmid` and `ddu √Φnext` `ν`-a.e.
strongly measurable. Then `∫ du² Φmid dν ≤ A0 ‖u‖_Φprev ‖ddu‖_Φnext + A1 ‖u‖_Φprev ‖du‖_Φmid`, where
`‖g‖_Φ = (∫ g² Φ dν)^(1/2)`. -/
theorem interpolation_row_radial_of_tendsto_of_ae
    {μ : Measure ℝ} [SFinite μ]
    {u du ddu Φprev Φmid Φnext dΦ : ℝ → ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ∀ᵐ z ∂μ, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ u s z) (du r z) r)
    (hdu : ∀ᵐ z ∂μ, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ du s z) (ddu r z) r)
    (hΦ : ∀ᵐ z ∂μ, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ Φmid s z) (dΦ r z) r)
    (hzero : ∀ᵐ z ∂μ,
      Tendsto (fun r ↦ u r z * du r z * Φmid r z) (𝓝[>] 0) (𝓝 0))
    (htop : ∀ᵐ z ∂μ,
      Tendsto (fun r ↦ u r z * du r z * Φmid r z) atTop (𝓝 0))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ),
      |Φmid p.1 p.2| ≤ A0 * √(Φprev p.1 p.2) * √(Φnext p.1 p.2))
    (hcompare1 : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ),
      |dΦ p.1 p.2| ≤ A1 * √(Φprev p.1 p.2) * √(Φmid p.1 p.2))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * ddu p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * du p.1 p.2 * dΦ p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * √(Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 * √(Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 * √(Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) :
    (∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) ≤
      A0 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) *
        √(∫ p : ℝ × ℝ, ddu p.1 p.2 ^ 2 * Φnext p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) +
      A1 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) *
        √(∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) := by
  have hslice : ∀ᵐ z ∂μ,
      (∫ r in Set.Ioi (0 : ℝ), du r z ^ 2 * Φmid r z) =
        -(∫ r in Set.Ioi (0 : ℝ), u r z * ddu r z * Φmid r z) -
          (∫ r in Set.Ioi (0 : ℝ), u r z * du r z * dΦ r z) := by
    filter_upwards [hu, hdu, hΦ, hzero, htop,
      hmid_int.prod_left_ae, hterm0_int.prod_left_ae, hterm1_int.prod_left_ae]
      with z huz hduz hΦz hzeroz htopz hmidz hterm0z hterm1z
    have hproduct : ∀ r ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun s ↦ u s z * du s z) (du r z ^ 2 + u r z * ddu r z) r := fun r hr ↦
      ((huz r hr).mul (hduz r hr)).congr_deriv (by cas)
    have hflux_eq :
        (fun r ↦ (du r z ^ 2 + u r z * ddu r z) * Φmid r z +
          u r z * du r z * dΦ r z) =
        (fun r ↦ du r z ^ 2 * Φmid r z +
          u r z * ddu r z * Φmid r z + u r z * du r z * dΦ r z) := by
      funext r
      cas
    have hflux_int : IntegrableOn
        (fun r ↦ (du r z ^ 2 + u r z * ddu r z) * Φmid r z +
          u r z * du r z * dΦ r z) (Set.Ioi (0 : ℝ)) := by
      rw [hflux_eq]
      exact (hmidz.add hterm0z).add hterm1z
    have hftc := integral_Ioi_deriv_mul_eq_sub hproduct hΦz hflux_int hzeroz htopz
    rw [hflux_eq] at hftc
    have hadd := integral_add (hmidz.add hterm0z) hterm1z
    have hadd0 := integral_add hmidz hterm0z
    simp only [Pi.add_apply] at hadd hadd0
    linarith
  have hid :
      (∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) =
        -(∫ p : ℝ × ℝ, u p.1 p.2 * ddu p.1 p.2 * Φmid p.1 p.2
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) -
          (∫ p : ℝ × ℝ, u p.1 p.2 * du p.1 p.2 * dΦ p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) := by
    have hsub := integral_sub hterm0_int.integral_prod_right.neg hterm1_int.integral_prod_right
    simp only [Pi.neg_apply] at hsub
    rw [integral_prod_symm _ hmid_int, integral_prod_symm _ hterm0_int,
      integral_prod_symm _ hterm1_int, integral_congr_ae hslice, hsub, integral_neg]
  exact weightedInterpolation_row_base_integral_measure_of_ae hA0 hA1
    (fun p ↦ hprev_nonneg p.1 p.2) (fun p ↦ hmid_nonneg p.1 p.2) (fun p ↦ hnext_nonneg p.1 p.2)
    hcompare0 hcompare1 hprev_int hmid_int hnext_int hterm0_int hterm1_int hprev_meas hmid_meas
    hnext_meas hid

/-- Let `μ` be s-finite, `A0, A1 ≥ 0` and `ν = (volume.restrict (Ioi 0)).prod μ`, for pairs
`(r, z)`. Suppose that for `μ`-almost every `z`, `r ↦ u r z`, `r ↦ du r z` and `r ↦ Φmid r z` have
derivatives `du r z`, `ddu r z` and `dΦ r z` at every `r > 0`, and `u r z * du r z * Φmid r z` tends
to `0` as `r → 0+` and as `r → ∞`. Let the weights be nonnegative, with `|Φmid| ≤ A0 √Φprev √Φnext`
and `|dΦ| ≤ A1 √Φprev √Φmid` everywhere, let `u² Φprev`, `du² Φmid`, `ddu² Φnext`, `u ddu Φmid` and
`u du dΦ` be `ν`-integrable and `u √Φprev`, `du √Φmid` and `ddu √Φnext` `ν`-a.e. strongly
measurable. Then `∫ du² Φmid dν ≤ A0 ‖u‖_Φprev ‖ddu‖_Φnext + A1 ‖u‖_Φprev ‖du‖_Φmid`, where
`‖g‖_Φ = (∫ g² Φ dν)^(1/2)`. No compact support is assumed, `u du Φmid` need not be integrable, and
neither `u` nor `du` has to vanish at `r = 0`. -/
theorem interpolation_row_radial_of_tendsto
    {μ : Measure ℝ} [SFinite μ]
    {u du ddu Φprev Φmid Φnext dΦ : ℝ → ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ∀ᵐ z ∂μ, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ u s z) (du r z) r)
    (hdu : ∀ᵐ z ∂μ, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ du s z) (ddu r z) r)
    (hΦ : ∀ᵐ z ∂μ, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ Φmid s z) (dΦ r z) r)
    (hzero : ∀ᵐ z ∂μ,
      Tendsto (fun r ↦ u r z * du r z * Φmid r z) (𝓝[>] 0) (𝓝 0))
    (htop : ∀ᵐ z ∂μ,
      Tendsto (fun r ↦ u r z * du r z * Φmid r z) atTop (𝓝 0))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤ A0 * √(Φprev r z) * √(Φnext r z))
    (hcompare1 : ∀ r z,
      |dΦ r z| ≤ A1 * √(Φprev r z) * √(Φmid r z))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * ddu p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * du p.1 p.2 * dΦ p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * √(Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ du p.1 p.2 * √(Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ddu p.1 p.2 * √(Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) :
    (∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) ≤
      A0 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) *
        √(∫ p : ℝ × ℝ, ddu p.1 p.2 ^ 2 * Φnext p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) +
      A1 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) *
        √(∫ p : ℝ × ℝ, du p.1 p.2 ^ 2 * Φmid p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod μ)) :=
  interpolation_row_radial_of_tendsto_of_ae hu hdu hΦ hzero htop hA0 hA1 hprev_nonneg hmid_nonneg
    hnext_nonneg (ae_of_all _ fun p ↦ hcompare0 p.1 p.2) (ae_of_all _ fun p ↦ hcompare1 p.1 p.2)
    hprev_int hmid_int hnext_int hterm0_int hterm1_int hprev_meas hmid_meas hnext_meas

end SobolevSpace.Weighted
