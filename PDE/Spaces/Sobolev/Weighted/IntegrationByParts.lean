/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.IntegrationByParts.Basic

import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.Integration.SingularEndpoints
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Weighted transport and interpolation identities

We prove the integration-by-parts identities behind the weighted transport and interpolation
estimates. For `C¹` functions `G` and `Φ` and a compactly supported `C¹` function `f`,

  `∫ (-G f') f Φ = (1/2) ∫ f² (G Φ)'`, and `|∫ (-G f') f Φ| ≤ (C/2) ∫ f² Φ` if `|(G Φ)'| ≤ C Φ`,

on the line, on the half line `r > 0` when `f 0 = 0`, for each partial derivative on `ℝ²`, and as
iterated integrals for `∂_r` (when `f 0 z = 0`) and for `∂_z` on the half plane `r > 0`. For a
compactly supported `C²` function `u` and a `C¹` weight `Φ`,

  `∫ u'² Φ = -∫ u u'' Φ - ∫ u u' Φ'`

on the line, on the half line when `u 0 = 0`, and for `∂_r` (when `u 0 z = 0`) and for `∂_z` on the
half plane, where the integrability of the three terms for the product measure is a hypothesis.

## Main results

* `weighted_transport_integral_identity_real`, `weighted_transport_integral_identity_Ioi`,
  `weighted_transport_integral_identity_R2`: the transport identity on `ℝ`, on `(0, ∞)` and on `ℝ²`;
  the `bound` versions give the transport bound.
* `weighted_transport_integral_identity_halfPlane_radial`,
  `weighted_transport_integral_identity_halfPlane_axial`: the iterated half-plane identities; the
  `bound` versions assume that the slice integrals are integrable in the outer variable.
* `weightedInterpolation_integral_identity_real`, `weightedInterpolation_integral_identity_Ioi`: the
  interpolation identity on `ℝ` and on `(0, ∞)`.
* `weightedInterpolation_integral_identity_halfPlane_radial`,
  `weightedInterpolation_integral_identity_halfPlane_radial_rz`,
  `weightedInterpolation_integral_identity_halfPlane_axial`: the half-plane identities for the
  product measure; `_radial_rz` uses the pair order `(r, z)` of the axial identity.

## How it works

The transport identity is `2 f f' = (f²)'` followed by one integration by parts of `(f²)' (G Φ)`: on
`ℝ` with `PDE.Analysis.integral_mul_deriv_eq_neg_deriv_mul_of_compactSupport`, which rests on
Mathlib's `integral_mul_deriv_eq_deriv_mul_of_integrable`, on `(0, ∞)` with
`SobolevSpace.Weighted.weightedSquareEnergyIoi_eq_neg_two_cross`, where `f 0 = 0` removes the
boundary term at `0`, and on `ℝ²` with `PDE.Analysis.integral_mul_partialDeriv_eq_neg`. The bounds
follow from `|(G Φ)'| ≤ C Φ` and `|∫ g| ≤ ∫ |g|`; we state this hypothesis without dividing by `Φ`,
so `Φ` may vanish. The half-plane transport results apply the line results on every slice and
integrate in the other variable. The interpolation identity integrates `u (u' Φ)'` by parts in the
same way, on `(0, ∞)` with `PDE.Analysis.integral_Ioi_mul_deriv_eq_neg_deriv_mul_of_left_eq_zero`,
and the half-plane versions pass to the product measure with `MeasureTheory.integral_prod` and
`MeasureTheory.integral_prod_symm`. The transport identity and bound are (509)-(512) in the proof of
Proposition 17 of Duruisseaux, Ganeshram, George and Anandkumar for compactly supported `f`, and the
interpolation identity is (177) in the proof of their Proposition 3.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix A, Proposition 3, (177),
  p. 39, for the interpolation identity, and Appendix B.8.2, Proposition 17, (507)-(512), p. 85, for
  the transport identity (509)-(510) and the bound (511)-(512).
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open Filter MeasureTheory Set
open Asymptotics
open scoped Topology

/-!
## Compact-support transport and derivative energies

The transport coefficients and weights are arbitrary `C¹` functions. Compact support removes the
boundary terms at infinity, and on the half line `r > 0` the condition `f 0 = 0` or `u 0 = 0`
removes the boundary term at `0`.
-/

open LineDeriv
open scoped ENNReal RealInnerProductSpace

namespace SobolevSpace.Weighted

/-- For `C¹` functions `G`, `Φ` and `f` with `f` compactly supported and `f 0 = 0`,
`∫ (-G f') f Φ = (1/2) ∫ f² (G Φ)'`, with both integrals over `(0, ∞)`. -/
theorem weighted_transport_integral_identity_Ioi
    {G Φ f : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hΦ : ContDiff ℝ 1 Φ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (hf0 : f 0 = 0) :
    (∫ r in Set.Ioi (0 : ℝ), (-G r * deriv f r) * f r * Φ r) =
      (1 / 2 : ℝ) *
        ∫ r in Set.Ioi (0 : ℝ), f r ^ 2 * deriv (fun s ↦ G s * Φ s) r := by
  have hGΦ : ContDiff ℝ 1 (fun s ↦ G s * Φ s) := hG.mul hΦ
  have hcfsq : HasCompactSupport (fun r ↦ f r ^ 2) :=
    hcf.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hflux : HasCompactSupport (fun r ↦ G r * Φ r * f r ^ 2) := hcfsq.mul_left
  have hlower : Tendsto (fun r ↦ G r * Φ r * f r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r ↦ G r * Φ r * f r ^ 2) (𝓝[>] 0)
        (𝓝 (G 0 * Φ 0 * f 0 ^ 2)) :=
      (((hG.continuous.mul hΦ.continuous).mul (hf.continuous.pow 2)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    simpa [hf0] using h
  have hibp := SobolevSpace.Weighted.weightedSquareEnergyIoi_eq_neg_two_cross
    (a := 0) (weight := deriv fun s ↦ G s * Φ s) (primitive := fun s ↦ G s * Φ s)
    (field := f) (fieldDerivative := deriv f)
    (fun x _ ↦ (hGΦ.differentiable_one x).hasDerivAt)
    (fun x _ ↦ (hf.differentiable_one x).hasDerivAt)
    (((hGΦ.continuous_deriv le_rfl).mul (hf.continuous.pow 2)).integrable_of_hasCompactSupport
      hcfsq.mul_left).integrableOn
    ((((hG.continuous.mul hΦ.continuous).mul hf.continuous).mul
      (hf.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hcf.mul_left.mul_right).integrableOn
    hlower
    (hflux.is_zero_at_infty.mono_left atTop_le_cocompact)
  simp only [SobolevSpace.Weighted.weightedSquareEnergyIoi,
    SobolevSpace.Weighted.weightedPrimitiveCrossIoi] at hibp
  have hleft : (∫ r in Set.Ioi (0 : ℝ), (-G r * deriv f r) * f r * Φ r) =
      -∫ r in Set.Ioi (0 : ℝ), G r * Φ r * f r * deriv f r := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun r ↦ by ring)
  have hright : (∫ r in Set.Ioi (0 : ℝ), f r ^ 2 * deriv (fun s ↦ G s * Φ s) r) =
      ∫ r in Set.Ioi (0 : ℝ), deriv (fun s ↦ G s * Φ s) r * f r ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun r ↦ mul_comm _ _)
  rw [hleft, hright, hibp]
  ring

/-- Let `G`, `Φ` and `f` be `C¹`, with `f` compactly supported and `f 0 = 0`. If `|(G Φ)'| ≤ C Φ` on
`(0, ∞)`, then `|∫ (-G f') f Φ| ≤ (C/2) ∫ f² Φ`, with both integrals over `(0, ∞)`. The hypothesis
is the bound `‖(G Φ)'/Φ‖_∞ ≤ C` written without the division, so `Φ` may vanish. -/
theorem weighted_transport_integral_bound_Ioi
    {G Φ f : ℝ → ℝ} {C : ℝ}
    (hG : ContDiff ℝ 1 G) (hΦ : ContDiff ℝ 1 Φ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (hf0 : f 0 = 0)
    (hderiv : ∀ r ∈ Set.Ioi (0 : ℝ),
      |deriv (fun s ↦ G s * Φ s) r| ≤ C * Φ r) :
    |∫ r in Set.Ioi (0 : ℝ), (-G r * deriv f r) * f r * Φ r| ≤
      (C / 2) * ∫ r in Set.Ioi (0 : ℝ), f r ^ 2 * Φ r := by
  let d : ℝ → ℝ := fun r ↦ deriv (fun s ↦ G s * Φ s) r
  have hGΦ : ContDiff ℝ 1 (fun r ↦ G r * Φ r) := hG.mul hΦ
  have hd_cont : Continuous d := by
    simpa [d] using hGΦ.continuous_deriv le_rfl
  have hcfsq : HasCompactSupport (fun r ↦ f r ^ 2) :=
    hcf.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hF_int : IntegrableOn (fun r ↦ f r ^ 2 * d r) (Set.Ioi (0 : ℝ)) :=
    ((hf.continuous.pow 2).mul hd_cont).integrable_of_hasCompactSupport
      hcfsq.mul_right |>.integrableOn
  have henergy_int : IntegrableOn (fun r ↦ f r ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) :=
    ((hf.continuous.pow 2).mul hΦ.continuous).integrable_of_hasCompactSupport
      hcfsq.mul_right |>.integrableOn
  have hpoint : ∀ r ∈ Set.Ioi (0 : ℝ),
      |f r ^ 2 * d r| ≤ C * (f r ^ 2 * Φ r) := by
    intro r hr
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f r))]
    calc
      f r ^ 2 * |d r| ≤ f r ^ 2 * (C * Φ r) :=
        mul_le_mul_of_nonneg_left (hderiv r hr) (sq_nonneg (f r))
      _ = C * (f r ^ 2 * Φ r) := by ring
  have hintegral :
      (∫ r in Set.Ioi (0 : ℝ), |f r ^ 2 * d r|) ≤
        ∫ r in Set.Ioi (0 : ℝ), C * (f r ^ 2 * Φ r) := by
    refine integral_mono_ae hF_int.abs (henergy_int.const_mul C) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hpoint r hr
  rw [weighted_transport_integral_identity_Ioi hG hΦ hf hcf hf0, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∫ r in Set.Ioi (0 : ℝ), f r ^ 2 * d r| ≤
        (1 / 2 : ℝ) * ∫ r in Set.Ioi (0 : ℝ), |f r ^ 2 * d r| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          ∫ r in Set.Ioi (0 : ℝ), C * (f r ^ 2 * Φ r) :=
      mul_le_mul_of_nonneg_left hintegral (by norm_num)
    _ = (C / 2) * ∫ r in Set.Ioi (0 : ℝ), f r ^ 2 * Φ r := by
      rw [integral_const_mul]
      ring

/-- `linearPrincipalTransportModel Gr Gz f r z = -Gr r z * ∂_r f - Gz r z * ∂_z f` at `(r, z)`, the
derivative of `f` along the vector field `(-Gr, -Gz)` in curried coordinates. -/
def linearPrincipalTransportModel
    (Gr Gz f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r z ↦
    -Gr r z * deriv (fun s ↦ f s z) r - Gz r z * deriv (f r) z

/-- Let `G r z`, `Φ r z` and `f r z` be `C¹` in `r` for every `z`, with `r ↦ f r z` compactly
supported and `f 0 z = 0`. Then
`∫ z, ∫ r in Ioi 0, (-G ∂_r f) f Φ = (1/2) ∫ z, ∫ r in Ioi 0, f² ∂_r (G Φ)`. Both sides are iterated
integrals; no integrability in `z` is assumed or asserted. -/
theorem weighted_transport_integral_identity_halfPlane_radial
    {G Φ f : ℝ → ℝ → ℝ}
    (hG : ∀ z, ContDiff ℝ 1 (fun r ↦ G r z))
    (hΦ : ∀ z, ContDiff ℝ 1 (fun r ↦ Φ r z))
    (hf : ∀ z, ContDiff ℝ 1 (fun r ↦ f r z))
    (hcf : ∀ z, HasCompactSupport (fun r ↦ f r z))
    (hf_axis : ∀ z, f 0 z = 0) :
    (∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
        (-G r z * deriv (fun s ↦ f s z) r) * f r z * Φ r z) =
      (1 / 2 : ℝ) *
        ∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
          f r z ^ 2 * deriv (fun s ↦ G s z * Φ s z) r := by
  calc
    (∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
        (-G r z * deriv (fun s ↦ f s z) r) * f r z * Φ r z)
        = ∫ z : ℝ, (1 / 2 : ℝ) *
            ∫ r in Set.Ioi (0 : ℝ),
              f r z ^ 2 * deriv (fun s ↦ G s z * Φ s z) r := by
          refine integral_congr_ae ?_
          filter_upwards with z
          exact weighted_transport_integral_identity_Ioi
            (hG z) (hΦ z) (hf z) (hcf z) (hf_axis z)
    _ = (1 / 2 : ℝ) *
          ∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
            f r z ^ 2 * deriv (fun s ↦ G s z * Φ s z) r := by
        rw [integral_const_mul]

/-- Let `G r z`, `Φ r z` and `f r z` be `C¹` in `r` for every `z`, with `r ↦ f r z` compactly
supported, `f 0 z = 0` and `|∂_r (G Φ)| ≤ C Φ` for `r > 0`. If `z ↦ ∫ r in Ioi 0, (-G ∂_r f) f Φ`
and `z ↦ ∫ r in Ioi 0, f² Φ` are integrable, then
`|∫ z, ∫ r in Ioi 0, (-G ∂_r f) f Φ| ≤ (C/2) ∫ z, ∫ r in Ioi 0, f² Φ`. The integrability of the
integrands for the product measure is not assumed. -/
theorem weighted_transport_integral_bound_halfPlane_radial
    {G Φ f : ℝ → ℝ → ℝ} {C : ℝ}
    (hG : ∀ z, ContDiff ℝ 1 (fun r ↦ G r z))
    (hΦ : ∀ z, ContDiff ℝ 1 (fun r ↦ Φ r z))
    (hf : ∀ z, ContDiff ℝ 1 (fun r ↦ f r z))
    (hcf : ∀ z, HasCompactSupport (fun r ↦ f r z))
    (hf_axis : ∀ z, f 0 z = 0)
    (hderiv : ∀ r z, r ∈ Set.Ioi (0 : ℝ) →
      |deriv (fun s ↦ G s z * Φ s z) r| ≤ C * Φ r z)
    (htransport_int : Integrable (fun z ↦
      ∫ r in Set.Ioi (0 : ℝ),
        (-G r z * deriv (fun s ↦ f s z) r) * f r z * Φ r z))
    (henergy_int : Integrable (fun z ↦
      ∫ r in Set.Ioi (0 : ℝ), f r z ^ 2 * Φ r z)) :
    |∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
        (-G r z * deriv (fun s ↦ f s z) r) * f r z * Φ r z| ≤
      (C / 2) *
        ∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ), f r z ^ 2 * Φ r z := by
  have hslice : ∀ z,
      |∫ r in Set.Ioi (0 : ℝ),
          (-G r z * deriv (fun s ↦ f s z) r) * f r z * Φ r z| ≤
        (C / 2) * ∫ r in Set.Ioi (0 : ℝ), f r z ^ 2 * Φ r z := by
    intro z
    exact weighted_transport_integral_bound_Ioi
      (hG z) (hΦ z) (hf z) (hcf z) (hf_axis z) (fun r hr ↦ hderiv r z hr)
  calc
    |∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
        (-G r z * deriv (fun s ↦ f s z) r) * f r z * Φ r z|
        ≤ ∫ z : ℝ, |∫ r in Set.Ioi (0 : ℝ),
            (-G r z * deriv (fun s ↦ f s z) r) * f r z * Φ r z| :=
          abs_integral_le_integral_abs
    _ ≤ ∫ z : ℝ, (C / 2) *
          ∫ r in Set.Ioi (0 : ℝ), f r z ^ 2 * Φ r z := by
        exact integral_mono htransport_int.abs (henergy_int.const_mul (C / 2)) hslice
    _ = (C / 2) *
          ∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ), f r z ^ 2 * Φ r z := by
        rw [integral_const_mul]

/-- For `C¹` functions `G`, `Φ` and `f` with `f` compactly supported,
`∫ (-G f') f Φ = (1/2) ∫ f² (G Φ)'`, with both integrals over `ℝ`. -/
theorem weighted_transport_integral_identity_real
    {G Φ f : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hΦ : ContDiff ℝ 1 Φ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    (∫ z : ℝ, (-G z * deriv f z) * f z * Φ z) =
      (1 / 2 : ℝ) * ∫ z : ℝ, f z ^ 2 * deriv (fun s ↦ G s * Φ s) z := by
  have hfsq : ContDiff ℝ 1 (fun z ↦ f z ^ 2) := by
    simpa [pow_two] using hf.mul hf
  have hcfsq : HasCompactSupport (fun z ↦ f z ^ 2) :=
    hcf.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hibp := PDE.Analysis.integral_mul_deriv_eq_neg_deriv_mul_of_compactSupport
    hfsq (hG.mul hΦ) hcfsq
  calc
    (∫ z : ℝ, (-G z * deriv f z) * f z * Φ z)
        = ∫ z : ℝ,
            (-1 / 2 : ℝ) * (deriv (fun s ↦ f s ^ 2) z * (G z * Φ z)) := by
          refine integral_congr_ae ?_
          filter_upwards with z
          rw [deriv_fun_pow hf.differentiable_one.differentiableAt]
          norm_num
          ring
    _ = (-1 / 2 : ℝ) * ∫ z : ℝ,
          deriv (fun s ↦ f s ^ 2) z * (G z * Φ z) := by
        rw [integral_const_mul]
    _ = (1 / 2 : ℝ) * ∫ z : ℝ,
          f z ^ 2 * deriv (fun s ↦ G s * Φ s) z := by
        rw [hibp]
        ring

/-- For `C¹` functions `G`, `Φ` and `f` with `f` compactly supported and `|(G Φ)'| ≤ C Φ` on `ℝ`,
`|∫ (-G f') f Φ| ≤ (C/2) ∫ f² Φ`, with both integrals over `ℝ`. -/
theorem weighted_transport_integral_bound_real
    {G Φ f : ℝ → ℝ} {C : ℝ}
    (hG : ContDiff ℝ 1 G) (hΦ : ContDiff ℝ 1 Φ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (hderiv : ∀ z, |deriv (fun s ↦ G s * Φ s) z| ≤ C * Φ z) :
    |∫ z : ℝ, (-G z * deriv f z) * f z * Φ z| ≤
      (C / 2) * ∫ z : ℝ, f z ^ 2 * Φ z := by
  let d : ℝ → ℝ := fun z ↦ deriv (fun s ↦ G s * Φ s) z
  have hGΦ : ContDiff ℝ 1 (fun z ↦ G z * Φ z) := hG.mul hΦ
  have hd_cont : Continuous d := by
    simpa [d] using hGΦ.continuous_deriv le_rfl
  have hcfsq : HasCompactSupport (fun z ↦ f z ^ 2) :=
    hcf.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hF_int : Integrable (fun z ↦ f z ^ 2 * d z) :=
    Continuous.integrable_of_hasCompactSupport ((hf.continuous.pow 2).mul hd_cont)
      hcfsq.mul_right
  have henergy_int : Integrable (fun z ↦ f z ^ 2 * Φ z) :=
    Continuous.integrable_of_hasCompactSupport ((hf.continuous.pow 2).mul hΦ.continuous)
      hcfsq.mul_right
  have hpoint : ∀ z, |f z ^ 2 * d z| ≤ C * (f z ^ 2 * Φ z) := by
    intro z
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f z))]
    calc
      f z ^ 2 * |d z| ≤ f z ^ 2 * (C * Φ z) :=
        mul_le_mul_of_nonneg_left (hderiv z) (sq_nonneg (f z))
      _ = C * (f z ^ 2 * Φ z) := by ring
  have hintegral :
      (∫ z : ℝ, |f z ^ 2 * d z|) ≤ ∫ z : ℝ, C * (f z ^ 2 * Φ z) :=
    integral_mono hF_int.abs (henergy_int.const_mul C) hpoint
  rw [weighted_transport_integral_identity_real hG hΦ hf hcf, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∫ z : ℝ, f z ^ 2 * d z| ≤
        (1 / 2 : ℝ) * ∫ z : ℝ, |f z ^ 2 * d z| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∫ z : ℝ, C * (f z ^ 2 * Φ z) :=
      mul_le_mul_of_nonneg_left hintegral (by norm_num)
    _ = (C / 2) * ∫ z : ℝ, f z ^ 2 * Φ z := by
      rw [integral_const_mul]
      ring

/-- Let `G r z`, `Φ r z` and `f r z` be `C¹` in `z` for every `r`, with `z ↦ f r z` compactly
supported. Then `∫ r in Ioi 0, ∫ z, (-G ∂_z f) f Φ = (1/2) ∫ r in Ioi 0, ∫ z, f² ∂_z (G Φ)`. Both
sides are iterated integrals; no integrability in `r` is assumed or asserted. -/
theorem weighted_transport_integral_identity_halfPlane_axial
    {G Φ f : ℝ → ℝ → ℝ}
    (hG : ∀ r, ContDiff ℝ 1 (fun z ↦ G r z))
    (hΦ : ∀ r, ContDiff ℝ 1 (fun z ↦ Φ r z))
    (hf : ∀ r, ContDiff ℝ 1 (fun z ↦ f r z))
    (hcf : ∀ r, HasCompactSupport (fun z ↦ f r z)) :
    (∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
        (-G r z * deriv (fun s ↦ f r s) z) * f r z * Φ r z) =
      (1 / 2 : ℝ) * ∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
        f r z ^ 2 * deriv (fun s ↦ G r s * Φ r s) z := by
  calc
    (∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
        (-G r z * deriv (fun s ↦ f r s) z) * f r z * Φ r z)
        = ∫ r in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * ∫ z : ℝ,
          f r z ^ 2 * deriv (fun s ↦ G r s * Φ r s) z := by
          refine integral_congr_ae ?_
          filter_upwards with r
          exact weighted_transport_integral_identity_real
            (hG r) (hΦ r) (hf r) (hcf r)
    _ = (1 / 2 : ℝ) * ∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
          f r z ^ 2 * deriv (fun s ↦ G r s * Φ r s) z := by
        rw [integral_const_mul]

/-- Let `G r z`, `Φ r z` and `f r z` be `C¹` in `z` for every `r`, with `z ↦ f r z` compactly
supported and `|∂_z (G Φ)| ≤ C Φ` everywhere. If `r ↦ ∫ z, (-G ∂_z f) f Φ` and `r ↦ ∫ z, f² Φ` are
integrable on `(0, ∞)`, then `|∫ r in Ioi 0, ∫ z, (-G ∂_z f) f Φ| ≤ (C/2) ∫ r in Ioi 0, ∫ z, f² Φ`.
The integrability of the integrands for the product measure is not assumed. -/
theorem weighted_transport_integral_bound_halfPlane_axial
    {G Φ f : ℝ → ℝ → ℝ} {C : ℝ}
    (hG : ∀ r, ContDiff ℝ 1 (fun z ↦ G r z))
    (hΦ : ∀ r, ContDiff ℝ 1 (fun z ↦ Φ r z))
    (hf : ∀ r, ContDiff ℝ 1 (fun z ↦ f r z))
    (hcf : ∀ r, HasCompactSupport (fun z ↦ f r z))
    (hderiv : ∀ r z, |deriv (fun s ↦ G r s * Φ r s) z| ≤ C * Φ r z)
    (htransport_int : IntegrableOn (fun r ↦ ∫ z : ℝ,
      (-G r z * deriv (fun s ↦ f r s) z) * f r z * Φ r z) (Set.Ioi (0 : ℝ)))
    (henergy_int : IntegrableOn (fun r ↦ ∫ z : ℝ,
      f r z ^ 2 * Φ r z) (Set.Ioi (0 : ℝ))) :
    |∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
        (-G r z * deriv (fun s ↦ f r s) z) * f r z * Φ r z| ≤
      (C / 2) * ∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ, f r z ^ 2 * Φ r z := by
  have hslice : ∀ r,
      |∫ z : ℝ, (-G r z * deriv (fun s ↦ f r s) z) * f r z * Φ r z| ≤
        (C / 2) * ∫ z : ℝ, f r z ^ 2 * Φ r z := by
    intro r
    exact weighted_transport_integral_bound_real
      (hG r) (hΦ r) (hf r) (hcf r) (hderiv r)
  calc
    |∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
        (-G r z * deriv (fun s ↦ f r s) z) * f r z * Φ r z|
        ≤ ∫ r in Set.Ioi (0 : ℝ), |∫ z : ℝ,
          (-G r z * deriv (fun s ↦ f r s) z) * f r z * Φ r z| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), (C / 2) * ∫ z : ℝ,
          f r z ^ 2 * Φ r z := by
      refine integral_mono_ae htransport_int.abs (henergy_int.const_mul (C / 2)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hslice r
    _ = (C / 2) * ∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
          f r z ^ 2 * Φ r z := by
      rw [integral_const_mul]

/-- For `C¹` functions `G`, `Φ` and `f` on `ℝ²` with `f` compactly supported and each coordinate
`i`, `∫ (-G ∂_i f) f Φ = (1/2) ∫ f² ∂_i (G Φ)`. -/
theorem weighted_transport_integral_identity_R2
    (i : Fin 2) {G Φ f : (ℝ^2 → ℝ)}
    (hG : ContDiff ℝ 1 G) (hΦ : ContDiff ℝ 1 Φ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    (∫ x : (ℝ^2),
        (-G x * (∂[i] f) x) * f x * Φ x) =
      (1 / 2 : ℝ) *
        ∫ x : (ℝ^2),
          f x ^ 2 *
            (∂[i] (fun y ↦ G y * Φ y)) x := by
  have hfsq : ContDiff ℝ 1 (fun x : (ℝ^2) ↦ f x ^ 2) := by
    simpa [pow_two] using hf.mul hf
  have hcfsq : HasCompactSupport (fun x : (ℝ^2) ↦ f x ^ 2) :=
    hcf.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hibp :=
    PDE.Analysis.integral_mul_partialDeriv_eq_neg
      (f := fun x : (ℝ^2) ↦ f x ^ 2) (g := fun x ↦ G x * Φ x) i
      hfsq (hG.mul hΦ) hcfsq
  calc
    (∫ x : (ℝ^2),
        (-G x * (∂[i] f) x) * f x * Φ x)
        = ∫ x : (ℝ^2),
            (-1 / 2 : ℝ) *
              ((∂[i] (fun y ↦ f y ^ 2)) x *
                (G x * Φ x)) := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [PDE.partialDeriv_sq i hf.differentiable_one.differentiableAt]
            ring
    _ = (-1 / 2 : ℝ) *
          ∫ x : (ℝ^2),
            (∂[i] (fun y ↦ f y ^ 2)) x *
              (G x * Φ x) := by
          rw [integral_const_mul]
    _ = (1 / 2 : ℝ) *
          ∫ x : (ℝ^2),
            f x ^ 2 *
              (∂[i] (fun y ↦ G y * Φ y)) x := by
          rw [hibp]
          ring

/-- For `C¹` functions `G`, `Φ` and `f` on `ℝ²` with `f` compactly supported and `|∂_i (G Φ)| ≤ C Φ`
everywhere, `|∫ (-G ∂_i f) f Φ| ≤ (C/2) ∫ f² Φ`. The hypothesis is the bound `‖∂_i (G Φ)/Φ‖_∞ ≤ C`
written without the division, so `Φ` may vanish. -/
theorem weighted_transport_integral_bound_R2
    (i : Fin 2) {G Φ f : (ℝ^2 → ℝ)} {C : ℝ}
    (hG : ContDiff ℝ 1 G) (hΦ : ContDiff ℝ 1 Φ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (hderiv : ∀ x,
      |(∂[i] (fun y ↦ G y * Φ y)) x| ≤ C * Φ x) :
    |∫ x : (ℝ^2),
        (-G x * (∂[i] f) x) * f x * Φ x| ≤
      (C / 2) * ∫ x : (ℝ^2), f x ^ 2 * Φ x := by
  let d : (ℝ^2 → ℝ) :=
    fun x ↦ (∂[i] (fun y ↦ G y * Φ y)) x
  have hGΦ : ContDiff ℝ 1 (fun x : (ℝ^2) ↦ G x * Φ x) := hG.mul hΦ
  have hd_cont : Continuous d := by
    have hcont :
        Continuous (fun x : (ℝ^2) ↦
          (fderiv ℝ (fun y : (ℝ^2) ↦ G y * Φ y) x : (ℝ^2) →L[ℝ] ℝ)
            (EuclideanSpace.single i (1 : ℝ))) :=
      (hGΦ.continuous_fderiv_apply (hn := by norm_num)).comp
        (continuous_id.prodMk continuous_const)
    simpa [d, partialDeriv, partialDeriv] using hcont
  have hcfsq : HasCompactSupport (fun x : (ℝ^2) ↦ f x ^ 2) :=
    hcf.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hF_int : Integrable (fun x : (ℝ^2) ↦ f x ^ 2 * d x) volume :=
    ((hf.continuous.pow 2).mul hd_cont).integrable_of_hasCompactSupport hcfsq.mul_right
  have henergy_int : Integrable (fun x : (ℝ^2) ↦ f x ^ 2 * Φ x) volume :=
    ((hf.continuous.pow 2).mul hΦ.continuous).integrable_of_hasCompactSupport
      hcfsq.mul_right
  have hpoint : ∀ x : (ℝ^2),
      |f x ^ 2 * d x| ≤ C * (f x ^ 2 * Φ x) := by
    intro x
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f x))]
    calc
      f x ^ 2 * |d x| ≤ f x ^ 2 * (C * Φ x) :=
        mul_le_mul_of_nonneg_left (hderiv x) (sq_nonneg (f x))
      _ = C * (f x ^ 2 * Φ x) := by ring
  have hintegral :
      (∫ x : (ℝ^2), |f x ^ 2 * d x|) ≤
        ∫ x : (ℝ^2), C * (f x ^ 2 * Φ x) := by
    exact integral_mono hF_int.abs (henergy_int.const_mul C) hpoint
  rw [weighted_transport_integral_identity_R2 i hG hΦ hf hcf, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∫ x : (ℝ^2), f x ^ 2 * d x| ≤
        (1 / 2 : ℝ) * ∫ x : (ℝ^2), |f x ^ 2 * d x| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∫ x : (ℝ^2), C * (f x ^ 2 * Φ x) :=
      mul_le_mul_of_nonneg_left hintegral (by norm_num)
    _ = (C / 2) * ∫ x : (ℝ^2), f x ^ 2 * Φ x := by
      rw [integral_const_mul]
      ring

/-- For a compactly supported `C²` function `u` and a `C¹` function `Φ` on `ℝ`,
`∫ u'² Φ = -∫ u u'' Φ - ∫ u u' Φ'`. -/
theorem weightedInterpolation_integral_identity_real
    {u Φ : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 1 Φ)
    (hcu : HasCompactSupport u) :
    (∫ x : ℝ, deriv u x ^ 2 * Φ x) =
      -(∫ x : ℝ, u x * deriv (deriv u) x * Φ x) -
        (∫ x : ℝ, u x * deriv u x * deriv Φ x) := by
  have hdu : ContDiff ℝ 1 (deriv u) := by
    simpa using (hu.deriv' : ContDiff ℝ 1 (deriv u))
  have hibp := PDE.Analysis.integral_mul_deriv_eq_neg_deriv_mul_of_compactSupport
    (hu.of_le (by norm_num) : ContDiff ℝ 1 u) (hdu.mul hΦ) hcu
  have hsecond_int : Integrable (fun x ↦ u x * deriv (deriv u) x * Φ x) :=
    Continuous.integrable_of_hasCompactSupport
      ((hu.continuous.mul (hdu.continuous_deriv le_rfl)).mul hΦ.continuous)
      hcu.mul_right.mul_right
  have hweight_int : Integrable (fun x ↦ u x * deriv u x * deriv Φ x) :=
    Continuous.integrable_of_hasCompactSupport
      ((hu.continuous.mul hdu.continuous).mul (hΦ.continuous_deriv le_rfl))
      hcu.mul_right.mul_right
  have hexpand :
      (∫ x : ℝ, u x * deriv (fun y ↦ deriv u y * Φ y) x) =
        (∫ x : ℝ, u x * deriv (deriv u) x * Φ x) +
          ∫ x : ℝ, u x * deriv u x * deriv Φ x := by
    calc
      (∫ x : ℝ, u x * deriv (fun y ↦ deriv u y * Φ y) x)
          = ∫ x : ℝ,
              u x * deriv (deriv u) x * Φ x +
                u x * deriv u x * deriv Φ x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [deriv_fun_mul hdu.differentiable_one.differentiableAt
              hΦ.differentiable_one.differentiableAt]
            ring
      _ = (∫ x : ℝ, u x * deriv (deriv u) x * Φ x) +
            ∫ x : ℝ, u x * deriv u x * deriv Φ x :=
          integral_add hsecond_int hweight_int
  have henergy :
      (∫ x : ℝ, deriv u x * (deriv u x * Φ x)) =
        ∫ x : ℝ, deriv u x ^ 2 * Φ x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  rw [hexpand, henergy] at hibp
  calc
    (∫ x : ℝ, deriv u x ^ 2 * Φ x)
        = -(-(∫ x : ℝ, deriv u x ^ 2 * Φ x)) := by ring
    _ = -((∫ x : ℝ, u x * deriv (deriv u) x * Φ x) +
          (∫ x : ℝ, u x * deriv u x * deriv Φ x)) := by rw [← hibp]
    _ = -(∫ x : ℝ, u x * deriv (deriv u) x * Φ x) -
          (∫ x : ℝ, u x * deriv u x * deriv Φ x) := by ring

/-- For a compactly supported `C²` function `u` with `u 0 = 0` and a `C¹` function `Φ`,
`∫ u'² Φ = -∫ u u'' Φ - ∫ u u' Φ'`, with the integrals over `(0, ∞)`. -/
theorem weightedInterpolation_integral_identity_Ioi
    {u Φ : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 1 Φ)
    (hcu : HasCompactSupport u) (hu0 : u 0 = 0) :
    (∫ x in Set.Ioi (0 : ℝ), deriv u x ^ 2 * Φ x) =
      -(∫ x in Set.Ioi (0 : ℝ), u x * deriv (deriv u) x * Φ x) -
        (∫ x in Set.Ioi (0 : ℝ), u x * deriv u x * deriv Φ x) := by
  have hdu : ContDiff ℝ 1 (deriv u) := by
    simpa using (hu.deriv' : ContDiff ℝ 1 (deriv u))
  have hibp := PDE.Analysis.integral_Ioi_mul_deriv_eq_neg_deriv_mul_of_left_eq_zero
    (hu.of_le (by norm_num) : ContDiff ℝ 1 u) (hdu.mul hΦ) hcu hu0
  have hsecond_int : IntegrableOn
      (fun x ↦ u x * deriv (deriv u) x * Φ x) (Set.Ioi (0 : ℝ)) :=
    (((hu.continuous.mul (hdu.continuous_deriv le_rfl)).mul
      hΦ.continuous).integrable_of_hasCompactSupport
      hcu.mul_right.mul_right).integrableOn
  have hweight_int : IntegrableOn
      (fun x ↦ u x * deriv u x * deriv Φ x) (Set.Ioi (0 : ℝ)) :=
    (((hu.continuous.mul hdu.continuous).mul
      (hΦ.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hcu.mul_right.mul_right).integrableOn
  have hexpand :
      (∫ x in Set.Ioi (0 : ℝ),
          u x * deriv (fun y ↦ deriv u y * Φ y) x) =
        (∫ x in Set.Ioi (0 : ℝ), u x * deriv (deriv u) x * Φ x) +
          ∫ x in Set.Ioi (0 : ℝ), u x * deriv u x * deriv Φ x := by
    calc
      (∫ x in Set.Ioi (0 : ℝ), u x * deriv (fun y ↦ deriv u y * Φ y) x)
          = ∫ x in Set.Ioi (0 : ℝ),
              u x * deriv (deriv u) x * Φ x +
                u x * deriv u x * deriv Φ x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [deriv_fun_mul hdu.differentiable_one.differentiableAt
              hΦ.differentiable_one.differentiableAt]
            ring
      _ = (∫ x in Set.Ioi (0 : ℝ), u x * deriv (deriv u) x * Φ x) +
            ∫ x in Set.Ioi (0 : ℝ), u x * deriv u x * deriv Φ x :=
          integral_add hsecond_int hweight_int
  have henergy :
      (∫ x in Set.Ioi (0 : ℝ), deriv u x * (deriv u x * Φ x)) =
        ∫ x in Set.Ioi (0 : ℝ), deriv u x ^ 2 * Φ x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  rw [hexpand, henergy] at hibp
  calc
    (∫ x in Set.Ioi (0 : ℝ), deriv u x ^ 2 * Φ x)
        = -(-(∫ x in Set.Ioi (0 : ℝ), deriv u x ^ 2 * Φ x)) := by ring
    _ = -((∫ x in Set.Ioi (0 : ℝ), u x * deriv (deriv u) x * Φ x) +
          (∫ x in Set.Ioi (0 : ℝ), u x * deriv u x * deriv Φ x)) := by
        rw [← hibp]
    _ = -(∫ x in Set.Ioi (0 : ℝ), u x * deriv (deriv u) x * Φ x) -
          (∫ x in Set.Ioi (0 : ℝ), u x * deriv u x * deriv Φ x) := by ring

/-- Let `u r z` be `C²` with compact support in `r` for every `z`, with `u 0 z = 0`, and let `Φ r z`
be `C¹` in `r`. If `(∂_r u)² Φ`, `u ∂_r² u Φ` and `u ∂_r u ∂_r Φ` are integrable for `dz dr` on
`ℝ × (0, ∞)`, with pairs `(z, r)`, then `∫ (∂_r u)² Φ = -∫ u ∂_r² u Φ - ∫ u ∂_r u ∂_r Φ` for that
measure. -/
theorem weightedInterpolation_integral_identity_halfPlane_radial
    {u Φ : ℝ → ℝ → ℝ}
    (hu : ∀ z, ContDiff ℝ 2 (fun r ↦ u r z))
    (hΦ : ∀ z, ContDiff ℝ 1 (fun r ↦ Φ r z))
    (hcu : ∀ z, HasCompactSupport (fun r ↦ u r z))
    (hu0 : ∀ z, u 0 z = 0)
    (henergy : Integrable
      (fun p : ℝ × ℝ ↦ deriv (fun r ↦ u r p.1) p.2 ^ 2 * Φ p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hterm0 : Integrable
      (fun p : ℝ × ℝ ↦
        u p.2 p.1 * deriv (deriv (fun r ↦ u r p.1)) p.2 * Φ p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hterm1 : Integrable
      (fun p : ℝ × ℝ ↦
        u p.2 p.1 * deriv (fun r ↦ u r p.1) p.2 *
          deriv (fun r ↦ Φ r p.1) p.2)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) :
    (∫ p : ℝ × ℝ,
      deriv (fun r ↦ u r p.1) p.2 ^ 2 * Φ p.2 p.1
        ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) =
      -(∫ p : ℝ × ℝ,
        u p.2 p.1 * deriv (deriv (fun r ↦ u r p.1)) p.2 * Φ p.2 p.1
          ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) -
      (∫ p : ℝ × ℝ,
        u p.2 p.1 * deriv (fun r ↦ u r p.1) p.2 *
          deriv (fun r ↦ Φ r p.1) p.2
          ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) := by
  rw [integral_prod _ henergy, integral_prod _ hterm0, integral_prod _ hterm1]
  calc
    (∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
        deriv (fun s ↦ u s z) r ^ 2 * Φ r z) =
      ∫ z : ℝ,
        (-(∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z) -
          (∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (fun s ↦ u s z) r *
              deriv (fun s ↦ Φ s z) r)) := by
        refine integral_congr_ae ?_
        filter_upwards with z
        exact weightedInterpolation_integral_identity_Ioi
          (hu z) (hΦ z) (hcu z) (hu0 z)
    _ = -(∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
          u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z) -
        (∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
          u r z * deriv (fun s ↦ u s z) r *
            deriv (fun s ↦ Φ s z) r) := by
      have hterm0_outer : Integrable (fun z : ℝ ↦
          ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z) := by
        simpa using hterm0.integral_prod_left
      have hterm1_outer : Integrable (fun z : ℝ ↦
          ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (fun s ↦ u s z) r *
              deriv (fun s ↦ Φ s z) r) := by
        simpa using hterm1.integral_prod_left
      change (∫ z : ℝ,
          (-(fun z ↦ ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z)) z -
          (fun z ↦ ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (fun s ↦ u s z) r *
              deriv (fun s ↦ Φ s z) r) z) = _
      rw [integral_sub hterm0_outer.neg hterm1_outer, integral_neg']

/-- Let `u r z` be `C²` with compact support in `r` for every `z`, with `u 0 z = 0`, and let `Φ r z`
be `C¹` in `r`. If `(∂_r u)² Φ`, `u ∂_r² u Φ` and `u ∂_r u ∂_r Φ` are integrable for `dr dz` on
`(0, ∞) × ℝ`, with pairs `(r, z)`, then `∫ (∂_r u)² Φ = -∫ u ∂_r² u Φ - ∫ u ∂_r u ∂_r Φ` for that
measure. This is the measure and pair order of
`weightedInterpolation_integral_identity_halfPlane_axial`. -/
theorem weightedInterpolation_integral_identity_halfPlane_radial_rz
    {u Φ : ℝ → ℝ → ℝ}
    (hu : ∀ z, ContDiff ℝ 2 (fun r ↦ u r z))
    (hΦ : ∀ z, ContDiff ℝ 1 (fun r ↦ Φ r z))
    (hcu : ∀ z, HasCompactSupport (fun r ↦ u r z))
    (hu0 : ∀ z, u 0 z = 0)
    (henergy : Integrable
      (fun p : ℝ × ℝ ↦ deriv (fun r ↦ u r p.2) p.1 ^ 2 * Φ p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm0 : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (deriv (fun r ↦ u r p.2)) p.1 * Φ p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm1 : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (fun r ↦ u r p.2) p.1 *
          deriv (fun r ↦ Φ r p.2) p.1)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∫ p : ℝ × ℝ,
      deriv (fun r ↦ u r p.2) p.1 ^ 2 * Φ p.1 p.2
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) =
      -(∫ p : ℝ × ℝ,
        u p.1 p.2 * deriv (deriv (fun r ↦ u r p.2)) p.1 * Φ p.1 p.2
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) -
      (∫ p : ℝ × ℝ,
        u p.1 p.2 * deriv (fun r ↦ u r p.2) p.1 *
          deriv (fun r ↦ Φ r p.2) p.1
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
  rw [integral_prod_symm _ henergy, integral_prod_symm _ hterm0,
    integral_prod_symm _ hterm1]
  calc
    (∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
        deriv (fun s ↦ u s z) r ^ 2 * Φ r z) =
      ∫ z : ℝ,
        (-(∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z) -
          (∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (fun s ↦ u s z) r *
              deriv (fun s ↦ Φ s z) r)) := by
        refine integral_congr_ae ?_
        filter_upwards with z
        exact weightedInterpolation_integral_identity_Ioi
          (hu z) (hΦ z) (hcu z) (hu0 z)
    _ = -(∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
          u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z) -
        (∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ),
          u r z * deriv (fun s ↦ u s z) r *
            deriv (fun s ↦ Φ s z) r) := by
      have hterm0_outer : Integrable (fun z : ℝ ↦
          ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z) := by
        simpa using hterm0.integral_prod_right
      have hterm1_outer : Integrable (fun z : ℝ ↦
          ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (fun s ↦ u s z) r *
              deriv (fun s ↦ Φ s z) r) := by
        simpa using hterm1.integral_prod_right
      change (∫ z : ℝ,
          (-(fun z ↦ ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (deriv (fun s ↦ u s z)) r * Φ r z)) z -
          (fun z ↦ ∫ r in Set.Ioi (0 : ℝ),
            u r z * deriv (fun s ↦ u s z) r *
              deriv (fun s ↦ Φ s z) r) z) = _
      rw [integral_sub hterm0_outer.neg hterm1_outer, integral_neg']

/-- Let `u r z` be `C²` with compact support in `z` for every `r`, and let `Φ r z` be `C¹` in `z`.
If `(∂_z u)² Φ`, `u ∂_z² u Φ` and `u ∂_z u ∂_z Φ` are integrable for `dr dz` on `(0, ∞) × ℝ`, with
pairs `(r, z)`, then `∫ (∂_z u)² Φ = -∫ u ∂_z² u Φ - ∫ u ∂_z u ∂_z Φ` for that measure. -/
theorem weightedInterpolation_integral_identity_halfPlane_axial
    {u Φ : ℝ → ℝ → ℝ}
    (hu : ∀ r, ContDiff ℝ 2 (fun z ↦ u r z))
    (hΦ : ∀ r, ContDiff ℝ 1 (fun z ↦ Φ r z))
    (hcu : ∀ r, HasCompactSupport (fun z ↦ u r z))
    (henergy : Integrable
      (fun p : ℝ × ℝ ↦ deriv (fun z ↦ u p.1 z) p.2 ^ 2 * Φ p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm0 : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (deriv (fun z ↦ u p.1 z)) p.2 * Φ p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm1 : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (fun z ↦ u p.1 z) p.2 *
          deriv (fun z ↦ Φ p.1 z) p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∫ p : ℝ × ℝ,
      deriv (fun z ↦ u p.1 z) p.2 ^ 2 * Φ p.1 p.2
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) =
      -(∫ p : ℝ × ℝ,
        u p.1 p.2 * deriv (deriv (fun z ↦ u p.1 z)) p.2 * Φ p.1 p.2
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) -
      (∫ p : ℝ × ℝ,
        u p.1 p.2 * deriv (fun z ↦ u p.1 z) p.2 *
          deriv (fun z ↦ Φ p.1 z) p.2
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
  rw [integral_prod _ henergy, integral_prod _ hterm0, integral_prod _ hterm1]
  calc
    (∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
        deriv (fun s ↦ u r s) z ^ 2 * Φ r z) =
      ∫ r in Set.Ioi (0 : ℝ),
        (-(∫ z : ℝ,
            u r z * deriv (deriv (fun s ↦ u r s)) z * Φ r z) -
          (∫ z : ℝ,
            u r z * deriv (fun s ↦ u r s) z *
              deriv (fun s ↦ Φ r s) z)) := by
        refine integral_congr_ae ?_
        filter_upwards with r
        exact weightedInterpolation_integral_identity_real
          (hu r) (hΦ r) (hcu r)
    _ = -(∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
          u r z * deriv (deriv (fun s ↦ u r s)) z * Φ r z) -
        (∫ r in Set.Ioi (0 : ℝ), ∫ z : ℝ,
          u r z * deriv (fun s ↦ u r s) z *
            deriv (fun s ↦ Φ r s) z) := by
      have hterm0_outer : IntegrableOn (fun r : ℝ ↦
          ∫ z : ℝ,
            u r z * deriv (deriv (fun s ↦ u r s)) z * Φ r z)
          (Set.Ioi (0 : ℝ)) := by
        change Integrable (fun r : ℝ ↦ ∫ z : ℝ,
          u r z * deriv (deriv (fun s ↦ u r s)) z * Φ r z)
          (volume.restrict (Set.Ioi 0))
        exact hterm0.integral_prod_left
      have hterm1_outer : IntegrableOn (fun r : ℝ ↦
          ∫ z : ℝ,
            u r z * deriv (fun s ↦ u r s) z *
              deriv (fun s ↦ Φ r s) z)
          (Set.Ioi (0 : ℝ)) := by
        change Integrable (fun r : ℝ ↦ ∫ z : ℝ,
          u r z * deriv (fun s ↦ u r s) z * deriv (fun s ↦ Φ r s) z)
          (volume.restrict (Set.Ioi 0))
        exact hterm1.integral_prod_left
      change (∫ r in Set.Ioi (0 : ℝ),
          (-(fun r ↦ ∫ z : ℝ,
            u r z * deriv (deriv (fun s ↦ u r s)) z * Φ r z)) r -
          (fun r ↦ ∫ z : ℝ,
            u r z * deriv (fun s ↦ u r s) z *
              deriv (fun s ↦ Φ r s) z) r) = _
      rw [integral_sub hterm0_outer.neg hterm1_outer, integral_neg']

end SobolevSpace.Weighted
