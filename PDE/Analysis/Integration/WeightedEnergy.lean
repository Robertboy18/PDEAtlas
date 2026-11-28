/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.Divergence
public import PDE.Analysis.Integration.InnerProductByParts
public import PDE.FDeriv.PartialDeriv.Energy
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDE.Analysis.Calculus.Gradient.HessianBounds
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Continuity
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Energy identities with a compactly supported weight

We pair a field `v` on `ℝⁿ` with `ψ v` for a scalar weight `ψ` and compute what the dilation
drift `x·∇v`, a divergence-free transport `W·∇v` and the Laplacian contribute. When `v` has
compact support and `ψ = 1` these are the classical energy identities. In weighted estimates it
is the weight that has compact support, and `v` is only smooth, so here the compact support sits
on the weight and `v` needs no decay. The identities of
`PDE.Analysis.Integration.InnerProductByParts` are the same computations with the compact
support on the field.

## Main results

* `integral_fderiv_apply_eq_neg_integral_mul_divergence`: `∫ Dφ B = -∫ φ div B` for a `C¹`
  scalar `φ` and a compactly supported `C¹` field `B`.
* `integral_inner_fderiv_apply_eq_neg_half_divergence`: `∫ ⟨Dv B, v⟩ = -½ ∫ |v|² div B` for a
  `C¹` field `v` and a compactly supported `C¹` field `B`.
* `integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero`: `∫ ψ ∇P·u = -∫ P ∇ψ·u` for a `C¹`
  scalar `P`, a divergence-free `C¹` field `u` and a compactly supported `C¹` weight `ψ`.
* `integral_mul_inner_laplacian`: the weighted Dirichlet identity
  `∫ ψ ⟨Δv, v⟩ = -∫ ψ Σᵢ |∂ᵢv|² + ½ ∫ Δψ |v|²` for a `C²` field and a compactly supported `C²`
  weight.
* `integral_mul_similarityPairing`: the weighted energy identity
  `∫ ψ · similarityPairing = ∫ energyDensity` of the self-similar operator
  `c v - ½ x·∇v + W·∇v - Δv`, for a `C²` field `v`, a divergence-free `C¹` field `W`, a
  compactly supported `C²` weight `ψ` and every `c`.

## How it works

Every term is one integration by parts against a compactly supported factor, so no boundary
term appears. For a compactly supported field `B`, `⟨Dv B, v⟩ = ½ B·∇|v|²` gives
`∫ ⟨Dv B, v⟩ = -½ ∫ |v|² div B`. With `B = ψ x` this is the drift, with `B = ψ W` the transport,
and with `B = ∇ψ` the cross term of the Laplacian. The diffusion identity
`⟨-ΔU, χ_R φ_L U⟩ = ⟨∇U, χ_R φ_L ∇U⟩ - ½ ⟨U, Δ(χ_R φ_L) U⟩` of Hou, Wang and Yang is
`integral_mul_inner_laplacian` with `ψ = χ_R φ_L`, and their drift term is the drift part of
`integral_mul_similarityPairing`. Weights without compact support are reached through cutoffs
in `integral_energyDensity_le_of_forall_radialCutoff`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, proof of
  Proposition 4: the pairings with `χ_R φ_L U_near` and `χ_R φ_L |ξ|^α ∇U_near`.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace Gradient

namespace PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Moving the derivative of a `C¹` scalar onto a compactly supported `C¹` vector field gives
minus the divergence of the field: `∫ Dφ B = -∫ φ div B`. The scalar needs no decay. -/
theorem integral_fderiv_apply_eq_neg_integral_mul_divergence {φ : ℝ^n → ℝ} {B : ℝ^n → ℝ^n}
    (hφ : ContDiff ℝ 1 φ) (hB : ContDiff ℝ 1 B) (hc : HasCompactSupport B) :
    (∫ x, fderiv ℝ φ x (B x)) = -∫ x, φ x * ∇· B x := by
  have hBi (i : Fin n) : ContDiff ℝ 1 (fun x ↦ B x i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hB
  have hci (i : Fin n) : HasCompactSupport (fun x ↦ B x i) :=
    hc.comp_left (g := fun y : ℝ^n ↦ y i) (by simp)
  have hleft (i : Fin n) : Integrable (fun x ↦ B x i * ∂[i] φ x) :=
    ((hBi i).continuous.mul (hφ.continuous_partialDeriv i)).integrable_of_hasCompactSupport
      (hci i).mul_right
  have hright (i : Fin n) : Integrable (fun x ↦ ∂[i] (fun y ↦ B y i) x * φ x) :=
    (((hBi i).continuous_partialDeriv i).mul hφ.continuous).integrable_of_hasCompactSupport
      ((hci i).partialDeriv i).mul_right
  have hpoint (x : ℝ^n) : fderiv ℝ φ x (B x) = ∑ i : Fin n, B x i * ∂[i] φ x := by
    rw [fderiv_apply_eq_sum_partialDeriv_mul]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hdiv (x : ℝ^n) : φ x * ∇· B x = ∑ i : Fin n, ∂[i] (fun y ↦ B y i) x * φ x := by
    simp [PDE.divergence, Finset.mul_sum, mul_comm]
  simp_rw [hpoint, hdiv]
  rw [integral_finsetSum _ fun i _ ↦ hleft i, integral_finsetSum _ fun i _ ↦ hright i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ integral_mul_partialDeriv_eq_neg i (hBi i) hφ (hci i)

/-- Transport energy with the compact support on the transporting field:
`∫ ⟨Dv B, v⟩ = -½ ∫ |v|² div B` for a `C¹` field `v` and a compactly supported `C¹` field `B`.
The transported field needs no decay. -/
theorem integral_inner_fderiv_apply_eq_neg_half_divergence {v : ℝ^n → E} {B : ℝ^n → ℝ^n}
    (hv : ContDiff ℝ 1 v) (hB : ContDiff ℝ 1 B) (hc : HasCompactSupport B) :
    (∫ x, ⟪fderiv ℝ v x (B x), v x⟫_ℝ) = -(1 / 2 : ℝ) * ∫ x, ‖v x‖ ^ 2 * ∇· B x := by
  let φ : ℝ^n → ℝ := fun x ↦ ⟪v x, v x⟫_ℝ
  have hφ : ContDiff ℝ 1 φ := hv.inner ℝ hv
  have hparts := integral_fderiv_apply_eq_neg_integral_mul_divergence hφ hB hc
  have hpoint (x : ℝ^n) : fderiv ℝ φ x (B x) = 2 * ⟪fderiv ℝ v x (B x), v x⟫_ℝ := by
    dsimp [φ]
    rw [fderiv_inner_apply ℝ hv.differentiable_one.differentiableAt
      hv.differentiable_one.differentiableAt, real_inner_comm (v x)]
    ring
  simp_rw [hpoint, φ, real_inner_self_eq_norm_sq] at hparts
  rw [integral_const_mul] at hparts
  linarith

/-- **A gradient paired with a weighted divergence-free field.** For a `C¹` scalar `P`, a
divergence-free `C¹` field `u` and a compactly supported `C¹` weight `ψ`,
`∫ ψ ∇P·u = -∫ P ∇ψ·u`: the derivative moves from `P` to the weight, and no term with `div u`
appears. Neither `P` nor `u` needs decay. -/
theorem integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero {P : ℝ^n → ℝ} {u : ℝ^n → ℝ^n}
    {ψ : ℝ^n → ℝ} (hP : ContDiff ℝ 1 P) (hu : ContDiff ℝ 1 u) (hdiv : ∀ x, ∇· u x = 0)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ψ x * fderiv ℝ P x (u x)) = -∫ x, P x * fderiv ℝ ψ x (u x) := by
  have h := integral_fderiv_apply_eq_neg_integral_mul_divergence (B := fun x ↦ ψ x • u x) hP
    (hψ.smul hu) hc.smul_right
  have hdivB (x : ℝ^n) : ∇· (fun y : ℝ^n ↦ ψ y • u y) x = fderiv ℝ ψ x (u x) := by
    rw [divergence_smul (hψ.differentiable (by norm_num) x) (hu.differentiable (by norm_num) x),
      hdiv, mul_zero, add_zero]
  simp_rw [hdivB, map_smul, smul_eq_mul] at h
  exact h

/-- **The weighted Dirichlet identity.** For a `C²` field `v` and a compactly supported `C²`
weight `ψ`, `∫ ψ ⟨Δv, v⟩ = -∫ ψ Σᵢ |∂ᵢv|² + ½ ∫ Δψ |v|²`. -/
theorem integral_mul_inner_laplacian {v : ℝ^n → E} {ψ : ℝ^n → ℝ} (hv : ContDiff ℝ 2 v)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ψ x * ⟪laplacian v x, v x⟫_ℝ) =
      -(∫ x, ψ x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) + (1 / 2 : ℝ) * ∫ x, laplacian ψ x * ‖v x‖ ^ 2 := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hpartial (i : Fin n) : ContDiff ℝ 1 (∂[i] v) := contDiff_partialDeriv_of_succ (m := 1) hv
  have hsecond (i : Fin n) : Continuous (∂[i] ∂[i] v) :=
    (contDiff_partialDeriv_of_succ (m := 0) (hpartial i)).continuous
  have hf : ContDiff ℝ 1 (fun x ↦ ψ x • v x) := hψ1.smul hv1
  have hfc : HasCompactSupport (fun x ↦ ψ x • v x) := hc.smul_right
  -- One integration by parts in each coordinate.
  have hcoord (i : Fin n) : (∫ x, ψ x * ⟪∂[i] ∂[i] v x, v x⟫_ℝ) =
      -(∫ x, ψ x * ‖∂[i] v x‖ ^ 2) - ∫ x, ∂[i] ψ x * ⟪∂[i] v x, v x⟫_ℝ := by
    have h := integral_inner_partialDeriv_eq_neg i hf (hpartial i) hfc
    have h₁ : (fun x ↦ ⟪ψ x • v x, ∂[i] ∂[i] v x⟫_ℝ) =
        fun x ↦ ψ x * ⟪∂[i] ∂[i] v x, v x⟫_ℝ := funext fun x ↦ by
      rw [real_inner_smul_left, real_inner_comm]
    have h₂ : (fun x ↦ ⟪∂[i] (fun y ↦ ψ y • v y) x, ∂[i] v x⟫_ℝ) =
        fun x ↦ ψ x * ‖∂[i] v x‖ ^ 2 + ∂[i] ψ x * ⟪∂[i] v x, v x⟫_ℝ := funext fun x ↦ by
      rw [partialDeriv_smul (hψ1.differentiable (by norm_num) x)
        (hv1.differentiable (by norm_num) x), inner_add_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm (∂[i] v x)]
    have hi₁ : Integrable (fun x ↦ ψ x * ‖∂[i] v x‖ ^ 2) :=
      (hψ.continuous.mul ((hpartial i).continuous.norm.pow 2)).integrable_of_hasCompactSupport
        hc.mul_right
    have hi₂ : Integrable (fun x ↦ ∂[i] ψ x * ⟪∂[i] v x, v x⟫_ℝ) :=
      ((hψ1.continuous_partialDeriv i).mul
        ((hpartial i).continuous.inner hv.continuous)).integrable_of_hasCompactSupport
        (hc.partialDeriv i).mul_right
    rw [h₁, h₂, integral_add hi₁ hi₂] at h
    linarith
  -- The cross terms add up to the transport of `|v|²` by `∇ψ`.
  have hgrad : ContDiff ℝ 1 (∇ ψ) := contDiff_gradient_of_contDiff_two hψ
  have hgradc : HasCompactSupport (∇ ψ) := HasCompactSupport.intro hc.isCompact fun x hx ↦ by
    ext i
    rw [gradient_apply_eq_partialDeriv, partialDeriv_eq_zero_of_notMem_tsupport i hx]
    rfl
  have hcross := integral_inner_fderiv_apply_eq_neg_half_divergence hv1 hgrad hgradc
  have hcrossPoint (x : ℝ^n) : ⟪fderiv ℝ v x (∇ ψ x), v x⟫_ℝ =
      ∑ i : Fin n, ∂[i] ψ x * ⟪∂[i] v x, v x⟫_ℝ := by
    rw [fderiv_apply_eq_sum_smul_partialDeriv, sum_inner]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [real_inner_smul_left, gradient_apply_eq_partialDeriv]
  have hint₀ (i : Fin n) : Integrable (fun x ↦ ψ x * ⟪∂[i] ∂[i] v x, v x⟫_ℝ) :=
    (hψ.continuous.mul ((hsecond i).inner hv.continuous)).integrable_of_hasCompactSupport
      hc.mul_right
  have hint₁ (i : Fin n) : Integrable (fun x ↦ ψ x * ‖∂[i] v x‖ ^ 2) :=
    (hψ.continuous.mul ((hpartial i).continuous.norm.pow 2)).integrable_of_hasCompactSupport
      hc.mul_right
  have hint₂ (i : Fin n) : Integrable (fun x ↦ ∂[i] ψ x * ⟪∂[i] v x, v x⟫_ℝ) :=
    ((hψ1.continuous_partialDeriv i).mul
      ((hpartial i).continuous.inner hv.continuous)).integrable_of_hasCompactSupport
      (hc.partialDeriv i).mul_right
  have hL (x : ℝ^n) : ψ x * ⟪laplacian v x, v x⟫_ℝ =
      ∑ i : Fin n, ψ x * ⟪∂[i] ∂[i] v x, v x⟫_ℝ := by
    simp only [laplacian, sum_inner, Finset.mul_sum]
  have hD (x : ℝ^n) : ψ x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 =
      ∑ i : Fin n, ψ x * ‖∂[i] v x‖ ^ 2 := Finset.mul_sum _ _ _
  simp_rw [hL, hD]
  rw [integral_finsetSum _ fun i _ ↦ hint₀ i, integral_finsetSum _ fun i _ ↦ hint₁ i]
  simp_rw [hcoord]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ ↦ hint₂ i]
  simp_rw [← hcrossPoint]
  rw [hcross]
  simp_rw [← laplacian_eq_divergence_gradient, mul_comm (‖v _‖ ^ 2)]
  ring

/-- The pairing `⟨c v - ½ x·∇v + W·∇v - Δv, v⟩` of the self-similar operator with drift `W`,
applied to `v`, with `v` itself. -/
def similarityPairing (c : ℝ) (v : ℝ^n → E) (W : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ :=
  ⟪c • v x - (1 / 2 : ℝ) • fderiv ℝ v x x + fderiv ℝ v x (W x) - laplacian v x, v x⟫_ℝ

/-- The energy density of the self-similar operator with the weight `ψ`:
`ψ |∇v|² + ((c + n/4) ψ + ¼ x·∇ψ - ½ W·∇ψ - ½ Δψ) |v|²`. -/
def energyDensity (c : ℝ) (v : ℝ^n → E) (W : ℝ^n → ℝ^n) (ψ : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  ψ x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 +
    ((c + n / 4) * ψ x + (1 / 4 : ℝ) * fderiv ℝ ψ x x - (1 / 2 : ℝ) * fderiv ℝ ψ x (W x) -
      (1 / 2 : ℝ) * laplacian ψ x) * ‖v x‖ ^ 2

/-- The energy density is continuous when `v` and the weight are `C²` and `W` is continuous. -/
theorem continuous_energyDensity {v : ℝ^n → E} {W : ℝ^n → ℝ^n} {ψ : ℝ^n → ℝ}
    (hv : ContDiff ℝ 2 v) (hW : Continuous W) (hψ : ContDiff ℝ 2 ψ) (c : ℝ) :
    Continuous (energyDensity c v W ψ) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hDψ : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
  have hΔψ : Continuous (laplacian ψ) := hψ.continuous_coordinate_laplacian
  have hD : Continuous (fun x ↦ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) :=
    continuous_finsetSum _ fun i _ ↦
      (contDiff_partialDeriv_of_succ (m := 1) hv (i := i)).continuous.norm.pow 2
  unfold energyDensity
  exact (hψ.continuous.mul hD).add (((((continuous_const.mul hψ.continuous).add
    (continuous_const.mul (hDψ.clm_apply continuous_id))).sub
    (continuous_const.mul (hDψ.clm_apply hW))).sub (continuous_const.mul hΔψ)).mul
    (hv.continuous.norm.pow 2))

/-- The energy density vanishes outside the closed support of the weight. -/
theorem energyDensity_of_notMem_tsupport (c : ℝ) (v : ℝ^n → E) (W : ℝ^n → ℝ^n) {ψ : ℝ^n → ℝ}
    {x : ℝ^n} (hx : x ∉ tsupport ψ) : energyDensity c v W ψ x = 0 := by
  have hΔ : laplacian ψ x = 0 := Finset.sum_eq_zero fun i _ ↦
    partialDeriv_eq_zero_of_notMem_tsupport i fun h ↦ hx (tsupport_partialDeriv_subset i h)
  simp [energyDensity, image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx, hΔ]

/-- The energy density of a compactly supported `C²` weight is integrable. -/
theorem integrable_energyDensity {v : ℝ^n → E} {W : ℝ^n → ℝ^n} {ψ : ℝ^n → ℝ}
    (hv : ContDiff ℝ 2 v) (hW : Continuous W) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (c : ℝ) : Integrable (energyDensity c v W ψ) :=
  (continuous_energyDensity hv hW hψ c).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hc.isCompact fun _ hx ↦ energyDensity_of_notMem_tsupport c v W hx)

/-- **The weighted energy identity of the self-similar operator.** Let `v` be a `C²` field on
`ℝⁿ`, `W` a divergence-free `C¹` field, and `ψ` a compactly supported `C²` weight. Then

`∫ ψ ⟨c v - ½ x·∇v + W·∇v - Δv, v⟩ = ∫ ψ |∇v|² + ∫ ((c + n/4) ψ + ¼ x·∇ψ - ½ W·∇ψ - ½ Δψ) |v|²`,

that is, `∫ ψ · similarityPairing = ∫ energyDensity`. The drift contributes
`n/4 ψ + ¼ x·∇ψ`, the transport `-½ W·∇ψ`, and the Laplacian `ψ |∇v|² - ½ Δψ |v|²`. The field
`v` needs no decay. -/
theorem integral_mul_similarityPairing {v : ℝ^n → E} {W : ℝ^n → ℝ^n} {ψ : ℝ^n → ℝ}
    (hv : ContDiff ℝ 2 v) (hW : ContDiff ℝ 1 W) (hdiv : ∀ x, ∇· W x = 0) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (c : ℝ) :
    (∫ x, ψ x * similarityPairing c v W x) = ∫ x, energyDensity c v W ψ x := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ1.differentiable (by norm_num)
  have hDv : Continuous (fderiv ℝ v) := hv1.continuous_fderiv one_ne_zero
  have hΔv : Continuous (laplacian v) := hv.continuous_coordinate_laplacian
  have hq : Continuous (fun x ↦ ‖v x‖ ^ 2) := hv.continuous.norm.pow 2
  -- The drift and the transport, each with the weight inside the direction.
  have hdrift := integral_inner_fderiv_apply_eq_neg_half_divergence (B := fun x ↦ ψ x • x) hv1
    (hψ1.smul contDiff_id) hc.smul_right
  have htrans := integral_inner_fderiv_apply_eq_neg_half_divergence (B := fun x ↦ ψ x • W x)
    hv1 (hψ1.smul hW) hc.smul_right
  have hdivId (x : ℝ^n) : ∇· (fun y : ℝ^n ↦ ψ y • y) x = fderiv ℝ ψ x x + ψ x * n := by
    rw [divergence_smul (hψd x) differentiableAt_fun_id]
    simp [PDE.divergence, partialDeriv_coord]
  have hdivW (x : ℝ^n) : ∇· (fun y : ℝ^n ↦ ψ y • W y) x = fderiv ℝ ψ x (W x) := by
    rw [divergence_smul (hψd x) (hW.differentiable (by norm_num) x), hdiv, mul_zero, add_zero]
  simp_rw [hdivId, map_smul, real_inner_smul_left] at hdrift
  simp_rw [hdivW, map_smul, real_inner_smul_left] at htrans
  have hlap := integral_mul_inner_laplacian hv hψ hc
  -- Integrability of the pieces on the left.
  have hi₁ : Integrable (fun x ↦ ψ x * ‖v x‖ ^ 2) :=
    (hψ.continuous.mul hq).integrable_of_hasCompactSupport hc.mul_right
  have hi₂ : Integrable (fun x ↦ ψ x * ⟪fderiv ℝ v x x, v x⟫_ℝ) :=
    (hψ.continuous.mul ((hDv.clm_apply continuous_id).inner
      hv.continuous)).integrable_of_hasCompactSupport hc.mul_right
  have hi₃ : Integrable (fun x ↦ ψ x * ⟪fderiv ℝ v x (W x), v x⟫_ℝ) :=
    (hψ.continuous.mul ((hDv.clm_apply hW.continuous).inner
      hv.continuous)).integrable_of_hasCompactSupport hc.mul_right
  have hi₄ : Integrable (fun x ↦ ψ x * ⟪laplacian v x, v x⟫_ℝ) :=
    (hψ.continuous.mul (hΔv.inner hv.continuous)).integrable_of_hasCompactSupport hc.mul_right
  have hLeft : (fun x ↦ ψ x * similarityPairing c v W x) = fun x ↦ c * (ψ x * ‖v x‖ ^ 2) -
      (1 / 2 : ℝ) * (ψ x * ⟪fderiv ℝ v x x, v x⟫_ℝ) + ψ x * ⟪fderiv ℝ v x (W x), v x⟫_ℝ -
      ψ x * ⟪laplacian v x, v x⟫_ℝ := funext fun x ↦ by
    rw [similarityPairing, inner_sub_left, inner_add_left, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hA : Integrable (fun x ↦ c * (ψ x * ‖v x‖ ^ 2)) := hi₁.const_mul c
  have hB : Integrable (fun x ↦ (1 / 2 : ℝ) * (ψ x * ⟪fderiv ℝ v x x, v x⟫_ℝ)) :=
    hi₂.const_mul _
  have hAB : Integrable (fun x ↦ c * (ψ x * ‖v x‖ ^ 2) -
      (1 / 2 : ℝ) * (ψ x * ⟪fderiv ℝ v x x, v x⟫_ℝ)) := hA.sub hB
  have hABC : Integrable (fun x ↦ c * (ψ x * ‖v x‖ ^ 2) -
      (1 / 2 : ℝ) * (ψ x * ⟪fderiv ℝ v x x, v x⟫_ℝ) + ψ x * ⟪fderiv ℝ v x (W x), v x⟫_ℝ) :=
    hAB.add hi₃
  -- Integrability of the pieces on the right.
  have hDψ : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
  have hΔψ : Continuous (laplacian ψ) := hψ.continuous_coordinate_laplacian
  have hi₅ : Integrable (fun x ↦ ‖v x‖ ^ 2 * (fderiv ℝ ψ x x + ψ x * n)) := by
    refine (hq.mul ((hDψ.clm_apply continuous_id).add
      (hψ.continuous.mul continuous_const))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_left (HasCompactSupport.intro hc.isCompact fun x hx ↦ ?_)
    change fderiv ℝ ψ x x + ψ x * n = 0
    rw [fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]
    simp
  have hi₆ : Integrable (fun x ↦ ‖v x‖ ^ 2 * fderiv ℝ ψ x (W x)) := by
    refine (hq.mul (hDψ.clm_apply hW.continuous)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_left (HasCompactSupport.intro hc.isCompact fun x hx ↦ ?_)
    change fderiv ℝ ψ x (W x) = 0
    rw [fderiv_of_notMem_tsupport ℝ hx]
    simp
  have hi₇ : Integrable (fun x ↦ laplacian ψ x * ‖v x‖ ^ 2) :=
    (hΔψ.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right (HasCompactSupport.intro hc.isCompact fun x hx ↦
        Finset.sum_eq_zero fun i _ ↦ partialDeriv_eq_zero_of_notMem_tsupport i fun h ↦
          hx (tsupport_partialDeriv_subset i h)))
  have hi₈ : Integrable (fun x ↦ ψ x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) :=
    (hψ.continuous.mul (continuous_finsetSum _ fun i _ ↦
      ((contDiff_partialDeriv_of_succ (m := 1) hv (i := i)).continuous.norm.pow
        2))).integrable_of_hasCompactSupport hc.mul_right
  have hRight : energyDensity c v W ψ = fun x ↦ ψ x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 +
      (c * (ψ x * ‖v x‖ ^ 2) + (1 / 4 : ℝ) * (‖v x‖ ^ 2 * (fderiv ℝ ψ x x + ψ x * n)) -
        (1 / 2 : ℝ) * (‖v x‖ ^ 2 * fderiv ℝ ψ x (W x)) -
        (1 / 2 : ℝ) * (laplacian ψ x * ‖v x‖ ^ 2)) := funext fun x ↦ by
    rw [energyDensity]
    ring
  have hE : Integrable (fun x ↦ (1 / 4 : ℝ) * (‖v x‖ ^ 2 * (fderiv ℝ ψ x x + ψ x * n))) :=
    hi₅.const_mul _
  have hG : Integrable (fun x ↦ (1 / 2 : ℝ) * (‖v x‖ ^ 2 * fderiv ℝ ψ x (W x))) :=
    hi₆.const_mul _
  have hH : Integrable (fun x ↦ (1 / 2 : ℝ) * (laplacian ψ x * ‖v x‖ ^ 2)) := hi₇.const_mul _
  have hAE : Integrable (fun x ↦ c * (ψ x * ‖v x‖ ^ 2) +
      (1 / 4 : ℝ) * (‖v x‖ ^ 2 * (fderiv ℝ ψ x x + ψ x * n))) := hA.add hE
  have hAEG : Integrable (fun x ↦ c * (ψ x * ‖v x‖ ^ 2) +
      (1 / 4 : ℝ) * (‖v x‖ ^ 2 * (fderiv ℝ ψ x x + ψ x * n)) -
      (1 / 2 : ℝ) * (‖v x‖ ^ 2 * fderiv ℝ ψ x (W x))) := hAE.sub hG
  have hAEGH : Integrable (fun x ↦ c * (ψ x * ‖v x‖ ^ 2) +
      (1 / 4 : ℝ) * (‖v x‖ ^ 2 * (fderiv ℝ ψ x x + ψ x * n)) -
      (1 / 2 : ℝ) * (‖v x‖ ^ 2 * fderiv ℝ ψ x (W x)) -
      (1 / 2 : ℝ) * (laplacian ψ x * ‖v x‖ ^ 2)) := hAEG.sub hH
  rw [hLeft, hRight, integral_sub hABC hi₄, integral_add hAB hi₃, integral_sub hA hB,
    integral_add hi₈ hAEGH, integral_sub hAEG hH, integral_sub hAE hG, integral_add hA hE]
  simp only [integral_const_mul]
  rw [hlap, hdrift, htrans]
  ring

end PDE.Analysis
