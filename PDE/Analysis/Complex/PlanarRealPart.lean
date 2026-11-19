/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus

/-!
# Real parts of holomorphic functions in planar coordinates

Write `𝔠 : ℝ² → ℂ` for the coordinate isometry `x ↦ x₀ + i x₁` and `eₖ = 𝔠 (single k 1)`, so
`e₀ = 1` and `e₁ = i`. For a holomorphic `G`, the function `F(x) = Re G(𝔠 x)` has
`∂ₖ F(x) = Re(G'(𝔠 x) eₖ)` and `∂ₗ ∂ₖ F(x) = Re(G''(𝔠 x) eₖ eₗ)`, so
`ΔF = Re(G'' (1 + i²)) = 0`, and `F` is smooth where `G` is holomorphic.

## Main results

* `partialDeriv_re_comp`: `∂ₖ Re G(𝔠 x) = Re(G'(𝔠 x) eₖ)`.
* `partialDeriv_partialDeriv_re_comp`: `∂ₗ ∂ₖ Re G(𝔠 x) = Re(G''(𝔠 x) eₖ eₗ)`.
* `laplacian_re_comp_eq_zero`: the real part of a holomorphic function is harmonic.
* `contDiffOn_re_comp`: the real part of a function holomorphic on an open set `V ⊆ ℂ` is smooth
  on `𝔠⁻¹ V`.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- The coordinate directions in complex form: `e₀ = 1`. -/
theorem orthonormalBasisOneI_repr_symm_single_zero :
    𝔠 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := by
  rw [OrthonormalBasis.repr_symm_single, Complex.coe_orthonormalBasisOneI]
  rfl

/-- The coordinate directions in complex form: `e₁ = i`. -/
theorem orthonormalBasisOneI_repr_symm_single_one :
    𝔠 (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = Complex.I := by
  rw [OrthonormalBasis.repr_symm_single, Complex.coe_orthonormalBasisOneI]
  rfl

/-- The coordinate directions have complex modulus one: `|𝔠 eₖ| = 1`. -/
theorem norm_orthonormalBasisOneI_repr_symm_single (k : Fin 2) :
    ‖𝔠 (EuclideanSpace.single k (1 : ℝ))‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, PiLp.norm_single, norm_one]

/-- The coordinate isometry as a real continuous linear map. -/
private def cxL : ℝ^2 →L[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The map `cxL` is the coordinate isometry `𝔠`. -/
private theorem cxL_apply (y : ℝ^2) : cxL y = 𝔠 y := rfl

/-- The real derivative of `x ↦ Re G(𝔠 x)` at a point where `G` is complex differentiable. -/
private theorem hasFDerivAt_re_comp {G : ℂ → ℂ} {g : ℂ} {x : ℝ^2} (h : HasDerivAt G g (𝔠 x)) :
    HasFDerivAt (fun y ↦ (G (𝔠 y)).re)
      (Complex.reCLM.comp (((ContinuousLinearMap.toSpanSingleton ℂ g).restrictScalars ℝ).comp
        cxL)) x := by
  have hG := (h.hasFDerivAt.restrictScalars ℝ).comp x cxL.hasFDerivAt
  exact Complex.reCLM.hasFDerivAt.comp x hG

/-- `x ↦ Re G(𝔠 x)` is differentiable where `G` is complex differentiable. -/
theorem differentiableAt_re_comp {G : ℂ → ℂ} {g : ℂ} {x : ℝ^2} (h : HasDerivAt G g (𝔠 x)) :
    DifferentiableAt ℝ (fun y ↦ (G (𝔠 y)).re) x :=
  (hasFDerivAt_re_comp h).differentiableAt

/-- **First derivatives**: `∂ₖ Re G(𝔠 x) = Re(G'(𝔠 x) eₖ)`. -/
theorem partialDeriv_re_comp (k : Fin 2) {G : ℂ → ℂ} {g : ℂ} {x : ℝ^2}
    (h : HasDerivAt G g (𝔠 x)) :
    (∂[k] (fun y ↦ (G (𝔠 y)).re)) x = (g * 𝔠 (EuclideanSpace.single k 1)).re := by
  change fderiv ℝ (fun y ↦ (G (𝔠 y)).re) x (EuclideanSpace.single k 1) = _
  rw [(hasFDerivAt_re_comp h).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.reCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, cxL_apply]
  rw [mul_comm]

/-- **Second derivatives**: if `G' = dG/dz` on an open set `U` of the plane and `G'` has
derivative `g₂` at `𝔠 x`, `x ∈ U`, then `∂ₗ ∂ₖ Re G(𝔠 x) = Re(g₂ eₖ eₗ)`. -/
theorem partialDeriv_partialDeriv_re_comp (k l : Fin 2) {G G' : ℂ → ℂ} {g₂ : ℂ} {U : Set (ℝ^2)}
    (hU : IsOpen U) (hG : ∀ y ∈ U, HasDerivAt G (G' (𝔠 y)) (𝔠 y)) {x : ℝ^2} (hx : x ∈ U)
    (hG' : HasDerivAt G' g₂ (𝔠 x)) :
    (∂[l] (∂[k] (fun y ↦ (G (𝔠 y)).re))) x =
      (g₂ * 𝔠 (EuclideanSpace.single k 1) * 𝔠 (EuclideanSpace.single l 1)).re := by
  have hev : ∂[k] (fun y ↦ (G (𝔠 y)).re) =ᶠ[𝓝 x]
      fun y ↦ ((fun u ↦ G' u * 𝔠 (EuclideanSpace.single k 1)) (𝔠 y)).re := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact partialDeriv_re_comp k (hG y hy)
  rw [partialDeriv_congr_nhds l hev]
  exact partialDeriv_re_comp l (hG'.mul_const _)

/-- **Harmonicity**: the real part of a holomorphic function is harmonic. -/
theorem laplacian_re_comp_eq_zero {G G' : ℂ → ℂ} {g₂ : ℂ} {U : Set (ℝ^2)}
    (hU : IsOpen U) (hG : ∀ y ∈ U, HasDerivAt G (G' (𝔠 y)) (𝔠 y)) {x : ℝ^2} (hx : x ∈ U)
    (hG' : HasDerivAt G' g₂ (𝔠 x)) :
    PDE.laplacian (fun y ↦ (G (𝔠 y)).re) x = 0 := by
  simp only [PDE.laplacian, Fin.sum_univ_two]
  rw [partialDeriv_partialDeriv_re_comp 0 0 hU hG hx hG',
    partialDeriv_partialDeriv_re_comp 1 1 hU hG hx hG', orthonormalBasisOneI_repr_symm_single_zero,
    orthonormalBasisOneI_repr_symm_single_one]
  simp

/-- The real part of a function holomorphic on an open set `V ⊆ ℂ` is smooth on `𝔠⁻¹ V`. -/
theorem contDiffOn_re_comp {G : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hG : DifferentiableOn ℂ G V) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun y ↦ (G (𝔠 y)).re) (𝔠 ⁻¹' V) := by
  have h : ContDiffOn ℝ n G V := (hG.contDiffOn (n := n) hV).restrict_scalars ℝ
  have hc : ContDiffOn ℝ n (fun y ↦ G (cxL y)) (cxL ⁻¹' V) :=
    h.comp cxL.contDiff.contDiffOn fun y hy ↦ hy
  exact Complex.reCLM.contDiff.comp_contDiffOn hc

end PDE.Analysis
