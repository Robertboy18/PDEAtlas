/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Characteristics.Scalar
public import PDE.FDeriv.Calculus

/-!
# Characteristic first integrals in Euclidean coordinates

The inverse label of a scalar characteristic family gives a C² function satisfying
`ξₓ + c ξᵧ = 0` near any point where the slope `c` is C². Its transverse derivative
at the initial point is one. Both conclusions follow from the constructed ODE family.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Hyperbolic.CanonicalForm2D

/-- A C² slope constructs a normalized local first integral in the physical plane. -/
theorem exists_local_firstIntegral {c : ℝ^2 → ℝ} {x : ℝ^2} (hc : ContDiffAt ℝ 2 c x) :
    ∃ ξ : ℝ^2 → ℝ, ContDiffAt ℝ 2 ξ x ∧ (∂[1] ξ) x = 1 ∧
      (∀ᶠ y in 𝓝 x, (∂[0] ξ) y + c y * (∂[1] ξ) y = 0) := by
  let e : (ℝ × ℝ) ≃L[ℝ] ℝ^2 := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hex : e (x 0, x 1) = x := by
    ext i
    fin_cases i <;> rfl
  have hc' : ContDiffAt ℝ 2 (fun p : ℝ × ℝ ↦ c (e p)) (x 0, x 1) := by
    apply (hex.symm ▸ hc).comp _ e.contDiff.contDiffAt
  obtain ⟨label, hl, hl₀, htransport⟩ := PDE.Analysis.ODE.exists_local_characteristic_label hc'
  let q : ℝ^2 → ℝ × ℝ := fun y ↦ (y 0 - x 0, y 1)
  let D : ℝ^2 →L[ℝ] ℝ × ℝ := (EuclideanSpace.proj 0).prod (EuclideanSpace.proj 1)
  have hq (y : ℝ^2) : HasFDerivAt q D y := by
    have h₀ : HasFDerivAt (fun z : ℝ^2 ↦ z 0 - x 0) (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ) y :=
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).hasFDerivAt.sub_const (x 0)
    have h₁ : HasFDerivAt (fun z : ℝ^2 ↦ z 1) (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ) y :=
      (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
    exact h₀.prodMk h₁
  have hqreg : ContDiff ℝ 2 q :=
    ((EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).contDiff.sub contDiff_const).prodMk
      (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).contDiff
  have hqx : q x = (0, x 1) := by simp only [q, sub_self]
  let ξ : ℝ^2 → ℝ := label ∘ q
  have hξ : ContDiffAt ℝ 2 ξ x := (hqx.symm ▸ hl).comp x hqreg.contDiffAt
  have hspace : fderiv ℝ label (0, x 1) (0, 1) = 1 := by
    have hd := (hl.differentiableAt (by norm_num)).hasFDerivAt.comp (x 1)
      (hasFDerivAt_prodMk_right (0 : ℝ) (x 1))
    have heq := congrArg (fun A ↦ A (1 : ℝ)) hd.fderiv
    change fderiv ℝ (fun y ↦ label (0, y)) (x 1) 1 = fderiv ℝ label (0, x 1) (0, 1) at heq
    rw [hl₀.fderiv_eq] at heq
    simpa using heq.symm
  refine ⟨ξ, hξ, ?_, ?_⟩
  · have hd := ((hqx.symm ▸ hl).differentiableAt (by norm_num)).hasFDerivAt.comp x (hq x)
    change (fderiv ℝ ξ x) (EuclideanSpace.single 1 1) = 1
    rw [hd.fderiv]
    simpa only [ContinuousLinearMap.comp_apply, D, ContinuousLinearMap.prod_apply,
      EuclideanSpace.proj, PiLp.proj_apply, PiLp.single_apply, Fin.isValue,
      zero_ne_one, ↓reduceIte, hqx] using hspace
  · have ht : Tendsto q (𝓝 x) (𝓝 (0, x 1)) := by
      have h : ContinuousAt q x := hqreg.contDiffAt.continuousAt
      change Tendsto q (𝓝 x) (𝓝 (q x)) at h
      simpa only [hqx] using h
    filter_upwards [ht.eventually htransport,
      ht.eventually (hl.eventually (by norm_num))] with y hy hly
    have hd := (hly.differentiableAt (by norm_num)).hasFDerivAt.comp y (hq y)
    have hdir : fderiv ℝ ξ y !₂[1, c y] = 0 := by
      rw [hd.fderiv]
      have he : e (x 0 + (q y).1, (q y).2) = y := by
        ext i
        fin_cases i
        · change x 0 + (y 0 - x 0) = y 0
          simp only [← add_sub_assoc, add_sub_cancel_left]
        · rfl
      simpa only [ContinuousLinearMap.comp_apply, D, ContinuousLinearMap.prod_apply,
        EuclideanSpace.proj, PiLp.proj_apply, WithLp.ofLp_toLp, Matrix.cons_val_zero,
        Matrix.cons_val_one, he] using hy
    simpa [PDE.fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_two, mul_comm] using hdir

end Hyperbolic.CanonicalForm2D
