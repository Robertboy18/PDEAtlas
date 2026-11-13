/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.ContinuousJets
import CAS.ExactTactic

/-!
# Parabolic rescaling of classical heat fields

The pullback by `(y,s) ↦ (x+r y,t+r²s)` has spatial jets `r Dx`, `r² Dxx`
and relative time derivative `r² Dt`. These jets identify the coordinate
Laplacian of the pullback, so the heat equation is preserved without assuming
a mixed derivative or an extension past the terminal time.
-/

@[expose] public section

open PDE (laplacian)

open Set

namespace HeatEquation

/-- A heat field on a closed time slab pulls back to a heat field
on `[-1,0]`. All derivative fields of the pullback are constructed and
identified, including its derivative at the terminal time. -/
theorem exists_classical_jets_parabolic_pullback
    {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ} (x : ℝ^n) (t r : ℝ)
    (hΩ : IsOpen Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t))
    (hDx : ContinuousOn Dx (Ω ×ˢ Icc (t - r ^ 2) t))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ Icc (t - r ^ 2) t))
    (hDt : ContinuousOn Dt (Ω ×ˢ Icc (t - r ^ 2) t))
    (hspace : ∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
      HasFDerivAt (fun y ↦ u y p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
      HasFDerivAt (fun y ↦ Dx (y, p.2)) (Dxx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
      HasDerivWithinAt (u p.1) (Dt p) (Icc (t - r ^ 2) t) p.2)
    (hheat : ∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
      Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0) :
    let V := (fun y : ℝ^n ↦ x + r • y) ⁻¹' Ω
    let v := fun y s ↦ u (x + r • y) (t + r ^ 2 * s)
    ContinuousOn v.uncurry (V ×ˢ Icc (-1) 0) ∧
      ∃ (Vx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ)
        (Vxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ)
        (Vt : ℝ^n × ℝ → ℝ),
        ContinuousOn Vx (V ×ˢ Icc (-1) 0) ∧
        ContinuousOn Vxx (V ×ˢ Icc (-1) 0) ∧
        ContinuousOn Vt (V ×ˢ Icc (-1) 0) ∧
        (∀ p ∈ V ×ˢ Icc (-1) 0,
          HasFDerivAt (fun y ↦ v y p.2) (Vx p) p.1) ∧
        (∀ p ∈ V ×ˢ Icc (-1) 0,
          HasFDerivAt (fun y ↦ Vx (y, p.2)) (Vxx p) p.1) ∧
        (∀ p ∈ V ×ˢ Icc (-1) 0,
          HasDerivWithinAt (v p.1) (Vt p) (Icc (-1) 0) p.2) ∧
        (∀ p ∈ V ×ˢ Icc (-1) 0,
          Vt p - laplacian (fun y ↦ v y p.2) p.1 = 0) := by
  let V := (fun y : ℝ^n ↦ x + r • y) ⁻¹' Ω
  let A := fun p : ℝ^n × ℝ ↦ (x + r • p.1, t + r ^ 2 * p.2)
  let v := fun y s ↦ u (x + r • y) (t + r ^ 2 * s)
  let Vx := fun p ↦ r • Dx (A p)
  let Vxx := fun p ↦ r ^ 2 • Dxx (A p)
  let Vt := fun p ↦ r ^ 2 * Dt (A p)
  have hV : IsOpen V := hΩ.preimage (by fun_prop)
  have hA : Continuous A := by fun_prop
  have htimeMap : MapsTo (fun s ↦ t + r ^ 2 * s) (Icc (-1) 0)
      (Icc (t - r ^ 2) t) := by
    intro s hs
    constructor
    · linarith [mul_le_mul_of_nonneg_left hs.1 (sq_nonneg r)]
    · linarith [mul_le_mul_of_nonneg_left hs.2 (sq_nonneg r)]
  have hmap : MapsTo A (V ×ˢ Icc (-1) 0) (Ω ×ˢ Icc (t - r ^ 2) t) :=
    fun p hp ↦ ⟨hp.1, htimeMap hp.2⟩
  have hspatialMap (y : ℝ^n) :
      HasFDerivAt (fun z : ℝ^n ↦ x + r • z) (r • ContinuousLinearMap.id ℝ (ℝ^n)) y :=
    ((hasFDerivAt_id y).const_smul r).const_add x
  have hspace' : ∀ p ∈ V ×ˢ Icc (-1) 0,
      HasFDerivAt (fun y ↦ v y p.2) (Vx p) p.1 := by
    intro p hp
    simpa only [v, Vx, A, Function.comp_def,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using
      (hspace (A p) (hmap hp)).comp p.1 (hspatialMap p.1)
  have hhessian' : ∀ p ∈ V ×ˢ Icc (-1) 0,
      HasFDerivAt (fun y ↦ Vx (y, p.2)) (Vxx p) p.1 := by
    intro p hp
    simpa only [Vx, Vxx, A, Function.comp_def, Pi.smul_def,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, smul_smul, ← pow_two] using
      ((hhessian (A p) (hmap hp)).comp p.1 (hspatialMap p.1)).const_smul r
  refine ⟨hu.comp hA.continuousOn hmap, Vx, Vxx, Vt,
    (hDx.comp hA.continuousOn hmap).const_smul r,
    (hDxx.comp hA.continuousOn hmap).const_smul (r ^ 2),
    (hDt.comp hA.continuousOn hmap).const_mul (r ^ 2), hspace', hhessian', ?_, ?_⟩
  · intro p hp
    have hscalar : HasDerivAt (fun s : ℝ ↦ t + r ^ 2 * s) (r ^ 2) p.2 := by
      cas
    simpa only [v, Vt, A, Function.comp_def, mul_comm] using
      (htime (A p) (hmap hp)).comp p.2 hscalar.hasDerivWithinAt htimeMap
  · intro p hp
    have hΔ : laplacian (fun y ↦ v y p.2) p.1 =
        r ^ 2 * laplacian (fun y ↦ u y (A p).2) (A p).1 := by
      simp only [laplacian, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [PDE.secondPartialDeriv_spatial_eq_of_hasFDerivAt hV hspace' hhessian' hp,
        PDE.secondPartialDeriv_spatial_eq_of_hasFDerivAt hΩ hspace hhessian (hmap hp)]
      simp only [Vxx, smul_apply, smul_eq_mul]
    change r ^ 2 * Dt (A p) - _ = 0
    rw [hΔ, ← mul_sub, hheat (A p) (hmap hp), mul_zero]

end HeatEquation
