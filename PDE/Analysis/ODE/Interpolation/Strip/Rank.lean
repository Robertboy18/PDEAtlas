/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import PDE.Common.Euclidean

import PDE.Analysis.Calculus.Prod.ParameterDerivative
import CAS.ExactTactic

/-!
# First derivatives and rank of smooth strips

The joint differential of a smooth strip is determined by its time and parameter
columns. A parameter-dependent time translation adds a multiple of the time
column to the parameter column. A smooth cubic difference vanishes to first
order, so the two strips share their first parameter jet.

These derivative statements apply to any real normed space. In three dimensions,
shearing a column preserves the determinant; a nonzero determinant gives a
continuous linear equivalence through Mathlib's finite-dimensional API.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Analysis.ODE.StripRank

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Blend two strips using a time-dependent transition. -/
def blendedStrip (U V : ℝ → ℝ → E) (θ : ℝ → ℝ) (z : ℝ × ℝ) : E :=
  U z.1 z.2 + θ z.1 • (V z.1 z.2 - U z.1 z.2)

/-- The three columns, ordered as time, speed, and normal displacement. -/
def stripDifferential (v W ν : E) : ((ℝ × ℝ) × ℝ) →L[ℝ] E :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight W).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)) +
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).smulRight ν

@[simp] theorem stripDifferential_apply (v W ν : E) (z : (ℝ × ℝ) × ℝ) :
    stripDifferential v W ν z = z.1.1 • v + z.1.2 • W + z.2 • ν := rfl

/-- Read off the actual Fréchet derivative columns in the product coordinates. -/
theorem fderiv_strip_columns {Ξ : ((ℝ × ℝ) × ℝ) → E} {t : ℝ} {v W ν : E}
    (hΞ : HasFDerivAt Ξ (stripDifferential v W ν) ((t, 0), 0)) :
    fderiv ℝ Ξ ((t, 0), 0) ((1, 0), 0) = v ∧
      fderiv ℝ Ξ ((t, 0), 0) ((0, 1), 0) = W ∧
      fderiv ℝ Ξ ((t, 0), 0) ((0, 0), 1) = ν := by
  simp only [hΞ.fderiv, stripDifferential_apply, one_smul, zero_smul,
    zero_add, add_zero, and_self]

/-- Ordinary time and speed derivatives determine the joint differential. -/
theorem hasFDerivAt_of_time_speed {U : ℝ → ℝ → E} {t : ℝ} {v W : E}
    (hU : DifferentiableAt ℝ U.uncurry (t, 0))
    (htime : HasDerivAt (fun s ↦ U s 0) v t) (hspeed : HasDerivAt (U t) W 0) :
    HasFDerivAt U.uncurry
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight W) (t, 0) := by
  have htimeCol : fderiv ℝ U.uncurry (t, 0) (1, 0) = v :=
    (PDE.Analysis.deriv_parameter_eq hU).symm.trans htime.deriv
  have hspeedCol : fderiv ℝ U.uncurry (t, 0) (0, 1) = W := by
    calc
      fderiv ℝ U.uncurry (t, 0) (0, 1) = fderiv ℝ (U t) 0 1 :=
        (PDE.Analysis.fderiv_space_apply hU 1).symm
      _ = W := by rw [fderiv_eq_smul_deriv, hspeed.deriv, one_smul]
  have hD : fderiv ℝ U.uncurry (t, 0) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight W := by
    apply ContinuousLinearMap.ext
    intro z
    have hz : z = z.1 • ((1 : ℝ), (0 : ℝ)) + z.2 • ((0 : ℝ), (1 : ℝ)) := by
      simp
    calc
      fderiv ℝ U.uncurry (t, 0) z =
          z.1 • fderiv ℝ U.uncurry (t, 0) (1, 0) +
            z.2 • fderiv ℝ U.uncurry (t, 0) (0, 1) := by
        conv_lhs => rw [hz]
        rw [map_add, map_smul, map_smul]
      _ = z.1 • v + z.2 • W := by rw [htimeCol, hspeedCol]
      _ = _ := rfl
  exact hD ▸ hU.hasFDerivAt

/-- Phase alignment adds exactly the event-time slope times the base tangent.
The supplied germ is the actual localized translation, not a new flow. -/
theorem hasDerivAt_phase_speed {F U : ℝ → ℝ → E} {τ : ℝ → ℝ}
    {t e : ℝ} {v W : E} (hF : ContDiff ℝ ∞ F.uncurry)
    (hτ : DifferentiableAt ℝ τ 0) (hτzero : τ 0 = e)
    (htime : HasDerivAt (fun s ↦ F s 0) v t) (hspeed : deriv (F t) 0 = W)
    (hgerm : U t =ᶠ[𝓝 (0 : ℝ)] (fun μ ↦ F (t + τ μ - e) μ)) :
    HasDerivAt (U t) (W + deriv τ 0 • v) 0 := by
  have hshift : HasDerivAt (fun μ ↦ t + τ μ - e) (deriv τ 0) 0 := by
    simpa only [zero_add] using
      ((hasDerivAt_const (x := (0 : ℝ)) (c := t)).fun_add hτ.hasDerivAt).sub_const e
  have hshiftZero : t + τ 0 - e = t := by rw [hτzero, add_sub_cancel_right]
  have hswap : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ F z.2 z.1) (0, t) :=
    ((hF.comp (contDiff_snd.prodMk contDiff_fst)).differentiable (by simp)) (0, t)
  have h := PDE.Analysis.hasDerivAt_moving_point
    (U := fun μ s ↦ F s μ) hswap hshift hshiftZero
  have hphase : HasDerivAt (fun μ ↦ F (t + τ μ - e) μ)
      (W + deriv τ 0 • v) 0 := by
    simpa only [fderiv_eq_smul_deriv, htime.deriv, hspeed] using h
  exact hphase.congr_of_eventuallyEq hgerm

/-- A smooth cubic difference gives equality of the actual first speed jets. -/
theorem firstJet_eq_of_cubic_difference {U V : ℝ → ℝ → E}
    {A : ℝ × ℝ → E} {J : Set ℝ} {t : ℝ}
    (hU : ContDiff ℝ ∞ U.uncurry) (hV : ContDiff ℝ ∞ V.uncurry)
    (hA : ContDiff ℝ ∞ A) (hJ : IsOpen J) (hzero : (0 : ℝ) ∈ J)
    (hcubic : ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • A (t, μ)) :
    V t 0 = U t 0 ∧ deriv (V t) 0 = deriv (U t) 0 := by
  have hvalue : V t 0 = U t 0 := sub_eq_zero.mp (by simpa using hcubic 0 hzero)
  have hp : HasDerivAt (fun μ : ℝ ↦ μ ^ 3) 0 0 := by cas
  have hAslice : HasDerivAt (fun μ ↦ A (t, μ)) (deriv (fun μ ↦ A (t, μ)) 0) 0 :=
    ((hA.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) 0).hasDerivAt
  have hfactor : HasDerivAt (fun μ : ℝ ↦ μ ^ 3 • A (t, μ)) 0 0 := by
    simpa only [zero_pow (by decide : 3 ≠ 0), zero_smul, add_zero] using hp.fun_smul hAslice
  have hgerm : (fun μ ↦ V t μ - U t μ) =ᶠ[𝓝 (0 : ℝ)]
      (fun μ ↦ μ ^ 3 • A (t, μ)) := by
    filter_upwards [hJ.mem_nhds hzero] with μ hμ
    exact hcubic μ hμ
  have hUslice : HasDerivAt (U t) (deriv (U t) 0) 0 :=
    ((hU.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) 0).hasDerivAt
  have hVslice : HasDerivAt (V t) (deriv (V t) 0) 0 :=
    ((hV.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) 0).hasDerivAt
  have hfirst : deriv (V t) 0 - deriv (U t) 0 = 0 :=
    (hVslice.fun_sub hUslice).unique (hfactor.congr_of_eventuallyEq hgerm)
  exact ⟨hvalue, sub_eq_zero.mp hfirst⟩

/-- Shearing the speed column by the tangent preserves the determinant.
Swapping its last two rows puts it in chart-column order and introduces a minus sign. -/
theorem det_phase_columns (v ν W : ℝ^3) (α : ℝ) :
    Matrix.det ![⇑v, ⇑(W + α • v), ⇑ν] = -Matrix.det ![⇑v, ⇑ν, ⇑W] := by
  classical
  let M : Matrix (Fin 3) (Fin 3) ℝ := ![⇑v, ⇑ν, ⇑W]
  have hupdate : M.updateRow 2 (M 2 + α • M 0) = ![⇑v, ⇑ν, ⇑(W + α • v)] := by
    ext row col
    fin_cases row <;> rfl
  have hshear := Matrix.det_updateRow_add_smul_self M
    (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide) α
  rw [hupdate] at hshear
  have hswap :
      Matrix.submatrix (![⇑v, ⇑ν, ⇑(W + α • v)] : Matrix (Fin 3) (Fin 3) ℝ)
        (Equiv.swap (1 : Fin 3) 2) id = ![⇑v, ⇑(W + α • v), ⇑ν] := by
    ext row col
    fin_cases row <;> simp [Matrix.submatrix, Equiv.swap_apply_def]
  have hperm := Matrix.det_permute (Equiv.swap (1 : Fin 3) 2)
    (![⇑v, ⇑ν, ⇑(W + α • v)] : Matrix (Fin 3) (Fin 3) ℝ)
  rw [hswap, hshear] at hperm
  simpa [M] using hperm

/-- Convert the actual three independent columns into Mathlib's continuous linear
equivalence. Only dimension and linear independence are used, with no inverse formula. -/
theorem exists_equiv_stripDifferential (v W ν : ℝ^3)
    (hdet : Matrix.det ![⇑v, ⇑W, ⇑ν] ≠ 0) :
    ∃ D : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ℝ^3,
      (D : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ^3) = stripDifferential v W ν := by
  classical
  let L := stripDifferential v W ν
  have hlin := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hker : LinearMap.ker L.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change L z = 0 at hz
    let c : Fin 3 → ℝ := ![z.1.1, z.1.2, z.2]
    have hsum : ∑ k : Fin 3, c k • (![⇑v, ⇑W, ⇑ν] : Matrix (Fin 3) (Fin 3) ℝ) k = 0 := by
      have hc := congrArg (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) hz
      simpa [L, stripDifferential_apply, c, Fin.sum_univ_three, map_add, map_smul]
        using hc
    have hc := Fintype.linearIndependent_iff.mp hlin c hsum
    apply Prod.ext
    · apply Prod.ext
      · simpa [c] using hc 0
      · simpa [c] using hc 1
    · simpa [c] using hc 2
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := L.toLinearMap) (by simp)).mp hinj
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  rfl

end PDE.Analysis.ODE.StripRank
