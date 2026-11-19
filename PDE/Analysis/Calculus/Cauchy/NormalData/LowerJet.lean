/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Jet.Hypersurface
public import PDE.Analysis.Calculus.LocalExtension
public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet

/-!
# Lower jets determined by normal Cauchy data

Tangential differentiation of an equal lower trace leaves only a conormal
tensor at the next order. Evaluation on the nonzero normal detects this
tensor. Thus all lower derivatives are
determined by the normal data alone, before using any differential equation.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace PDE.Analysis.Cauchy

open MultiIndex

variable {n k : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Equal normal data through order `k - 1` imply equality of every
ordinary derivative below order `k` along a parametrized hypersurface. The
functions need be smooth only on an open neighborhood of that hypersurface. -/
theorem iteratedFDeriv_eq_on_lt_of_normal_data
    {Γ Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) (hΓΩ : Γ ⊆ Ω)
    (ν : ℝ^n → ℝ^n) (hν : ∀ x ∈ Γ, ν x ≠ 0)
    (hΓ : HasConormalParametrizations H Γ
      (fun x ↦ (innerSL ℝ (ν x)).toLinearMap))
    {u v : ℝ^n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (hdata : ∀ j < k, ∀ x ∈ Γ, normalData j u (ν x) x = normalData j v (ν x) x) :
    ∀ j < k, EqOn (iteratedFDeriv ℝ j u) (iteratedFDeriv ℝ j v) Γ := by
  classical
  intro j hj x hx
  obtain ⟨U, hU, -, huU⟩ :=
    hu.exists_contDiff_compactSupport_eventuallyEq hΩ (hΓΩ hx)
  obtain ⟨V, hV, -, hvV⟩ :=
    hv.exists_contDiff_compactSupport_eventuallyEq hΩ (hΓΩ hx)
  obtain ⟨s, hs, hopen, hxs⟩ := mem_nhds_iff.mp (huU.and hvV)
  have hujet (i : ℕ) {y : ℝ^n} (hy : y ∈ s) :
      iteratedFDeriv ℝ i u y = iteratedFDeriv ℝ i U y :=
    (((show EqOn u U s from fun _ hz ↦ (hs hz).1).eventuallyEq_of_mem
      (hopen.mem_nhds hy)).iteratedFDeriv ℝ i).self_of_nhds
  have hvjet (i : ℕ) {y : ℝ^n} (hy : y ∈ s) :
      iteratedFDeriv ℝ i v y = iteratedFDeriv ℝ i V y :=
    (((show EqOn v V s from fun _ hz ↦ (hs hz).2).eventuallyEq_of_mem
      (hopen.mem_nhds hy)).iteratedFDeriv ℝ i).self_of_nhds
  have hd (i : ℕ) (hi : i < k) {y : ℝ^n} (hy : y ∈ Γ ∩ s) :
      normalData i U (ν y) y = normalData i V (ν y) y := by
    simpa only [normalData, hujet i hy.2, hvjet i hy.2]
      using hdata i hi y hy.1
  have hsame : ∀ i < k,
      EqOn (iteratedFDeriv ℝ i U) (iteratedFDeriv ℝ i V) (Γ ∩ s) := by
    intro i
    induction i with
    | zero =>
      intro hi y hy
      have hvalue : U y = V y := by
        simpa only [normalData_zero] using hd 0 hi hy
      ext w
      simp only [iteratedFDeriv_zero_apply, hvalue]
    | succ i ih =>
      intro hi y hy
      let e : ℝ^n := (‖ν y‖ ^ 2)⁻¹ • ν y
      have he : (innerSL ℝ (ν y)).toLinearMap e = 1 := by
        change inner ℝ (ν y) ((‖ν y‖ ^ 2)⁻¹ • ν y) = 1
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        exact inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hν y hy.1)))
      let A := iteratedFDeriv ℝ (i + 1) U y - iteratedFDeriv ℝ (i + 1) V y
      have hA (w : Fin (i + 1) → ℝ^n) :
          A w = (∏ a, (innerSL ℝ (ν y)).toLinearMap (w a)) * A (fun _ ↦ e) :=
        (hΓ.inter_open hopen).iteratedFDeriv_sub_eq_prod_smul hU hV
          (ih (by omega)) hy he w
      have hnormal : A (fun _ ↦ ν y) = 0 :=
        sub_eq_zero.mpr (hd (i + 1) hi hy)
      have hae : A (fun _ ↦ e) = 0 := by
        dsimp only [e]
        rw [A.map_smul_univ, hnormal, smul_zero]
      apply sub_eq_zero.mp
      ext w
      change A w = 0
      rw [hA, hae, mul_zero]
  exact (hujet j hxs).trans ((hsame j hj ⟨hx, hxs⟩).trans (hvjet j hxs).symm)

end PDE.Analysis.Cauchy
