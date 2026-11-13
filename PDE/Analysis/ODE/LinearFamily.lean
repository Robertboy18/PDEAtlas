/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Continuous families of linear ODE solutions

A continuous time-dependent coefficient gives a local solution of `γ' = B(t) γ`
in a real Banach algebra. For coefficients depending continuously on a compact
parameter space, solve the equation in the Banach algebra of continuous maps.
Evaluation then gives a jointly continuous family of fundamental matrices,
without requiring derivatives with respect to the parameter.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous coefficient in a real Banach algebra gives a local solution
of `γ' = B(t) γ` from any initial value. The prescribed positive time bound
allows this construction to be restricted to an existing trajectory cylinder. -/
theorem exists_local_linear_equation
    {R : Type*} [NormedRing R] [NormedSpace ℝ R] [CompleteSpace R]
    (B : ℝ → R) (hB : Continuous B) (x0 : R) {T : ℝ} (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ ε < T ∧ ∃ γ : ℝ → R,
      γ 0 = x0 ∧ ContinuousOn γ (Icc (-ε) ε) ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (B t * γ t) t := by
  obtain ⟨d, hd, hnear⟩ := Metric.continuousAt_iff.mp
    (hB.continuousAt (x := 0)) 1 zero_lt_one
  let K : ℝ≥0 := ‖B 0‖₊ + 1
  let L : ℝ≥0 := K * (‖x0‖₊ + 1)
  let ε : ℝ := min (T / 2) (min (d / 2) (1 / ((L : ℝ) + 1)))
  have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hε : 0 < ε := lt_min (half_pos hT)
    (lt_min (half_pos hd) (one_div_pos.mpr (by positivity)))
  have hεT : ε < T := (min_le_left _ _).trans_lt (half_lt_self hT)
  have hεd : ε < d :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hd)
  have hεL : ε ≤ 1 / ((L : ℝ) + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hnormB (t : ℝ) (ht : t ∈ Icc (-ε) ε) : ‖B t‖ ≤ K := by
    have htd : dist t 0 < d := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith only [ht.1, ht.2, hεd]
    have h := norm_le_norm_add_const_of_dist_le (hnear htd).le
    simpa only [K, NNReal.coe_add, NNReal.coe_one, coe_nnnorm] using h
  have hpl : IsPicardLindelof (fun (t : ℝ) (y : R) ↦ B t * y)
      (tmin := -ε) (tmax := ε) ⟨0, by constructor <;> linarith only [hε]⟩
      x0 1 0 L K := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro y _ z _
      calc
        dist (B t * y) (B t * z) = ‖B t * (y - z)‖ := by
          rw [dist_eq_norm, mul_sub]
        _ ≤ ‖B t‖ * ‖y - z‖ := norm_mul_le _ _
        _ ≤ (K : ℝ) * dist y z := by
          rw [dist_eq_norm]
          exact mul_le_mul_of_nonneg_right (hnormB t ht) (norm_nonneg _)
    · intro y _
      exact (hB.mul continuous_const).continuousOn
    · intro t ht y hy
      have hy' : ‖y‖ ≤ ‖x0‖ + 1 :=
        norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hy)
      calc
        ‖B t * y‖ ≤ ‖B t‖ * ‖y‖ := norm_mul_le _ _
        _ ≤ (K : ℝ) * (‖x0‖ + 1) :=
          mul_le_mul (hnormB t ht) hy' (norm_nonneg _) K.coe_nonneg
        _ = L := by simp only [L, NNReal.coe_mul, NNReal.coe_add,
          NNReal.coe_one, coe_nnnorm]
    · have hεL' : ε * ((L : ℝ) + 1) ≤ 1 :=
        (le_div_iff₀ (by positivity : 0 < (L : ℝ) + 1)).mp hεL
      simp only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_one,
        NNReal.coe_zero]
      nlinarith only [hεL', hε]
  obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨ε, hε, hεT, γ, hγ0, HasDerivWithinAt.continuousOn hγ,
    fun t ht ↦ (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩

/-- Construct a jointly continuous family of fundamental matrices for a
continuous coefficient on a compact parameter space.

The unknown is a curve in the Banach algebra of continuous maps
`X → (E →L[ℝ] E)`. Evaluation gives the individual variational equations.
Consequently, continuity in the parameter is part of the construction and
requires no parameter derivative of the coefficient. -/
theorem exists_local_continuous_linear_family
    [CompleteSpace E] {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : X × ℝ → E →L[ℝ] E) {T : ℝ} (hT : 0 < T)
    (hA : ContinuousOn A (univ ×ˢ Icc (-T) T)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < T ∧ ∃ J : X × ℝ → E →L[ℝ] E,
      ContinuousOn J (univ ×ˢ Icc (-ε) ε) ∧
      ∀ x : X, J (x, 0) = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (fun s ↦ J (x, s)) ((A (x, t)).comp (J (x, t))) t := by
  let clamp : ℝ → ℝ := fun t ↦ max (-T) (min t T)
  have hclamp : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hclamp_mem (t : ℝ) : clamp t ∈ Icc (-T) T := by
    refine ⟨le_max_left _ _, max_le (by linarith only [hT]) (min_le_right _ _)⟩
  have hclamp_eq {t : ℝ} (ht : t ∈ Icc (-T) T) : clamp t = t := by
    simp only [clamp, min_eq_left ht.2, max_eq_right ht.1]
  let coefficient : C(ℝ × X, E →L[ℝ] E) :=
    ⟨fun tx ↦ A (tx.2, clamp tx.1),
      hA.comp_continuous
        (continuous_snd.prodMk (hclamp.comp continuous_fst))
        (fun tx ↦ ⟨mem_univ _, hclamp_mem tx.1⟩)⟩
  let B : ℝ → C(X, E →L[ℝ] E) := coefficient.curry
  obtain ⟨ε, hε, hεT, γ, hγ0, hγcont, hγ⟩ :=
    exists_local_linear_equation B coefficient.curry.continuous 1 hT
  let J : X × ℝ → E →L[ℝ] E := fun xt ↦ γ xt.2 xt.1
  have hJ : ContinuousOn J (univ ×ˢ Icc (-ε) ε) :=
    continuous_eval.comp_continuousOn
      ((hγcont.comp continuousOn_snd (fun _ h ↦ h.2)).prodMk continuousOn_fst)
  refine ⟨ε, hε, hεT, J, hJ, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · change γ 0 x = _
    rw [hγ0]
    rfl
  · intro t ht
    have htT : t ∈ Icc (-T) T := by
      constructor <;> linarith only [ht.1, ht.2, hεT]
    let ev : C(X, E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := ContinuousMap.evalCLM ℝ x
    have hev : HasFDerivAt ev ev (γ t) := ev.hasFDerivAt
    have hcomp : HasDerivAt (ev ∘ γ) (ev (B t * γ t)) t :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := C(X, E →L[ℝ] E)) (E := E →L[ℝ] E)
        (f := γ) (f' := B t * γ t) (l := ev) (l' := ev)
        t hev (hγ t ht)
    have heval : HasDerivAt (fun s ↦ γ s x) ((B t * γ t) x) t := by
      simpa only [Function.comp_def, ev, ContinuousMap.evalCLM_apply] using hcomp
    change HasDerivAt (fun s ↦ γ s x)
      (A (x, clamp t) * γ t x) t at heval
    simpa only [hclamp_eq htT, ContinuousLinearMap.mul_def, J] using heval

end

end PDE.Analysis.ODE
