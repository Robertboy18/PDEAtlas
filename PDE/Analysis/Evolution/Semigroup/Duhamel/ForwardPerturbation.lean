/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.ForwardSmoothing

/-!
# Forward Volterra equations with a time-dependent perturbation

Let a kernel `K r : F →L E` satisfy `‖K r‖ ≤ M r^(-1/2)` at positive lag, and let
`A s : E →L F` be a family with `‖A s‖ ≤ a` whose action is jointly continuous at positive
times. For every forcing `g` that is continuous at positive times and has a singular bound
`D t^(-1/2) exp (ω t)`, the forward Volterra equation

`v t = g t + ∫₀ᵗ K (t - s) (A s (v s)) ds`

has a solution with a singular bound. On bounded continuous paths over positive times with
the weight `√t exp (-ω t)` the perturbation is the operator `forwardPerturbationOperator`, of
norm at most `(2√2 + √(2π)) M a / √ω`, so a large weight makes it a contraction.

The same weighted estimate gives uniqueness on a bounded interval `(0, T]`: the homogeneous
equation halves every singular bound with a large rate, so a solution with a singular bound
vanishes. This step needs no continuity of the path. Two continuous solutions of the same
inhomogeneous equation on `(0, T]` therefore agree.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace PDE.Analysis.Evolution

/-! ## Real estimates -/

/-- The singular weight `s^(-1/2) exp s` is at least one at positive times. -/
theorem one_le_rpow_neg_one_half_mul_exp {s : ℝ} (hs : 0 < s) :
    1 ≤ s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s) := by
  rw [rpow_neg_one_half_eq_inv_sqrt hs.le, one_mul, inv_mul_eq_div,
    one_le_div (Real.sqrt_pos.mpr hs)]
  calc
    Real.sqrt s ≤ Real.sqrt ((1 + s) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 + s := Real.sqrt_sq (by linarith)
    _ ≤ Real.exp s := by linarith [Real.add_one_le_exp s]

/-- A uniform bound is a singular bound with rate one. -/
theorem le_mul_rpow_neg_one_half_mul_exp {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) :
    B ≤ B * s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s) := by
  calc
    B = B * 1 := (mul_one B).symm
    _ ≤ B * (s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s)) :=
      mul_le_mul_of_nonneg_left (one_le_rpow_neg_one_half_mul_exp hs) hB
    _ = _ := (mul_assoc _ _ _).symm

/-- The convolution of the two square-root singularities against `exp (ω s)` is at most
`(2√2 + √(2π)) / √ω · t^(-1/2) exp (ω t)`. -/
theorem integral_singularPair_mul_exp_le {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) :
    (∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) ≤
      forwardSmoothingConstant / Real.sqrt ω * (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) := by
  have hpos : 0 ≤ t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t) :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  calc
    _ = (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) * (Real.sqrt t * Real.exp (-(ω * t)) *
        ∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) := by
      rw [← mul_assoc, rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp ht ω, one_mul]
    _ ≤ (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) * (forwardSmoothingConstant / Real.sqrt ω) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_exp_mul_integral_singularPair_le ht hω) hpos
    _ = _ := mul_comm _ _

/-! ## Forward integrals on a bounded interval -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {M D ω T : ℝ}

/-- A singular bound of the forcing on `(0, t)` gives the forward integral at time `t` the
singular bound `(2√2 + √(2π)) M D / √ω · t^(-1/2) exp (ω t)`. -/
theorem norm_forwardDuhamel_le_singular
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ))) {t : ℝ} (ht : 0 < t)
    (hf : ∀ s ∈ Ioo 0 t, ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (hω : 0 < ω) (hD : 0 ≤ D) :
    ‖forwardDuhamel K f t‖ ≤ forwardSmoothingConstant * M * D / Real.sqrt ω *
      (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) := by
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  calc
    _ ≤ M * D * ∫ s in (0 : ℝ)..t,
        (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) :=
      norm_forwardDuhamel_le_of_le hK ht hf
    _ ≤ M * D * (forwardSmoothingConstant / Real.sqrt ω *
        (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t))) :=
      mul_le_mul_of_nonneg_left (integral_singularPair_mul_exp_le ht hω) (mul_nonneg hM hD)
    _ = _ := by ring

/-! ## Uniqueness on a bounded interval -/

variable {A : ℝ → E →L[ℝ] F} {a : ℝ}

/-- The rate `max ω₀ ((2 (2√2 + √(2π)) M a + 1)²)` lies above `ω₀`, is positive and makes
the contraction factor `(2√2 + √(2π)) M a / √ω` at most one half. -/
theorem exists_forwardContraction_rate (hM : 0 ≤ M) (ha : 0 ≤ a) (ω₀ : ℝ) :
    ∃ ω, ω₀ ≤ ω ∧ 0 < ω ∧ forwardSmoothingConstant * M * a / Real.sqrt ω ≤ 1 / 2 := by
  have hcMa : 0 ≤ 2 * forwardSmoothingConstant * M * a :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two forwardSmoothingConstant_nonneg) hM) ha
  have hb1 : 0 < 2 * forwardSmoothingConstant * M * a + 1 := by linarith
  have hω : 0 < max ω₀ ((2 * forwardSmoothingConstant * M * a + 1) ^ 2) :=
    lt_of_lt_of_le (pow_pos hb1 2) (le_max_right _ _)
  have hsqrt : 2 * forwardSmoothingConstant * M * a + 1 ≤
      Real.sqrt (max ω₀ ((2 * forwardSmoothingConstant * M * a + 1) ^ 2)) :=
    (Real.sqrt_sq hb1.le).symm.le.trans (Real.sqrt_le_sqrt (le_max_right _ _))
  refine ⟨_, le_max_left _ _, hω, ?_⟩
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hω)]
  nlinarith

/-- The homogeneous perturbed equation halves a singular bound whose rate makes the
contraction factor `(2√2 + √(2π)) M a / √ω` at most one half. -/
theorem norm_le_half_of_eq_forwardDuhamel
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hA : ∀ s ∈ Ioc 0 T, ‖A s‖ ≤ a) (ha : 0 ≤ a) {w : ℝ → E}
    (hw : ∀ t ∈ Ioc 0 T, w t = forwardDuhamel K (fun s ↦ A s (w s)) t)
    {N : ℝ} (hω : 0 < ω) (hsmall : forwardSmoothingConstant * M * a / Real.sqrt ω ≤ 1 / 2)
    (hN : 0 ≤ N) (hb : ∀ s ∈ Ioc 0 T, ‖w s‖ ≤ N * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    ‖w t‖ ≤ N / 2 * t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t) := by
  have hf : ∀ s ∈ Ioo 0 t, ‖A s (w s)‖ ≤ (a * N) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) := by
    intro s hs
    have hs' : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
    calc
      _ ≤ ‖A s‖ * ‖w s‖ := (A s).le_opNorm _
      _ ≤ a * (N * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
        mul_le_mul (hA s hs') (hb s hs') (norm_nonneg _) ha
      _ = _ := by ring
  have hpos : 0 ≤ t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t) :=
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le
  rw [hw t ht]
  calc
    _ ≤ forwardSmoothingConstant * M * (a * N) / Real.sqrt ω *
        (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) :=
      norm_forwardDuhamel_le_singular hK ht.1 hf hω (mul_nonneg ha hN)
    _ = (forwardSmoothingConstant * M * a / Real.sqrt ω) * N *
        (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) := by ring
    _ ≤ 1 / 2 * N * (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall hN) hpos
    _ = _ := by ring

/-- Uniqueness for the homogeneous perturbed equation on `(0, T]`. A path with a singular
bound `C s^(-1/2) exp (ω s)` on `(0, T]` that satisfies
`w t = ∫₀ᵗ K (t - s) (A s (w s)) ds` for `0 < t ≤ T` vanishes on `(0, T]`. -/
theorem eq_zero_of_eq_forwardDuhamel_on
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hA : ∀ s ∈ Ioc 0 T, ‖A s‖ ≤ a) {w : ℝ → E} {C : ℝ}
    (hwb : ∀ s ∈ Ioc 0 T, ‖w s‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (hw : ∀ t ∈ Ioc 0 T, w t = forwardDuhamel K (fun s ↦ A s (w s)) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) : w t = 0 := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hA t ht)
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  obtain ⟨ω', hωω', hω', hsmall⟩ := exists_forwardContraction_rate hM ha ω
  have hiter : ∀ j : ℕ, ∀ s ∈ Ioc 0 T, ‖w s‖ ≤ max C 0 / 2 ^ j * s ^ (-(1 / 2 : ℝ)) *
      Real.exp (ω' * s) := by
    intro j
    induction j with
    | zero =>
      intro s hs
      rw [pow_zero, div_one]
      exact (hwb s hs).trans (mul_rpow_neg_one_half_mul_exp_le hs.1 hωω')
    | succ j ih =>
      intro s hs
      have hN : 0 ≤ max C 0 / 2 ^ j := div_nonneg (le_max_right _ _) (by positivity)
      calc
        _ ≤ _ := norm_le_half_of_eq_forwardDuhamel hK hA ha hw hω' hsmall hN ih hs
        _ = _ := by rw [pow_succ]; ring
  have hlim : Tendsto (fun j : ℕ ↦ max C 0 / 2 ^ j * t ^ (-(1 / 2 : ℝ)) *
      Real.exp (ω' * t)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun j : ℕ ↦ ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h3 := (h2.const_mul (max C 0)).mul_const (t ^ (-(1 / 2 : ℝ)) *
      Real.exp (ω' * t))
    rw [mul_zero, zero_mul] at h3
    refine h3.congr fun j ↦ ?_
    rw [one_div_pow]
    ring
  exact norm_le_zero_iff.mp (ge_of_tendsto' hlim fun j ↦ hiter j t ht)

/-- Two paths that are continuous on `(0, T]`, have singular bounds there and satisfy the same
perturbed equation `v t = g t + ∫₀ᵗ K (t - s) (h s + A s (v s)) ds` for `0 < t ≤ T` agree on
`(0, T]`. -/
theorem eq_of_eq_add_forwardDuhamel_on
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hAc : ContinuousOn (fun p : ℝ × E ↦ A p.1 p.2) (Ioc 0 T ×ˢ univ))
    (hA : ∀ s ∈ Ioc 0 T, ‖A s‖ ≤ a) {g v₁ v₂ : ℝ → E} {h : ℝ → F}
    (hhc : ContinuousOn h (Ioc 0 T))
    (hhb : ∀ s ∈ Ioc 0 T, ‖h s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (hc₁ : ContinuousOn v₁ (Ioc 0 T)) (hc₂ : ContinuousOn v₂ (Ioc 0 T)) {C₁ C₂ : ℝ}
    (hb₁ : ∀ s ∈ Ioc 0 T, ‖v₁ s‖ ≤ C₁ * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (hb₂ : ∀ s ∈ Ioc 0 T, ‖v₂ s‖ ≤ C₂ * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (h₁ : ∀ t ∈ Ioc 0 T, v₁ t = g t + forwardDuhamel K (fun s ↦ h s + A s (v₁ s)) t)
    (h₂ : ∀ t ∈ Ioc 0 T, v₂ t = g t + forwardDuhamel K (fun s ↦ h s + A s (v₂ s)) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) : v₁ t = v₂ t := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hA t ht)
  have hforce {v : ℝ → E} {C : ℝ} (hc : ContinuousOn v (Ioc 0 T))
      (hb : ∀ s ∈ Ioc 0 T, ‖v s‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
      {τ : ℝ} (hτ : τ ∈ Ioc 0 T) :
      IntervalIntegrable (fun s ↦ K (τ - s) (h s + A s (v s))) volume 0 τ := by
    refine intervalIntegrable_forwardIntegrand_of_le (D := D + a * C) (ω := ω) hKc hK
      (hhc.add (hAc.comp (continuousOn_id.prodMk hc) fun s hs ↦ ⟨hs, mem_univ _⟩)) ?_
      hτ.1.le hτ.2
    intro s hs
    calc
      _ ≤ ‖h s‖ + ‖A s‖ * ‖v s‖ := (norm_add_le _ _).trans (add_le_add le_rfl ((A s).le_opNorm _))
      _ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) +
          a * (C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
        add_le_add (hhb s hs) (mul_le_mul (hA s hs) (hb s hs) (norm_nonneg _) ha)
      _ = _ := by ring
  refine sub_eq_zero.mp (eq_zero_of_eq_forwardDuhamel_on (C := max C₁ 0 + max C₂ 0) (ω := ω)
    (w := v₁ - v₂) hK hA ?_ ?_ ht)
  · intro s hs
    have hp := Real.rpow_nonneg hs.1.le (-(1 / 2 : ℝ))
    have he := (Real.exp_pos (ω * s)).le
    calc
      ‖(v₁ - v₂) s‖ ≤ ‖v₁ s‖ + ‖v₂ s‖ := norm_sub_le _ _
      _ ≤ max C₁ 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) +
          max C₂ 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) :=
        add_le_add ((hb₁ s hs).trans (mul_rpow_neg_one_half_mul_exp_le hs.1 le_rfl))
          ((hb₂ s hs).trans (mul_rpow_neg_one_half_mul_exp_le hs.1 le_rfl))
      _ = _ := by ring
  · intro τ hτ
    have hsub : forwardDuhamel K (fun s ↦ h s + A s (v₁ s)) τ -
        forwardDuhamel K (fun s ↦ h s + A s (v₂ s)) τ =
        forwardDuhamel K (fun s ↦ A s ((v₁ - v₂) s)) τ := by
      simp only [forwardDuhamel]
      rw [← intervalIntegral.integral_sub (hforce hc₁ hb₁ hτ) (hforce hc₂ hb₂ hτ)]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [Pi.sub_apply, map_sub, map_add]
      abel
    rw [Pi.sub_apply, h₁ τ hτ, h₂ τ hτ, ← hsub]
    abel

/-! ## Existence -/

/-- The perturbed forward Volterra equation `v t = g t + ∫₀ᵗ K (t - s) (A s (v s)) ds` has a
solution at positive times that is continuous and has a singular bound, for every forcing
that is continuous at positive times with a singular bound. -/
theorem exists_eq_add_forwardDuhamel [CompleteSpace E]
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hAc : ContinuousOn (fun p : ℝ × E ↦ A p.1 p.2) (Ioi 0 ×ˢ univ))
    (hA : ∀ s, 0 < s → ‖A s‖ ≤ a) {g : ℝ → E} (hgc : ContinuousOn g (Ioi 0))
    (hgb : ∀ t, 0 < t → ‖g t‖ ≤ D * t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) :
    ∃ v : ℝ → E, ContinuousOn v (Ioi 0) ∧
      (∃ C ω' : ℝ, ∀ t, 0 < t → ‖v t‖ ≤ C * t ^ (-(1 / 2 : ℝ)) * Real.exp (ω' * t)) ∧
      ∀ t, 0 < t → v t = g t + forwardDuhamel K (fun s ↦ A s (v s)) t := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hA 1 one_pos)
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  obtain ⟨ω', hωω', hω', hsmall⟩ := exists_forwardContraction_rate hM ha ω
  have hV : ‖-forwardPerturbationOperator K A hω' hKc hK hAc hA‖ < 1 := by
    rw [norm_neg]
    exact ((norm_forwardPerturbationOperator_le K A hω' hKc hK hAc hA).trans hsmall).trans_lt
      (by norm_num)
  obtain ⟨w, hw⟩ : ∃ w : Ioi (0 : ℝ) →ᵇ E,
      w + (-forwardPerturbationOperator K A hω' hKc hK hAc hA) w =
        forwardEncode ω' hωω' hgc hgb :=
    ⟨_, inverseOneAdd_add_apply _ hV _⟩
  refine ⟨forwardDecode ω' w,
    continuousOn_forwardDecode _ w, ⟨‖w‖, _, fun t ht ↦ norm_forwardDecode_le _ w ht⟩,
    fun t ht ↦ ?_⟩
  have hwt := congrArg (fun z : Ioi (0 : ℝ) →ᵇ E ↦ z ⟨t, ht⟩) hw
  simp only [BoundedContinuousFunction.add_apply] at hwt
  rw [neg_apply, BoundedContinuousFunction.neg_apply] at hwt
  have hwt' : w ⟨t, ht⟩ = forwardEncode ω' hωω' hgc hgb ⟨t, ht⟩ +
      forwardPerturbationOperator K A hω' hKc hK hAc hA w ⟨t, ht⟩ := by
    rw [← hwt]
    abel
  rw [forwardDecode_of_pos _ _ ht, hwt', forwardEncode_apply, forwardPerturbationOperator_apply,
    ← smul_add, smul_smul, rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp ht, one_smul]

end PDE.Analysis.Evolution
