/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.FiniteRankResponse.Discontinuous
public import PDE.Analysis.Evolution.Core.Gronwall

/-!
# Linear Volterra equations with discontinuous convolution kernels

The coefficients of a finite-rank response that feeds back through linear functionals solve a
linear Volterra equation of the second kind `c(t) = f(t) + ∫₀ᵗ K(t - s) c(s) ds`
(`responseIntegral K c t`). The kernel is only required to be a.e. strongly measurable and
bounded on every `[0, T]`, so it may jump in time.

## Main results

* `eqOn_Icc_of_eq_add_responseIntegral`: two continuous solutions agree on `[0, T₀]`.
* `eqOn_of_eq_add_responseIntegral`: two continuous solutions agree on `[0, ∞)`.
* `exists_eq_add_responseIntegral`: a continuous forcing has a continuous solution on `[0, ∞)`,
  the sum of the Picard series `f + ∑ₙ (cₙ₊₁ - cₙ)`, whose terms are bounded by `B (M t)ⁿ / n!`
  on `[0, T]`.
* `exists_eq_add_responseIntegral_Icc`: a continuous forcing on `[0, T₀]` has a continuous
  solution on `[0, T₀]`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 4.2.4, (4.19) and
  Remark 4.3. <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology Nat

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniqueness for linear Volterra equations on `[0, T₀]`.** Two continuous solutions of
`c(t) = f(t) + ∫₀ᵗ K(t - s) c(s) ds` with a locally bounded measurable kernel agree on
`[0, T₀]`. -/
theorem eqOn_Icc_of_eq_add_responseIntegral {K : ℝ → E →L[ℝ] E} {f c₁ c₂ : ℝ → E} {T₀ : ℝ}
    (hKm : ∀ T, AEStronglyMeasurable K (volume.restrict (Icc 0 T)))
    (hKb : ∀ T, ∃ M, ∀ s ∈ Icc 0 T, ‖K s‖ ≤ M)
    (hc₁ : ContinuousOn c₁ (Icc 0 T₀)) (hc₂ : ContinuousOn c₂ (Icc 0 T₀))
    (h₁ : ∀ t ∈ Icc 0 T₀, c₁ t = f t + responseIntegral K c₁ t)
    (h₂ : ∀ t ∈ Icc 0 T₀, c₂ t = f t + responseIntegral K c₂ t) :
    EqOn c₁ c₂ (Icc 0 T₀) := by
  intro T hT
  obtain ⟨M, hM⟩ := hKb T
  have hT₀ : Icc 0 T ⊆ Icc 0 T₀ := Icc_subset_Icc_right hT.2
  have hdiff : ContinuousOn (fun t ↦ ‖c₁ t - c₂ t‖) (Icc 0 T) :=
    ((hc₁.sub hc₂).norm).mono hT₀
  have key := eq_zero_on_of_nonneg_le_mul_intervalIntegral (e := fun t ↦ ‖c₁ t - c₂ t‖)
    (K := M) hT.1 hdiff (fun _ _ ↦ norm_nonneg _) ?_ T ⟨hT.1, le_rfl⟩
  · exact sub_eq_zero.1 (norm_eq_zero.1 key)
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hMt : ∀ s ∈ Icc 0 t, ‖K s‖ ≤ M := fun s hs ↦ hM s (hsub hs)
  rw [h₁ t (hT₀ ht), h₂ t (hT₀ ht), add_sub_add_left_eq_sub,
    responseIntegral_sub ht.1 (hKm t) hMt (hc₁.mono (hsub.trans hT₀))
      (hc₂.mono (hsub.trans hT₀)), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le ht.1 (Eventually.of_forall fun s hs ↦ ?_)
    ((hdiff.mono hsub).intervalIntegrable_of_Icc ht.1 |>.const_mul M)
  have hts : t - s ∈ Icc 0 t := ⟨sub_nonneg.2 hs.2, sub_le_self t hs.1.le⟩
  exact ((K (t - s)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hMt _ hts) (norm_nonneg _))

/-- **Uniqueness for linear Volterra equations.** Two continuous solutions of
`c(t) = f(t) + ∫₀ᵗ K(t - s) c(s) ds` with a locally bounded measurable kernel agree on
`[0, ∞)`. -/
theorem eqOn_of_eq_add_responseIntegral {K : ℝ → E →L[ℝ] E} {f c₁ c₂ : ℝ → E}
    (hKm : ∀ T, AEStronglyMeasurable K (volume.restrict (Icc 0 T)))
    (hKb : ∀ T, ∃ M, ∀ s ∈ Icc 0 T, ‖K s‖ ≤ M)
    (hc₁ : ContinuousOn c₁ (Ici 0)) (hc₂ : ContinuousOn c₂ (Ici 0))
    (h₁ : ∀ t, 0 ≤ t → c₁ t = f t + responseIntegral K c₁ t)
    (h₂ : ∀ t, 0 ≤ t → c₂ t = f t + responseIntegral K c₂ t) :
    EqOn c₁ c₂ (Ici 0) := fun T hT ↦
  eqOn_Icc_of_eq_add_responseIntegral (T₀ := T) hKm hKb (hc₁.mono Icc_subset_Ici_self)
    (hc₂.mono Icc_subset_Ici_self) (fun t ht ↦ h₁ t ht.1) (fun t ht ↦ h₂ t ht.1)
    ⟨mem_Ici.1 hT, le_rfl⟩

variable [CompleteSpace E] in
/-- **Existence for linear Volterra equations by Picard iteration.** A locally bounded,
a.e. strongly measurable kernel `K` and a continuous forcing `f` give a continuous solution of
`c(t) = f(t) + ∫₀ᵗ K(t - s) c(s) ds` on `[0, ∞)`. The kernel may jump in time. -/
theorem exists_eq_add_responseIntegral {K : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hKm : ∀ T, AEStronglyMeasurable K (volume.restrict (Icc 0 T)))
    (hKb : ∀ T, ∃ M, ∀ s ∈ Icc 0 T, ‖K s‖ ≤ M) (hf : ContinuousOn f (Ici 0)) :
    ∃ c : ℝ → E, ContinuousOn c (Ici 0) ∧ ∀ t, 0 ≤ t → c t = f t + responseIntegral K c t := by
  set c : ℕ → ℝ → E := fun n ↦ (fun c t ↦ f t + responseIntegral K c t)^[n] f with hc_def
  have hsucc : ∀ n, c (n + 1) = fun t ↦ f t + responseIntegral K (c n) t := fun n ↦
    Function.iterate_succ_apply' _ _ _
  have hKi : ∀ T, IntegrableOn K (Icc 0 T) := fun T ↦
    (hKb T).elim fun M hM ↦ Integrable.of_bound (hKm T) M
      ((ae_restrict_mem measurableSet_Icc).mono hM)
  have hcont : ∀ n, ContinuousOn (c n) (Ici 0) := fun n ↦ by
    induction n with
    | zero => exact hf
    | succ n ih => exact hsucc n ▸ hf.add (continuousOn_responseIntegral_Ici hKi ih)
  -- the factorial bound of the differences on `[0, T]`
  have hbound : ∀ T, 0 ≤ T → ∃ B M : ℝ, 0 ≤ B ∧ 0 ≤ M ∧ (∀ s ∈ Icc 0 T, ‖K s‖ ≤ M) ∧
      ∀ n, ∀ t ∈ Icc 0 T, ‖c (n + 1) t - c n t‖ ≤ B * (M * t) ^ n / n ! := by
    intro T hT
    obtain ⟨M, hM⟩ := hKb T
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((((hcont 1).sub (hcont 0)).mono Icc_subset_Ici_self))
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT⟩)
    refine ⟨B, M, hB0, hM0, hM, fun n ↦ ?_⟩
    induction n with
    | zero => intro t ht; simpa using hB t ht
    | succ n ih =>
      intro t ht
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
      have hMt : ∀ s ∈ Icc 0 t, ‖K s‖ ≤ M := fun s hs ↦ hM s (hsub hs)
      have hct : ∀ m, ContinuousOn (c m) (Icc 0 t) := fun m ↦
        (hcont m).mono (hsub.trans Icc_subset_Ici_self)
      have heq : c (n + 1 + 1) t - c (n + 1) t =
          responseIntegral K (c (n + 1) - c n) t := by
        rw [hsucc (n + 1), hsucc n]
        simp only
        rw [add_sub_add_left_eq_sub, ← hsucc n,
          responseIntegral_sub ht.1 (hKm t) hMt (hct (n + 1)) (hct n)]
      rw [heq, responseIntegral]
      calc ‖∫ s in (0 : ℝ)..t, K (t - s) ((c (n + 1) - c n) s)‖
          ≤ ∫ s in (0 : ℝ)..t, M * (B * (M * s) ^ n / n !) := by
            refine intervalIntegral.norm_integral_le_of_norm_le ht.1
              (Eventually.of_forall fun s hs ↦ ?_) (Continuous.intervalIntegrable (by fun_prop) _ _)
            have hts : t - s ∈ Icc 0 t := ⟨sub_nonneg.2 hs.2, sub_le_self t hs.1.le⟩
            exact ((K (t - s)).le_opNorm _).trans (mul_le_mul (hMt _ hts)
              (ih s (hsub (Ioc_subset_Icc_self hs))) (norm_nonneg _) hM0)
        _ = B * (M * t) ^ (n + 1) / (n + 1)! := by
            simp only [mul_pow, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_div, integral_pow]
            rw [Nat.factorial_succ]
            push_cast
            field_simp
            ring
  -- the solution as the sum of the telescoping series
  set d : ℕ → ℝ → E := fun n t ↦ c (n + 1) t - c n t
  have hsum : ∀ t, 0 ≤ t → Summable fun n ↦ d n t := by
    intro t ht
    obtain ⟨B, M, hB0, hM0, -, hd⟩ := hbound t ht
    exact Summable.of_norm_bounded ((Real.summable_pow_div_factorial (M * t)).mul_left B)
      fun n ↦ (hd n t ⟨ht, le_rfl⟩).trans_eq (by ring)
  set u : ℝ → E := fun t ↦ f t + ∑' n, d n t
  have hpartial : ∀ N t, c N t = f t + ∑ n ∈ Finset.range N, d n t := by
    intro N t
    rw [Finset.sum_range_sub (fun n ↦ c n t)]
    simp [hc_def]
  -- uniform convergence on `[0, T]`
  have hunif : ∀ T, 0 ≤ T → ContinuousOn u (Icc 0 T) ∧
      TendstoUniformlyOn (fun N t ↦ ∑ n ∈ Finset.range N, d n t) (fun t ↦ ∑' n, d n t) atTop
        (Icc 0 T) := by
    intro T hT
    obtain ⟨B, M, hB0, hM0, -, hd⟩ := hbound T hT
    have hmaj : Summable fun n : ℕ ↦ B * (M * T) ^ n / n ! := by
      simpa [mul_div_assoc] using (Real.summable_pow_div_factorial (M * T)).mul_left B
    have hle : ∀ n, ∀ t ∈ Icc 0 T, ‖d n t‖ ≤ B * (M * T) ^ n / n ! := by
      intro n t ht
      refine (hd n t ht).trans ?_
      gcongr
      exacts [mul_nonneg hM0 ht.1, ht.2]
    refine ⟨(hf.mono Icc_subset_Ici_self).add (continuousOn_tsum (fun n ↦
      (((hcont (n + 1)).sub (hcont n)).mono Icc_subset_Ici_self)) hmaj hle), ?_⟩
    exact tendstoUniformlyOn_tsum_nat hmaj hle
  refine ⟨u, ?_, ?_⟩
  · intro t ht
    have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
      rw [← Ici_inter_Iic]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds (lt_add_one t))
    exact ((hunif (t + 1) (by linarith [mem_Ici.1 ht])).1 t ⟨ht, by linarith⟩)
      |>.mono_of_mem_nhdsWithin hmem
  · intro t ht
    obtain ⟨B, M, hB0, hM0, hM, -⟩ := hbound t ht
    obtain ⟨hu, hU⟩ := hunif t ht
    -- `c (N + 1) t` tends to `u t`
    have h1 : Tendsto (fun N ↦ c (N + 1) t) atTop (𝓝 (u t)) := by
      simpa only [hpartial, Function.comp_def] using
        (((hsum t ht).hasSum.tendsto_sum_nat).const_add (f t)).comp (tendsto_add_atTop_nat 1)
    -- and to `f t + ∫ K u`
    have h2 : Tendsto (fun N ↦ c (N + 1) t) atTop (𝓝 (f t + responseIntegral K u t)) := by
      simp only [hsucc]
      refine tendsto_const_nhds.add ?_
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hδ : 0 < ε / (M * t + 1) := div_pos hε (by positivity)
      obtain ⟨N₀, hN₀⟩ := (Metric.tendstoUniformlyOn_iff.1 hU _ hδ).exists_forall_of_atTop
      refine ⟨N₀, fun N hN ↦ ?_⟩
      have hcN : ContinuousOn (c N) (Icc 0 t) := (hcont N).mono Icc_subset_Ici_self
      rw [dist_eq_norm, responseIntegral_sub ht (hKm t) hM hcN hu]
      refine (norm_responseIntegral_le ht hM (D := ε / (M * t + 1)) fun s hs ↦ ?_).trans_lt ?_
      · have := hN₀ N hN s hs
        rw [dist_comm, dist_eq_norm] at this
        simpa [u, hpartial] using this.le
      · rw [mul_assoc, mul_comm (ε / _) t, ← mul_assoc, mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hM0 ht]
    exact tendsto_nhds_unique h1 h2

variable [CompleteSpace E] in
/-- **Existence for linear Volterra equations on `[0, T₀]`.** A continuous forcing on `[0, T₀]`
gives a continuous solution of `c(t) = f(t) + ∫₀ᵗ K(t - s) c(s) ds` on `[0, T₀]`. -/
theorem exists_eq_add_responseIntegral_Icc {K : ℝ → E →L[ℝ] E} {f : ℝ → E} {T₀ : ℝ}
    (hKm : ∀ T, AEStronglyMeasurable K (volume.restrict (Icc 0 T)))
    (hKb : ∀ T, ∃ M, ∀ s ∈ Icc 0 T, ‖K s‖ ≤ M) (hf : ContinuousOn f (Icc 0 T₀)) :
    ∃ c : ℝ → E, ContinuousOn c (Icc 0 T₀) ∧
      ∀ t ∈ Icc 0 T₀, c t = f t + responseIntegral K c t := by
  rcases lt_or_ge T₀ 0 with hT₀ | hT₀
  · exact ⟨f, by simp [Icc_eq_empty_of_lt hT₀], by simp [Icc_eq_empty_of_lt hT₀]⟩
  set g : ℝ → E := fun t ↦ f (max 0 (min t T₀)) with hg_def
  have hg : Continuous g :=
    hf.comp_continuous (by fun_prop) fun τ ↦ ⟨le_max_left _ _, max_le hT₀ (min_le_right _ _)⟩
  obtain ⟨c, hc, hceq⟩ := exists_eq_add_responseIntegral hKm hKb hg.continuousOn
  refine ⟨c, hc.mono Icc_subset_Ici_self, fun t ht ↦ ?_⟩
  rw [hceq t ht.1, hg_def]
  simp only [min_eq_left ht.2, max_eq_right ht.1]

end PDE.Analysis.Evolution
