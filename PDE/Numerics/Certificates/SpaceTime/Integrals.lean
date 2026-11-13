/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.SpaceTime.Blocks

/-!
# Time integrals of norms of block fields

Let `N : E → ℝ≥0∞` be a weighted supremum norm, a Hölder seminorm, or the absolute value of a
derivative at a point, with `N(∑ᵢ aᵢ cᵢ) ≤ ∑ᵢ |aᵢ| N(cᵢ)` on the combinations at hand
(`le_sum_enorm_mul` derives this from subadditivity and homogeneity). On block `m`,
`∫ N(∑ⱼ bⱼ(τₘ(t)) rⱼ) dt ≤ kₘ ∑ⱼ (∫_lo^hi |bⱼ|) N(rⱼ)` (`lintegral_block_le`): the time integral of
the norm is bounded by the norms of the coefficients and the exact absolute integrals of the basis,
which for the cubic blocks of Chen and Hou, Part II, (3.31), are the constants
`C_I = [3, 9/4, 9/8, 27/64]` (`lintegral_block_le_cubic`).

## Main results

* `BlockField.lintegral_block_le`: on block `m`,
  `∫ N(∑ⱼ bⱼ(τₘ(t)) rⱼ) dt ≤ kₘ ∑ⱼ (∫_lo^hi |bⱼ|) N(rⱼ)`.
* `BlockField.lintegral_block_le_cubic`: on a cubic block of three time steps of length `k`,
  `∫ N(∑ᵢ (τⁱ / i!) rᵢ) dt ≤ k (3 A₀ + 9/4 A₁ + 9/8 A₂ + 27/64 A₃)`.
* `lintegral_le_of_blocks`: any function bounded on every open block by such a combination and
  vanishing after the stopping time has `∫_{s₀}^∞` bounded by the sum over the blocks; block
  boundaries are a finite set.
* `lintegral_value_le`, `lintegral_residual_le`: the field and its residual
  `π (∂ₜ F) - L F`, whose coefficients on each block are `residualCoeff π L m j`.
* `le_sum_supBound`: the supremum in time of `N(F(t))` on a block from the bounds of the basis.
* `lintegral_add_sum_smul_le`: corrections `∑ₗ aₗ(t) wₗ` with scalar time factors (the second
  correction `a(t) ∘ χ` of Part II, Section 3.3, which persists after the stopping time) add
  `∑ₗ N(wₗ) ∫ |aₗ|`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Sections 3.3
  and 3.5, (3.31).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.SpaceTime

open Finset Set MeasureTheory
open scoped ENNReal

variable {n : ℕ} {B : TimeBasis n} {E E' : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup E'] [Module ℝ E']

/-- A subadditive, absolutely homogeneous `N` bounds finite combinations termwise. -/
theorem le_sum_enorm_mul {N : E → ℝ≥0∞} (h0 : N 0 = 0) (hadd : ∀ x y, N (x + y) ≤ N x + N y)
    (hsmul : ∀ (a : ℝ) x, N (a • x) ≤ ‖a‖ₑ * N x) {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (c : ι → E) : N (∑ i ∈ s, a i • c i) ≤ ∑ i ∈ s, ‖a i‖ₑ * N (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (hadd _ _).trans (add_le_add (hsmul _ _) ih)

/-- **Scalar corrections.** `∫ N(g + ∑ₗ aₗ wₗ) ≤ ∫ N(g) + ∑ₗ N(wₗ) ∫ |aₗ|`. -/
theorem lintegral_add_sum_smul_le {N : E → ℝ≥0∞} (h0 : N 0 = 0)
    (hadd : ∀ x y, N (x + y) ≤ N x + N y) (hsmul : ∀ (a : ℝ) x, N (a • x) ≤ ‖a‖ₑ * N x)
    (s : Set ℝ) (g : ℝ → E) {ι : Type*} (u : Finset ι) (a : ι → ℝ → ℝ)
    (ha : ∀ l ∈ u, AEMeasurable (a l) (volume.restrict s)) (w : ι → E) :
    ∫⁻ t in s, N (g t + ∑ l ∈ u, a l t • w l) ≤
      (∫⁻ t in s, N (g t)) + ∑ l ∈ u, N (w l) * ∫⁻ t in s, ‖a l t‖ₑ := by
  calc ∫⁻ t in s, N (g t + ∑ l ∈ u, a l t • w l)
      ≤ ∫⁻ t in s, (N (g t) + ∑ l ∈ u, ‖a l t‖ₑ * N (w l)) :=
        lintegral_mono fun t ↦ (hadd _ _).trans (add_le_add le_rfl
          (le_sum_enorm_mul h0 hadd hsmul u (fun l ↦ a l t) w))
    _ = (∫⁻ t in s, N (g t)) + ∑ l ∈ u, ∫⁻ t in s, ‖a l t‖ₑ * N (w l) := by
        rw [lintegral_add_right' _ (Finset.aemeasurable_fun_sum _ fun l hl ↦
          ((ha l hl).enorm.mul_const _)), lintegral_finsetSum' _ fun l hl ↦
            (ha l hl).enorm.mul_const _]
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [lintegral_mul_const'' _ (ha l hl).enorm, mul_comm]

namespace BlockField

variable {F : BlockField B E}

omit [AddCommGroup E] [Module ℝ E] in
/-- Change of variables to the local time of a block: `dt = kₘ dτ`. -/
theorem integral_comp_localTime (hB : B.Sound) (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count)
    (f : ℝ → ℝ) :
    ∫ t in F.start m..F.start (m + 1), f (F.localTime m t) =
      F.scale m * ∫ τ in (B.lo : ℝ)..B.hi, f τ := by
  have hk := (scale_pos hB hF hm).ne'
  have e : ∀ t, F.localTime m t = (F.scale m)⁻¹ * t + (B.lo - F.start m / F.scale m) := by
    intro t
    simp only [localTime]
    field_simp
    ring
  simp only [e]
  rw [intervalIntegral.integral_comp_mul_add _ (inv_ne_zero hk), inv_inv, smul_eq_mul]
  congr 2
  · field_simp
    ring
  · rw [← e, localTime_end hB hF hm]

omit [AddCommGroup E] [Module ℝ E] in
/-- On block `m` the integral of `‖bⱼ(τₘ(t))‖ₑ` is `kₘ ∫_lo^hi |bⱼ|`, by the change of variables to
the local time. -/
theorem lintegral_enorm_eval_localTime (hB : B.Sound) (hF : F.IsOrdered) {m : ℕ}
    (hm : m < F.count) (j : Fin n) :
    ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), ‖B.eval j (F.localTime m t)‖ₑ =
      ENNReal.ofReal (F.scale m * ∫ τ in (B.lo : ℝ)..B.hi, |B.eval j τ|) := by
  have hc : Continuous fun t ↦ |B.eval j (F.localTime m t)| :=
    ((B.continuous_eval j).comp (continuous_iff_continuousAt.2 fun t ↦
      (F.hasDerivAt_localTime m t).continuousAt)).abs
  have hle : F.start m ≤ F.start (m + 1) := (hF m hm).le
  simp only [Real.enorm_eq_ofReal_abs]
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle,
    integral_comp_localTime hB hF hm (fun τ ↦ |B.eval j τ|)]

omit [AddCommGroup E] [Module ℝ E] in
/-- **The time integral on one block.** -/
theorem lintegral_block_le (hB : B.Sound) (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count)
    {f : ℝ → ℝ≥0∞} {A : Fin n → ℝ≥0∞}
    (hf : ∀ t ∈ Ioo (F.start m) (F.start (m + 1)),
      f t ≤ ∑ j, ‖B.eval j (F.localTime m t)‖ₑ * A j) :
    ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), f t ≤
      ENNReal.ofReal (F.scale m) * ∑ j, ENNReal.ofReal (B.absIntegral j) * A j := by
  have hk := (scale_pos hB hF hm).le
  have hmeas₀ : ∀ j : Fin n, Measurable fun t ↦ ‖B.eval j (F.localTime m t)‖ₑ := fun j ↦
    ((B.continuous_eval j).comp (continuous_iff_continuousAt.2 fun t ↦
      (F.hasDerivAt_localTime m t).continuousAt)).measurable.enorm
  have hmeas : ∀ j : Fin n, Measurable fun t ↦ ‖B.eval j (F.localTime m t)‖ₑ * A j := fun j ↦
    (hmeas₀ j).mul_const _
  calc ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), f t
      ≤ ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), ∑ j, ‖B.eval j (F.localTime m t)‖ₑ * A j :=
        setLIntegral_mono (Finset.measurable_sum _ fun j _ ↦ hmeas j) hf
    _ = ∑ j, ENNReal.ofReal (F.scale m * ∫ τ in (B.lo : ℝ)..B.hi, |B.eval j τ|) * A j := by
        rw [lintegral_finsetSum _ fun j _ ↦ hmeas j]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [lintegral_mul_const _ (hmeas₀ j), lintegral_enorm_eval_localTime hB hF hm j]
    _ ≤ ∑ j, ENNReal.ofReal (F.scale m * B.absIntegral j) * A j := by
        gcongr with j
        exact hB.integral_abs_le j
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [ENNReal.ofReal_mul hk, mul_assoc]

omit [AddCommGroup E] [Module ℝ E] in
/-- **Part II (3.31).** On a cubic block of three time steps of length `k` each,
`∫ N(∑ᵢ (τⁱ / i!) rᵢ) dt ≤ k (3 A₀ + 9/4 A₁ + 9/8 A₂ + 27/64 A₃)`. -/
theorem lintegral_block_le_cubic {F : BlockField (taylor 4 (3 / 2)) E} (hF : F.IsOrdered)
    {m : ℕ} (hm : m < F.count) {f : ℝ → ℝ≥0∞} {A : Fin 4 → ℝ≥0∞}
    (hf : ∀ t ∈ Ioo (F.start m) (F.start (m + 1)),
      f t ≤ ∑ j, ‖(taylor 4 (3 / 2)).eval j (F.localTime m t)‖ₑ * A j) :
    ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), f t ≤
      ENNReal.ofReal (F.scale m) * ∑ j, ENNReal.ofReal
        (((![3, 9 / 4, 9 / 8, 27 / 64] : Fin 4 → ℚ) j : ℚ) : ℝ) * A j := by
  have h := lintegral_block_le (taylor_sound 4 (by norm_num)) hF hm hf
  rwa [taylor_absIntegral] at h

omit [AddCommGroup E] [Module ℝ E] in
/-- Every time after `s₀` lies in an open block, at a block boundary, or after the stop. -/
theorem Ioi_start_subset :
    Ioi (F.start 0) ⊆ (⋃ m : Fin F.count, Ioo (F.start m) (F.start (m + 1))) ∪ Ioi F.stop ∪
      ((range (F.count + 1)).image F.start : Set ℝ) := by
  intro t ht
  by_cases hT : F.stop < t
  · exact Or.inl (Or.inr hT)
  by_cases hb : ∃ m ≤ F.count, t = F.start m
  · obtain ⟨m, hm, rfl⟩ := hb
    exact Or.inr (Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩))
  push Not at hb
  have hlt : t < F.stop := lt_of_le_of_ne (not_lt.1 hT) (hb F.count le_rfl)
  obtain ⟨m, hm, hmem⟩ := exists_mem_Ico (F := F) (le_of_lt ht) hlt
  refine Or.inl (Or.inl (Set.mem_iUnion.2 ⟨⟨m, hm⟩, ?_⟩))
  exact ⟨lt_of_le_of_ne hmem.1 (hb m hm.le).symm, hmem.2⟩

omit [AddCommGroup E] [Module ℝ E] in
/-- **The time integral over all blocks.** A function bounded on every open block by a
combination of the basis and vanishing after the stopping time has
`∫_{s₀}^∞ f ≤ ∑ₘ kₘ ∑ⱼ (∫ |bⱼ|) Aₘⱼ`. -/
theorem lintegral_le_of_blocks (hB : B.Sound) (hF : F.IsOrdered) {f : ℝ → ℝ≥0∞}
    {A : ℕ → Fin n → ℝ≥0∞}
    (hf : ∀ m < F.count, ∀ t ∈ Ioo (F.start m) (F.start (m + 1)),
      f t ≤ ∑ j, ‖B.eval j (F.localTime m t)‖ₑ * A m j)
    (hstop : ∀ t, F.stop < t → f t = 0) :
    ∫⁻ t in Ioi (F.start 0), f t ≤
      ∑ m ∈ range F.count, ENNReal.ofReal (F.scale m) *
        ∑ j, ENNReal.ofReal (B.absIntegral j) * A m j := by
  have hS : volume (((range (F.count + 1)).image F.start : Finset ℝ) : Set ℝ) = 0 :=
    (Finset.finite_toSet _).measure_zero _
  have hzero : ∫⁻ t in Ioi F.stop, f t = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ 0) fun t ht ↦ hstop t ht]
    simp
  calc ∫⁻ t in Ioi (F.start 0), f t
      ≤ ∫⁻ t in (⋃ m : Fin F.count, Ioo (F.start m) (F.start (m + 1))) ∪ Ioi F.stop ∪
          ((range (F.count + 1)).image F.start : Set ℝ), f t :=
        lintegral_mono_set Ioi_start_subset
    _ ≤ (∫⁻ t in ⋃ m : Fin F.count, Ioo (F.start m) (F.start (m + 1)), f t) +
          (∫⁻ t in Ioi F.stop, f t) +
          ∫⁻ t in ((range (F.count + 1)).image F.start : Set ℝ), f t :=
        (lintegral_union_le _ _ _).trans (add_le_add (lintegral_union_le _ _ _) le_rfl)
    _ = ∫⁻ t in ⋃ m : Fin F.count, Ioo (F.start m) (F.start (m + 1)), f t := by
        rw [hzero, setLIntegral_measure_zero _ _ hS, add_zero, add_zero]
    _ ≤ ∑' m : Fin F.count, ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), f t :=
        lintegral_iUnion_le _ _
    _ = ∑ m ∈ range F.count, ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), f t := by
        rw [tsum_fintype, Fin.sum_univ_eq_sum_range
          (fun m ↦ ∫⁻ t in Ioo (F.start m) (F.start (m + 1)), f t)]
    _ ≤ _ := Finset.sum_le_sum fun m hm ↦
        lintegral_block_le hB hF (Finset.mem_range.1 hm) (hf m (Finset.mem_range.1 hm))

/-- **The time integral of a norm of the field.** -/
theorem lintegral_value_le (hB : B.Sound) (hF : F.IsOrdered) {N : E → ℝ≥0∞} (h0 : N 0 = 0)
    (hN : ∀ m < F.count, ∀ τ ∈ Icc (B.lo : ℝ) B.hi,
      N (∑ i, B.eval i τ • F.coeff m i) ≤ ∑ i, ‖B.eval i τ‖ₑ * N (F.coeff m i)) :
    ∫⁻ t in Ioi (F.start 0), N (F.value t) ≤
      ∑ m ∈ range F.count, ENNReal.ofReal (F.scale m) *
        ∑ j, ENNReal.ofReal (B.absIntegral j) * N (F.coeff m j) := by
  refine lintegral_le_of_blocks hB hF (fun m hm t ht ↦ ?_) fun t ht ↦ ?_
  · rw [value_eq hF hm ⟨ht.1.le, ht.2⟩]
    exact hN m hm _ (localTime_mem_Icc hB hF hm ⟨ht.1.le, ht.2.le⟩)
  · rw [value_eq_zero_of_stop_le hF ht.le, h0]

/-- **The time integral of a norm of the residual** `π (∂ₜ F) - L F`: the coefficients on each
block are `residualCoeff π L m j`. -/
theorem lintegral_residual_le (hB : B.Sound) (hF : F.IsOrdered) (π L : E →ₗ[ℝ] E')
    {N : E' → ℝ≥0∞} (h0 : N 0 = 0)
    (hN : ∀ m < F.count, ∀ τ ∈ Icc (B.lo : ℝ) B.hi,
      N (∑ j, B.eval j τ • F.residualCoeff π L m j) ≤
        ∑ j, ‖B.eval j τ‖ₑ * N (F.residualCoeff π L m j)) :
    ∫⁻ t in Ioi (F.start 0), N (π (F.timeDeriv t) - L (F.value t)) ≤
      ∑ m ∈ range F.count, ENNReal.ofReal (F.scale m) *
        ∑ j, ENNReal.ofReal (B.absIntegral j) * N (F.residualCoeff π L m j) := by
  refine lintegral_le_of_blocks hB hF (fun m hm t ht ↦ ?_) fun t ht ↦ ?_
  · rw [timeDeriv_eq hF hm ht, value_eq hF hm ⟨ht.1.le, ht.2⟩,
      map_blockDeriv_sub_map_blockValue]
    exact hN m hm _ (localTime_mem_Icc hB hF hm ⟨ht.1.le, ht.2.le⟩)
  · rw [timeDeriv_eq_zero_of_stop_le hF ht.le, value_eq_zero_of_stop_le hF ht.le, map_zero,
      map_zero, sub_zero, h0]

/-- **The supremum in time on a block.** -/
theorem le_sum_supBound (hB : B.Sound) (hF : F.IsOrdered) {N : E → ℝ≥0∞} {m : ℕ}
    (hm : m < F.count)
    (hN : ∀ τ ∈ Icc (B.lo : ℝ) B.hi,
      N (∑ i, B.eval i τ • F.coeff m i) ≤ ∑ i, ‖B.eval i τ‖ₑ * N (F.coeff m i)) {t : ℝ}
    (ht : t ∈ Icc (F.start m) (F.start (m + 1))) :
    N (F.blockValue m t) ≤ ∑ i, ENNReal.ofReal (B.supBound i) * N (F.coeff m i) := by
  have hτ := localTime_mem_Icc hB hF hm ht
  refine (hN _ hτ).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  gcongr
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (hB.abs_le_supBound i _ hτ)

end BlockField

end CAS.Numerics.SpaceTime
