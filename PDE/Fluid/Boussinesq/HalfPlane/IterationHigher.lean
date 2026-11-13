/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.LevelK
public import PDE.Fluid.Boussinesq.HalfPlane.LocalExistence
import PDE.Fluid.Boussinesq.HalfPlane.CarriedVorticityHigher

/-!
# Local existence at level `k`

The Picard iterates `ωⁿ` of the local existence proof, started at the extended vorticity datum, keep
the regularity of data `ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}`, `k ≥ 2`: they are `C^{k,α}` histories with
one bound on the interval `[-T, T]` of the local theorem (`exists_isCkVorticityHistory`). The length
of that interval depends only on the `C^{1,α} × C^{2,α}` bounds of the data, and no further
restriction of the time is needed. The limit of the iterates keeps these bounds, so the solution of
the local theorem is a regular solution of order `k` (`exists_isRegularSolutionOfOn_Ioo`).

## Main results

* `exists_isCkVorticityHistory`: uniform `C^{k,α}` bounds of the iterates.
* `IsPicardSetting.isCkVorticityHistory_picardLimit`: the limit keeps them.
* `exists_isRegularSolutionOfOn_Ioo`: local existence of regular solutions of order `k ≥ 2` on
  the time interval of the local theorem.

## How it works

We argue by induction on the order `j ≤ k`, starting from the `C^{1,α}` bounds of the local theorem.
At order `j + 1 ≥ 2` the iterates have one bound of order at most `j`, so the constant terms `c` and
the slopes `s` of the top-order bounds `c + s ∫₀^{|t|} P` of `carriedVorticity_bounds` are the same
for all of them. With `M` above the data bound and every `|c|`, and `C` above every `|s|`, the
majorant `P(r) = M exp (C r)` satisfies `c + s ∫₀ˣ P ≤ P(x)` (`add_mul_integral_exp_le`). Hence if
`ωⁿ` has the top-order majorant `P`, so does `ωⁿ⁺¹`, and induction on `n` gives one bound for all
iterates (`exists_isCkVorticityHistory_succ`). Uniform `C^{k,α}` bounds pass to uniform limits
(`IsCkVorticityHistory.of_tendsto`). The limit is then a history whose top-order majorant is its
constant bound, and `carriedTemperature_bounds` and `uniform_carriedTemperature` make its carried
temperature `C^{k+1,α}` with derivatives continuous in time.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

namespace Boussinesq.HalfPlane

variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R T : ℝ}

/-- The constant history of the extended vorticity datum of data of order `k` is a `C^{k,α}`
history with the support radius and the bound of the data. -/
theorem isCkVorticityHistory_dataVorticity {k : ℕ} {Nd : ℝ} (hd : IsHolderDataOf k ω₀ θ₀ α R Nd)
    (a b : ℝ) : IsCkVorticityHistory k (fun _ ↦ dataVorticity ω₀) a b α R Nd := by
  have he : EqOn (dataVorticity ω₀) ω₀ H̄ := fun x hx ↦ dataVorticity_of_nonneg ω₀ hx
  have hD (j : ℕ) {y : ℝ^2} (hy : 0 ≤ y 1) :
      iteratedFDerivWithin ℝ j (dataVorticity ω₀) H̄ y = iteratedFDerivWithin ℝ j ω₀ H̄ y :=
    iteratedFDerivWithin_congr he hy j
  exact
    { contDiffOn := fun _ _ ↦ hd.vorticity_contDiffOn.congr he
      eq_zero := fun _ _ y hy hyR ↦ by
        rw [dataVorticity_of_nonneg ω₀ hy]; exact (hd.eq_zero y hy hyR).1
      norm_le := fun _ _ j hj y hy ↦ by rw [hD j hy]; exact hd.norm_vorticity_le j hj y hy
      holder := fun _ _ y z hy hz ↦ by
        rw [hD k hy, hD k hz]; exact hd.holder_vorticity y z hy hz
      uniform := fun _ _ _ _ ε hε ↦ ⟨1, one_pos, fun _ _ _ _ _ ↦ by simp [hε.le]⟩ }

/-- `C ∫₀ˣ M exp (C r) dr = M exp (C x) - M`. -/
theorem mul_integral_exp (M C x : ℝ) :
    C * ∫ r in (0)..x, M * Real.exp (C * r) = M * Real.exp (C * x) - M := by
  have hd (r : ℝ) : HasDerivAt (fun r ↦ M * Real.exp (C * r)) (C * (M * Real.exp (C * r))) r := by
    have h := (((hasDerivAt_id' r).const_mul C).exp).const_mul M
    convert h using 1
    ring
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hd r)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- **The exponential majorant.** If `|c| ≤ M` and `|s| ≤ C`, then
`c + s ∫₀ˣ M exp (C r) dr ≤ M exp (C x)` for `x ≥ 0`. -/
theorem add_mul_integral_exp_le {c s M C x : ℝ} (hc : |c| ≤ M) (hs : |s| ≤ C) (hx : 0 ≤ x) :
    c + s * ∫ r in (0)..x, M * Real.exp (C * r) ≤ M * Real.exp (C * x) := by
  have hM : 0 ≤ M := (abs_nonneg c).trans hc
  have hΦ : 0 ≤ ∫ r in (0)..x, M * Real.exp (C * r) :=
    intervalIntegral.integral_nonneg hx fun r _ ↦ by positivity
  have h1 : s * ∫ r in (0)..x, M * Real.exp (C * r) ≤ C * ∫ r in (0)..x, M * Real.exp (C * r) :=
    mul_le_mul_of_nonneg_right ((le_abs_self s).trans hs) hΦ
  linarith [mul_integral_exp M C x, (le_abs_self c).trans hc]

variable {ω : ℕ → ℝ → ℝ^2 → ℝ}

/-- **One more derivative for all iterates.** Let `ωⁿ` be the iterates of the map
`carriedHistory ω₀ θ₀ (-T) T` started at the extended vorticity datum, for data of order
`j + 1 ≥ 2`. If all of them are `C^{j,α}` histories on `[-T, T]` with one support radius `R₁` and
one bound, then all of them are `C^{j+1,α}` histories with one bound. -/
theorem exists_isCkVorticityHistory_succ {j : ℕ} {R₁ Nd Nlow : ℝ} (hj : 1 ≤ j)
    (hd : IsHolderDataOf (j + 1) ω₀ θ₀ α R Nd) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (hR₁ : 0 ≤ R₁) (h0 : ω 0 = fun _ ↦ dataVorticity ω₀)
    (hs : ∀ n, ω (n + 1) = carriedHistory ω₀ θ₀ (-T) T (ω n))
    (hlow : ∀ n, IsCkVorticityHistory j (ω n) (-T) T α R₁ Nlow) :
    ∃ B, ∀ n, IsCkVorticityHistory (j + 1) (ω n) (-T) T α R₁ B := by
  have hk : 2 ≤ j + 1 := by omega
  set c₁ := vorticityTopConst (j + 1) α R₁ Nd Nlow T
  set s₁ := vorticityTopSlope (j + 1) α R₁ Nd Nlow T
  set c₂ := vorticityTopHolderConst (j + 1) α R₁ Nd Nlow T
  set s₂ := vorticityTopHolderSlope (j + 1) α R₁ Nd Nlow T
  obtain ⟨M, C, hNdM, hc₁, hs₁, hc₂, hs₂⟩ :
      ∃ M C : ℝ, Nd ≤ M ∧ |c₁| ≤ M ∧ |s₁| ≤ C ∧ |c₂| ≤ M ∧ |s₂| ≤ C :=
    ⟨max Nd (max |c₁| |c₂|), max |s₁| |s₂|, le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), le_max_left _ _,
      (le_max_right _ _).trans (le_max_right _ _), le_max_right _ _⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans hc₁
  have hC : 0 ≤ C := (abs_nonneg _).trans hs₁
  obtain ⟨B, hB₀, hB₁⟩ : ∃ B, Nd ≤ B ∧
      carriedBound (j + 1) α R₁ Nd Nlow T (∫ r in (0)..T, M * Real.exp (C * r)) ≤ B :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hPM {t : ℝ} : Nd ≤ M * Real.exp (C * |t|) :=
    hNdM.trans (le_mul_of_one_le_right hM (Real.one_le_exp (mul_nonneg hC (abs_nonneg t))))
  have hiter : ∀ n, IsTopBoundedHistory (j + 1) (ω n) T α R₁ B Nlow
      (fun r ↦ M * Real.exp (C * r)) := by
    intro n
    induction n with
    | zero =>
      have hl := hlow 0
      rw [h0] at hl ⊢
      have hdat := isCkVorticityHistory_dataVorticity hd (-T) T
      exact
        { history := (hdat.of_le hB₀).of_eq_zero hl.eq_zero
          low := hl
          continuousOn := (by fun_prop : Continuous fun r ↦ M * Real.exp (C * r)).continuousOn
          nonneg := fun r _ ↦ by positivity
          norm_le := fun t ht y hy ↦ (hdat.norm_le t ht (j + 1) le_rfl y hy).trans hPM
          holder := fun t ht y z hy hz ↦ (hdat.holder t ht y z hy hz).trans
            (mul_le_mul_of_nonneg_right hPM (Real.rpow_nonneg (norm_nonneg _) α)) }
    | succ n ih =>
      have hl := hlow (n + 1)
      rw [hs n] at hl ⊢
      have hc := isCkVorticityHistory_carriedHistory ih hd hα hα1 hk hT hR₁
      exact
        { history := (hc.of_le hB₁).of_eq_zero hl.eq_zero
          low := hl
          continuousOn := (by fun_prop : Continuous fun r ↦ M * Real.exp (C * r)).continuousOn
          nonneg := fun r _ ↦ by positivity
          norm_le := fun t ht y hy ↦
            ((carriedVorticity_bounds ih hd hα hα1 hk hT ht).norm_top_le y hy).trans
              (add_mul_integral_exp_le hc₁ hs₁ (abs_nonneg t))
          holder := fun t ht y z hy hz ↦
            ((carriedVorticity_bounds ih hd hα hα1 hk hT ht).holder_top y z hy hz).trans
              (mul_le_mul_of_nonneg_right (add_mul_integral_exp_le hc₂ hs₂ (abs_nonneg t))
                (Real.rpow_nonneg (norm_nonneg _) α)) }
  exact ⟨B, fun n ↦ (hiter n).history⟩

/-- **Uniform `C^{k,α}` bounds of the iterates.** Let `ωⁿ` be the iterates of the map
`carriedHistory ω₀ θ₀ (-T) T` started at the extended vorticity datum, for data of order `k`. If
all of them are `C^{1,α}` histories on `[-T, T]` with one support radius `R₁` and one set of
bounds, as for the time of the local theorem, then all of them are `C^{k,α}` histories with one
bound. -/
theorem exists_isCkVorticityHistory {k : ℕ} {R₁ Nk B₀ M₀ B₁ M₁ : ℝ}
    (hd : IsHolderDataOf k ω₀ θ₀ α R Nk) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (hR₁ : 0 ≤ R₁) (h0 : ω 0 = fun _ ↦ dataVorticity ω₀)
    (hs : ∀ n, ω (n + 1) = carriedHistory ω₀ θ₀ (-T) T (ω n))
    (h1 : ∀ n, IsC1VorticityHistory (ω n) (-T) T α R₁ B₀ M₀ B₁ M₁) :
    ∃ B, ∀ n, IsCkVorticityHistory k (ω n) (-T) T α R₁ B := by
  suffices h : ∀ j ≤ k, ∃ B, ∀ n, IsCkVorticityHistory j (ω n) (-T) T α R₁ B from h k le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨_, fun n ↦ (h1 n).toIsCkVorticityHistory.mono hα.le hα1.le (Nat.zero_le 1)⟩
  | succ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨_, fun n ↦ (h1 n).toIsCkVorticityHistory⟩
    · obtain ⟨Nlow, hlow⟩ := ih (by omega)
      exact exists_isCkVorticityHistory_succ hj0 (hd.mono hα.le hα1.le hj) hα hα1 hT hR₁ h0 hs
        hlow

/-- **The limit of the iteration keeps uniform `C^{k,α}` bounds.** If all Picard iterates of a
setting are `C^{k,α}` histories on `[-T, T]` with one support radius and one bound, so is their
limit. -/
theorem IsPicardSetting.isCkVorticityHistory_picardLimit {ω : ℝ → ℝ^2 → ℝ}
    {R₁ B M B₁ M₁ N L : ℝ} (hP : IsPicardSetting ω₀ θ₀ ω T α R₁ B M B₁ M₁ N L) {k : ℕ}
    {R' B' : ℝ} (hk : ∀ n, IsCkVorticityHistory k (picardIterate ω₀ θ₀ T ω n) (-T) T α R' B') :
    IsCkVorticityHistory k (picardLimit ω₀ θ₀ T ω) (-T) T α R' B' :=
  IsCkVorticityHistory.of_tendsto hP.pos hP.lt_one.le hk hP.picardIterate_cauchy
    fun _ ht _ hy ↦ hP.tendsto_picardLimit ht hy

/-- **Local existence at level `k`.** For `k ≥ 2`, `0 < α < 1` and bounds `R, N ≥ 0` there is a
time `T > 0`, depending only on `α`, `R`, `N`, such that all data of the class
`IsHolderData ω₀ θ₀ α R N` that are moreover data of order `k` have a regular solution of order
`k` on `(-T, T)` with these data at time zero. Its time slices are data of the class with support
radius `R + 1` and bound `iterationOutputBound α R N T`, and data of order `k` with support radius
`R + 1` and one bound. -/
theorem exists_isRegularSolutionOfOn_Ioo {k : ℕ} {N : ℝ} (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) (hR : 0 ≤ R) (hN : 0 ≤ N) :
    ∃ T > 0, ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N → ∀ Nk : ℝ,
      IsHolderDataOf k ω₀ θ₀ α R Nk →
      ∃ sol : VorticityStreamFields, IsRegularSolutionOfOn k sol (Ioo (-T) T) α ∧
        HasDataAt sol 0 ω₀ θ₀ ∧
        (∀ t ∈ Ioo (-T) T, IsHolderData (fun x ↦ sol.vorticity x t)
          (fun x ↦ sol.temperature x t) α (R + 1) (iterationOutputBound α R N T)) ∧
        ∃ N' : ℝ, ∀ t ∈ Ioo (-T) T, IsHolderDataOf k (fun x ↦ sol.vorticity x t)
          (fun x ↦ sol.temperature x t) α (R + 1) N' := by
  obtain ⟨T, hT, h₁, h₂, h₃, h₄⟩ := exists_iterationTime (R := R) hα hN
  refine ⟨T, hT, fun ω₀ θ₀ hd Nk hdk ↦ ?_⟩
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hR₁ : 0 ≤ R + 1 := by linarith
  have hstart : IsIterationClass T α R N (fun _ ↦ dataVorticity ω₀) :=
    isIterationClass_dataVorticity hd hα.le hα1.le
  have hinv (ω : ℝ → ℝ^2 → ℝ) (hω : IsIterationClass T α R N ω) :
      IsIterationClass T α R N (carriedHistory ω₀ θ₀ (-T) T ω) :=
    isIterationClass_carriedHistory hd hα hα1 hR hT h₁ h₂ h₃ h₄ hω
  have hσ : 0 ≤ iterationSecondBound α R N T :=
    (hstart.isBoundedFlowOn hα hα1 hR hT.le).zero_le_σ h0
  have hL0 : 0 ≤ iterationAmplitudeLipschitz α R N T :=
    add_nonneg hN (mul_nonneg hT.le (forcingDerivBound_nonneg hN (Real.exp_pos _).le hσ))
  have hP : IsPicardSetting ω₀ θ₀ (fun _ ↦ dataVorticity ω₀) T α (R + 1) (2 * N + 1)
      (2 * (2 * N + 1)) (2 * N + 1) (2 * N + 1) N (iterationAmplitudeLipschitz α R N T) :=
    ⟨hT.le, hα, hα1, hd.temperature_contDiffOn, hd.norm_fderivWithin_temperature_le, hL0, hstart,
      hinv, fun ω' hω' t ht a' a'' ha' ha'' ↦
        IsIterationClass.abs_amplitude_sub_le hω' hd hα hα1 hR hT.le ht ha' ha''⟩
  set ωl := picardLimit ω₀ θ₀ T (fun _ ↦ dataVorticity ω₀)
  have hl : IsIterationClass T α R N ωl := hP.isC1VorticityHistory_picardLimit
  have hfix : ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 →
      ωl t x = carriedVorticity ω₀ θ₀ ωl (-T) T x t :=
    fun t ht x hx ↦ hP.picardLimit_eq_carriedVorticity ht hx
  obtain ⟨B, hB⟩ := exists_isCkVorticityHistory (ω := picardIterate ω₀ θ₀ T
    (fun _ ↦ dataVorticity ω₀)) hdk hα hα1 hT.le hR₁ rfl (picardIterate_succ ω₀ θ₀ T _)
    hP.iterate_mem
  have hkl : IsCkVorticityHistory k ωl (-T) T α (R + 1) B := hP.isCkVorticityHistory_picardLimit hB
  have hB0 : 0 ≤ B := hkl.nonneg h0
  have htop : IsTopBoundedHistory k ωl T α (R + 1) B (2 * B) (fun _ ↦ B) :=
    { history := hkl
      low := hkl.mono hα.le hα1.le (Nat.sub_le k 1)
      continuousOn := continuousOn_const
      nonneg := fun _ _ ↦ hB0
      norm_le := fun t ht y hy ↦ hkl.norm_le t ht k le_rfl y hy
      holder := fun t ht y z hy hz ↦ hkl.holder t ht y z hy hz }
  obtain ⟨N', hN₁, hN₂, hN₃, hN₄, hN₅⟩ : ∃ N' : ℝ, B ≤ N' ∧ Nk ≤ N' ∧
      temperatureBound k α (R + 1) Nk (2 * B) T ≤ N' ∧
      |temperatureTopConst k α (R + 1) Nk (2 * B) T| +
        |temperatureTopSlope k α (R + 1) Nk (2 * B) T| * (T * B) ≤ N' ∧
      |temperatureTopHolderConst k α (R + 1) Nk (2 * B) T| +
        |temperatureTopHolderSlope k α (R + 1) Nk (2 * B) T| * (T * B) ≤ N' :=
    ⟨max B (max Nk (max _ (max _ _))), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _),
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)⟩
  have hωθ {t : ℝ} (ht : t ∈ Icc (-T) T) : IsHolderDataOf k (ωl t)
      (fun x ↦ carriedTemperature θ₀ ωl (-T) T x t) α (R + 1) N' := by
    have hθb := carriedTemperature_bounds htop hdk hα hα1 hk ht
    have h1 := isHolderData_carried hd hα hα1 hR hT h₄ hl (hinv ωl hl) ht
    have hΦ : 0 ≤ ∫ r in (0)..(|t|), B :=
      intervalIntegral.integral_nonneg (abs_nonneg t) fun _ _ ↦ hB0
    have hΦ' : ∫ r in (0)..(|t|), B ≤ T * B := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      exact mul_le_mul_of_nonneg_right (abs_le_of_mem_Icc_neg ht) hB0
    refine
      { vorticity_contDiffOn := hkl.contDiffOn t ht
        temperature_contDiffOn := hθb.contDiffOn
        eq_zero := fun x hx hxR ↦ ⟨hkl.eq_zero t ht x hx hxR, (h1.eq_zero x hx hxR).2⟩
        norm_vorticity_le := fun j hj x hx ↦ (hkl.norm_le t ht j hj x hx).trans hN₁
        holder_vorticity := fun x y hx hy ↦ (hkl.holder t ht x y hx hy).trans
          (mul_le_mul_of_nonneg_right hN₁ (Real.rpow_nonneg (norm_nonneg _) α))
        norm_temperature_le := fun j hj x hx ↦ ?_
        holder_temperature := fun x y hx hy ↦ (hθb.holder_top x y hx hy).trans
          (mul_le_mul_of_nonneg_right ((add_mul_le_abs_add_abs_mul hΦ hΦ').trans hN₅)
            (Real.rpow_nonneg (norm_nonneg _) α)) }
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact (abs_carriedTemperature_le htop hdk hα hα1 (by omega) ht hx).trans hN₂
    rcases hj.lt_or_eq with hjk | rfl
    · exact (hθb.norm_le j hj0 hjk x hx).trans hN₃
    · exact (hθb.norm_top_le x hx).trans ((add_mul_le_abs_add_abs_mul hΦ hΦ').trans hN₄)
  obtain ⟨hsol, hdat⟩ := isSolutionOn_of_fixedPoint hα hα1 hd (by linarith) hT hl hfix
  have hslice {t : ℝ} (ht : t ∈ Icc (-T) T) :
      IsHolderDataOf k (fun x ↦ (assembled ω₀ θ₀ ωl (-T) T).vorticity x t)
        (fun x ↦ (assembled ω₀ θ₀ ωl (-T) T).temperature x t) α (R + 1) N' :=
    (hωθ ht).congr (fun x hx ↦ assembled_vorticity_of_nonneg hfix ht hx) fun _ _ ↦ rfl
  refine ⟨assembled ω₀ θ₀ ωl (-T) T,
    { toIsSolutionOn := hsol
      holderData := fun a b hab ↦ ⟨R + 1, N', fun t ht ↦ hslice (Ioo_subset_Icc_self (hab ht))⟩
      vorticity_uniform := fun j hj t ht ε hε ↦ ?_
      temperature_uniform := fun j hj t ht ε hε ↦ ?_ }, hdat,
    fun t ht ↦ isHolderData_carried hd hα hα1 hR hT h₄ hl (hinv ωl hl) (Ioo_subset_Icc_self ht),
    N', fun t ht ↦ hslice (Ioo_subset_Icc_self ht)⟩
  · have hEq {s : ℝ} (hs : s ∈ Icc (-T) T) :
        EqOn (fun y ↦ (assembled ω₀ θ₀ ωl (-T) T).vorticity y s) (ωl s) H̄ :=
      fun y hy ↦ assembled_vorticity_of_nonneg hfix hs hy
    obtain ⟨δ, hδ, h⟩ := hkl.uniform j hj t (Ioo_subset_Icc_self ht) ε hε
    refine ⟨δ, hδ, fun s hs hst x hx ↦ ?_⟩
    rw [iteratedFDerivWithin_congr (hEq (Ioo_subset_Icc_self hs)) hx,
      iteratedFDerivWithin_congr (hEq (Ioo_subset_Icc_self ht)) hx]
    exact h s (Ioo_subset_Icc_self hs) hst x hx
  · obtain ⟨δ, hδ, h⟩ := uniform_carriedTemperature htop hdk hα hα1 hk hT.le hR₁ j hj t
      (Ioo_subset_Icc_self ht) ε hε
    exact ⟨δ, hδ, fun s hs hst x hx ↦ h s (Ioo_subset_Icc_self hs) hst x hx⟩

end Boussinesq.HalfPlane
