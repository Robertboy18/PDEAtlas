/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.LevelK
public import PDE.Fluid.HalfPlaneSystem.LocalExistence
import PDE.Fluid.HalfPlaneSystem.CarriedHigher
import PDE.Fluid.Boussinesq.HalfPlane.IterationHigher
import PDE.Fluid.Boussinesq.HalfPlane.IterationBounds

/-!
# Local existence at level `k` for half-plane systems

The local existence theorem gives a solution in the class `ω ∈ C^{1,α}`, `θ ∈ C^{2,α}` on a time
interval that depends on the size of the data in this class. This module shows that data with
`k ≥ 2` derivatives and a Hölder condition, `ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}`, give a solution with
them on the same interval, without shrinking the time.

Let `U` be a velocity law up to the radius `R₀` with the constants `C` and `κ` a forcing coefficient
with the bounds `Bκ`. The Picard iterates `ωⁿ` of the local existence proof, started at the extended
vorticity datum, keep the regularity of the data on the interval `[-T, T]` of the local theorem. The
bounds are proved by induction on the order `j ≤ k`. At order `j + 1 ≥ 2` the bounds of the iterates
of order at most `j` are uniform, the constants of `carriedVorticity_holderBounds` depend only on
them, and the top-order bound `Pₙ(|t|)` of `ωⁿ` obeys `Pₙ₊₁(r) ≤ A + C' ∫₀ʳ Pₙ`. The majorant
`P(r) = M exp (C' r)` with `M ≥ A` and `M` above the data bound satisfies `A + C' ∫₀ʳ P ≤ P(r)`, so
it bounds every iterate (`exists_isCkVorticityHistory`); no further restriction of the time is
needed. The resulting bound of the slices is not explicit.

Uniform `C^{k,α}` bounds pass to uniform limits
(`IncompressibleFlow.IsCkVorticityHistory.of_tendsto`), so the limit of the iterates is a `C^{k,α}`
history. Its carried temperature is `C^{k+1,α}` by `carriedTemperature_holderBounds`, and the
solution of the local theorem is a regular solution of order `k` on the same interval. The library
also proves the theorem for the Biot-Savart law directly
(`Boussinesq.HalfPlane.exists_isRegularSolutionOfOn_Ioo`).

## Main results

* `exists_isCkVorticityHistory_succ`: if all iterates are `C^{j,α}` histories with one bound,
  `j ≥ 1`, and the data are of order `j + 1`, all iterates are `C^{j+1,α}` histories with one bound.
* `exists_isCkVorticityHistory`: uniform `C^{k,α}` bounds of the iterates, when they are `C^{1,α}`
  histories with one set of bounds.
* `IsOsgoodIteration.isCkVorticityHistory_picardLimit`: the limit of the iterates of a map of Osgood
  type keeps uniform `C^{k,α}` bounds.
* `isRegularSolutionOfOn_of_iterationTime`: for every time `T` of the local theorem, the solution on
  `(-T, T)` is a regular solution of order `k ≥ 2`, with slices that are data of order `k` with
  support radius `(R + R₀) / 2` and one bound.
* `exists_isRegularSolutionOfOn_Ioo`: local existence of regular solutions of order `k ≥ 2`: there
  is `T > 0`, depending only on `α`, `R`, `N`, `R₀`, `C` and `Bκ`, that serves all data of the class
  `IsHolderData … α R N` which are moreover data of order `k`.

`Persistence.lean` uses `exists_isRegularSolutionOfOn_Ioo` to propagate the regularity of order `k`
along a regular solution. The order `k = 1` is `exists_isSolutionOn_Ioo` of `LocalExistence.lean`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

open Boussinesq.HalfPlane (mul_integral_exp add_mul_integral_exp_le add_mul_le_abs_add_abs_mul)
namespace HalfPlaneSystem

set_option linter.missingDocs true

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R T : ℝ}

variable {ω : ℕ → ℝ → ℝ^2 → ℝ}

/-- **One more derivative for all iterates.** Let `ωⁿ` be the iterates of the map
`carriedHistory U κ ω₀ θ₀ (-T) T` started at the extended vorticity datum, for data of order
`j + 1 ≥ 2`. If all of them are `C^{j,α}` histories on `[-T, T]` with one support radius
`R₁ ≤ R₀` and one bound, then all of them are `C^{j+1,α}` histories with one bound. This is the
step of the induction on the order. Proof: the top-order bound of the carried vorticity is
affine in the time integral of the top-order majorant of the history, with constants that
depend only on the bounds of order `j`; the majorant `M exp (C' r)` reproduces itself under
this affine map, so it bounds every iterate. -/
theorem exists_isCkVorticityHistory_succ (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {j : ℕ} {R₁ Nd Nlow : ℝ} (hj : 1 ≤ j)
    (hd : IsHolderDataOf (j + 1) ω₀ θ₀ α R Nd) (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (hR₁ : R₁ ≤ R₀) (h0 : ω 0 = fun _ ↦ dataVorticity ω₀)
    (hs : ∀ n, ω (n + 1) = carriedHistory U κ ω₀ θ₀ (-T) T (ω n))
    (hlow : ∀ n, IsCkVorticityHistory j (ω n) (-T) T α R₁ Nlow) :
    ∃ B, ∀ n, IsCkVorticityHistory (j + 1) (ω n) (-T) T α R₁ B := by
  have hk : 2 ≤ j + 1 := by omega
  set c := lawConst C (j + 1) α * Nlow
  set c' := lawConst C (j + 1) α
  obtain ⟨M, C', hNdM, hc₁, hs₁, hc₂, hs₂⟩ : ∃ M C' : ℝ, Nd ≤ M ∧
      |vorticityTopConst Bκ (j + 1) c Nd T| ≤ M ∧
      |vorticityTopSlope Bκ (j + 1) c c' Nd T| ≤ C' ∧
      |vorticityTopHolderConst Bκ (j + 1) α c Nd T| ≤ M ∧
      |vorticityTopHolderSlope Bκ (j + 1) α c c' Nd T| ≤ C' :=
    ⟨Nd + |vorticityTopConst Bκ (j + 1) c Nd T| + |vorticityTopHolderConst Bκ (j + 1) α c Nd T|,
      |vorticityTopSlope Bκ (j + 1) c c' Nd T| +
        |vorticityTopHolderSlope Bκ (j + 1) α c c' Nd T|,
      by linarith [abs_nonneg (vorticityTopConst Bκ (j + 1) c Nd T),
        abs_nonneg (vorticityTopHolderConst Bκ (j + 1) α c Nd T)],
      by linarith [hd.nonneg, abs_nonneg (vorticityTopHolderConst Bκ (j + 1) α c Nd T)],
      by linarith [abs_nonneg (vorticityTopHolderSlope Bκ (j + 1) α c c' Nd T)],
      by linarith [hd.nonneg, abs_nonneg (vorticityTopConst Bκ (j + 1) c Nd T)],
      by linarith [abs_nonneg (vorticityTopSlope Bκ (j + 1) c c' Nd T)]⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans hc₁
  have hC : 0 ≤ C' := (abs_nonneg _).trans hs₁
  obtain ⟨B, hB₀, hB₁⟩ : ∃ B, Nd ≤ B ∧
      carriedBound Bκ (j + 1) α c c' Nd T (∫ r in (0)..T, M * Real.exp (C' * r)) ≤ B :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hPM {t : ℝ} : Nd ≤ M * Real.exp (C' * |t|) :=
    hNdM.trans (le_mul_of_one_le_right hM (Real.one_le_exp (mul_nonneg hC (abs_nonneg t))))
  have hiter : ∀ n, IsTopBoundedHistory (j + 1) (ω n) T α R₁ B Nlow
      (fun r ↦ M * Real.exp (C' * r)) := by
    intro n
    induction n with
    | zero =>
      have hl := hlow 0
      rw [h0] at hl ⊢
      have hdat := isCkVorticityHistory_dataVorticity hd (-T) T
      exact
        { history := (hdat.of_le hB₀).of_eq_zero hl.eq_zero
          low := hl
          continuousOn := (by fun_prop : Continuous fun r ↦ M * Real.exp (C' * r)).continuousOn
          nonneg := fun r _ ↦ by positivity
          norm_le := fun t ht y hy ↦ (hdat.norm_le t ht (j + 1) le_rfl y hy).trans hPM
          holder := fun t ht y z hy hz ↦ (hdat.holder t ht y z hy hz).trans
            (mul_le_mul_of_nonneg_right hPM (Real.rpow_nonneg (norm_nonneg _) α)) }
    | succ n ih =>
      have hl := hlow (n + 1)
      rw [hs n] at hl ⊢
      have hc := isCkVorticityHistory_carriedHistory hU hκ ih hd hR₁ hk hα hα1 hT
      exact
        { history := (hc.of_le hB₁).of_eq_zero hl.eq_zero
          low := hl
          continuousOn := (by fun_prop : Continuous fun r ↦ M * Real.exp (C' * r)).continuousOn
          nonneg := fun r _ ↦ by positivity
          norm_le := fun t ht y hy ↦
            ((carriedVorticity_holderBounds hU hκ ih hd hR₁ hk hα hα1 hT ht).norm_top_le y
              hy).trans (add_mul_integral_exp_le hc₁ hs₁ (abs_nonneg t))
          holder := fun t ht y z hy hz ↦
            ((carriedVorticity_holderBounds hU hκ ih hd hR₁ hk hα hα1 hT ht).holder_top y z hy
              hz).trans (mul_le_mul_of_nonneg_right
                (add_mul_integral_exp_le hc₂ hs₂ (abs_nonneg t))
                (Real.rpow_nonneg (norm_nonneg _) α)) }
  exact ⟨B, fun n ↦ (hiter n).history⟩

/-- **Uniform `C^{k,α}` bounds of the iterates.** Let `ωⁿ` be the iterates of the map
`carriedHistory U κ ω₀ θ₀ (-T) T` started at the extended vorticity datum, for data of order `k`.
If all of them are `C^{1,α}` histories on `[-T, T]` with one support radius `R₁ ≤ R₀` and one set
of bounds, as for the time of the local theorem, then all of them are `C^{k,α}` histories with
one bound. -/
theorem exists_isCkVorticityHistory (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    {k : ℕ} {R₁ Nk B₀ M₀ B₁ M₁ : ℝ} (hd : IsHolderDataOf k ω₀ θ₀ α R Nk) (hα : 0 < α)
    (hα1 : α < 1) (hT : 0 ≤ T) (hR₁ : R₁ ≤ R₀) (h0 : ω 0 = fun _ ↦ dataVorticity ω₀)
    (hs : ∀ n, ω (n + 1) = carriedHistory U κ ω₀ θ₀ (-T) T (ω n))
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
      exact exists_isCkVorticityHistory_succ hU hκ hj0 (hd.mono hα.le hα1.le hj) hα hα1 hT hR₁
        h0 hs hlow

/-- **The limit of the iteration keeps uniform `C^{k,α}` bounds.** If all Picard iterates of a
map of Osgood type are `C^{k,α}` histories on `[-T, T]` with one support radius and one bound, so
is their limit. -/
theorem IsOsgoodIteration.isCkVorticityHistory_picardLimit
    {Φ : (ℝ → ℝ^2 → ℝ) → ℝ → ℝ^2 → ℝ} {ω : ℝ → ℝ^2 → ℝ} {R₁ B M B₁ M₁ c A : ℝ}
    (hP : IsOsgoodIteration Φ ω T α R₁ B M B₁ M₁ c A) (hα1 : α ≤ 1) {k : ℕ} {R' B' : ℝ}
    (hk : ∀ n, IsCkVorticityHistory k (picardIterate Φ ω n) (-T) T α R' B') :
    IsCkVorticityHistory k (picardLimit Φ ω) (-T) T α R' B' :=
  IsCkVorticityHistory.of_tendsto hP.pos hα1 hk hP.picardIterate_cauchy
    fun _ ht _ hy ↦ hP.tendsto_picardLimit ht hy

/-- **Local existence at level `k` on the interval of the local theorem.** Let `k ≥ 2`,
`0 < α < 1`, `R < R₀`, `R' = (R + R₀) / 2`, and let `T > 0` satisfy the four conditions of
`exists_iterationTime` with the margin `R' - R`, which depend only on `α`, `N`, `R' - R`, `C` and
`Bκ`. Data of the class `IsHolderData ω₀ θ₀ α R N` that are moreover data of order `k` have a
regular solution of order `k` on `(-T, T)` with these data at time zero, whose time slices are
data of the class with support radius `R'` and bound `iterationOutputBound C α N T`, and data of
order `k` with support radius `R'` and one bound. So higher regularity of the data costs no
time of existence. Proof: the iterates of the local theorem have uniform `C^{k,α}` bounds, which
pass to their limit; the limit is a fixed point of the iteration map, so it is the vorticity of
the solution, and its carried temperature has `C^{k+1,α}` bounds. -/
theorem isRegularSolutionOfOn_of_iterationTime (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {k : ℕ} {N Nk : ℝ} (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) (hR : R < R₀) (hT : 0 < T)
    (h₁ : N + T * weightedForcingBound Bκ N (iterationVariationBound C α N T) ≤ 2 * N + 1)
    (h₂ : iterationGradientBound C Bκ α N T ≤ 2 * N + 1)
    (h₃ : iterationHolderBound C Bκ α N T ≤ 2 * N + 1)
    (h₄ : iterationVelocityBound C N * T ≤ (R + R₀) / 2 - R)
    (hd : IsHolderData ω₀ θ₀ α R N) (hdk : IsHolderDataOf k ω₀ θ₀ α R Nk) :
    ∃ sol : Fields, IsRegularSolutionOfOn U κ R₀ k sol (Ioo (-T) T) α ∧
      HasDataAt sol 0 ω₀ θ₀ ∧
      (∀ t ∈ Ioo (-T) T, IsHolderData (fun x ↦ sol.vorticity x t)
        (fun x ↦ sol.temperature x t) α ((R + R₀) / 2) (iterationOutputBound C α N T)) ∧
      ∃ N' : ℝ, ∀ t ∈ Ioo (-T) T, IsHolderDataOf k (fun x ↦ sol.vorticity x t)
        (fun x ↦ sol.temperature x t) α ((R + R₀) / 2) N' := by
  set R' := (R + R₀) / 2
  have hRR' : R < R' := by simp only [R']; linarith
  have hR'R₀ : R' < R₀ := by simp only [R']; linarith
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  -- The iteration of the local theorem and its limit `ωl`, a fixed point in the class of the
  -- iteration.
  have hP := isOsgoodIteration_carriedHistory (U := U) (κ := κ) hU hκ hd hα hα1 hRR'.le
    hR'R₀.le hT h₁ h₂ h₃ h₄
  set Φ := carriedHistory U κ ω₀ θ₀ (-T) T
  set ωl := picardLimit Φ (fun _ ↦ dataVorticity ω₀)
  have hl : IsIterationClass T α R' N ωl := hP.isC1VorticityHistory_picardLimit
  have hinv : IsIterationClass T α R' N (carriedHistory U κ ω₀ θ₀ (-T) T ωl) :=
    isIterationClass_carriedHistory hU hκ hd hα hα1 hR'R₀.le hT h₁ h₂ h₃ h₄ hl
  have hfix : ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 →
      ωl t x = carriedVorticity κ ω₀ θ₀ (lawField U ωl) (lawFieldDeriv U ωl) (-T) T x t :=
    fun t ht x hx ↦ hP.picardLimit_eq ht hx
  -- All iterates are `C^{k,α}` histories with one bound, hence so is the limit.
  obtain ⟨B, hB⟩ := exists_isCkVorticityHistory (ω := picardIterate Φ (fun _ ↦ dataVorticity ω₀))
    hU hκ hdk hα hα1 hT.le hR'R₀.le rfl (picardIterate_succ Φ _) hP.iterate_mem
  have hkl : IsCkVorticityHistory k ωl (-T) T α R' B :=
    hP.isCkVorticityHistory_picardLimit hα1.le hB
  have hB0 : 0 ≤ B := hkl.nonneg h0
  -- The limit has the constant top-order majorant `B`.
  have htop : IsTopBoundedHistory k ωl T α R' B (2 * B) (fun _ ↦ B) :=
    { history := hkl
      low := hkl.mono hα.le hα1.le (Nat.sub_le k 1)
      continuousOn := continuousOn_const
      nonneg := fun _ _ ↦ hB0
      norm_le := fun t ht y hy ↦ hkl.norm_le t ht k le_rfl y hy
      holder := fun t ht y z hy hz ↦ hkl.holder t ht y z hy hz }
  set c := lawConst C k α * (2 * B)
  set c' := lawConst C k α
  obtain ⟨N', hN₁, hN₂, hN₃, hN₄, hN₅⟩ : ∃ N' : ℝ, B ≤ N' ∧ Nk ≤ N' ∧
      temperatureBound k c Nk T ≤ N' ∧
      |temperatureTopConst k c Nk T| + |temperatureTopSlope k c c' Nk T| * (T * B) ≤ N' ∧
      |temperatureTopHolderConst k α c Nk T| +
        |temperatureTopHolderSlope k α c c' Nk T| * (T * B) ≤ N' :=
    ⟨max B (max Nk (max _ (max _ _))), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _),
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)⟩
  -- At every time the limit and its carried temperature are data of order `k` with one bound.
  have hωθ {t : ℝ} (ht : t ∈ Icc (-T) T) : IsHolderDataOf k (ωl t)
      (fun x ↦ carriedTemperature θ₀ (lawField U ωl) (-T) T x t) α R' N' := by
    have hθb := carriedTemperature_holderBounds hU htop hdk hR'R₀.le hk hα hα1 ht
    have h1 := isHolderData_carried hU hd hα hα1 hR'R₀.le hT h₄ hl hinv ht
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
      exact (abs_carriedTemperature_le hU htop hdk hR'R₀.le (by omega) hα hα1 ht hx).trans hN₂
    rcases hj.lt_or_eq with hjk | rfl
    · exact (hθb.norm_le j hj0 hjk x hx).trans hN₃
    · exact (hθb.norm_top_le x hx).trans ((add_mul_le_abs_add_abs_mul hΦ hΦ').trans hN₄)
  have hV : iterationVelocityBound C N * T ≤ R' - R := h₄
  have hsupp : R + C 0 0 * (2 * N + 1) * max (-(-T)) T < R₀ := by
    rw [neg_neg, max_self]
    unfold iterationVelocityBound at hV
    linarith
  -- The fixed point gives a solution, whose slices on the closed half-plane are those of the
  -- limit and of its carried temperature.
  obtain ⟨hsol, hdat⟩ := isSolutionOn_of_fixedPoint hU hκ hα hα1 hd (by linarith) hT hl
    hR'R₀.le hsupp hfix
  have hslice {t : ℝ} (ht : t ∈ Icc (-T) T) :
      IsHolderDataOf k (fun x ↦ (assembled U κ ω₀ θ₀ ωl (-T) T).vorticity x t)
        (fun x ↦ (assembled U κ ω₀ θ₀ ωl (-T) T).temperature x t) α R' N' :=
    (hωθ ht).congr (fun x hx ↦ (hfix t ht x hx).symm) fun _ _ ↦ rfl
  refine ⟨assembled U κ ω₀ θ₀ ωl (-T) T,
    { toIsSolutionOn := hsol
      holderData := fun a b hab ↦ ⟨R', hR'R₀, N', fun t ht ↦ hslice (Ioo_subset_Icc_self
        (hab ht))⟩
      vorticity_uniform := fun j hj t ht ε hε ↦ ?_
      temperature_uniform := fun j hj t ht ε hε ↦ ?_ }, hdat,
    fun t ht ↦ isHolderData_carried hU hd hα hα1 hR'R₀.le hT h₄ hl hinv
      (Ioo_subset_Icc_self ht),
    N', fun t ht ↦ hslice (Ioo_subset_Icc_self ht)⟩
  · have hEq {s : ℝ} (hs : s ∈ Icc (-T) T) :
        EqOn (fun y ↦ (assembled U κ ω₀ θ₀ ωl (-T) T).vorticity y s) (ωl s) H̄ :=
      fun y hy ↦ (hfix s hs y hy).symm
    obtain ⟨δ, hδ, h⟩ := hkl.uniform j hj t (Ioo_subset_Icc_self ht) ε hε
    refine ⟨δ, hδ, fun s hs hst x hx ↦ ?_⟩
    rw [iteratedFDerivWithin_congr (hEq (Ioo_subset_Icc_self hs)) hx,
      iteratedFDerivWithin_congr (hEq (Ioo_subset_Icc_self ht)) hx]
    exact h s (Ioo_subset_Icc_self hs) hst x hx
  · obtain ⟨δ, hδ, h⟩ := uniform_carriedTemperature hU htop hdk hR'R₀.le hk hα hα1 hT.le j hj t
      (Ioo_subset_Icc_self ht) ε hε
    exact ⟨δ, hδ, fun s hs hst x hx ↦ h s (Ioo_subset_Icc_self hs) hst x hx⟩

/-- **Local existence at level `k`.** For a velocity law `U` up to the radius `R₀`, a forcing
coefficient `κ`, `k ≥ 2`, `0 < α < 1`, `R < R₀` and `N ≥ 0` there is a time `T > 0`, depending
only on `α`, `R`, `N`, `R₀`, `C` and `Bκ` (the time of the local theorem
`exists_isSolutionOn_Ioo`), such that all data of the class `IsHolderData ω₀ θ₀ α R N` that are
moreover data of order `k` have a regular solution of order `k` on `(-T, T)` with these data at
time zero. Its time slices are data of the class with support radius `(R + R₀) / 2` and bound
`iterationOutputBound C α N T`, and data of order `k` with support radius `(R + R₀) / 2` and one
bound. -/
theorem exists_isRegularSolutionOfOn_Ioo (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {k : ℕ} {N : ℝ} (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1)
    (hR : R < R₀) (hN : 0 ≤ N) :
    ∃ T > 0, ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N → ∀ Nk : ℝ,
      IsHolderDataOf k ω₀ θ₀ α R Nk →
      ∃ sol : Fields, IsRegularSolutionOfOn U κ R₀ k sol (Ioo (-T) T) α ∧
        HasDataAt sol 0 ω₀ θ₀ ∧
        (∀ t ∈ Ioo (-T) T, IsHolderData (fun x ↦ sol.vorticity x t)
          (fun x ↦ sol.temperature x t) α ((R + R₀) / 2) (iterationOutputBound C α N T)) ∧
        ∃ N' : ℝ, ∀ t ∈ Ioo (-T) T, IsHolderDataOf k (fun x ↦ sol.vorticity x t)
          (fun x ↦ sol.temperature x t) α ((R + R₀) / 2) N' := by
  obtain ⟨T, hT, h₁, h₂, h₃, h₄⟩ :=
    exists_iterationTime (d := (R + R₀) / 2 - R) C Bκ hα hN (by linarith)
  exact ⟨T, hT, fun ω₀ θ₀ hd Nk hdk ↦ isRegularSolutionOfOn_of_iterationTime hU hκ hk hα hα1 hR
    hT h₁ h₂ h₃ h₄ hd hdk⟩

end HalfPlaneSystem
