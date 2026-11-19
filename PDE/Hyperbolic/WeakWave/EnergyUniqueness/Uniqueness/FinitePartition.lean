/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Uniqueness.ShortInterval

/-!
# Finite-partition weak-wave uniqueness

The restart of the short-interval argument across the whole time interval. Evans, §7.2.2
proves uniqueness of weak solutions of second-order hyperbolic equations by showing that a
zero-data homogeneous solution vanishes on a short interval `[0, T₁]` and repeating the
argument. Here a finite partition
`a = τ 0 < τ 1 < … < τ N = b` whose cells satisfy the shortness condition
`(2 (L_A + L_R) / κ)(τ (n+1) - τ n) < 1` is constructed, and induction on `n` carries the zero
traces of the continuous displacement and Riesz velocity from `τ n` to `τ (n+1)`.

## Main results

* `exists_uniform_finite_short_partition`: for `α ≥ 0` there is an arithmetic mesh of `N`
  cells on `[a, b]` with `α (τ (n+1) - τ n) < 1` on every cell, together with the covering
  property used by the induction. This is an Archimedean choice `N > 1 + α (b - a)`, kept
  separate from the global theorem.
* `continuousDisplacement_eq_zero_of_finite_short_partition`: given any ordered finite partition
  whose cells are short, the continuous displacement of a zero-data homogeneous weak wave
  vanishes on all of `[a, b]`. The velocity trace at each new base point is recovered from the
  vanishing displacement by `continuousRieszVelocity_eq_zero_at_of_displacement_eq_zero`.

## Implementation notes

The partition is an argument rather than a uniform mesh built inside the proof, so the
theorem also applies to nonuniform partitions refined only where the coefficient bounds
require it.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, step 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}

/--
Every finite interval admits a uniform finite partition whose cells satisfy
the short-time condition in Evans's backward-energy argument.

For a nonnegative coefficient `α`, choose `N > 1 + α (b-a)` and use the
arithmetic mesh

`τ n = a + n (b-a)/N`.

Then `α (τ (n+1)-τ n) < 1` on every cell.  The final clause records the
covering property needed by the restart induction.  Keeping this elementary
Archimedean step explicit prevents the global uniqueness theorem from
assuming the finite restart that it is meant to prove.
-/
theorem exists_uniform_finite_short_partition
    {a b α : ℝ} (hab : a < b) (hα : 0 ≤ α) :
    ∃ (N : ℕ) (τ : ℕ → ℝ), τ 0 = a ∧ τ N = b ∧ (∀ n ≤ N, τ n ∈ Set.Icc a b) ∧
      (∀ n < N, τ n < τ (n + 1)) ∧
      (∀ t ∈ Set.Icc a b, ∃ n < N, t ∈ Set.Icc (τ n) (τ (n + 1))) ∧
      ∀ n < N, α * (τ (n + 1) - τ n) < 1 := by
  have hlength : 0 < b - a := sub_pos.mpr hab
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (1 + α * (b - a))
  have hNreal : 0 < (N : ℝ) := (add_nonneg zero_le_one (mul_nonneg hα hlength.le)).trans_lt hNlarge
  have hN : 0 < N := by exact_mod_cast hNreal
  have hd : 0 < (b - a) / N := div_pos hlength hNreal
  have hNd : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
  refine ⟨N, fun n ↦ a + n * ((b - a) / N), by simp, by simp [hNd], fun n hn ↦ ⟨?_, ?_⟩,
    fun n _ ↦ add_lt_add_right (mul_lt_mul_of_pos_right (Nat.cast_lt.2 n.lt_succ_self) hd) a,
    fun t ht ↦ ?_, fun n _ ↦ ?_⟩
  · have : 0 ≤ (n : ℝ) * ((b - a) / N) := by positivity
    linarith
  · have := mul_le_mul_of_nonneg_right (show (n : ℝ) ≤ N by exact_mod_cast hn) hd.le
    linarith
  · rcases ht.2.lt_or_eq with htb | rfl
    · have hx : 0 ≤ (t - a) / ((b - a) / N) := div_nonneg (by linarith [ht.1]) hd.le
      refine ⟨⌊(t - a) / ((b - a) / N)⌋₊,
        by exact_mod_cast (Nat.floor_le hx).trans_lt ((div_lt_iff₀ hd).2
          (show t - a < (N : ℝ) * ((b - a) / N) by linarith)), ?_, ?_⟩
      · linarith [(le_div_iff₀ hd).1 (Nat.floor_le hx)]
      · push_cast
        linarith [(div_lt_iff₀ hd).1 (Nat.lt_floor_add_one ((t - a) / ((b - a) / N)))]
    · refine ⟨N - 1, by omega, ?_, ?_⟩
      · have := mul_le_mul_of_nonneg_right
          (show ((N - 1 : ℕ) : ℝ) ≤ N by exact_mod_cast Nat.sub_le N 1) hd.le
        linarith
      · rw [Nat.sub_add_cancel hN]
        linarith
  · rw [show a + ((n + 1 : ℕ) : ℝ) * ((b - a) / N) - (a + n * ((b - a) / N)) = (b - a) / N by
      push_cast; ring, ← mul_div_assoc, div_lt_one hNreal]
    exact (lt_one_add _).trans hNlarge

/--
Finite restart of the short-interval Evans uniqueness argument.

The points `τ 0, …, τ N` form an ordered finite partition of `[a,b]`.
Each adjacent interval is short enough for estimate (40), and `hcover`
records that these intervals cover the full time domain.  Induction carries
both zero traces from one partition point to the next; the velocity trace is
recovered from the vanishing displacement by weak derivative uniqueness.

The partition is explicit so this theorem is useful beyond uniform meshes:
applications may refine only where coefficient bounds require it.
-/
theorem continuousDisplacement_eq_zero_of_finite_short_partition [CompleteSpace V]
    {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (Edisplacement : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    (Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
      (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b)
    (hdisplacementInitial : Edisplacement.representative a = 0)
    (hvelocityInitial : Evelocity.representative a = 0) (N : ℕ) (τ : ℕ → ℝ) (hτzero : τ 0 = a)
    (hτmem : ∀ n ≤ N, τ n ∈ Set.Icc a b) (hτstep : ∀ n < N, τ n < τ (n + 1))
    (hcover : ∀ t ∈ Set.Icc a b, ∃ n < N, t ∈ Set.Icc (τ n) (τ (n + 1)))
    (hBsplit : ∀ t ∈ Set.Icc a b, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.Icc a b, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable
      (fun t ↦ Adot t (backwardTimePrimitive (fun r ↦ u r) σ t)
      (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hAIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b →
      IntervalIntegrable (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (hRIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b →
      IntervalIntegrable (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ)
    (κ LA LR : ℝ) (hκ : 0 < κ) (hLA : 0 ≤ LA) (hLR : 0 ≤ LR)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ x : V, κ * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.Icc a b, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.Icc a b, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖)
    (hshort : ∀ n < N, (2 * (LA + LR) / κ) * (τ (n + 1) - τ n) < 1) :
    ∀ t ∈ Set.Icc a b, Edisplacement.representative t = 0 := by
  have hlocal (n : ℕ) (hn : n < N) (hdisplacementN : Edisplacement.representative (τ n) = 0)
      (hvelocityN : Evelocity.representative (τ n) = 0) : ∀ t ∈ Set.Icc (τ n) (τ (n + 1)),
        Edisplacement.representative t = 0 ∧ (∫ r in τ n..t, u r) = 0 := by
    have hleft := hτmem n hn.le
    have hright := hτmem (n + 1) hn
    have hsub (t : ℝ) (ht : t ∈ Icc (τ n) (τ (n + 1))) : t ∈ Icc a b :=
      ⟨hleft.1.trans ht.1, ht.2.trans hright.2⟩
    have hmono {f : ℝ → ℝ} {σ : ℝ} (hσ : σ ∈ Icc (τ n) (τ (n + 1)))
        (hf : IntervalIntegrable f volume a σ) : IntervalIntegrable f volume (τ n) σ :=
      hf.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc ⟨hleft.1, hσ.1⟩) right_mem_uIcc)
    exact h.continuousDisplacement_eq_zero_of_short_subinterval hab Edisplacement Evelocity hleft
      hright (hτstep n hn).le hdisplacementN hvelocityN (fun t ht ↦ hBsplit t (hsub t ht))
      (hAAC.mono (uIcc_subset_uIcc (Icc_subset_uIcc hleft) (Icc_subset_uIcc hright)))
      (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc hleft.1 hright.2) hAderiv)
      (fun t ht ↦ hAsymm t (hsub t ht)) (fun hσ ↦ hmono hσ (hAdotIntegrable (hsub _ hσ)))
      (fun hσ ↦ hmono hσ (hAIntegrable (hsub _ hσ)))
      (fun hσ ↦ hmono hσ (hRIntegrable (hsub _ hσ))) κ LA LR hκ hLA hLR
      (fun t ht ↦ hcoercive t (hsub t ht)) (fun t ht ↦ hAdotBound t (hsub t ht))
      (fun t ht ↦ hRBound t (hsub t ht)) (hshort n hn)
  have hsegments : ∀ n < N, ∀ t ∈ Set.Icc (τ n) (τ (n + 1)),
      Edisplacement.representative t = 0 ∧ (∫ r in τ n..t, u r) = 0 := by
    intro n
    induction n with
    | zero => exact fun hn ↦ hlocal 0 hn (by rwa [hτzero]) (by rwa [hτzero])
    | succ n ih =>
      intro hnSucc
      have hn : n < N := by omega
      have hprevious := ih hn
      exact hlocal (n + 1) hnSucc (hprevious _ (right_mem_Icc.mpr (hτstep n hn).le)).1
        (continuousRieszVelocity_eq_zero_at_of_displacement_eq_zero hab (hτmem n hn.le)
          (hτstep n hn) (hτmem (n + 1) hn) Edisplacement Evelocity fun t ht ↦ (hprevious t ht).1)
  intro t ht
  obtain ⟨n, hn, htn⟩ := hcover t ht
  exact (hsegments n hn t htn).1

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
