/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Canonical
public import PDE.Fluid.HalfPlaneSystem.LocalExistence
public import PDE.Fluid.HalfPlaneSystem.Uniqueness
public import PDE.Fluid.Boussinesq.HalfPlane.Maximal

/-!
# The maximal solution of a half-plane system

Local existence gives a solution for a short time. This module builds one solution on a maximal
interval of times that contains every other solution with the same data, and proves the blow-up
alternative when this interval is finite. It needs uniqueness, a way to glue local solutions, and a
local existence time that depends only on the size of the data.

For a velocity law `U` up to the radius `R₀`, a forcing coefficient `κ`, `0 < α < 1` and data
`ω₀ ∈ C^{1,α}`, `θ₀ ∈ C^{2,α}` of the class `IsHolderData … α R N` with support radius `R < R₀`,
`maximalTime U κ R₀ α ω₀ θ₀` is the supremum of the life spans `T` of the regular solutions on
`lifeSpan T = [0, T)` with these data. It is positive (local existence), and no estimate from below
beyond positivity is given. It is attained (`exists_maximal`): the canonical representatives of the
solutions of shorter life spans agree on their common times by uniqueness and glue to a regular
solution on `[0, maximalTime)`, and every solution with these data agrees with it on the closed
half-plane.

If the maximal time is finite, then for no radius `R' < R₀` and no bound `N'` are all slices on
`[0, maximalTime)` data of the class `IsHolderData α R' N'` (`not_forall_isHolderData`): the norms
are unbounded or the supports leave every disc of radius less than `R₀`. Otherwise local existence
from a time close to the end, whose life span depends only on the radius and the bound, would extend
the solution (`IsRegularSolutionOn.exists_extension`). The library has the same construction for the
Boussinesq system (`Boussinesq.HalfPlane.exists_maximal`).

## Main results

* `maximalTime U κ R₀ α ω₀ θ₀`: the maximal time of existence, an extended nonnegative number;
  `maximalTime_pos`, `le_maximalTime`: it is positive, and every regular solution with the data
  lives at most until it.
* `exists_maximal`: the data have a regular solution on `[0, maximalTime)`, built by gluing.
* `IsSolutionOn.eq_of_hasDataAt_lifeSpan`, `IsRegularSolutionOn.eq_of_hasDataAt`: two solutions on
  life spans with the same data agree on the closed half-plane at every common time.
* `not_forall_isHolderData`: the blow-up alternative for a finite maximal time.
* `AgreeAt`, `IsSolutionOn.of_local`, `IsRegularSolutionOn.of_local`, `IsRegularSolutionOn.glue`:
  two fields agree at a time on the whole plane; being a solution is local in time, and two regular
  solutions that overlap glue to one.
* `exists_isRegularSolutionOn_Ioo`: local existence of regular solutions, with a time that depends
  only on the radius and the bound of the data.
* `IsRegularSolutionOn.exists_extension`: a regular solution on `[0, T)` whose slice at a time `t₁`
  is in a class of data with local existence time `τ > T - t₁` extends to `[0, t₁ + τ)`.
* `IsRegularSolutionOn.mono`, `IsRegularSolutionOn.shiftTime`: restriction to fewer times and shifts
  of the time.

`Continuation.lean` turns the blow-up alternative into the continuation criterion with the gradient
of the velocity, and `PersistenceMaximal.lean` adds the propagation of regularity and states the
theorem on maximal solutions `exists_maximalSolutionOf`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ENNReal Topology
open Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
  {sol sol' : Fields} {I : Set ℝ} {α : ℝ}

/-! ### Restriction, time shifts and uniqueness of regular solutions -/

/-- Regular solutions restrict to smaller sets of times. -/
theorem IsRegularSolutionOn.mono (h : IsRegularSolutionOn U κ R₀ sol I α) {J : Set ℝ}
    (hJ : J ⊆ I) : IsRegularSolutionOn U κ R₀ sol J α :=
  ⟨h.toIsSolutionOn.mono hJ, fun a b hab ↦ h.holderData a b (hab.trans hJ)⟩

/-- Regular solutions are invariant under shifts of the time. -/
theorem IsRegularSolutionOn.shiftTime (h : IsRegularSolutionOn U κ R₀ sol I α) (t₀ : ℝ) :
    IsRegularSolutionOn U κ R₀ (sol.shiftTime t₀) ((· + t₀) ⁻¹' I) α where
  toIsSolutionOn := h.toIsSolutionOn.shiftTime t₀
  holderData a b hab := by
    have hsub : Icc (a + t₀) (b + t₀) ⊆ I := fun s hs ↦ by
      have := hab (show s - t₀ ∈ Icc a b from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      simpa using this
    obtain ⟨R, N, hRN⟩ := h.holderData (a + t₀) (b + t₀) hsub
    exact ⟨R, N, fun t ht ↦ hRN (t + t₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- **Uniqueness.** Two solutions on life spans with the same data agree on the closed
half-plane at every common time. -/
theorem IsSolutionOn.eq_of_hasDataAt_lifeSpan (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {T T' : ℝ≥0∞} {ω₀ θ₀ : ℝ^2 → ℝ}
    (h : IsSolutionOn U κ R₀ sol (lifeSpan T)) (h' : IsSolutionOn U κ R₀ sol' (lifeSpan T'))
    (hd : HasDataAt sol 0 ω₀ θ₀) (hd' : HasDataAt sol' 0 ω₀ θ₀) {t : ℝ}
    (ht : t ∈ lifeSpan (min T T')) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  refine (h.mono (lifeSpan_mono (min_le_left T T'))).eq_of_hasDataAt hU hκ
    (h'.mono (lifeSpan_mono (min_le_right T T'))) (ordConnected_lifeSpan _)
    (zero_mem_lifeSpan (pos_of_mem_lifeSpan ht)) (fun y hy ↦ ?_) ht ht.1 hx
  rw [(hd y hy).1, (hd y hy).2, (hd' y hy).1, (hd' y hy).2]
  exact ⟨rfl, rfl⟩

/-! ### Locality in time -/

/-- The fields of `sol` and `sol'` agree at the time `s` on the whole plane. -/
def AgreeAt (sol sol' : Fields) (s : ℝ) : Prop :=
  ∀ x : ℝ^2, sol.vorticity x s = sol'.vorticity x s ∧ sol.temperature x s = sol'.temperature x s

/-- **Solutions are local in time.** If near every time of `I` the fields agree with a solution
on the times of `I` near it, and the supports are bounded on compact subintervals, the fields are
a solution on `I`. -/
theorem IsSolutionOn.of_local
    (hloc : ∀ t ∈ I, ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ ∃ sol' : Fields,
      IsSolutionOn U κ R₀ sol' (I ∩ V) ∧ ∀ s ∈ V, AgreeAt sol sol' s)
    (hsupp : HasBoundedSupportOn R₀ sol I) : IsSolutionOn U κ R₀ sol I := by
  have hslice {sol' : Fields} {s : ℝ} (h : AgreeAt sol sol' s) :
      (fun y ↦ sol.vorticity y s) = (fun y ↦ sol'.vorticity y s) ∧
        (fun y ↦ sol.temperature y s) = (fun y ↦ sol'.temperature y s) :=
    ⟨funext fun y ↦ (h y).1, funext fun y ↦ (h y).2⟩
  have hcd (field : Fields → ℝ^2 → ℝ → ℝ)
      (hfield : ∀ {sol' : Fields} {s : ℝ}, AgreeAt sol sol' s →
        ∀ y, field sol y s = field sol' y s)
      (hreg : ∀ {sol' : Fields} {J : Set ℝ}, IsSolutionOn U κ R₀ sol' J →
        ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ field sol' xt.1 xt.2) (univ ×ˢ J)) :
      ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ field sol xt.1 xt.2) (univ ×ˢ I) := by
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨V, hV, htV, sol', h', heq⟩ := hloc p.2 hp.2
    refine ⟨univ ×ˢ V, isOpen_univ.prod hV, ⟨mem_univ _, htV⟩, ?_⟩
    rw [prod_inter_prod, inter_self]
    exact (hreg h').congr fun q hq ↦ hfield (heq q.2 hq.2.2) q.1
  have hdt (field : Fields → ℝ^2 → ℝ → ℝ)
      (hfield : ∀ {sol' : Fields} {s : ℝ}, AgreeAt sol sol' s →
        ∀ y, field sol y s = field sol' y s)
      (hreg : ∀ {sol' : Fields} {J : Set ℝ}, IsSolutionOn U κ R₀ sol' J →
        ∀ {x : ℝ^2} {t : ℝ}, t ∈ J → DifferentiableAt ℝ (fun s ↦ field sol' x s) t)
      {x : ℝ^2} {t : ℝ} (ht : t ∈ I) : DifferentiableAt ℝ (fun s ↦ field sol x s) t := by
    obtain ⟨V, hV, htV, sol', h', heq⟩ := hloc t ht
    refine (hreg h' (x := x) ⟨ht, htV⟩).congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds htV] with s hs
    exact hfield (heq s hs) x
  have hderiv (field : Fields → ℝ^2 → ℝ → ℝ)
      (hfield : ∀ {sol' : Fields} {s : ℝ}, AgreeAt sol sol' s →
        ∀ y, field sol y s = field sol' y s)
      {sol' : Fields} {V : Set ℝ} (hV : IsOpen V) {t : ℝ} (htV : t ∈ V)
      (heq : ∀ s ∈ V, AgreeAt sol sol' s) (x : ℝ^2) :
      deriv (fun s ↦ field sol x s) t = deriv (fun s ↦ field sol' x s) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hV.mem_nhds htV] with s hs
    exact hfield (heq s hs) x
  exact
    { vorticity_contDiffOn := hcd (fun f ↦ f.vorticity) (fun h y ↦ (h y).1)
        fun h' ↦ h'.vorticity_contDiffOn
      temperature_contDiffOn := hcd (fun f ↦ f.temperature) (fun h y ↦ (h y).2)
        fun h' ↦ h'.temperature_contDiffOn
      vorticity_differentiableAt_time := fun ht ↦
        hdt (fun f ↦ f.vorticity) (fun h y ↦ (h y).1)
          (fun h' _ _ ht' ↦ h'.vorticity_differentiableAt_time ht') ht
      temperature_differentiableAt_time := fun ht ↦
        hdt (fun f ↦ f.temperature) (fun h y ↦ (h y).2)
          (fun h' _ _ ht' ↦ h'.temperature_differentiableAt_time ht') ht
      vorticity_equation := fun {x t} hx ht ↦ by
        obtain ⟨V, hV, htV, sol', h', heq⟩ := hloc t ht
        have hs := hslice (heq t htV)
        rw [hderiv (fun f ↦ f.vorticity) (fun h y ↦ (h y).1) hV htV heq x, hs.1, hs.2]
        exact h'.vorticity_equation hx ⟨ht, htV⟩
      temperature_equation := fun {x t} hx ht ↦ by
        obtain ⟨V, hV, htV, sol', h', heq⟩ := hloc t ht
        have hs := hslice (heq t htV)
        rw [hderiv (fun f ↦ f.temperature) (fun h y ↦ (h y).2) hV htV heq x, hs.1, hs.2]
        exact h'.temperature_equation hx ⟨ht, htV⟩
      support := hsupp }

/-- Regular solutions are local in time. -/
theorem IsRegularSolutionOn.of_local
    (hloc : ∀ t ∈ I, ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ ∃ sol' : Fields,
      IsSolutionOn U κ R₀ sol' (I ∩ V) ∧ ∀ s ∈ V, AgreeAt sol sol' s)
    (hsupp : HasBoundedSupportOn R₀ sol I)
    (hholder : ∀ a b : ℝ, Icc a b ⊆ I → ∃ R N : ℝ, ∀ t ∈ Icc a b,
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N) :
    IsRegularSolutionOn U κ R₀ sol I α :=
  ⟨IsSolutionOn.of_local hloc hsupp, hholder⟩

/-- **Gluing two regular solutions.** Fields that agree with a regular solution `A` on the times
before `d` and with a regular solution `B` on the times after `c < d` are a regular solution. -/
theorem IsRegularSolutionOn.glue {c d : ℝ} (hcd : c < d) {A B : Fields}
    (hA : IsRegularSolutionOn U κ R₀ A (I ∩ Iio d) α)
    (hB : IsRegularSolutionOn U κ R₀ B (I ∩ Ioi c) α)
    (hsA : ∀ s < d, AgreeAt sol A s) (hsB : ∀ s > c, AgreeAt sol B s) :
    IsRegularSolutionOn U κ R₀ sol I α := by
  set m := (c + d) / 2
  have hm₁ : m < d := by simp only [m]; linarith
  have hm₂ : c < m := by simp only [m]; linarith
  have hJ₁ {a b : ℝ} (hab : Icc a b ⊆ I) : Icc a (min b m) ⊆ I ∩ Iio d := fun s hs ↦
    ⟨hab ⟨hs.1, hs.2.trans (min_le_left _ _)⟩, (hs.2.trans (min_le_right _ _)).trans_lt hm₁⟩
  have hJ₂ {a b : ℝ} (hab : Icc a b ⊆ I) : Icc (max a m) b ⊆ I ∩ Ioi c := fun s hs ↦
    ⟨hab ⟨(le_max_left _ _).trans hs.1, hs.2⟩, hm₂.trans_le ((le_max_right _ _).trans hs.1)⟩
  have hcases {a b t : ℝ} (ht : t ∈ Icc a b) :
      (t ∈ Icc a (min b m) ∧ t < d) ∨ (t ∈ Icc (max a m) b ∧ c < t) := by
    rcases le_or_gt t m with htm | htm
    · exact Or.inl ⟨⟨ht.1, le_min ht.2 htm⟩, htm.trans_lt hm₁⟩
    · exact Or.inr ⟨⟨max_le ht.1 htm.le, ht.2⟩, hm₂.trans htm⟩
  refine IsRegularSolutionOn.of_local (fun t ht ↦ ?_) (fun a b hab ↦ ?_) (fun a b hab ↦ ?_)
  · rcases lt_or_ge t d with htd | htd
    · exact ⟨Iio d, isOpen_Iio, htd, A, hA.toIsSolutionOn, hsA⟩
    · exact ⟨Ioi c, isOpen_Ioi, hcd.trans_le htd, B, hB.toIsSolutionOn, hsB⟩
  · obtain ⟨R₁, hR₁₀, hR₁⟩ := hA.support a (min b m) (hJ₁ hab)
    obtain ⟨R₂, hR₂₀, hR₂⟩ := hB.support (max a m) b (hJ₂ hab)
    refine ⟨max R₁ R₂, max_lt hR₁₀ hR₂₀, fun t ht x hx hxR ↦ ?_⟩
    rcases hcases ht with ⟨ht', htd⟩ | ⟨ht', htc⟩
    · rw [(hsA t htd x).1, (hsA t htd x).2]
      exact hR₁ t ht' x hx ((le_max_left _ _).trans_lt hxR)
    · rw [(hsB t htc x).1, (hsB t htc x).2]
      exact hR₂ t ht' x hx ((le_max_right _ _).trans_lt hxR)
  · obtain ⟨R₁, N₁, hR₁⟩ := hA.holderData a (min b m) (hJ₁ hab)
    obtain ⟨R₂, N₂, hR₂⟩ := hB.holderData (max a m) b (hJ₂ hab)
    refine ⟨max R₁ R₂, max N₁ N₂, fun t ht ↦ ?_⟩
    rcases hcases ht with ⟨ht', htd⟩ | ⟨ht', htc⟩
    · have h₁ : (fun x ↦ sol.vorticity x t) = (fun x ↦ A.vorticity x t) :=
        funext fun x ↦ (hsA t htd x).1
      have h₂ : (fun x ↦ sol.temperature x t) = (fun x ↦ A.temperature x t) :=
        funext fun x ↦ (hsA t htd x).2
      rw [h₁, h₂]
      exact (hR₁ t ht').mono (le_max_left _ _) (le_max_left _ _)
    · have h₁ : (fun x ↦ sol.vorticity x t) = (fun x ↦ B.vorticity x t) :=
        funext fun x ↦ (hsB t htc x).1
      have h₂ : (fun x ↦ sol.temperature x t) = (fun x ↦ B.temperature x t) :=
        funext fun x ↦ (hsB t htc x).2
      rw [h₁, h₂]
      exact (hR₂ t ht').mono (le_max_right _ _) (le_max_right _ _)

/-! ### Local existence and restart -/

/-- **Local existence of regular solutions.** For a radius `R < R₀` and a bound `N ≥ 0` there
is a time `τ > 0` such that all data of the class `IsHolderData α R N` have a regular solution
on `(-τ, τ)`. -/
theorem exists_isRegularSolutionOn_Ioo (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {R N : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : R < R₀)
    (hN : 0 ≤ N) :
    ∃ τ > 0, ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N →
      ∃ sol : Fields, IsRegularSolutionOn U κ R₀ sol (Ioo (-τ) τ) α ∧ HasDataAt sol 0 ω₀ θ₀ := by
  obtain ⟨τ, hτ, h⟩ := exists_isSolutionOn_Ioo hU hκ hα hα1 hR hN
  refine ⟨τ, hτ, fun ω₀ θ₀ hd ↦ ?_⟩
  obtain ⟨sol, hs, hd', hb⟩ := h ω₀ θ₀ hd
  exact ⟨sol, ⟨hs, fun a b hab ↦ ⟨_, _, fun t ht ↦ hb t (hab ht)⟩⟩, hd'⟩

/-- **Restart by local existence.** Let `sol` be a regular solution on `[0, T)` whose slices at a
time `t₁ ∈ (0, T)` are data of the class `IsHolderData α R N`, and let every datum of this class
have a regular solution on `(-τ, τ)`, where `T < t₁ + τ`. Then there is a regular solution on
`[0, t₁ + τ)` that agrees with `sol` on the closed half-plane at the times of `[0, T)`. -/
theorem IsRegularSolutionOn.exists_extension (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {T t₁ τ R N : ℝ}
    (h : IsRegularSolutionOn U κ R₀ sol (Ico 0 T) α) (ht₁ : 0 < t₁) (ht₁T : t₁ < T)
    (hTτ : T < t₁ + τ)
    (hd : IsHolderData (fun x ↦ sol.vorticity x t₁) (fun x ↦ sol.temperature x t₁) α R N)
    (hlocal : ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N → ∃ sol₁ : Fields,
      IsRegularSolutionOn U κ R₀ sol₁ (Ioo (-τ) τ) α ∧ HasDataAt sol₁ 0 ω₀ θ₀) :
    ∃ sol' : Fields, IsRegularSolutionOn U κ R₀ sol' (Ico 0 (t₁ + τ)) α ∧
      ∀ t ∈ Ico 0 T, ∀ x : ℝ^2, 0 ≤ x 1 →
        sol'.vorticity x t = sol.vorticity x t ∧ sol'.temperature x t = sol.temperature x t := by
  obtain ⟨sol₁, h₁, hd₁⟩ := hlocal _ _ hd
  set S₁ := sol₁.shiftTime (-t₁)
  have hS₁ : IsRegularSolutionOn U κ R₀ S₁ (Ioo (t₁ - τ) (t₁ + τ)) α :=
    (h₁.shiftTime (-t₁)).mono fun s hs ↦ by
      simp only [mem_preimage, mem_Ioo] at hs ⊢
      constructor <;> linarith [hs.1, hs.2]
  have hJ : Ico t₁ T ⊆ Ioo (t₁ - τ) (t₁ + τ) := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hJ' : Ico t₁ T ⊆ Ico 0 T := fun s hs ↦ ⟨ht₁.le.trans hs.1, hs.2⟩
  have hagree : ∀ t ∈ Ico t₁ T, ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t = S₁.vorticity x t ∧ sol.temperature x t = S₁.temperature x t := by
    intro t ht x hx
    refine (h.toIsSolutionOn.mono hJ').eq_of_eq_at_of_le hU hκ (hS₁.toIsSolutionOn.mono hJ)
      ordConnected_Ico ⟨le_rfl, ht₁T⟩ (fun y hy ↦ ?_) ht ht.1 hx
    have := hd₁ y hy
    simp only [S₁, Fields.shiftTime, add_neg_cancel]
    exact ⟨this.1.symm, this.2.symm⟩
  set A := HalfPlaneSystem.canonical sol
  set B := HalfPlaneSystem.canonical S₁
  have hA : IsRegularSolutionOn U κ R₀ A (Ico 0 T) α := h.canonical hU (uniqueDiffOn_Ico 0 T)
  have hB : IsRegularSolutionOn U κ R₀ B (Ioo (t₁ - τ) (t₁ + τ)) α :=
    hS₁.canonical hU isOpen_Ioo.uniqueDiffOn
  have hAB : ∀ s ∈ Ico t₁ T, AgreeAt A B s := fun s hs ↦ canonical_eq_of_eqOn (hagree s hs)
  let G : Fields :=
    { vorticity := fun x t ↦ if t < t₁ then A.vorticity x t else B.vorticity x t
      temperature := fun x t ↦ if t < t₁ then A.temperature x t else B.temperature x t }
  have hGA : ∀ s < T, AgreeAt G A s := by
    intro s hs x
    by_cases hst : s < t₁
    · simp [G, hst]
    · simp only [G, hst, ↓reduceIte]
      have := hAB s ⟨not_lt.mp hst, hs⟩ x
      exact ⟨this.1.symm, this.2.symm⟩
  have hGB : ∀ s > t₁, AgreeAt G B s := by
    intro s hs x
    simp [G, not_lt.mpr hs.le]
  refine ⟨G, IsRegularSolutionOn.glue ht₁T (hA.mono fun s hs ↦ ⟨hs.1.1, hs.2⟩)
    (hB.mono fun s hs ↦ ⟨by linarith [hs.2.out], hs.1.2⟩) hGA hGB, fun t ht x hx ↦ ?_⟩
  rw [(hGA t ht.2 x).1, (hGA t ht.2 x).2]
  exact ⟨canonical_vorticity_of_nonneg hx t, canonical_temperature_of_nonneg hx t⟩

/-! ### The maximal time and the maximal solution -/

/-- The maximal time of existence of regular solutions with the data `(ω₀, θ₀)`: the supremum of
the life spans `T` of the regular solutions on `lifeSpan T` with these data at time zero. -/
def maximalTime (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (κ : ℝ^2 → ℝ) (R₀ α : ℝ) (ω₀ θ₀ : ℝ^2 → ℝ) :
    ℝ≥0∞ :=
  sSup {T | ∃ sol : Fields, IsRegularSolutionOn U κ R₀ sol (lifeSpan T) α ∧
    HasDataAt sol 0 ω₀ θ₀}

variable {ω₀ θ₀ : ℝ^2 → ℝ}

/-- Every regular solution with the data lives at most until the maximal time. -/
theorem le_maximalTime {T : ℝ≥0∞} (h : IsRegularSolutionOn U κ R₀ sol (lifeSpan T) α)
    (hd : HasDataAt sol 0 ω₀ θ₀) : T ≤ maximalTime U κ R₀ α ω₀ θ₀ :=
  le_sSup ⟨sol, h, hd⟩

/-- **The maximal time is positive.** -/
theorem maximalTime_pos (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (hα : 0 < α) (hα1 : α < 1) {R N : ℝ} (hR : R < R₀) (hdata : IsHolderData ω₀ θ₀ α R N) :
    0 < maximalTime U κ R₀ α ω₀ θ₀ := by
  obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOn_Ioo hU hκ hα hα1 hR (le_max_right N 0)
  obtain ⟨sol₁, h₁, hd₁⟩ := hloc ω₀ θ₀ (hdata.mono le_rfl (le_max_left N 0))
  have hsub : lifeSpan (ENNReal.ofReal τ) ⊆ Ioo (-τ) τ := by
    rw [lifeSpan_ofReal hτ]
    exact fun s hs ↦ ⟨by linarith [hs.1], hs.2⟩
  exact (ENNReal.ofReal_pos.mpr hτ).trans_le (le_maximalTime (h₁.mono hsub) hd₁)

/-- **Uniqueness.** Two regular solutions with the same data agree on the closed half-plane at
every common time. -/
theorem IsRegularSolutionOn.eq_of_hasDataAt (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {T T' : ℝ≥0∞}
    (h : IsRegularSolutionOn U κ R₀ sol (lifeSpan T) α)
    (h' : IsRegularSolutionOn U κ R₀ sol' (lifeSpan T') α)
    (hd : HasDataAt sol 0 ω₀ θ₀) (hd' : HasDataAt sol' 0 ω₀ θ₀) {t : ℝ}
    (ht : t ∈ lifeSpan (min T T')) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t :=
  h.toIsSolutionOn.eq_of_hasDataAt_lifeSpan hU hκ h'.toIsSolutionOn hd hd' ht hx

/-- **The maximal solution.** The data have a regular solution on `[0, maximalTime)`. Every
other regular solution with the data is a restriction of it on the closed half-plane. Proof:
for every time `m` below the maximal time choose a regular solution that lives beyond `m`. The
canonical representatives of these solutions agree at their common times by uniqueness, so the
field that takes at the time `t` the value of the solution chosen for `t` is a regular solution
near every time, hence on the whole interval. -/
theorem exists_maximal (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (hα : 0 < α) (hα1 : α < 1) {R N : ℝ} (hR : R < R₀) (hdata : IsHolderData ω₀ θ₀ α R N) :
    ∃ sol : Fields, IsRegularSolutionOn U κ R₀ sol (lifeSpan (maximalTime U κ R₀ α ω₀ θ₀)) α ∧
      HasDataAt sol 0 ω₀ θ₀ := by
  classical
  set Tstar := maximalTime U κ R₀ α ω₀ θ₀
  have hpos : 0 < Tstar := maximalTime_pos hU hκ hα hα1 hR hdata
  -- For every time `m` below the maximal time choose a regular solution `sm m` with the data
  -- that lives beyond `m`.
  have hch (m : ℝ) (hm : ENNReal.ofReal m < Tstar) : ∃ T : ℝ≥0∞, ENNReal.ofReal m < T ∧
      ∃ sol : Fields, IsRegularSolutionOn U κ R₀ sol (lifeSpan T) α ∧
        HasDataAt sol 0 ω₀ θ₀ := by
    obtain ⟨T, ⟨sol, hs, hd⟩, hT⟩ := lt_sSup_iff.mp hm
    exact ⟨T, hT, sol, hs, hd⟩
  let Tm (m : ℝ) : ℝ≥0∞ := if hm : ENNReal.ofReal m < Tstar then (hch m hm).choose else 0
  let sm (m : ℝ) : Fields :=
    if hm : ENNReal.ofReal m < Tstar then (hch m hm).choose_spec.2.choose
    else { vorticity := 0, temperature := 0 }
  have hspec (m : ℝ) (hm : ENNReal.ofReal m < Tstar) : ENNReal.ofReal m < Tm m ∧
      IsRegularSolutionOn U κ R₀ (sm m) (lifeSpan (Tm m)) α ∧ HasDataAt (sm m) 0 ω₀ θ₀ := by
    simp only [Tm, sm, hm, ↓reduceDIte]
    exact ⟨(hch m hm).choose_spec.1, (hch m hm).choose_spec.2.choose_spec.1,
      (hch m hm).choose_spec.2.choose_spec.2⟩
  have hle (m : ℝ) (hm : ENNReal.ofReal m < Tstar) : Tm m ≤ Tstar :=
    le_maximalTime (hspec m hm).2.1 (hspec m hm).2.2
  have hcanon (m : ℝ) (hm : ENNReal.ofReal m < Tstar) :
      IsRegularSolutionOn U κ R₀ (canonical (sm m)) (lifeSpan (Tm m)) α :=
    (hspec m hm).2.1.canonical hU (uniqueDiffOn_lifeSpan _)
  -- The canonical representatives of two chosen solutions agree on the whole plane at their
  -- common times, by uniqueness on the closed half-plane.
  have hagree (m m' : ℝ) (hm : ENNReal.ofReal m < Tstar) (hm' : ENNReal.ofReal m' < Tstar)
      (s : ℝ) (hs : s ∈ lifeSpan (Tm m)) (hs' : s ∈ lifeSpan (Tm m')) :
      AgreeAt (canonical (sm m)) (canonical (sm m')) s :=
    canonical_eq_of_eqOn fun x hx ↦ IsRegularSolutionOn.eq_of_hasDataAt hU hκ
      (hspec m hm).2.1 (hspec m' hm').2.1 (hspec m hm).2.2 (hspec m' hm').2.2
      ⟨hs.1, lt_min hs.2 hs'.2⟩ hx
  -- The glued field: at the time `t` the canonical representative of the solution chosen
  -- for `t`.
  let sol : Fields :=
    { vorticity := fun x t ↦ (canonical (sm (max t 0))).vorticity x t
      temperature := fun x t ↦ (canonical (sm (max t 0))).temperature x t }
  have hsol_at (b s : ℝ) (hb : ENNReal.ofReal b < Tstar) (hs : s ∈ lifeSpan (Tm b)) :
      AgreeAt sol (canonical (sm b)) s := by
    have hs0 : max s 0 = s := max_eq_left hs.1
    have hsT : ENNReal.ofReal s < Tstar := hs.2.trans_le (hle b hb)
    intro x
    have := hagree s b hsT hb s ⟨hs.1, (hspec s hsT).1⟩ hs x
    simp only [sol, hs0]
    exact this
  have hstar : ∀ t ∈ lifeSpan Tstar, ENNReal.ofReal t < Tstar := fun t ht ↦ ht.2
  -- Being a regular solution is local in time: near every time the glued field is one of the
  -- chosen solutions, and on a compact interval its supports and bounds are those of one of them.
  refine ⟨sol, IsRegularSolutionOn.of_local (fun t ht ↦ ?_) (fun a b hab ↦ ?_)
    (fun a b hab ↦ ?_), fun x hx ↦ ?_⟩
  · have hb := hstar t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      refine ⟨{s | ENNReal.ofReal s < Tm 0}, isOpen_lt ENNReal.continuous_ofReal
        continuous_const, (hspec 0 hb).1, canonical (sm 0),
        (hcanon 0 hb).toIsSolutionOn.mono fun s hs ↦ ⟨hs.1.1, hs.2⟩, fun s hs ↦ ?_⟩
      rcases le_or_gt s 0 with hs0 | hs0
      · intro x
        simp [sol, max_eq_right hs0]
      · exact hsol_at 0 s hb ⟨hs0.le, hs⟩
    · refine ⟨Ioi 0 ∩ {s | ENNReal.ofReal s < Tm t}, isOpen_Ioi.inter
        (isOpen_lt ENNReal.continuous_ofReal continuous_const), ⟨h0, (hspec t hb).1⟩,
        canonical (sm t), (hcanon t hb).toIsSolutionOn.mono fun s hs ↦ ⟨hs.1.1, hs.2.2⟩,
        fun s hs ↦ hsol_at t s hb ⟨hs.1.le, hs.2⟩⟩
  · rcases lt_or_ge b a with hba | hab'
    · exact ⟨R₀ - 1, by linarith, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)⟩
    have hbI := hab ⟨hab', le_rfl⟩
    have hb := hstar b hbI
    have hsub : Icc a b ⊆ lifeSpan (Tm b) := fun s hs ↦
      ⟨(hab hs).1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt (hspec b hb).1⟩
    obtain ⟨R', hR'₀, hR'⟩ := (hcanon b hb).support a b hsub
    refine ⟨R', hR'₀, fun t ht x hx hxR ↦ ?_⟩
    rw [(hsol_at b t hb (hsub ht) x).1, (hsol_at b t hb (hsub ht) x).2]
    exact hR' t ht x hx hxR
  · rcases lt_or_ge b a with hba | hab'
    · exact ⟨0, 0, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)⟩
    have hbI := hab ⟨hab', le_rfl⟩
    have hb := hstar b hbI
    have hsub : Icc a b ⊆ lifeSpan (Tm b) := fun s hs ↦
      ⟨(hab hs).1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt (hspec b hb).1⟩
    obtain ⟨R', N', hRN⟩ := (hcanon b hb).holderData a b hsub
    refine ⟨R', N', fun t ht ↦ ?_⟩
    have h₁ : (fun x ↦ sol.vorticity x t) = (fun x ↦ (canonical (sm b)).vorticity x t) :=
      funext fun x ↦ (hsol_at b t hb (hsub ht) x).1
    have h₂ : (fun x ↦ sol.temperature x t) = (fun x ↦ (canonical (sm b)).temperature x t) :=
      funext fun x ↦ (hsol_at b t hb (hsub ht) x).2
    rw [h₁, h₂]
    exact hRN t ht
  · have h0 : ENNReal.ofReal 0 < Tstar := by simpa using hpos
    have h1 := (hspec 0 h0).2.2 x hx
    simp only [sol, max_self, canonical_vorticity_of_nonneg hx,
      canonical_temperature_of_nonneg hx]
    exact h1

/-- **The blow-up alternative.** If the maximal time is finite, then for no radius `R' < R₀` and
no bound `N'` are the slices of a regular solution on `[0, maximalTime)` with the data all data
of the class `IsHolderData α R' N'`: the `C^{1,α} × C^{2,α}` norms are unbounded or the supports
are contained in no disc of radius less than `R₀`. The continuation criterion is derived from
this alternative. Proof: otherwise the local existence time `τ` of the class `α R' N'` is
uniform, and restarting the solution at a time `t₁` with `T - τ < t₁ < T` gives a regular
solution beyond the maximal time `T`. -/
theorem not_forall_isHolderData (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (hα : 0 < α) (hα1 : α < 1) {R N : ℝ} (hR : R < R₀) (hdata : IsHolderData ω₀ θ₀ α R N)
    (hT : maximalTime U κ R₀ α ω₀ θ₀ < ⊤)
    (hsol : IsRegularSolutionOn U κ R₀ sol (lifeSpan (maximalTime U κ R₀ α ω₀ θ₀)) α)
    (hd : HasDataAt sol 0 ω₀ θ₀) {R' : ℝ} (hR' : R' < R₀) (N' : ℝ) :
    ¬ ∀ t ∈ lifeSpan (maximalTime U κ R₀ α ω₀ θ₀),
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R' N' := by
  intro hb
  obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOn_Ioo hU hκ hα hα1 hR' (le_max_right N' 0)
  set Tstar := maximalTime U κ R₀ α ω₀ θ₀
  set T := Tstar.toReal
  have hpos : 0 < T := ENNReal.toReal_pos (maximalTime_pos hU hκ hα hα1 hR hdata).ne' hT.ne
  have hspan : lifeSpan Tstar = Ico 0 T := lifeSpan_of_ne_top hT.ne
  set t₁ := max (T - τ / 2) (T / 2)
  have ht₁ : 0 < t₁ := (half_pos hpos).trans_le (le_max_right _ _)
  have ht₁T : t₁ < T := max_lt (by linarith) (by linarith)
  have hTτ : T < t₁ + τ := by linarith [le_max_left (T - τ / 2) (T / 2)]
  have hsol' : IsRegularSolutionOn U κ R₀ sol (Ico 0 T) α := hspan ▸ hsol
  have hd₁ := (hb t₁ (hspan ▸ ⟨ht₁.le, ht₁T⟩)).mono le_rfl (le_max_left N' 0)
  obtain ⟨sol', h', heq⟩ := hsol'.exists_extension hU hκ ht₁ ht₁T hTτ hd₁ hloc
  have hd' : HasDataAt sol' 0 ω₀ θ₀ := fun x hx ↦ by
    rw [(heq 0 ⟨le_rfl, hpos⟩ x hx).1, (heq 0 ⟨le_rfl, hpos⟩ x hx).2]
    exact hd x hx
  have hle : ENNReal.ofReal (t₁ + τ) ≤ Tstar := le_maximalTime
    (h'.mono (lifeSpan_ofReal (by linarith : (0 : ℝ) < t₁ + τ)).subset) hd'
  have hTstar : Tstar = ENNReal.ofReal T := (ENNReal.ofReal_toReal hT.ne).symm
  rw [hTstar, ENNReal.ofReal_le_ofReal_iff hpos.le] at hle
  linarith

end HalfPlaneSystem
