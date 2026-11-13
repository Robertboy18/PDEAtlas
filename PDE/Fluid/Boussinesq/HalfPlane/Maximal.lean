/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Canonical
public import PDE.Fluid.Boussinesq.HalfPlane.LocalExistence
public import PDE.Fluid.Boussinesq.HalfPlane.Uniqueness

/-!
# The maximal solution of the half-plane Boussinesq system

For data `ω₀ ∈ C^{1,α}`, `θ₀ ∈ C^{2,α}` of the class `IsHolderData`, `maximalTime α ω₀ θ₀` is the
supremum of the life spans `T` of the regular solutions on `lifeSpan T = [0, T)` with these data. It
is positive (`maximalTime_pos`) and attained (`exists_maximal`), and every regular solution with
these data agrees with the maximal one on the closed half-plane
(`IsRegularSolutionOn.eq_of_hasDataAt`). If the maximal time is finite, the `C^{1,α} × C^{2,α}`
norms or the support radii of the slices are unbounded on `[0, maximalTime)`
(`not_forall_isHolderData`).

## Main definitions

* `maximalTime α ω₀ θ₀`: the maximal time of existence.

## Main results

* `IsSolutionOn.of_local`, `IsRegularSolutionOn.of_local`, `IsRegularSolutionOn.glue`: locality.
* `IsRegularSolutionOn.exists_extension`: restart by local existence.
* `maximalTime_pos`, `exists_maximal`, `le_maximalTime`, `IsRegularSolutionOn.eq_of_hasDataAt`.
* `not_forall_isHolderData`: the blow-up alternative.

## How it works

Gluing in time rests on two facts: the classes are local in time (`IsSolutionOn.of_local`,
`IsRegularSolutionOn.glue`), and solutions that agree on the closed half-plane have equal canonical
representatives (`IsSolutionOn.canonical_eq`). Local existence (`exists_isRegularSolutionOn_Ioo`)
gives one life span for all data of a class `IsHolderData α R N`, so the maximal time is positive.
For `exists_maximal` we choose for each `m` below the maximal time a regular solution with these
data on a life span longer than `m`. By uniqueness these solutions agree on the closed half-plane at
common times, so their canonical representatives agree, and taking at each time `t` the
representative chosen for `t` gives a regular solution on `[0, maximalTime)` by locality in time.
For the blow-up alternative suppose that all slices lie in one class `IsHolderData α R' N'`, and let
`τ` be the life span of local existence for this class. Restarting at a time `t₁ ∈ (T - τ, T)`,
where `T` is the maximal time, gives a regular solution with the same data on `[0, t₁ + τ)`
(`IsRegularSolutionOn.exists_extension`, by forward uniqueness `IsSolutionOn.eq_of_eq_at_of_le` and
gluing), which contradicts the maximality of `T`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ENNReal Topology

namespace Boussinesq.HalfPlane

/-! ### Restriction, time shifts and uniqueness of regular solutions -/

variable {sol sol' : VorticityStreamFields} {I : Set ℝ} {α : ℝ}

/-- A regular solution on `I` is a regular solution on every `J ⊆ I`. -/
theorem IsRegularSolutionOn.mono (h : IsRegularSolutionOn sol I α) {J : Set ℝ} (hJ : J ⊆ I) :
    IsRegularSolutionOn sol J α :=
  ⟨h.toIsSolutionOn.mono hJ, fun a b hab ↦ h.holderData a b (hab.trans hJ)⟩

/-- Shifting time by `t₀` takes a regular solution on `I` to a regular solution on `I - t₀`. -/
theorem IsRegularSolutionOn.shiftTime (h : IsRegularSolutionOn sol I α) (t₀ : ℝ) :
    IsRegularSolutionOn (sol.shiftTime t₀) ((· + t₀) ⁻¹' I) α where
  toIsSolutionOn := h.toIsSolutionOn.shiftTime t₀
  holderData a b hab := by
    have hsub : Icc (a + t₀) (b + t₀) ⊆ I := fun s hs ↦ by
      have := hab (show s - t₀ ∈ Icc a b from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      simpa using this
    obtain ⟨R, N, hRN⟩ := h.holderData (a + t₀) (b + t₀) hsub
    exact ⟨R, N, fun t ht ↦ hRN (t + t₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- Two solutions on life spans with the same data agree on the closed half-plane at every common
time. -/
theorem IsSolutionOn.eq_of_hasDataAt_lifeSpan {T T' : ℝ≥0∞} {ω₀ θ₀ : ℝ^2 → ℝ}
    (h : IsSolutionOn sol (lifeSpan T)) (h' : IsSolutionOn sol' (lifeSpan T'))
    (hd : HasDataAt sol 0 ω₀ θ₀) (hd' : HasDataAt sol' 0 ω₀ θ₀) {t : ℝ}
    (ht : t ∈ lifeSpan (min T T')) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  refine (h.mono (lifeSpan_mono (min_le_left T T'))).eq_of_hasDataAt
    (h'.mono (lifeSpan_mono (min_le_right T T'))) (ordConnected_lifeSpan _)
    (zero_mem_lifeSpan (pos_of_mem_lifeSpan ht)) (fun y hy ↦ ?_) ht ht.1 hx
  rw [(hd y hy).1, (hd y hy).2, (hd' y hy).1, (hd' y hy).2]
  exact ⟨rfl, rfl⟩

/-! ### Locality in time -/

/-- The fields of `sol` and `sol'` agree at the time `s` on the whole plane. -/
def AgreeAt (sol sol' : VorticityStreamFields) (s : ℝ) : Prop :=
  ∀ x : ℝ^2, sol.vorticity x s = sol'.vorticity x s ∧ sol.temperature x s = sol'.temperature x s ∧
    sol.streamFunction x s = sol'.streamFunction x s

/-- **Solutions are local in time.** If near every time of `I` the fields agree with a solution
on the times of `I` near it, and the supports are bounded on compact subintervals, the fields are
a solution on `I`. -/
theorem IsSolutionOn.of_local
    (hloc : ∀ t ∈ I, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ ∃ sol' : VorticityStreamFields,
      IsSolutionOn sol' (I ∩ U) ∧ ∀ s ∈ U, AgreeAt sol sol' s)
    (hsupp : HasBoundedSupportOn sol I) : IsSolutionOn sol I := by
  have hslice {sol' : VorticityStreamFields} {s : ℝ} (h : AgreeAt sol sol' s) :
      (fun y ↦ sol.vorticity y s) = (fun y ↦ sol'.vorticity y s) ∧
        (fun y ↦ sol.temperature y s) = (fun y ↦ sol'.temperature y s) ∧
        (fun y ↦ sol.streamFunction y s) = (fun y ↦ sol'.streamFunction y s) :=
    ⟨funext fun y ↦ (h y).1, funext fun y ↦ (h y).2.1, funext fun y ↦ (h y).2.2⟩
  have hvel {sol' : VorticityStreamFields} {s : ℝ} (h : AgreeAt sol sol' s) :
      (fun y ↦ vorticityStreamVelocity sol y s) = fun y ↦ vorticityStreamVelocity sol' y s :=
    funext fun y ↦ by simp only [vorticityStreamVelocity, (hslice h).2.2]
  have hcd (field : VorticityStreamFields → ℝ^2 → ℝ → ℝ)
      (hfield : ∀ {sol' : VorticityStreamFields} {s : ℝ}, AgreeAt sol sol' s →
        ∀ y, field sol y s = field sol' y s)
      (hreg : ∀ {sol' : VorticityStreamFields} {J : Set ℝ}, IsSolutionOn sol' J →
        ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ field sol' xt.1 xt.2) (univ ×ˢ J)) :
      ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ field sol xt.1 xt.2) (univ ×ˢ I) := by
    refine contDiffOn_of_locally_contDiffOn fun p hp ↦ ?_
    obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc p.2 hp.2
    refine ⟨univ ×ˢ U, isOpen_univ.prod hU, ⟨mem_univ _, htU⟩, ?_⟩
    rw [prod_inter_prod, inter_self]
    exact (hreg h').congr fun q hq ↦ hfield (heq q.2 hq.2.2) q.1
  have hdt (field : VorticityStreamFields → ℝ^2 → ℝ → ℝ)
      (hfield : ∀ {sol' : VorticityStreamFields} {s : ℝ}, AgreeAt sol sol' s →
        ∀ y, field sol y s = field sol' y s)
      (hreg : ∀ {sol' : VorticityStreamFields} {J : Set ℝ}, IsSolutionOn sol' J →
        ∀ {x : ℝ^2} {t : ℝ}, t ∈ J → DifferentiableAt ℝ (fun s ↦ field sol' x s) t)
      {x : ℝ^2} {t : ℝ} (ht : t ∈ I) : DifferentiableAt ℝ (fun s ↦ field sol x s) t := by
    obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc t ht
    refine (hreg h' (x := x) ⟨ht, htU⟩).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds htU] with s hs
    exact hfield (heq s hs) x
  have hderiv (field : VorticityStreamFields → ℝ^2 → ℝ → ℝ)
      (hfield : ∀ {sol' : VorticityStreamFields} {s : ℝ}, AgreeAt sol sol' s →
        ∀ y, field sol y s = field sol' y s)
      {sol' : VorticityStreamFields} {U : Set ℝ} (hU : IsOpen U) {t : ℝ} (htU : t ∈ U)
      (heq : ∀ s ∈ U, AgreeAt sol sol' s) (x : ℝ^2) :
      deriv (fun s ↦ field sol x s) t = deriv (fun s ↦ field sol' x s) t :=
    Filter.EventuallyEq.deriv_eq <|
      eventually_of_mem (hU.mem_nhds htU) fun s hs ↦ hfield (heq s hs) x
  refine
    { classical :=
        { regularity :=
            { vorticity_contDiffOn := hcd (fun f ↦ f.vorticity) (fun h y ↦ (h y).1)
                fun h' ↦ h'.classical.regularity.vorticity_contDiffOn
              temperature_contDiffOn := hcd (fun f ↦ f.temperature) (fun h y ↦ (h y).2.1)
                fun h' ↦ h'.classical.regularity.temperature_contDiffOn
              vorticity_differentiableAt_time := fun ht ↦
                hdt (fun f ↦ f.vorticity) (fun h y ↦ (h y).1)
                  (fun h' _ _ ht' ↦ h'.classical.regularity.vorticity_differentiableAt_time ht')
                  ht
              temperature_differentiableAt_time := fun ht ↦
                hdt (fun f ↦ f.temperature) (fun h y ↦ (h y).2.1)
                  (fun h' _ _ ht' ↦ h'.classical.regularity.temperature_differentiableAt_time ht')
                  ht
              streamFunction_spatial_contDiff := fun {t} ht ↦ by
                obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc t ht
                rw [(hslice (heq t htU)).2.2]
                exact h'.classical.regularity.streamFunction_spatial_contDiff ⟨ht, htU⟩ }
          vorticity_equation := fun x t hx ht ↦ by
            obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc t ht
            have hs := hslice (heq t htU)
            rw [hderiv (fun f ↦ f.vorticity) (fun h y ↦ (h y).1) hU htU heq x, hs.1, hs.2.1,
              hvel (heq t htU)]
            exact h'.classical.vorticity_equation hx ⟨ht, htU⟩
          temperature_equation := fun x t hx ht ↦ by
            obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc t ht
            have hs := hslice (heq t htU)
            rw [hderiv (fun f ↦ f.temperature) (fun h y ↦ (h y).2.1) hU htU heq x, hs.2.1,
              hvel (heq t htU)]
            exact h'.classical.temperature_equation hx ⟨ht, htU⟩
          streamFunction_equation := fun x t hx ht ↦ by
            obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc t ht
            rw [(hslice (heq t htU)).2.2, (heq t htU x).1]
            exact h'.classical.streamFunction_equation hx ⟨ht, htU⟩
          zero_streamFunction_boundary := fun x₁ t ht ↦ by
            obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc t ht
            rw [(heq t htU _).2.2]
            exact h'.classical.zero_streamFunction_boundary x₁ ⟨ht, htU⟩ }
      stream := fun t ht x hx ↦ by
        obtain ⟨U, hU, htU, sol', h', heq⟩ := hloc t ht
        rw [(heq t htU x).2.2, (hslice (heq t htU)).1]
        exact h'.stream t ⟨ht, htU⟩ x hx
      support := hsupp }

/-- Regular solutions are local in time. -/
theorem IsRegularSolutionOn.of_local
    (hloc : ∀ t ∈ I, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ ∃ sol' : VorticityStreamFields,
      IsSolutionOn sol' (I ∩ U) ∧ ∀ s ∈ U, AgreeAt sol sol' s)
    (hsupp : HasBoundedSupportOn sol I)
    (hholder : ∀ a b : ℝ, Icc a b ⊆ I → ∃ R N : ℝ, ∀ t ∈ Icc a b,
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N) :
    IsRegularSolutionOn sol I α :=
  ⟨IsSolutionOn.of_local hloc hsupp, hholder⟩

/-- **Gluing two regular solutions.** Fields that agree with a regular solution `A` on the times
before `d` and with a regular solution `B` on the times after `c < d` are a regular solution. -/
theorem IsRegularSolutionOn.glue {c d : ℝ} (hcd : c < d) {A B : VorticityStreamFields}
    (hA : IsRegularSolutionOn A (I ∩ Iio d) α) (hB : IsRegularSolutionOn B (I ∩ Ioi c) α)
    (hsA : ∀ s < d, AgreeAt sol A s) (hsB : ∀ s > c, AgreeAt sol B s) :
    IsRegularSolutionOn sol I α := by
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
  · obtain ⟨R₁, hR₁⟩ := hA.support a (min b m) (hJ₁ hab)
    obtain ⟨R₂, hR₂⟩ := hB.support (max a m) b (hJ₂ hab)
    refine ⟨max R₁ R₂, fun t ht x hx hxR ↦ ?_⟩
    rcases hcases ht with ⟨ht', htd⟩ | ⟨ht', htc⟩
    · rw [(hsA t htd x).1, (hsA t htd x).2.1]
      exact hR₁ t ht' x hx ((le_max_left _ _).trans_lt hxR)
    · rw [(hsB t htc x).1, (hsB t htc x).2.1]
      exact hR₂ t ht' x hx ((le_max_right _ _).trans_lt hxR)
  · obtain ⟨R₁, N₁, hR₁⟩ := hA.holderData a (min b m) (hJ₁ hab)
    obtain ⟨R₂, N₂, hR₂⟩ := hB.holderData (max a m) b (hJ₂ hab)
    refine ⟨max R₁ R₂, max N₁ N₂, fun t ht ↦ ?_⟩
    rcases hcases ht with ⟨ht', htd⟩ | ⟨ht', htc⟩
    · simpa only [fun x ↦ (hsA t htd x).1, fun x ↦ (hsA t htd x).2.1] using
        (hR₁ t ht').mono (le_max_left _ _) (le_max_left _ _)
    · simpa only [fun x ↦ (hsB t htc x).1, fun x ↦ (hsB t htc x).2.1] using
        (hR₂ t ht').mono (le_max_right _ _) (le_max_right _ _)

/-! ### Restart -/

/-- **Restart by local existence.** Let `sol` be a regular solution on `[0, T)` whose slices at a
time `t₁ ∈ (0, T)` are data of the class `IsHolderData α R N`, and let every datum of this class
have a regular solution on `(-τ, τ)`, where `T < t₁ + τ`. Then there is a regular solution on
`[0, t₁ + τ)` that agrees with `sol` on the closed half-plane at the times of `[0, T)`. -/
theorem IsRegularSolutionOn.exists_extension {T t₁ τ R N : ℝ}
    (h : IsRegularSolutionOn sol (Ico 0 T) α) (ht₁ : 0 < t₁) (ht₁T : t₁ < T)
    (hTτ : T < t₁ + τ)
    (hd : IsHolderData (fun x ↦ sol.vorticity x t₁) (fun x ↦ sol.temperature x t₁) α R N)
    (hlocal : ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N → ∃ sol₁ : VorticityStreamFields,
      IsRegularSolutionOn sol₁ (Ioo (-τ) τ) α ∧ HasDataAt sol₁ 0 ω₀ θ₀) :
    ∃ sol' : VorticityStreamFields, IsRegularSolutionOn sol' (Ico 0 (t₁ + τ)) α ∧
      ∀ t ∈ Ico 0 T, ∀ x : ℝ^2, 0 ≤ x 1 →
        sol'.vorticity x t = sol.vorticity x t ∧ sol'.temperature x t = sol.temperature x t := by
  have hτ : 0 < τ := by linarith
  have hT : 0 < T := ht₁.trans ht₁T
  obtain ⟨sol₁, h₁, hd₁⟩ := hlocal _ _ hd
  set S₁ := sol₁.shiftTime (-t₁)
  have hS₁ : IsRegularSolutionOn S₁ (Ioo (t₁ - τ) (t₁ + τ)) α :=
    (h₁.shiftTime (-t₁)).mono fun s hs ↦ by
      simp only [mem_preimage, mem_Ioo] at hs ⊢
      constructor <;> linarith [hs.1, hs.2]
  have hJ : Ico t₁ T ⊆ Ioo (t₁ - τ) (t₁ + τ) := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hJ' : Ico t₁ T ⊆ Ico 0 T := fun s hs ↦ ⟨ht₁.le.trans hs.1, hs.2⟩
  have hagree : ∀ t ∈ Ico t₁ T, ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t = S₁.vorticity x t ∧ sol.temperature x t = S₁.temperature x t := by
    refine fun t ht x hx ↦ (h.toIsSolutionOn.mono hJ').eq_of_eq_at_of_le
      (hS₁.toIsSolutionOn.mono hJ) ordConnected_Ico ⟨le_rfl, ht₁T⟩ (fun y hy ↦ ?_) ht ht.1 hx
    simpa only [S₁, VorticityStreamFields.shiftTime, add_neg_cancel] using
      ⟨(hd₁ y hy).1.symm, (hd₁ y hy).2.symm⟩
  set A := HalfPlane.canonical sol
  set B := HalfPlane.canonical S₁
  have hA : IsRegularSolutionOn A (Ico 0 T) α := h.canonical (uniqueDiffOn_Ico 0 T)
  have hB : IsRegularSolutionOn B (Ioo (t₁ - τ) (t₁ + τ)) α :=
    hS₁.canonical isOpen_Ioo.uniqueDiffOn
  have hAB : ∀ s ∈ Ico t₁ T, AgreeAt A B s := fun s hs ↦
    h.toIsSolutionOn.canonical_eq hS₁.toIsSolutionOn (hJ' hs) (hJ hs) (hagree s hs)
  let G : VorticityStreamFields :=
    { vorticity := fun x t ↦ if t < t₁ then A.vorticity x t else B.vorticity x t
      temperature := fun x t ↦ if t < t₁ then A.temperature x t else B.temperature x t
      streamFunction := fun x t ↦ if t < t₁ then A.streamFunction x t else B.streamFunction x t }
  have hGA : ∀ s < T, AgreeAt G A s := fun s hs x ↦ by
    by_cases hst : s < t₁
    · simp [G, hst]
    · have := hAB s ⟨not_lt.mp hst, hs⟩ x
      simpa only [G, hst, ↓reduceIte] using ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩
  have hGB : ∀ s > t₁, AgreeAt G B s := fun s hs x ↦ by simp [G, not_lt.mpr hs.le]
  refine ⟨G, IsRegularSolutionOn.glue ht₁T (hA.mono fun s hs ↦ ⟨hs.1.1, hs.2⟩)
    (hB.mono fun s hs ↦ ⟨by linarith [hs.2.out], hs.1.2⟩) hGA hGB, fun t ht x hx ↦ ?_⟩
  rw [(hGA t ht.2 x).1, (hGA t ht.2 x).2.1]
  exact ⟨canonical_vorticity_of_nonneg hx t, canonical_temperature_of_nonneg hx t⟩

/-! ### The maximal time and the maximal solution -/

/-- The maximal time of existence of regular solutions with the data `(ω₀, θ₀)`: the supremum of
the life spans `T` of the regular solutions on `lifeSpan T` with these data at time zero. -/
def maximalTime (α : ℝ) (ω₀ θ₀ : ℝ^2 → ℝ) : ℝ≥0∞ :=
  sSup {T | ∃ sol : VorticityStreamFields, IsRegularSolutionOn sol (lifeSpan T) α ∧
    HasDataAt sol 0 ω₀ θ₀}

variable {ω₀ θ₀ : ℝ^2 → ℝ}

/-- Every regular solution with the data lives at most until the maximal time. -/
theorem le_maximalTime {T : ℝ≥0∞} (h : IsRegularSolutionOn sol (lifeSpan T) α)
    (hd : HasDataAt sol 0 ω₀ θ₀) : T ≤ maximalTime α ω₀ θ₀ :=
  le_sSup ⟨sol, h, hd⟩

/-- **The maximal time is positive.** -/
theorem maximalTime_pos (hα : 0 < α) (hα1 : α < 1) {R N : ℝ}
    (hdata : IsHolderData ω₀ θ₀ α R N) : 0 < maximalTime α ω₀ θ₀ := by
  obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOn_Ioo hα hα1 (le_max_right R 0)
    (le_max_right N 0)
  obtain ⟨sol₁, h₁, hd₁, -⟩ := hloc ω₀ θ₀ (hdata.mono (le_max_left R 0) (le_max_left N 0))
  have hsub : lifeSpan (ENNReal.ofReal τ) ⊆ Ioo (-τ) τ := by
    rw [lifeSpan_ofReal hτ]
    exact fun s hs ↦ ⟨by linarith [hs.1], hs.2⟩
  exact (ENNReal.ofReal_pos.mpr hτ).trans_le (le_maximalTime (h₁.mono hsub) hd₁)

/-- **Uniqueness.** Two regular solutions with the same data agree on the closed half-plane at
every common time. -/
theorem IsRegularSolutionOn.eq_of_hasDataAt {T T' : ℝ≥0∞}
    (h : IsRegularSolutionOn sol (lifeSpan T) α) (h' : IsRegularSolutionOn sol' (lifeSpan T') α)
    (hd : HasDataAt sol 0 ω₀ θ₀) (hd' : HasDataAt sol' 0 ω₀ θ₀) {t : ℝ}
    (ht : t ∈ lifeSpan (min T T')) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t :=
  h.toIsSolutionOn.eq_of_hasDataAt_lifeSpan h'.toIsSolutionOn hd hd' ht hx

/-- **The maximal solution.** The data have a regular solution on `[0, maximalTime)`. -/
theorem exists_maximal (hα : 0 < α) (hα1 : α < 1) {R N : ℝ}
    (hdata : IsHolderData ω₀ θ₀ α R N) :
    ∃ sol : VorticityStreamFields,
      IsRegularSolutionOn sol (lifeSpan (maximalTime α ω₀ θ₀)) α ∧ HasDataAt sol 0 ω₀ θ₀ := by
  set Tstar := maximalTime α ω₀ θ₀
  have hpos : 0 < Tstar := maximalTime_pos hα hα1 hdata
  have hch (m : ℝ) (hm : ENNReal.ofReal m < Tstar) : ∃ T : ℝ≥0∞, ENNReal.ofReal m < T ∧
      ∃ sol : VorticityStreamFields, IsRegularSolutionOn sol (lifeSpan T) α ∧
        HasDataAt sol 0 ω₀ θ₀ := by
    obtain ⟨T, ⟨sol, hs, hd⟩, hT⟩ := lt_sSup_iff.mp hm
    exact ⟨T, hT, sol, hs, hd⟩
  have : Nonempty VorticityStreamFields := ⟨zeroVorticityStreamFields⟩
  choose! Tm hTm sm hsm hdm using hch
  have hcanon (m : ℝ) (hm : ENNReal.ofReal m < Tstar) :
      IsRegularSolutionOn (canonical (sm m)) (lifeSpan (Tm m)) α :=
    (hsm m hm).canonical (uniqueDiffOn_lifeSpan _)
  have hagree (m m' : ℝ) (hm : ENNReal.ofReal m < Tstar) (hm' : ENNReal.ofReal m' < Tstar)
      (s : ℝ) (hs : s ∈ lifeSpan (Tm m)) (hs' : s ∈ lifeSpan (Tm m')) :
      AgreeAt (canonical (sm m)) (canonical (sm m')) s :=
    (hsm m hm).toIsSolutionOn.canonical_eq (hsm m' hm').toIsSolutionOn hs hs' fun x hx ↦
      IsRegularSolutionOn.eq_of_hasDataAt (hsm m hm) (hsm m' hm') (hdm m hm) (hdm m' hm')
        ⟨hs.1, lt_min hs.2 hs'.2⟩ hx
  let sol : VorticityStreamFields :=
    { vorticity := fun x t ↦ (canonical (sm (max t 0))).vorticity x t
      temperature := fun x t ↦ (canonical (sm (max t 0))).temperature x t
      streamFunction := fun x t ↦ (canonical (sm (max t 0))).streamFunction x t }
  have hsol_at (b s : ℝ) (hb : ENNReal.ofReal b < Tstar) (hs : s ∈ lifeSpan (Tm b)) :
      AgreeAt sol (canonical (sm b)) s := by
    have hsT : ENNReal.ofReal s < Tstar := hs.2.trans_le (le_maximalTime (hsm b hb) (hdm b hb))
    intro x
    simpa only [sol, max_eq_left hs.1] using hagree s b hsT hb s ⟨hs.1, hTm s hsT⟩ hs x
  have hstar : ∀ t ∈ lifeSpan Tstar, ENNReal.ofReal t < Tstar := fun t ht ↦ ht.2
  have hcover {a b : ℝ} (hab : Icc a b ⊆ lifeSpan Tstar) (hab' : a ≤ b) :
      ∃ hb : ENNReal.ofReal b < Tstar, Icc a b ⊆ lifeSpan (Tm b) :=
    have hb := hstar b (hab ⟨hab', le_rfl⟩)
    ⟨hb, fun s hs ↦ ⟨(hab hs).1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt (hTm b hb)⟩⟩
  refine ⟨sol, IsRegularSolutionOn.of_local (fun t ht ↦ ?_) (fun a b hab ↦ ?_)
    (fun a b hab ↦ ?_), fun x hx ↦ ?_⟩
  · have hb := hstar t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      refine ⟨{s | ENNReal.ofReal s < Tm 0}, isOpen_lt ENNReal.continuous_ofReal
        continuous_const, hTm 0 hb, canonical (sm 0),
        (hcanon 0 hb).toIsSolutionOn.mono fun s hs ↦ ⟨hs.1.1, hs.2⟩, fun s hs ↦ ?_⟩
      rcases le_or_gt s 0 with hs0 | hs0
      · intro x
        simp [sol, max_eq_right hs0]
      · exact hsol_at 0 s hb ⟨hs0.le, hs⟩
    · refine ⟨Ioi 0 ∩ {s | ENNReal.ofReal s < Tm t}, isOpen_Ioi.inter
        (isOpen_lt ENNReal.continuous_ofReal continuous_const), ⟨h0, hTm t hb⟩,
        canonical (sm t), (hcanon t hb).toIsSolutionOn.mono fun s hs ↦ ⟨hs.1.1, hs.2.2⟩,
        fun s hs ↦ hsol_at t s hb ⟨hs.1.le, hs.2⟩⟩
  · rcases lt_or_ge b a with hba | hab'
    · exact ⟨0, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)⟩
    obtain ⟨hb, hsub⟩ := hcover hab hab'
    obtain ⟨R', hR'⟩ := (hcanon b hb).support a b hsub
    refine ⟨R', fun t ht x hx hxR ↦ ?_⟩
    rw [(hsol_at b t hb (hsub ht) x).1, (hsol_at b t hb (hsub ht) x).2.1]
    exact hR' t ht x hx hxR
  · rcases lt_or_ge b a with hba | hab'
    · exact ⟨0, 0, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)⟩
    obtain ⟨hb, hsub⟩ := hcover hab hab'
    obtain ⟨R', N', hRN⟩ := (hcanon b hb).holderData a b hsub
    exact ⟨R', N', fun t ht ↦ by simpa only [fun x ↦ (hsol_at b t hb (hsub ht) x).1,
      fun x ↦ (hsol_at b t hb (hsub ht) x).2.1] using hRN t ht⟩
  · simpa only [sol, max_self, canonical_vorticity_of_nonneg hx,
      canonical_temperature_of_nonneg hx] using hdm 0 (by simpa using hpos) x hx

/-- **The blow-up alternative.** If the maximal time is finite, the slices of a regular solution on
`[0, maximalTime)` with the data are not data of the class `IsHolderData α R' N'` at all times,
for any radius `R'` and bound `N'`. -/
theorem not_forall_isHolderData (hα : 0 < α) (hα1 : α < 1) {R N : ℝ}
    (hdata : IsHolderData ω₀ θ₀ α R N) (hT : maximalTime α ω₀ θ₀ < ⊤)
    (hsol : IsRegularSolutionOn sol (lifeSpan (maximalTime α ω₀ θ₀)) α)
    (hd : HasDataAt sol 0 ω₀ θ₀) (R' N' : ℝ) :
    ¬ ∀ t ∈ lifeSpan (maximalTime α ω₀ θ₀),
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R' N' := by
  intro hb
  obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOn_Ioo hα hα1 (le_max_right R' 0)
    (le_max_right N' 0)
  set Tstar := maximalTime α ω₀ θ₀
  set T := Tstar.toReal
  have hpos : 0 < T := ENNReal.toReal_pos (maximalTime_pos hα hα1 hdata).ne' hT.ne
  have hspan : lifeSpan Tstar = Ico 0 T := lifeSpan_of_ne_top hT.ne
  set t₁ := max (T - τ / 2) (T / 2)
  have ht₁ : 0 < t₁ := (half_pos hpos).trans_le (le_max_right _ _)
  have ht₁T : t₁ < T := max_lt (by linarith) (by linarith)
  have hTτ : T < t₁ + τ := by linarith [le_max_left (T - τ / 2) (T / 2)]
  have hsol' : IsRegularSolutionOn sol (Ico 0 T) α := hspan ▸ hsol
  have hd₁ := (hb t₁ (hspan ▸ ⟨ht₁.le, ht₁T⟩)).mono (le_max_left R' 0) (le_max_left N' 0)
  obtain ⟨sol', h', heq⟩ := hsol'.exists_extension ht₁ ht₁T hTτ hd₁
    fun ω₁ θ₁ hd' ↦ (hloc ω₁ θ₁ hd').elim fun s hs ↦ ⟨s, hs.1, hs.2.1⟩
  have hd' : HasDataAt sol' 0 ω₀ θ₀ := fun x hx ↦ by
    rw [(heq 0 ⟨le_rfl, hpos⟩ x hx).1, (heq 0 ⟨le_rfl, hpos⟩ x hx).2]
    exact hd x hx
  have hle := le_maximalTime (T := ENNReal.ofReal (t₁ + τ))
    (h'.mono (lifeSpan_ofReal (by linarith : (0 : ℝ) < t₁ + τ)).subset) hd'
  have hTstar : maximalTime α ω₀ θ₀ = ENNReal.ofReal T := (ENNReal.ofReal_toReal hT.ne).symm
  rw [hTstar, ENNReal.ofReal_le_ofReal_iff hpos.le] at hle
  linarith

end Boussinesq.HalfPlane
