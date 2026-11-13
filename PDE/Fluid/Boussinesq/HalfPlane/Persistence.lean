/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Continuation
public import PDE.Fluid.Boussinesq.HalfPlane.IterationHigher

/-!
# Persistence of regularity and well-posedness at level `k`

A regular solution of the half-plane Boussinesq system on a life span `[0, T)` whose data are
`ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}`, `k ≥ 2`, keeps this regularity on the whole life span
(`IsRegularSolutionOn.isRegularSolutionOfOn`). Hence the maximal time at level `k` is the maximal
time at level one. Data of order `k` have a regular solution of order `k` on the maximal life span
with the continuation criterion, maximality, uniqueness, globally `C^k × C^{k+1}` slices of compact
support, continuous spatial jets and the reflection symmetry (`exists_maximalSolutionOf`).

## Main results

* `IsSolutionOn.eq_of_restart`: agreement with a solution restarted at a later time.
* `IsRegularSolutionOn.exists_isHolderDataOf`: uniform bounds of order `k` on compact intervals.
* `IsRegularSolutionOn.isRegularSolutionOfOn`: persistence of `C^{k,α} × C^{k+1,α}`.
* `exists_maximalSolutionOf`: local well-posedness at level `k ≥ 2` on the maximal life span, with
  the continuation criterion, maximality, uniqueness, global regularity, continuity of the spatial
  jets and propagation of the reflection symmetry.
* `exists_maximalSolutionOf_jets`: for `k ≥ 3`, the same package with `C³ × C⁴` slices whose
  spatial derivatives of orders at most three and four are continuous on `ℝ² × [0, T)`.

## How it works

On `[0, t₁]` inside the life span the `C^{1,α} × C^{2,α}` norms and the support radii of the slices
are bounded, so local existence at level `k` (`exists_isRegularSolutionOfOn_Ioo`) gives one life
span `τ` for every starting time in `[0, t₁]`, whatever the level-`k` norm there. We restart at the
times `0, τ/2, τ, …`. By forward uniqueness each restarted solution agrees with the given one on the
closed half-plane (`IsSolutionOn.eq_of_restart`), so its level-`k` bound passes to the given
solution, and finitely many restarts give `IsRegularSolutionOn.exists_isHolderDataOf`; continuity in
time of the top derivatives comes from a restarted solution in the same way. For
`exists_maximalSolutionOf` we apply persistence to the maximal solution of `exists_maximal` and pass
to its representative `canonicalOf k`, which continues the fields below the boundary by weighted
reflections of orders `k`, `k + 1` and `k + 2`. This representative carries the global regularity
and the continuous jets, the criterion is `continuationIntegral_eq_top`, maximality is
`le_maximalTime`, and the symmetry comes from `IsSolutionOn.parity`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ENNReal Topology

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {sol sol₁ : VorticityStreamFields} {I : Set ℝ} {α : ℝ}

/-- **Agreement with a restarted solution.** If `sol₁` is a solution on `(-τ, τ)` whose data at
time zero are the slices of a solution `sol` at a time `t₀` of an order-connected set of times
`I`, then on the closed half-plane `sol` at a time `t ∈ I ∩ [t₀, t₀ + τ)` is `sol₁` at
`t - t₀`. -/
theorem IsSolutionOn.eq_of_restart (h : IsSolutionOn sol I) (hI : I.OrdConnected) {t₀ τ : ℝ}
    (ht₀ : t₀ ∈ I) (h₁ : IsSolutionOn sol₁ (Ioo (-τ) τ))
    (hd₁ : HasDataAt sol₁ 0 (fun x ↦ sol.vorticity x t₀) (fun x ↦ sol.temperature x t₀))
    {t : ℝ} (ht : t ∈ I) (htt₀ : t₀ ≤ t) (htτ : t < t₀ + τ) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol₁.vorticity x (t - t₀) ∧
      sol.temperature x t = sol₁.temperature x (t - t₀) := by
  have hτ : 0 < τ := by linarith
  have hJ : I ∩ Ico t₀ (t₀ + τ) ⊆ (· + -t₀) ⁻¹' Ioo (-τ) τ := fun s hs ↦ by
    simp only [mem_preimage, mem_Ioo]
    constructor <;> linarith [hs.2.1, hs.2.2]
  have hS₁ := (h₁.shiftTime (-t₀)).mono hJ
  have h' := h.mono (inter_subset_left : I ∩ Ico t₀ (t₀ + τ) ⊆ I)
  have hdata : ∀ y : ℝ^2, 0 ≤ y 1 →
      sol.vorticity y t₀ = (sol₁.shiftTime (-t₀)).vorticity y t₀ ∧
        sol.temperature y t₀ = (sol₁.shiftTime (-t₀)).temperature y t₀ := by
    intro y hy
    have := hd₁ y hy
    simp only [VorticityStreamFields.shiftTime, add_neg_cancel]
    exact ⟨this.1.symm, this.2.symm⟩
  have := h'.eq_of_eq_at_of_le hS₁ (hI.inter ordConnected_Ico) ⟨ht₀, le_rfl, by linarith⟩ hdata
    ⟨ht, htt₀, htτ⟩ htt₀ hx
  simpa [VorticityStreamFields.shiftTime, sub_eq_add_neg] using this

/-- **Uniform bounds of order `k` on compact intervals.** Let `sol` be a regular solution on the
life span `T` whose slices at time zero are data of order `k ≥ 2`. On every interval `[0, t₁]`
inside the life span its slices are data of order `k` with one support radius and one bound. -/
theorem IsRegularSolutionOn.exists_isHolderDataOf {k : ℕ} (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {T : ℝ≥0∞} (h : IsRegularSolutionOn sol (lifeSpan T) α) {R N : ℝ}
    (hd : IsHolderDataOf k (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    {t₁ : ℝ} (ht₁ : t₁ ∈ lifeSpan T) :
    ∃ R' N' : ℝ, ∀ t ∈ Icc 0 t₁,
      IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R' N' := by
  have h0 : (0 : ℝ) ∈ lifeSpan T := zero_mem_lifeSpan (pos_of_mem_lifeSpan ht₁)
  have hsub : Icc 0 t₁ ⊆ lifeSpan T := (ordConnected_lifeSpan T).out h0 ht₁
  obtain ⟨R₁, N₁, h1⟩ := h.holderData 0 t₁ hsub
  have h1' (t : ℝ) (ht : t ∈ Icc 0 t₁) := (h1 t ht).mono (le_max_left R₁ 0) (le_max_left N₁ 0)
  obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOfOn_Ioo hk hα hα1 (le_max_right R₁ 0)
    (le_max_right N₁ 0)
  have key (m : ℕ) : ∃ N' : ℝ, ∀ t ∈ Icc 0 (min t₁ (m * (τ / 2))),
      IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α
        (max R₁ 0) N' := by
    induction m with
    | zero =>
      refine ⟨N, fun t ht ↦ ?_⟩
      have ht0 : t = 0 := le_antisymm (by simpa [min_eq_right ht₁.1] using ht.2) ht.1
      subst ht0
      exact hd.of_eq_zero (h1' 0 ⟨le_rfl, ht₁.1⟩).eq_zero
    | succ m ih =>
      obtain ⟨Nm, hNm⟩ := ih
      obtain ⟨t₀, ht₀def⟩ : ∃ t₀, t₀ = min t₁ (m * (τ / 2)) := ⟨_, rfl⟩
      rw [← ht₀def] at hNm
      have hm0 : (0 : ℝ) ≤ m * (τ / 2) := by positivity
      have ht₀ : t₀ ∈ Icc 0 t₁ := ⟨ht₀def ▸ le_min ht₁.1 hm0, ht₀def ▸ min_le_left _ _⟩
      obtain ⟨sol₁, hs₁, hd₁, -, N'', hN''⟩ := hloc _ _ (h1' t₀ ht₀) Nm (hNm t₀ ⟨ht₀.1, le_rfl⟩)
      refine ⟨max Nm N'', fun t ht ↦ ?_⟩
      rcases le_or_gt t t₀ with htt₀ | htt₀
      · exact (hNm t ⟨ht.1, htt₀⟩).of_le le_rfl (le_max_left _ _)
      have ht2 : t ≤ t₁ ∧ t ≤ (m + 1) * (τ / 2) := by
        have := ht.2
        push_cast at this
        exact le_min_iff.mp this
      have htI : t ∈ Icc 0 t₁ := ⟨ht.1, ht2.1⟩
      have ht₀m : t₀ = m * (τ / 2) := by
        rcases min_choice t₁ (m * (τ / 2)) with hc | hc
        · rw [hc] at ht₀def
          linarith
        · rw [hc] at ht₀def
          exact ht₀def
      have htτ : t < t₀ + τ := by
        rw [ht₀m]
        linarith [ht2.2]
      have hag (x : ℝ^2) (hx : 0 ≤ x 1) :=
        h.toIsSolutionOn.eq_of_restart (ordConnected_lifeSpan T) (hsub ht₀) hs₁.toIsSolutionOn
          hd₁ (hsub htI) htt₀.le htτ hx
      have hmem : t - t₀ ∈ Ioo (-τ) τ := ⟨by linarith, by linarith⟩
      exact (((hN'' (t - t₀) hmem).congr (fun x hx ↦ (hag x hx).1)
        (fun x hx ↦ (hag x hx).2)).of_eq_zero (h1' t htI).eq_zero).of_le le_rfl
          (le_max_right _ _)
  obtain ⟨m, hm⟩ := exists_nat_ge (t₁ / (τ / 2))
  obtain ⟨N', hN'⟩ := key m
  have hmin : min t₁ (m * (τ / 2)) = t₁ :=
    min_eq_left ((div_le_iff₀ (by positivity)).mp hm)
  exact ⟨max R₁ 0, N', fun t ht ↦ hN' t (by rwa [hmin])⟩

/-- **Persistence of regularity.** A regular solution on a life span whose slices at time zero
are data of order `k ≥ 2` is a regular solution of order `k` on the life span. -/
theorem IsRegularSolutionOn.isRegularSolutionOfOn {k : ℕ} (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {T : ℝ≥0∞} (h : IsRegularSolutionOn sol (lifeSpan T) α) {R N : ℝ}
    (hd : IsHolderDataOf k (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N) :
    IsRegularSolutionOfOn k sol (lifeSpan T) α := by
  have hI := ordConnected_lifeSpan T
  have hlocal (t : ℝ) (ht : t ∈ lifeSpan T) : ∃ τ > 0, ∃ t₀ ∈ lifeSpan T,
      (∀ s ∈ lifeSpan T, |s - t| < τ / 2 → t₀ ≤ s ∧ s < t₀ + τ) ∧
      ∃ sol₁ : VorticityStreamFields, IsRegularSolutionOfOn k sol₁ (Ioo (-τ) τ) α ∧
        HasDataAt sol₁ 0 (fun x ↦ sol.vorticity x t₀) (fun x ↦ sol.temperature x t₀) := by
    have h0 : (0 : ℝ) ∈ lifeSpan T := zero_mem_lifeSpan (pos_of_mem_lifeSpan ht)
    have hsub : Icc 0 t ⊆ lifeSpan T := hI.out h0 ht
    obtain ⟨R₁, N₁, h1⟩ := h.holderData 0 t hsub
    obtain ⟨Rk, Nk, hk'⟩ := h.exists_isHolderDataOf hk hα hα1 hd ht
    obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOfOn_Ioo hk hα hα1 (le_max_right R₁ 0)
      (le_max_right N₁ 0)
    have ht₀ : max 0 (t - τ / 2) ∈ Icc 0 t := ⟨le_max_left _ _, max_le ht.1 (by linarith)⟩
    have hd1 := (h1 _ ht₀).mono (le_max_left R₁ 0) (le_max_left N₁ 0)
    obtain ⟨sol₁, hs₁, hd₁, -⟩ := hloc _ _ hd1 Nk ((hk' _ ht₀).of_eq_zero hd1.eq_zero)
    refine ⟨τ, hτ, max 0 (t - τ / 2), hsub ht₀, fun s hs hst ↦ ?_, sol₁, hs₁, hd₁⟩
    have h2 := abs_lt.mp hst
    exact ⟨max_le hs.1 (by linarith), by linarith [le_max_right 0 (t - τ / 2)]⟩
  have hagree {τ t₀ : ℝ} (ht₀ : t₀ ∈ lifeSpan T) {sol₁ : VorticityStreamFields}
      (hs₁ : IsRegularSolutionOfOn k sol₁ (Ioo (-τ) τ) α)
      (hd₁ : HasDataAt sol₁ 0 (fun x ↦ sol.vorticity x t₀) (fun x ↦ sol.temperature x t₀))
      {s : ℝ} (hs : s ∈ lifeSpan T) (hs₀ : t₀ ≤ s ∧ s < t₀ + τ) :
      EqOn (fun y ↦ sol.vorticity y s) (fun y ↦ sol₁.vorticity y (s - t₀)) H̄ ∧
        EqOn (fun y ↦ sol.temperature y s) (fun y ↦ sol₁.temperature y (s - t₀)) H̄ :=
    ⟨fun y hy ↦ (h.toIsSolutionOn.eq_of_restart hI ht₀ hs₁.toIsSolutionOn hd₁ hs hs₀.1 hs₀.2
      hy).1, fun y hy ↦ (h.toIsSolutionOn.eq_of_restart hI ht₀ hs₁.toIsSolutionOn hd₁ hs hs₀.1
      hs₀.2 hy).2⟩
  have hmem {τ t₀ s : ℝ} (hs₀ : t₀ ≤ s ∧ s < t₀ + τ) : s - t₀ ∈ Ioo (-τ) τ :=
    ⟨by linarith [hs₀.1, hs₀.2], by linarith [hs₀.2]⟩
  refine
    { toIsSolutionOn := h.toIsSolutionOn
      holderData := fun a b hab ↦ ?_
      vorticity_uniform := fun j hj t ht ε hε ↦ ?_
      temperature_uniform := fun j hj t ht ε hε ↦ ?_ }
  · rcases lt_or_ge b a with hba | hab'
    · exact ⟨0, 0, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)⟩
    obtain ⟨R', N', hRN⟩ := h.exists_isHolderDataOf hk hα hα1 hd (hab ⟨hab', le_rfl⟩)
    exact ⟨R', N', fun t ht ↦ hRN t ⟨(hab ⟨le_rfl, hab'⟩).1.trans ht.1, ht.2⟩⟩
  · obtain ⟨τ, hτ, t₀, ht₀, hnear, sol₁, hs₁, hd₁⟩ := hlocal t ht
    have htt := hnear t ht (by simp [hτ])
    obtain ⟨δ, hδ, hδε⟩ := hs₁.vorticity_uniform j hj (t - t₀) (hmem htt) ε hε
    refine ⟨min δ (τ / 2), by positivity, fun s hs hst x hx ↦ ?_⟩
    have hss := hnear s hs (hst.trans_le (min_le_right _ _))
    rw [iteratedFDerivWithin_congr (hagree ht₀ hs₁ hd₁ hs hss).1 hx,
      iteratedFDerivWithin_congr (hagree ht₀ hs₁ hd₁ ht htt).1 hx]
    exact hδε (s - t₀) (hmem hss) (by
      rw [show s - t₀ - (t - t₀) = s - t by ring]; exact hst.trans_le (min_le_left _ _)) x hx
  · obtain ⟨τ, hτ, t₀, ht₀, hnear, sol₁, hs₁, hd₁⟩ := hlocal t ht
    have htt := hnear t ht (by simp [hτ])
    obtain ⟨δ, hδ, hδε⟩ := hs₁.temperature_uniform j hj (t - t₀) (hmem htt) ε hε
    refine ⟨min δ (τ / 2), by positivity, fun s hs hst x hx ↦ ?_⟩
    have hss := hnear s hs (hst.trans_le (min_le_right _ _))
    rw [iteratedFDerivWithin_congr (hagree ht₀ hs₁ hd₁ hs hss).2 hx,
      iteratedFDerivWithin_congr (hagree ht₀ hs₁ hd₁ ht htt).2 hx]
    exact hδε (s - t₀) (hmem hss) (by
      rw [show s - t₀ - (t - t₀) = s - t by ring]; exact hst.trans_le (min_le_left _ _)) x hx

/-- **Local well-posedness at level `k`.** For data `ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}` within the
closed half-plane, vanishing there outside a disc (`IsHolderDataOf k`), `k ≥ 2`, `0 < α < 1`, there
are a life span `T ∈ (0, ∞]` and a regular solution of order `k` on `[0, T)` with these data, such
that:
* if `T < ∞` then `∫₀^T (‖∇u‖_∞ + ‖∇θ‖_∞) = ∞`;
* no regular solution with these data lives longer;
* every solution in the class `IsSolutionOn` from the same data on a life span `T'` agrees with it
  on the closed half-plane up to `min T T'`;
* its slices are globally `C^k` and `C^{k+1}` with compact support, and on every compact interval
  of times the derivatives of orders `k` and `k + 1` are `α`-Hölder on the plane with one constant;
* the spatial derivatives of order at most `k` of the vorticity and at most `k + 1` of the
  temperature are continuous on `ℝ² × [0, T)`;
* data in the class `IsReflectionSymmetric` give fields in the class at every time, which are odd,
  even and odd in `x₀` on the whole plane. -/
theorem exists_maximalSolutionOf {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ} (hk : 2 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) (hdata : IsHolderDataOf k ω₀ θ₀ α R N) :
    ∃ (T : ℝ≥0∞) (sol : VorticityStreamFields), 0 < T ∧
      IsRegularSolutionOfOn k sol (lifeSpan T) α ∧ HasDataAt sol 0 ω₀ θ₀ ∧
      (T ≠ ⊤ → continuationIntegral sol T = ⊤) ∧
      (∀ (T' : ℝ≥0∞) (sol' : VorticityStreamFields), IsRegularSolutionOn sol' (lifeSpan T') α →
        HasDataAt sol' 0 ω₀ θ₀ → T' ≤ T) ∧
      (∀ (T' : ℝ≥0∞) (sol' : VorticityStreamFields), IsSolutionOn sol' (lifeSpan T') →
        HasDataAt sol' 0 ω₀ θ₀ → ∀ t ∈ lifeSpan (min T T'), ∀ x : ℝ^2, 0 ≤ x 1 →
          sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t) ∧
      (∀ t ∈ lifeSpan T, ContDiff ℝ k (fun x ↦ sol.vorticity x t) ∧
        ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun x ↦ sol.temperature x t) ∧
        HasCompactSupport (fun x ↦ sol.vorticity x t) ∧
        HasCompactSupport (fun x ↦ sol.temperature x t)) ∧
      (∀ a b : ℝ, Icc a b ⊆ lifeSpan T → ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x x' : ℝ^2,
        ‖iteratedFDeriv ℝ k (fun y ↦ sol.vorticity y t) x -
            iteratedFDeriv ℝ k (fun y ↦ sol.vorticity y t) x'‖ ≤ C * ‖x - x'‖ ^ α ∧
          ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ sol.temperature y t) x -
            iteratedFDeriv ℝ (k + 1) (fun y ↦ sol.temperature y t) x'‖ ≤ C * ‖x - x'‖ ^ α) ∧
      (∀ j ≤ k, ContinuousOn
        (fun p : ℝ^2 × ℝ ↦ iteratedFDeriv ℝ j (fun y ↦ sol.vorticity y p.2) p.1)
        (univ ×ˢ lifeSpan T)) ∧
      (∀ j ≤ k + 1, ContinuousOn
        (fun p : ℝ^2 × ℝ ↦ iteratedFDeriv ℝ j (fun y ↦ sol.temperature y p.2) p.1)
        (univ ×ˢ lifeSpan T)) ∧
      (IsReflectionSymmetric ω₀ θ₀ → ∀ t ∈ lifeSpan T,
        IsReflectionSymmetric (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) ∧
        ∀ x : ℝ^2, sol.vorticity (tangentialReflection x) t = -sol.vorticity x t ∧
          sol.temperature (tangentialReflection x) t = sol.temperature x t ∧
          sol.streamFunction (tangentialReflection x) t = -sol.streamFunction x t) := by
  have hk1 : 1 ≤ k := by omega
  have hd1 : IsHolderData ω₀ θ₀ α R (2 * N) := hdata.toIsHolderData hk1 hα.le hα1.le
  obtain ⟨sol₀, hsol₀, hd₀⟩ := exists_maximal hα hα1 hd1
  set T := maximalTime α ω₀ θ₀
  have hI := ordConnected_lifeSpan T
  have h0 : (0 : ℝ) ∈ lifeSpan T := zero_mem_lifeSpan (maximalTime_pos hα hα1 hd1)
  have hreg₀ : IsRegularSolutionOfOn k sol₀ (lifeSpan T) α :=
    hsol₀.isRegularSolutionOfOn hk hα hα1
      (hdata.congr (fun x hx ↦ (hd₀ x hx).1) fun x hx ↦ (hd₀ x hx).2)
  have hreg : IsRegularSolutionOfOn k (canonicalOf k sol₀) (lifeSpan T) α :=
    hreg₀.canonicalOf hk1 (uniqueDiffOn_lifeSpan T)
  have hd : HasDataAt (canonicalOf k sol₀) 0 ω₀ θ₀ := fun x hx ↦ by
    rw [canonicalOf_vorticity_of_nonneg hx, canonicalOf_temperature_of_nonneg hx]
    exact hd₀ x hx
  have hswap {F : Type} [TopologicalSpace F] {G : ℝ × ℝ^2 → F}
      (hG : ContinuousOn G (lifeSpan T ×ˢ univ)) :
      ContinuousOn (fun p : ℝ^2 × ℝ ↦ G (p.2, p.1)) (univ ×ˢ lifeSpan T) :=
    hG.comp continuous_swap.continuousOn fun p hp ↦ ⟨hp.2, mem_univ _⟩
  refine ⟨T, canonicalOf k sol₀, maximalTime_pos hα hα1 hd1, hreg, hd,
    fun hT ↦ continuationIntegral_eq_top hα hα1 hd1 hT (hreg.toIsRegularSolutionOn hk1 hα.le
      hα1.le) hd,
    fun T' sol' h' hd' ↦ le_maximalTime h' hd',
    fun T' sol' h' hd' t ht x hx ↦ hreg.toIsSolutionOn.eq_of_hasDataAt_lifeSpan h' hd hd' ht hx,
    fun t ht ↦ ?_, fun a b hab ↦ ?_,
    fun j hj ↦ hswap (G := fun p : ℝ × ℝ^2 ↦
      iteratedFDeriv ℝ j (fun x ↦ (canonicalOf k sol₀).vorticity x p.1) p.2)
      (hreg₀.continuousOn_iteratedFDeriv_canonicalOf_vorticity hk1 hj),
    fun j hj ↦ hswap (G := fun p : ℝ × ℝ^2 ↦
      iteratedFDeriv ℝ j (fun x ↦ (canonicalOf k sol₀).temperature x p.1) p.2)
      (hreg₀.continuousOn_iteratedFDeriv_canonicalOf_temperature hj),
    fun hsym t ht ↦ ?_⟩
  · obtain ⟨R', N', hRN⟩ := hreg₀.exists_isHolderDataOf ht
    exact ⟨hRN.contDiff_canonicalOf_vorticity hk1, hRN.contDiff_canonicalOf_temperature,
      hRN.hasCompactSupport_canonicalOf_vorticity, hRN.hasCompactSupport_canonicalOf_temperature⟩
  · obtain ⟨R', N', hRN⟩ := hreg₀.holderData a b hab
    refine ⟨max ((PDE.Analysis.reflectionBound k (k + 1) + 1) * N')
      ((PDE.Analysis.reflectionBound (k + 1) (k + 2) + 1) * N'), fun t ht x x' ↦ ⟨?_, ?_⟩⟩
    · exact ((hRN t ht).norm_iteratedFDeriv_canonicalOf_vorticity_sub_le hk1 hα.le hα1.le x
        x').trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (norm_nonneg _) α))
    · exact ((hRN t ht).norm_iteratedFDeriv_canonicalOf_temperature_sub_le hα.le hα1.le x
        x').trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg _) α))
  · have hS₀ := hsol₀.toIsSolutionOn
    have hR {x : ℝ^2} (hx : 0 ≤ x 1) : 0 ≤ tangentialReflection x 1 := by
      rwa [tangentialReflection_apply_one]
    have hω0 : ∀ x : ℝ^2, 0 ≤ x 1 →
        sol₀.vorticity (tangentialReflection x) 0 = -sol₀.vorticity x 0 := fun x hx ↦ by
      simpa only [(hd₀ _ (hR hx)).1, (hd₀ x hx).1] using hsym.vorticity_odd x hx
    have hθ0 : ∀ x : ℝ^2, 0 ≤ x 1 →
        sol₀.temperature (tangentialReflection x) 0 = sol₀.temperature x 0 := fun x hx ↦ by
      simpa only [(hd₀ _ (hR hx)).2, (hd₀ x hx).2] using hsym.temperature_even x hx
    have hax0 : ∀ x : ℝ^2, x 0 = 0 → 0 ≤ x 1 → sol₀.temperature x 0 = 0 := fun x hx0 hx ↦
      (hd₀ x hx).2.trans (hsym.temperature_axis x hx0 hx)
    have hpar {x : ℝ^2} (hx : 0 ≤ x 1) := hS₀.parity hI h0 hω0 hθ0 ht ht.1 hx
    have hodd (x : ℝ^2) : (canonicalOf k sol₀).vorticity (tangentialReflection x) t =
        -(canonicalOf k sol₀).vorticity x t :=
      canonicalOf_vorticity_tangentialReflection (fun y hy ↦ (hpar hy).1) x
    have heven (x : ℝ^2) : (canonicalOf k sol₀).temperature (tangentialReflection x) t =
        (canonicalOf k sol₀).temperature x t :=
      canonicalOf_temperature_tangentialReflection (fun y hy ↦ (hpar hy).2) x
    refine ⟨⟨fun x _ ↦ hodd x, fun x _ ↦ heven x, fun x hx0 hx ↦ ?_⟩, fun x ↦ ⟨hodd x, heven x,
      hS₀.canonicalOf_streamFunction_tangentialReflection ht (fun y hy ↦ (hpar hy).1) x⟩⟩
    rw [canonicalOf_temperature_of_nonneg hx]
    exact hS₀.temperature_axis hI h0 hω0 hθ0 hax0 ht ht.1 hx0 hx

/-- **Continuous jets at level `k ≥ 3`.** For data of order `k ≥ 3` the solution of
`exists_maximalSolutionOf` keeps the whole package of that theorem (continuation criterion,
maximality, uniqueness, compact support, Hölder top derivatives, symmetry) and in addition has
slices that are `C³` (vorticity) and `C⁴` (temperature) whose spatial derivatives of orders at
most three and at most four are continuous on `ℝ² × [0, T)`. -/
theorem exists_maximalSolutionOf_jets {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ} (hk : 3 ≤ k)
    (hα : 0 < α) (hα1 : α < 1) (hdata : IsHolderDataOf k ω₀ θ₀ α R N) :
    ∃ (T : ℝ≥0∞) (sol : VorticityStreamFields), 0 < T ∧
      IsRegularSolutionOfOn k sol (lifeSpan T) α ∧ HasDataAt sol 0 ω₀ θ₀ ∧
      (T ≠ ⊤ → continuationIntegral sol T = ⊤) ∧
      (∀ (T' : ℝ≥0∞) (sol' : VorticityStreamFields), IsRegularSolutionOn sol' (lifeSpan T') α →
        HasDataAt sol' 0 ω₀ θ₀ → T' ≤ T) ∧
      (∀ (T' : ℝ≥0∞) (sol' : VorticityStreamFields), IsSolutionOn sol' (lifeSpan T') →
        HasDataAt sol' 0 ω₀ θ₀ → ∀ t ∈ lifeSpan (min T T'), ∀ x : ℝ^2, 0 ≤ x 1 →
          sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t) ∧
      (∀ t ∈ lifeSpan T, ContDiff ℝ 3 (fun x ↦ sol.vorticity x t) ∧
        ContDiff ℝ 4 (fun x ↦ sol.temperature x t) ∧
        HasCompactSupport (fun x ↦ sol.vorticity x t) ∧
        HasCompactSupport (fun x ↦ sol.temperature x t)) ∧
      (∀ a b : ℝ, Icc a b ⊆ lifeSpan T → ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x x' : ℝ^2,
        ‖iteratedFDeriv ℝ k (fun y ↦ sol.vorticity y t) x -
            iteratedFDeriv ℝ k (fun y ↦ sol.vorticity y t) x'‖ ≤ C * ‖x - x'‖ ^ α ∧
          ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ sol.temperature y t) x -
            iteratedFDeriv ℝ (k + 1) (fun y ↦ sol.temperature y t) x'‖ ≤ C * ‖x - x'‖ ^ α) ∧
      (∀ j ≤ 3, ContinuousOn
        (fun p : ℝ^2 × ℝ ↦ iteratedFDeriv ℝ j (fun y ↦ sol.vorticity y p.2) p.1)
        (univ ×ˢ lifeSpan T)) ∧
      (∀ j ≤ 4, ContinuousOn
        (fun p : ℝ^2 × ℝ ↦ iteratedFDeriv ℝ j (fun y ↦ sol.temperature y p.2) p.1)
        (univ ×ˢ lifeSpan T)) ∧
      (IsReflectionSymmetric ω₀ θ₀ → ∀ t ∈ lifeSpan T,
        IsReflectionSymmetric (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) ∧
        ∀ x : ℝ^2, sol.vorticity (tangentialReflection x) t = -sol.vorticity x t ∧
          sol.temperature (tangentialReflection x) t = sol.temperature x t ∧
          sol.streamFunction (tangentialReflection x) t = -sol.streamFunction x t) := by
  obtain ⟨T, sol, hT, hreg, hd, hcont, hmax, huniq, hslice, hhol, hjω, hjθ, hsym⟩ :=
    exists_maximalSolutionOf (by omega) hα hα1 hdata
  refine ⟨T, sol, hT, hreg, hd, hcont, hmax, huniq, fun t ht ↦
    ⟨(hslice t ht).1.of_le (by exact_mod_cast hk),
      (hslice t ht).2.1.of_le (by exact_mod_cast (show 4 ≤ k + 1 by omega)),
      (hslice t ht).2.2.1, (hslice t ht).2.2.2⟩, hhol,
    fun j hj ↦ hjω j (by omega), fun j hj ↦ hjθ j (by omega), hsym⟩

end Boussinesq.HalfPlane
