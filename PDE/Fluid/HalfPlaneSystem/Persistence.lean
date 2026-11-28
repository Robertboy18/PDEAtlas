/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.PersistenceCanonical
public import PDE.Fluid.HalfPlaneSystem.IterationHigher
public import PDE.Fluid.HalfPlaneSystem.Continuation

/-!
# Persistence of regularity and well-posedness at level `k` for half-plane systems

A solution of a half-plane system lives as long as its `C^{1,α} × C^{2,α}` norms stay bounded and
its support stays in the domain of the velocity law. This module proves that data with `k ≥ 2`
derivatives and a Hölder condition keep them on the whole life span: the higher norms cannot blow up
earlier.

Let `U` be a velocity law up to the radius `R₀`, `κ` a forcing coefficient and `0 < α < 1`. A
regular solution on a life span `[0, T)` whose data are `ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}` keeps this
regularity on the whole life span (`IsRegularSolutionOn.isRegularSolutionOfOn`). On
`[0, t₁] ⊂ [0, T)` the `C^{1,α} × C^{2,α}` norms are bounded and the supports lie in one disc of
radius `R < R₀`, so local existence at level `k` (`exists_isRegularSolutionOfOn_Ioo`) restarts from
every time of `[0, t₁]` with one lifespan `τ`, whatever the level-`k` norms at that time. By forward
uniqueness the restarted solution agrees with the given one on the closed half-plane
(`IsSolutionOn.eq_of_restart`); restarting at the times `0, τ/2, τ, …` covers `[0, t₁]` in finitely
many steps, with the support radius `R` throughout. The bound of the norms of order `k` on `[0, t₁]`
is therefore not explicit: it is the maximum over finitely many restarts.

In particular the maximal time at level `k` is the maximal time at level one, and the blow-up
alternative and the continuation criterion of `Maximal.lean` and `Continuation.lean` apply
unchanged. The library has the same theorem for the Boussinesq system
(`Boussinesq.HalfPlane.IsRegularSolutionOn.isRegularSolutionOfOn`).

## Main results

* `IsRegularSolutionOfOn.toIsRegularSolutionOn`: for `α ∈ [0, 1]`, solutions of order `k ≥ 1` are
  regular solutions of the local theorem.
* `IsSolutionOn.eq_of_restart`: a solution agrees on the closed half-plane with a solution restarted
  from its slices at a later time `t₀`, at the times of `[t₀, t₀ + τ)`.
* `IsRegularSolutionOn.exists_isHolderDataOf`: if the slices at time zero are data of order `k ≥ 2`,
  then on every `[0, t₁]` inside the life span the slices are data of order `k` with one support
  radius less than `R₀` and one bound.
* `IsRegularSolutionOn.isRegularSolutionOfOn`: persistence of `C^{k,α} × C^{k+1,α}`: such a solution
  is a regular solution of order `k` on the life span.

`exists_maximalSolutionOf` (`PersistenceMaximal.lean`) applies the persistence to the maximal
solution.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ENNReal Topology
open Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
  {Ch : ℝ → ℝ} {sol sol₁ : Fields} {I : Set ℝ} {α : ℝ}

/-- Regular solutions of order `k ≥ 1` are regular solutions of the local theorem. -/
theorem IsRegularSolutionOfOn.toIsRegularSolutionOn {k : ℕ}
    (h : IsRegularSolutionOfOn U κ R₀ k sol I α) (hk : 1 ≤ k) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsRegularSolutionOn U κ R₀ sol I α where
  toIsSolutionOn := h.toIsSolutionOn
  holderData a b hab := by
    obtain ⟨R, -, N, hRN⟩ := h.holderData a b hab
    exact ⟨R, 2 * N, fun t ht ↦ (hRN t ht).toIsHolderData hk hα0 hα1⟩

/-- **Agreement with a restarted solution.** If `sol₁` is a solution on `(-τ, τ)` whose data at
time zero are the slices of a solution `sol` at a time `t₀` of an order-connected set of times
`I`, then on the closed half-plane `sol` at a time `t ∈ I ∩ [t₀, t₀ + τ)` is `sol₁` at
`t - t₀`. -/
theorem IsSolutionOn.eq_of_restart (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (h : IsSolutionOn U κ R₀ sol I) (hI : I.OrdConnected) {t₀ τ : ℝ} (ht₀ : t₀ ∈ I)
    (h₁ : IsSolutionOn U κ R₀ sol₁ (Ioo (-τ) τ))
    (hd₁ : HasDataAt sol₁ 0 (fun x ↦ sol.vorticity x t₀) (fun x ↦ sol.temperature x t₀))
    {t : ℝ} (ht : t ∈ I) (htt₀ : t₀ ≤ t) (htτ : t < t₀ + τ) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol₁.vorticity x (t - t₀) ∧
      sol.temperature x t = sol₁.temperature x (t - t₀) := by
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
    simp only [Fields.shiftTime, add_neg_cancel]
    exact ⟨this.1.symm, this.2.symm⟩
  have := h'.eq_of_eq_at_of_le hU hκ hS₁ (hI.inter ordConnected_Ico)
    ⟨ht₀, le_rfl, by linarith⟩ hdata ⟨ht, htt₀, htτ⟩ htt₀ hx
  simpa [Fields.shiftTime, sub_eq_add_neg] using this

/-- **Uniform bounds of order `k` on compact intervals.** Let `sol` be a regular solution on the
life span `T` whose slices at time zero are data of order `k ≥ 2`. On every interval `[0, t₁]`
inside the life span its slices are data of order `k` with one support radius less than `R₀` and
one bound. So the norms of order `k` cannot blow up before the norms of the local theory.
Proof: on `[0, t₁]` the slices are in one class of the local theory, so local existence at
level `k` has one life span `τ` from every time. By induction on `m` the bound holds on
`[0, min t₁ (m τ/2)]`: restart at the end of the interval and use forward uniqueness. -/
theorem IsRegularSolutionOn.exists_isHolderDataOf (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {k : ℕ} (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1)
    {T : ℝ≥0∞} (h : IsRegularSolutionOn U κ R₀ sol (lifeSpan T) α) {R N : ℝ}
    (hd : IsHolderDataOf k (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    {t₁ : ℝ} (ht₁ : t₁ ∈ lifeSpan T) :
    ∃ R' < R₀, ∃ N' : ℝ, ∀ t ∈ Icc 0 t₁,
      IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R' N' := by
  have h0 : (0 : ℝ) ∈ lifeSpan T := zero_mem_lifeSpan (pos_of_mem_lifeSpan ht₁)
  have hsub : Icc 0 t₁ ⊆ lifeSpan T := (ordConnected_lifeSpan T).out h0 ht₁
  obtain ⟨R₁, N₁, h1⟩ := h.holderData 0 t₁ hsub
  obtain ⟨R₂, hR₂, hz⟩ := h.support 0 t₁ hsub
  have h1' (t : ℝ) (ht : t ∈ Icc 0 t₁) :
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R₂ (max N₁ 0) :=
    { (h1 t ht).mono le_rfl (le_max_left N₁ 0) with eq_zero := hz t ht }
  -- One life span `τ` of local existence at level `k` serves every time of `[0, t₁]`.
  obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOfOn_Ioo hU hκ hk hα hα1 hR₂
    (le_max_right N₁ 0)
  -- Induction on the number of steps of length `τ/2`: restart at the end of the interval
  -- already covered and use forward uniqueness.
  have key (m : ℕ) : ∃ N' : ℝ, ∀ t ∈ Icc 0 (min t₁ (m * (τ / 2))),
      IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R₂ N' := by
    induction m with
    | zero =>
      refine ⟨N, fun t ht ↦ ?_⟩
      have ht0 : t = 0 := le_antisymm (by simpa [min_eq_right ht₁.1] using ht.2) ht.1
      subst ht0
      exact hd.of_eq_zero (hz 0 ⟨le_rfl, ht₁.1⟩)
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
        h.toIsSolutionOn.eq_of_restart hU hκ (ordConnected_lifeSpan T) (hsub ht₀)
          hs₁.toIsSolutionOn hd₁ (hsub htI) htt₀.le htτ hx
      have hmem : t - t₀ ∈ Ioo (-τ) τ := ⟨by linarith, by linarith⟩
      exact (((hN'' (t - t₀) hmem).congr (fun x hx ↦ (hag x hx).1)
        (fun x hx ↦ (hag x hx).2)).of_eq_zero (hz t htI)).of_le le_rfl (le_max_right _ _)
  -- Finitely many steps cover `[0, t₁]`.
  obtain ⟨m, hm⟩ := exists_nat_ge (t₁ / (τ / 2))
  obtain ⟨N', hN'⟩ := key m
  have hmin : min t₁ (m * (τ / 2)) = t₁ :=
    min_eq_left ((div_le_iff₀ (by positivity)).mp hm)
  exact ⟨R₂, hR₂, N', fun t ht ↦ hN' t (by rwa [hmin])⟩

/-- **Persistence of regularity.** A regular solution on a life span whose slices at time zero
are data of order `k ≥ 2` is a regular solution of order `k` on the life span. So the life
span at level `k` is the life span of the local theory. Proof: the uniform bounds of order `k`
are `exists_isHolderDataOf`; near every time the solution agrees on the closed half-plane with
a regular solution of order `k` restarted shortly before, which gives the continuity in time
of the derivatives. -/
theorem IsRegularSolutionOn.isRegularSolutionOfOn (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {k : ℕ} (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1)
    {T : ℝ≥0∞} (h : IsRegularSolutionOn U κ R₀ sol (lifeSpan T) α) {R N : ℝ}
    (hd : IsHolderDataOf k (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N) :
    IsRegularSolutionOfOn U κ R₀ k sol (lifeSpan T) α := by
  have hI := ordConnected_lifeSpan T
  -- Near every time `t` there is a regular solution of order `k`, restarted at a time `t₀`
  -- shortly before `t`, whose life span covers a neighbourhood of `t`.
  have hlocal (t : ℝ) (ht : t ∈ lifeSpan T) : ∃ τ > 0, ∃ t₀ ∈ lifeSpan T,
      (∀ s ∈ lifeSpan T, |s - t| < τ / 2 → t₀ ≤ s ∧ s < t₀ + τ) ∧
      ∃ sol₁ : Fields, IsRegularSolutionOfOn U κ R₀ k sol₁ (Ioo (-τ) τ) α ∧
        HasDataAt sol₁ 0 (fun x ↦ sol.vorticity x t₀) (fun x ↦ sol.temperature x t₀) := by
    have h0 : (0 : ℝ) ∈ lifeSpan T := zero_mem_lifeSpan (pos_of_mem_lifeSpan ht)
    have hsub : Icc 0 t ⊆ lifeSpan T := hI.out h0 ht
    obtain ⟨R₁, N₁, h1⟩ := h.holderData 0 t hsub
    obtain ⟨R₂, hR₂, hz⟩ := h.support 0 t hsub
    obtain ⟨Rk, -, Nk, hk'⟩ := h.exists_isHolderDataOf hU hκ hk hα hα1 hd ht
    obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOfOn_Ioo hU hκ hk hα hα1 hR₂
      (le_max_right N₁ 0)
    have ht₀ : max 0 (t - τ / 2) ∈ Icc 0 t := ⟨le_max_left _ _, max_le ht.1 (by linarith)⟩
    have hd1 : IsHolderData (fun x ↦ sol.vorticity x (max 0 (t - τ / 2)))
        (fun x ↦ sol.temperature x (max 0 (t - τ / 2))) α R₂ (max N₁ 0) :=
      { (h1 _ ht₀).mono le_rfl (le_max_left N₁ 0) with eq_zero := hz _ ht₀ }
    obtain ⟨sol₁, hs₁, hd₁, -⟩ := hloc _ _ hd1 Nk ((hk' _ ht₀).of_eq_zero (hz _ ht₀))
    refine ⟨τ, hτ, max 0 (t - τ / 2), hsub ht₀, fun s hs hst ↦ ?_, sol₁, hs₁, hd₁⟩
    have h2 := abs_lt.mp hst
    exact ⟨max_le hs.1 (by linarith), by linarith [le_max_right 0 (t - τ / 2)]⟩
  -- By forward uniqueness the solution agrees with the restarted one on the closed half-plane.
  have hagree {τ t₀ : ℝ} (ht₀ : t₀ ∈ lifeSpan T) {sol₁ : Fields}
      (hs₁ : IsRegularSolutionOfOn U κ R₀ k sol₁ (Ioo (-τ) τ) α)
      (hd₁ : HasDataAt sol₁ 0 (fun x ↦ sol.vorticity x t₀) (fun x ↦ sol.temperature x t₀))
      {s : ℝ} (hs : s ∈ lifeSpan T) (hs₀ : t₀ ≤ s ∧ s < t₀ + τ) :
      EqOn (fun y ↦ sol.vorticity y s) (fun y ↦ sol₁.vorticity y (s - t₀)) H̄ ∧
        EqOn (fun y ↦ sol.temperature y s) (fun y ↦ sol₁.temperature y (s - t₀)) H̄ :=
    ⟨fun y hy ↦ (h.toIsSolutionOn.eq_of_restart hU hκ hI ht₀ hs₁.toIsSolutionOn hd₁ hs hs₀.1
      hs₀.2 hy).1, fun y hy ↦ (h.toIsSolutionOn.eq_of_restart hU hκ hI ht₀ hs₁.toIsSolutionOn
      hd₁ hs hs₀.1 hs₀.2 hy).2⟩
  have hmem {τ t₀ s : ℝ} (hs₀ : t₀ ≤ s ∧ s < t₀ + τ) : s - t₀ ∈ Ioo (-τ) τ :=
    ⟨by linarith [hs₀.1, hs₀.2], by linarith [hs₀.2]⟩
  refine
    { toIsSolutionOn := h.toIsSolutionOn
      holderData := fun a b hab ↦ ?_
      vorticity_uniform := fun j hj t ht ε hε ↦ ?_
      temperature_uniform := fun j hj t ht ε hε ↦ ?_ }
  · rcases lt_or_ge b a with hba | hab'
    · exact ⟨R₀ - 1, by linarith, 0, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)⟩
    obtain ⟨R', hR', N', hRN⟩ := h.exists_isHolderDataOf hU hκ hk hα hα1 hd
      (hab ⟨hab', le_rfl⟩)
    exact ⟨R', hR', N', fun t ht ↦ hRN t ⟨(hab ⟨le_rfl, hab'⟩).1.trans ht.1, ht.2⟩⟩
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

end HalfPlaneSystem
