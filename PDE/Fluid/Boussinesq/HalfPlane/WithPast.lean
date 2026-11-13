/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Persistence

/-!
# The maximal solution continued into the past

The maximal solution of `exists_maximalSolutionOf` lives on the life span `[0, T)`; the local
solution of `exists_isRegularSolutionOfOn_Ioo` lives on `(-τ, τ)`. By forward uniqueness the two
agree on the closed half-plane on `[0, min(τ, T))`, so their representatives of order `k` agree on
the whole plane there, and the fields that follow the local solution before time zero and the
maximal solution after it form a regular solution of order `k` on the open set of times
`(-τ, T)` (`exists_maximalSolutionOf_withPast`). Such a solution has ordinary time derivatives at
`t = 0` and open sets of times around every time of `[0, T)`, which changes of time variable and
time derivatives of spatial jets need.

## Main results

* `IsRegularSolutionOfOn.mono_set`, `IsRegularSolutionOfOn.glue`: restriction and gluing of
  regular solutions of order `k`.
* `exists_maximalSolutionOf_withPast`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {k : ℕ} {sol A B : VorticityStreamFields} {I J : Set ℝ} {α : ℝ}

namespace IsRegularSolutionOfOn

/-- Regular solutions of order `k` restrict to smaller sets of times. -/
theorem mono_set (h : IsRegularSolutionOfOn k sol I α) (hJ : J ⊆ I) :
    IsRegularSolutionOfOn k sol J α where
  toIsSolutionOn := h.toIsSolutionOn.mono hJ
  holderData a b hab := h.holderData a b (hab.trans hJ)
  vorticity_uniform j hj t ht ε hε := by
    obtain ⟨δ, hδ, h'⟩ := h.vorticity_uniform j hj t (hJ ht) ε hε
    exact ⟨δ, hδ, fun s hs hst x hx ↦ h' s (hJ hs) hst x hx⟩
  temperature_uniform j hj t ht ε hε := by
    obtain ⟨δ, hδ, h'⟩ := h.temperature_uniform j hj t (hJ ht) ε hε
    exact ⟨δ, hδ, fun s hs hst x hx ↦ h' s (hJ hs) hst x hx⟩

/-- **Gluing two regular solutions of order `k`.** Fields that agree with a regular solution `A`
of order `k` on the times before `d` and with a regular solution `B` of order `k` on the times
after `c < d` are a regular solution of order `k`. -/
theorem glue {c d : ℝ} (hcd : c < d) (hA : IsRegularSolutionOfOn k A (I ∩ Iio d) α)
    (hB : IsRegularSolutionOfOn k B (I ∩ Ioi c) α) (hsA : ∀ s < d, AgreeAt sol A s)
    (hsB : ∀ s > c, AgreeAt sol B s) (hk : 1 ≤ k) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsRegularSolutionOfOn k sol I α := by
  have h1 : IsRegularSolutionOn sol I α := IsRegularSolutionOn.glue hcd
    (hA.toIsRegularSolutionOn hk hα0 hα1) (hB.toIsRegularSolutionOn hk hα0 hα1) hsA hsB
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
  have hd' {t δ s : ℝ} (hst : |s - t| < min δ (d - t)) : s < d := by
    linarith [(abs_lt.mp (hst.trans_le (min_le_right _ _))).2]
  have hc' {t δ s : ℝ} (hst : |s - t| < min δ (t - c)) : c < s := by
    linarith [(abs_lt.mp (hst.trans_le (min_le_right _ _))).1]
  have hω {X : VorticityStreamFields} {s : ℝ} (h : AgreeAt sol X s) :
      (fun x ↦ sol.vorticity x s) = fun x ↦ X.vorticity x s := funext fun x ↦ (h x).1
  have hθ {X : VorticityStreamFields} {s : ℝ} (h : AgreeAt sol X s) :
      (fun x ↦ sol.temperature x s) = fun x ↦ X.temperature x s := funext fun x ↦ (h x).2.1
  refine
    { toIsSolutionOn := h1.toIsSolutionOn
      holderData := fun a b hab ↦ ?_
      vorticity_uniform := fun j hj t ht ε hε ↦ ?_
      temperature_uniform := fun j hj t ht ε hε ↦ ?_ }
  · obtain ⟨R₁, N₁, hR₁⟩ := hA.holderData a (min b m) (hJ₁ hab)
    obtain ⟨R₂, N₂, hR₂⟩ := hB.holderData (max a m) b (hJ₂ hab)
    refine ⟨max R₁ R₂, max N₁ N₂, fun t ht ↦ ?_⟩
    rcases hcases ht with ⟨ht', htd⟩ | ⟨ht', htc⟩
    · rw [hω (hsA t htd), hθ (hsA t htd)]
      exact (hR₁ t ht').of_le (le_max_left _ _) (le_max_left _ _)
    · rw [hω (hsB t htc), hθ (hsB t htc)]
      exact (hR₂ t ht').of_le (le_max_right _ _) (le_max_right _ _)
  · rcases lt_or_ge t d with htd | htd
    · obtain ⟨δ, hδ, h'⟩ := hA.vorticity_uniform j hj t ⟨ht, htd⟩ ε hε
      refine ⟨min δ (d - t), lt_min hδ (by linarith), fun s hs hst x hx ↦ ?_⟩
      rw [hω (hsA s (hd' hst)), hω (hsA t htd)]
      exact h' s ⟨hs, hd' hst⟩ (hst.trans_le (min_le_left _ _)) x hx
    · have htc : c < t := hcd.trans_le htd
      obtain ⟨δ, hδ, h'⟩ := hB.vorticity_uniform j hj t ⟨ht, htc⟩ ε hε
      refine ⟨min δ (t - c), lt_min hδ (by linarith), fun s hs hst x hx ↦ ?_⟩
      rw [hω (hsB s (hc' hst)), hω (hsB t htc)]
      exact h' s ⟨hs, hc' hst⟩ (hst.trans_le (min_le_left _ _)) x hx
  · rcases lt_or_ge t d with htd | htd
    · obtain ⟨δ, hδ, h'⟩ := hA.temperature_uniform j hj t ⟨ht, htd⟩ ε hε
      refine ⟨min δ (d - t), lt_min hδ (by linarith), fun s hs hst x hx ↦ ?_⟩
      rw [hθ (hsA s (hd' hst)), hθ (hsA t htd)]
      exact h' s ⟨hs, hd' hst⟩ (hst.trans_le (min_le_left _ _)) x hx
    · have htc : c < t := hcd.trans_le htd
      obtain ⟨δ, hδ, h'⟩ := hB.temperature_uniform j hj t ⟨ht, htc⟩ ε hε
      refine ⟨min δ (t - c), lt_min hδ (by linarith), fun s hs hst x hx ↦ ?_⟩
      rw [hθ (hsB s (hc' hst)), hθ (hsB t htc)]
      exact h' s ⟨hs, hc' hst⟩ (hst.trans_le (min_le_left _ _)) x hx

end IsRegularSolutionOfOn

/-- The continuation quantity depends only on the velocity and the temperature on the open upper
half-plane at the times of the life span. -/
theorem continuationIntegral_congr {sol' : VorticityStreamFields} {T : ℝ≥0∞}
    (hu : ∀ t ∈ lifeSpan T, ∀ x ∈ upperHalfPlane,
      vorticityStreamVelocity sol x t = vorticityStreamVelocity sol' x t)
    (hθ : ∀ t ∈ lifeSpan T, ∀ x ∈ upperHalfPlane, sol.temperature x t = sol'.temperature x t) :
    continuationIntegral sol T = continuationIntegral sol' T := by
  have hmeas : MeasurableSet (lifeSpan T) :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  refine setLIntegral_congr_fun hmeas fun t ht ↦ ?_
  have h1 : ∀ x ∈ upperHalfPlane, fderiv ℝ (fun y ↦ vorticityStreamVelocity sol y t) x =
      fderiv ℝ (fun y ↦ vorticityStreamVelocity sol' y t) x := fun x hx ↦
    (eventuallyEq_of_mem (isOpen_upperHalfPlane.mem_nhds hx) fun y hy ↦ hu t ht y hy).fderiv_eq
  have h2 : ∀ x ∈ upperHalfPlane, fderiv ℝ (fun y ↦ sol.temperature y t) x =
      fderiv ℝ (fun y ↦ sol'.temperature y t) x := fun x hx ↦
    (eventuallyEq_of_mem (isOpen_upperHalfPlane.mem_nhds hx) fun y hy ↦ hθ t ht y hy).fderiv_eq
  congr 1
  · exact iSup_congr fun x ↦ iSup_congr fun hx ↦ by rw [h1 x hx]
  · exact iSup_congr fun x ↦ iSup_congr fun hx ↦ by rw [h2 x hx]

/-- **The maximal solution continued into the past.** For data `ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}`
on the closed half-plane (`IsHolderDataOf k`), `k ≥ 2`, `0 < α < 1`, there are a life span
`T ∈ (0, ∞]`, a time `τ > 0` and a regular solution `sol` of order `k` on the open set of times
`(-τ, T)` with the data at time zero, whose representative `canonicalOf k sol` satisfies the
continuation criterion on `[0, T)`, and whose slices on `[0, T)` stay in the symmetry class when the
data are in it. -/
theorem exists_maximalSolutionOf_withPast {ω₀ θ₀ : ℝ^2 → ℝ} {R N : ℝ} (hk : 2 ≤ k)
    (hα : 0 < α) (hα1 : α < 1) (hdata : IsHolderDataOf k ω₀ θ₀ α R N) :
    ∃ (T : ℝ≥0∞) (τ : ℝ) (sol : VorticityStreamFields), 0 < T ∧ 0 < τ ∧
      IsRegularSolutionOfOn k sol {t | -τ < t ∧ ENNReal.ofReal t < T} α ∧
      HasDataAt sol 0 ω₀ θ₀ ∧
      (T ≠ ⊤ → continuationIntegral (canonicalOf k sol) T = ⊤) ∧
      (IsReflectionSymmetric ω₀ θ₀ → ∀ t ∈ lifeSpan T,
        IsReflectionSymmetric (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t)) := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨T, P, hT, hP, hdP, hcont, -, -, -, -, -, -, hsymP⟩ :=
    exists_maximalSolutionOf hk hα hα1 hdata
  have hN : 0 ≤ N := hdata.nonneg
  have hd1 : IsHolderData ω₀ θ₀ α (max R 0) (2 * N) :=
    (hdata.toIsHolderData hk1 hα.le hα1.le).mono (le_max_left _ _) le_rfl
  obtain ⟨τ, hτ, hloc⟩ := exists_isRegularSolutionOfOn_Ioo (k := k) (N := 2 * N) hk hα hα1
    (le_max_right R 0) (by positivity)
  obtain ⟨S, hS, hdS, -, -⟩ := hloc ω₀ θ₀ hd1 N (hdata.of_le (le_max_left _ _) le_rfl)
  obtain ⟨r, -, hr, hrT⟩ := ENNReal.lt_iff_exists_real_btwn.mp hT
  set d := min r τ with hd
  have hd0 : 0 < d := lt_min (ENNReal.ofReal_pos.mp hr) hτ
  have hdτ : d ≤ τ := min_le_right _ _
  have hdT : ∀ s, s < d → ENNReal.ofReal s < T := fun s hs ↦
    (ENNReal.ofReal_le_ofReal (hs.le.trans (min_le_left _ _))).trans_lt hrT
  -- forward uniqueness on `[0, d)`
  have hagree : ∀ s, 0 ≤ s → s < d → ∀ x : ℝ^2, 0 ≤ x 1 →
      P.vorticity x s = S.vorticity x s ∧ P.temperature x s = S.temperature x s := by
    intro s hs0 hsd x hx
    have hsub1 : Ico 0 d ⊆ lifeSpan T := fun u hu ↦ ⟨hu.1, hdT u hu.2⟩
    have hsub2 : Ico 0 d ⊆ Ioo (-τ) τ := fun u hu ↦ ⟨by linarith [hu.1], hu.2.trans_le hdτ⟩
    refine (hP.toIsSolutionOn.mono hsub1).eq_of_hasDataAt (hS.toIsSolutionOn.mono hsub2)
      ordConnected_Ico ⟨le_rfl, hd0⟩ (fun y hy ↦ ⟨(hdP y hy).1.trans (hdS y hy).1.symm,
        (hdP y hy).2.trans (hdS y hy).2.symm⟩) ⟨hs0, hsd⟩ hs0 hx
  have hstream : ∀ s, 0 ≤ s → s < d → ∀ x : ℝ^2, 0 ≤ x 1 →
      P.streamFunction x s = S.streamFunction x s := by
    intro s hs0 hsd x hx
    rw [hP.stream s ⟨hs0, hdT s hsd⟩ x hx,
      hS.stream s ⟨by linarith, hsd.trans_le hdτ⟩ x hx,
      GreenFunction.halfSpaceGreenPotential_congr fun y hy ↦
        (hagree s hs0 hsd y (le_of_lt hy)).1]
  -- the glued fields
  let Q : VorticityStreamFields :=
    { vorticity := fun x t ↦ if t < 0 then S.vorticity x t else P.vorticity x t
      temperature := fun x t ↦ if t < 0 then S.temperature x t else P.temperature x t
      streamFunction := fun x t ↦ if t < 0 then S.streamFunction x t else P.streamFunction x t }
  have hQP {t : ℝ} (ht : 0 ≤ t) (x : ℝ^2) : Q.vorticity x t = P.vorticity x t ∧
      Q.temperature x t = P.temperature x t ∧ Q.streamFunction x t = P.streamFunction x t := by
    simp only [Q, not_lt.2 ht, ↓reduceIte, and_self]
  have hsA : ∀ s < d, AgreeAt (canonicalOf k Q) (canonicalOf k S) s := by
    intro s hsd x
    rcases lt_or_ge s 0 with hs0 | hs0
    · refine canonicalOf_eq_of_eqOn (fun y _ ↦ ?_) (fun y _ ↦ ?_) (fun y _ ↦ ?_) x <;>
        simp only [Q, hs0, ↓reduceIte]
    · exact canonicalOf_eq_of_eqOn (fun y hy ↦ (hQP hs0 y).1.trans (hagree s hs0 hsd y hy).1)
        (fun y hy ↦ (hQP hs0 y).2.1.trans (hagree s hs0 hsd y hy).2)
        (fun y hy ↦ (hQP hs0 y).2.2.trans (hstream s hs0 hsd y hy)) x
  have hsB : ∀ s > 0, AgreeAt (canonicalOf k Q) (canonicalOf k P) s := fun s hs x ↦
    canonicalOf_eq_of_eqOn (fun y _ ↦ (hQP hs.le y).1) (fun y _ ↦ (hQP hs.le y).2.1)
      (fun y _ ↦ (hQP hs.le y).2.2) x
  set J := {t : ℝ | -τ < t ∧ ENNReal.ofReal t < T}
  have hA : IsRegularSolutionOfOn k (canonicalOf k S) (J ∩ Iio d) α :=
    (hS.canonicalOf hk1 (uniqueDiffOn_Ioo _ _)).mono_set fun t ht ↦
      ⟨ht.1.1, (show t < d from ht.2).trans_le hdτ⟩
  have hB : IsRegularSolutionOfOn k (canonicalOf k P) (J ∩ Ioi 0) α :=
    (hP.canonicalOf hk1 (uniqueDiffOn_lifeSpan T)).mono_set fun t ht ↦
      ⟨le_of_lt (show 0 < t from ht.2), ht.1.2⟩
  have hsol : IsRegularSolutionOfOn k (canonicalOf k Q) J α :=
    IsRegularSolutionOfOn.glue hd0 hA hB hsA hsB hk1 hα.le hα1.le
  refine ⟨T, τ, canonicalOf k Q, hT, hτ, hsol, fun x hx ↦ ?_, fun hTt ↦ ?_, fun hs t ht ↦ ?_⟩
  · rw [canonicalOf_vorticity_of_nonneg hx, canonicalOf_temperature_of_nonneg hx,
      (hQP le_rfl x).1, (hQP le_rfl x).2.1]
    exact hdP x hx
  · rw [← hcont hTt]
    refine continuationIntegral_congr (fun t ht x hx ↦ ?_) (fun t ht x hx ↦ ?_)
    · rw [vorticityStreamVelocity_canonicalOf hx, vorticityStreamVelocity_canonicalOf hx]
      have hψ : (fun y ↦ Q.streamFunction y t) = fun y ↦ P.streamFunction y t :=
        funext fun y ↦ (hQP ht.1 y).2.2
      simp only [vorticityStreamVelocity, hψ]
    · have hx' : 0 ≤ x 1 := le_of_lt hx
      rw [canonicalOf_temperature_of_nonneg hx', canonicalOf_temperature_of_nonneg hx',
        (hQP ht.1 x).2.1]
  · have h := (hsymP hs t ht).1
    have hR {x : ℝ^2} (hx : 0 ≤ x 1) : 0 ≤ tangentialReflection x 1 := by
      rwa [tangentialReflection_apply_one]
    have hω {x : ℝ^2} (hx : 0 ≤ x 1) : (canonicalOf k Q).vorticity x t = P.vorticity x t := by
      rw [canonicalOf_vorticity_of_nonneg hx, (hQP ht.1 x).1]
    have hθ {x : ℝ^2} (hx : 0 ≤ x 1) : (canonicalOf k Q).temperature x t =
        P.temperature x t := by
      rw [canonicalOf_temperature_of_nonneg hx, (hQP ht.1 x).2.1]
    exact ⟨fun x hx ↦ by simpa only [hω hx, hω (hR hx)] using h.vorticity_odd x hx,
      fun x hx ↦ by simpa only [hθ hx, hθ (hR hx)] using h.temperature_even x hx,
      fun x hx0 hx ↦ by simpa only [hθ hx] using h.temperature_axis x hx0 hx⟩

end Boussinesq.HalfPlane
