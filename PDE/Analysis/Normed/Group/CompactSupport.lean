/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A common support radius

Two compactly supported functions on a normed group vanish outside one ball
(`HasCompactSupport.exists_common_radius`). This is the form for two functions of Mathlib's
`HasCompactSupport.exists_pos_le_norm`; Cauchy data, a displacement and a velocity, are the
typical pair. The codomains may differ and need only a zero.
-/

@[expose] public section

/-- Two compactly supported functions on a normed group vanish outside one ball of positive
radius. -/
theorem HasCompactSupport.exists_common_radius {E α β : Type*} [NormedAddGroup E] [Zero α]
    [Zero β] {g : E → α} {h : E → β} (hg : HasCompactSupport g) (hh : HasCompactSupport h) :
    ∃ R, 0 < R ∧ (∀ x, R < ‖x‖ → g x = 0) ∧ ∀ x, R < ‖x‖ → h x = 0 := by
  obtain ⟨Rg, hRg, hg⟩ := hg.exists_pos_le_norm
  obtain ⟨Rh, -, hh⟩ := hh.exists_pos_le_norm
  exact ⟨max Rg Rh, hRg.trans_le (le_max_left Rg Rh),
    fun x hx ↦ hg x ((le_max_left Rg Rh).trans hx.le),
    fun x hx ↦ hh x ((le_max_right Rg Rh).trans hx.le)⟩
