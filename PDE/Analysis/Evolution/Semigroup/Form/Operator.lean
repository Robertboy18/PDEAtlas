/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple

/-!
# The pivot-space operator associated with an energy form

For a dense continuous inclusion `j : V → H` and a bounded bilinear form `B` on `V`,
the partial operator `A` on `H` is defined by
`A (j u) = f` exactly when `B u v = -⟪f, j v⟫` for every `v`.
Density makes the value unique; injectivity of `j` makes the energy representative unique.
The sign convention gives the generator of `u' + B u = 0`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution.GelfandTriple

open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (T : GelfandTriple (V := V) (H := H)) (B : V →L[ℝ] StrongDual ℝ V)

/-- The graph of the negative operator represented by the form in the pivot space. -/
def formGraph : Submodule ℝ (H × H) where
  carrier := {p | ∃ u, T.inclusion u = p.1 ∧ B u = -T.pivotToDual p.2}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro p q ⟨u, hu, hBu⟩ ⟨v, hv, hBv⟩
    exact ⟨u + v, by simpa using congrArg₂ (· + ·) hu hv,
      by simp [hBu, hBv, add_comm]⟩
  smul_mem' := by
    rintro c p ⟨u, hu, hBu⟩
    exact ⟨c • u, by simpa using congrArg (c • ·) hu, by simp [hBu]⟩

/-- The form relation has no nonzero value above zero. -/
theorem formGraph_zero (p : H × H) (hp : p ∈ T.formGraph B) (hzero : p.1 = 0) :
    p.2 = 0 := by
  obtain ⟨u, hu, hBu⟩ := hp
  have hu0 : u = 0 := T.injective (by simpa using hu.trans hzero)
  apply T.pivotToDual_injective
  simpa [hu0] using (neg_eq_zero.mp (by simpa [hu0] using hBu.symm))

/-- The partial pivot-space operator associated with the negative of an energy form. -/
def formOperator : H →ₗ.[ℝ] H :=
  (T.formGraph B).toLinearPMap

/-- The constructed partial operator has exactly the prescribed weak graph. -/
theorem formOperator_graph :
    (T.formOperator B).graph = T.formGraph B :=
  Submodule.toLinearPMap_graph_eq _ (T.formGraph_zero B)

/-- Graph membership expresses the weak equation, including the energy representative. -/
theorem mem_formOperator_graph_iff (x f : H) :
    (x, f) ∈ (T.formOperator B).graph ↔
      ∃ u, T.inclusion u = x ∧ B u = -T.pivotToDual f := by
  rw [T.formOperator_graph]
  rfl

/-- The domain consists exactly of energy vectors whose form is represented in the pivot space. -/
theorem mem_formOperator_domain_iff (x : H) :
    x ∈ (T.formOperator B).domain ↔
      ∃ u, T.inclusion u = x ∧ ∃ f, B u = -T.pivotToDual f := by
  change x ∈ (T.formGraph B).map (LinearMap.fst ℝ H H) ↔ _
  constructor
  · rintro ⟨⟨y, f⟩, ⟨u, hu, hBu⟩, hxy⟩
    exact ⟨u, hu.trans hxy, f, hBu⟩
  · rintro ⟨u, hu, f, hBu⟩
    exact ⟨(x, f), ⟨u, hu, hBu⟩, rfl⟩

/-- Every domain vector has an energy representative satisfying the generator equation. -/
theorem formOperator_spec (x : (T.formOperator B).domain) :
    ∃ u, T.inclusion u = x ∧ B u = -T.pivotToDual (T.formOperator B x) :=
  (T.mem_formOperator_graph_iff B _ _).1 ((T.formOperator B).mem_graph x)

/-- A weak graph equation identifies the value of the partial operator. -/
theorem formOperator_eq (x : (T.formOperator B).domain) (u : V) (f : H)
    (hu : T.inclusion u = x) (hBu : B u = -T.pivotToDual f) :
    T.formOperator B x = f := by
  obtain ⟨v, hv, hBv⟩ := T.formOperator_spec B x
  have huv : v = u := T.injective (hv.trans hu.symm)
  exact T.pivotToDual_injective (neg_injective (hBv.symm.trans (huv ▸ hBu)))

end PDE.Analysis.Evolution.GelfandTriple
