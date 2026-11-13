/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.Topology
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Extending a real energy along a linear inclusion

A real energy on a normed space defines a signed extended energy on an
ambient space by assigning `+∞` outside the image of an injective linear
map, using Mathlib's `Function.extend`. Its real sublevels are exactly the
images of the original sublevels.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Convex

open Set

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Transport a real energy along a linear inclusion and assign `+∞`
outside its range. Injectivity identifies its finite values with the
original energy. -/
def linearImageEnergy (j : V →L[ℝ] H) (J : V → ℝ) : H → EReal :=
  Function.extend j (fun u ↦ (J u : EReal)) (fun _ ↦ ⊤)

/-- On the image of an injective inclusion, the signed real value is retained. -/
@[simp] theorem linearImageEnergy_apply (j : V →L[ℝ] H)
    (hj : Function.Injective j) (J : V → ℝ) (u : V) :
    linearImageEnergy j J (j u) = (J u : EReal) :=
  hj.extend_apply _ _ u

/-- Every point outside the included space has infinite energy. -/
theorem linearImageEnergy_eq_top_of_notMem (j : V →L[ℝ] H) (J : V → ℝ)
    {x : H} (hx : x ∉ range j) : linearImageEnergy j J x = ⊤ :=
  Function.extend_apply' _ _ _ hx

/-- Finiteness is exactly membership in the range, without a sign restriction. -/
theorem linearImageEnergy_ne_top_iff (j : V →L[ℝ] H)
    (hj : Function.Injective j) (J : V → ℝ) (x : H) :
    linearImageEnergy j J x ≠ ⊤ ↔ x ∈ range j := by
  constructor
  · intro h
    by_contra hx
    exact h (linearImageEnergy_eq_top_of_notMem j J hx)
  · rintro ⟨u, rfl⟩
    rw [linearImageEnergy_apply j hj]
    exact EReal.coe_ne_top _

/-- Extension by `+∞` of a real energy on a normed space is proper. Every value is a real
number or `+∞`, and the value at `j 0` is real, so `j` need not be injective. -/
theorem isProper_linearImageEnergy (j : V →L[ℝ] H) (J : V → ℝ) :
    IsProper (linearImageEnergy j J) := by
  classical
  refine ⟨fun x ↦ ?_, j 0, ?_⟩ <;> simp only [linearImageEnergy, Function.extend_def]
  · split_ifs
    · exact EReal.coe_ne_bot _
    · exact top_ne_bot
  · split_ifs with h
    · exact EReal.coe_ne_top _
    · exact absurd ⟨0, rfl⟩ h

/-- A finite real sublevel is precisely the image of the original sublevel. -/
theorem sublevel_linearImageEnergy (j : V →L[ℝ] H)
    (hj : Function.Injective j) (J : V → ℝ) (r : ℝ) :
    {x | linearImageEnergy j J x ≤ (r : EReal)} = j '' {u | J u ≤ r} := by
  ext x
  constructor
  · intro hx
    have hfin : linearImageEnergy j J x ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hx
    obtain ⟨u, rfl⟩ := (linearImageEnergy_ne_top_iff j hj J x).mp hfin
    refine ⟨u, ?_, rfl⟩
    change linearImageEnergy j J (j u) ≤ (r : EReal) at hx
    rw [linearImageEnergy_apply j hj] at hx
    exact EReal.coe_le_coe_iff.mp hx
  · rintro ⟨u, hu, rfl⟩
    change linearImageEnergy j J (j u) ≤ (r : EReal)
    rw [linearImageEnergy_apply j hj]
    exact EReal.coe_le_coe_iff.mpr hu

/-- A convex real energy remains convex after extension along a linear inclusion. -/
theorem convex_realEpigraph_linearImageEnergy (j : V →L[ℝ] H)
    (hj : Function.Injective j) {J : V → ℝ} (hJ : ConvexOn ℝ univ J) :
    Convex ℝ (realEpigraph (linearImageEnergy j J)) := by
  intro p hp q hq a b ha hb hab
  have hpfin : linearImageEnergy j J p.1 ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hp
  have hqfin : linearImageEnergy j J q.1 ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hq
  obtain ⟨u, hu⟩ := (linearImageEnergy_ne_top_iff j hj J p.1).mp hpfin
  obtain ⟨v, hv⟩ := (linearImageEnergy_ne_top_iff j hj J q.1).mp hqfin
  have hp' : J u ≤ p.2 := by
    change linearImageEnergy j J p.1 ≤ (p.2 : EReal) at hp
    rw [← hu, linearImageEnergy_apply j hj] at hp
    exact EReal.coe_le_coe_iff.mp hp
  have hq' : J v ≤ q.2 := by
    change linearImageEnergy j J q.1 ≤ (q.2 : EReal) at hq
    rw [← hv, linearImageEnergy_apply j hj] at hq
    exact EReal.coe_le_coe_iff.mp hq
  change linearImageEnergy j J (a • p.1 + b • q.1) ≤
    ((a * p.2 + b * q.2 : ℝ) : EReal)
  rw [← hu, ← hv, ← map_smul, ← map_smul, ← map_add, linearImageEnergy_apply j hj]
  exact EReal.coe_le_coe_iff.mpr ((hJ.2 (mem_univ u) (mem_univ v) ha hb hab).trans
    (add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb)))

end PDE.Analysis.Convex
