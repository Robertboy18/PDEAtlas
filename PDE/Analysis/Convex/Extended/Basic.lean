/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.EReal.Operations

/-!
# Convex energies with signed extended values

The real-height epigraph lets us use ordinary convex sets without imposing a vector-space
structure on `EReal`. An energy is proper when it never takes the value `-∞` and is finite
somewhere. Negative finite values and `+∞` remain part of the energy throughout.

The epigraph condition is equivalent to the usual extended convexity inequality. The endpoint
weights are treated separately so that zero times an infinite value causes no ambiguity.

Evans, §9.6.1, works with convex energies `I : H → (-∞, +∞]` that are proper, that is, not
identically `+∞`. Our `IsProper` is the same condition for an `EReal`-valued energy, and
convexity of `realEpigraph I` replaces his convexity inequality by `convex_realEpigraph_iff`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, the definitions of convex and proper functions,
  p. 560. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Convex

variable {E : Type*}

/-- A proper extended energy has no value `-∞` and has at least one finite value. -/
def IsProper (I : E → EReal) : Prop :=
  (∀ x, I x ≠ ⊥) ∧ ∃ x, I x ≠ ⊤

/-- The epigraph with real heights, even when the energy itself can equal `+∞`. -/
def realEpigraph (I : E → EReal) : Set (E × ℝ) :=
  {p | I p.1 ≤ (p.2 : EReal)}

/-- Properness supplies a point whose energy is a real number. -/
theorem IsProper.exists_eq_coe {I : E → EReal} (hI : IsProper I) :
    ∃ (x : E) (r : ℝ), I x = (r : EReal) := by
  obtain ⟨x, hx⟩ := hI.2
  exact ⟨x, (I x).toReal, (EReal.coe_toReal hx (hI.1 x)).symm⟩

/-- A finite-valued perturbation preserves properness, without a sign restriction. -/
theorem IsProper.add_real {I : E → EReal} (hI : IsProper I) (q : E → ℝ) :
    IsProper (fun x ↦ I x + (q x : EReal)) := by
  refine ⟨fun x ↦ ?_, ?_⟩
  · change I x + (q x : EReal) ≠ ⊥
    simp only [ne_eq, EReal.add_eq_bot_iff, not_or]
    exact ⟨hI.1 x, EReal.coe_ne_bot _⟩
  · obtain ⟨x, r, hx⟩ := hI.exists_eq_coe
    refine ⟨x, ?_⟩
    change I x + (q x : EReal) ≠ ⊤
    rw [hx, ← EReal.coe_add]
    exact EReal.coe_ne_top _

/-- A real-valued energy on a nonempty space is proper after coercion. -/
theorem isProper_coeReal [Nonempty E] (f : E → ℝ) :
    IsProper (fun x ↦ (f x : EReal)) := by
  refine ⟨fun x ↦ EReal.coe_ne_bot _, ?_⟩
  obtain ⟨x⟩ := ‹Nonempty E›
  exact ⟨x, EReal.coe_ne_top _⟩

variable [AddCommGroup E] [Module ℝ E]

/-- The convex epigraph controls every convex combination of finite epigraph points. -/
theorem le_of_mem_realEpigraph {I : E → EReal}
    (hI : Convex ℝ (realEpigraph I)) {x y : E} {r s a b : ℝ}
    (hx : I x ≤ (r : EReal)) (hy : I y ≤ (s : EReal))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    I (a • x + b • y) ≤ ((a * r + b * s : ℝ) : EReal) := by
  exact hI (x := (x, r)) (y := (y, s)) hx hy ha hb hab

/-- Real sublevels of an energy with convex epigraph are convex. -/
theorem convex_sublevel {I : E → EReal} (hI : Convex ℝ (realEpigraph I)) (r : ℝ) :
    Convex ℝ {x | I x ≤ (r : EReal)} := by
  intro x hx y hy a b ha hb hab
  change I (a • x + b • y) ≤ (r : EReal)
  have h := le_of_mem_realEpigraph hI hx hy ha hb hab
  simpa only [← add_mul, hab, one_mul] using h

/-- Convexity of the real epigraph is exactly the extended weighted convexity inequality. -/
theorem convex_realEpigraph_iff {I : E → EReal} (hbot : ∀ x, I x ≠ ⊥) :
    Convex ℝ (realEpigraph I) ↔
      ∀ (x y : E) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
        I (a • x + b • y) ≤ (a : EReal) * I x + (b : EReal) * I y := by
  constructor
  · intro hI x y a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by simpa [ha0] using hab
      simp [ha0, hb1]
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by simpa [hb0] using hab
      simp [ha1, hb0]
    have hmul (c : ℝ) (hc : 0 ≤ c) (z : E) : (c : EReal) * I z ≠ ⊥ :=
      (EReal.mul_ne_bot _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hbot z),
          Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.2 hc)⟩
    by_cases hx : I x = ⊤
    · rw [hx, EReal.coe_mul_top_of_pos (lt_of_le_of_ne ha (Ne.symm ha0)),
        EReal.top_add_of_ne_bot (hmul b hb y)]
      exact le_top
    by_cases hy : I y = ⊤
    · rw [hy, EReal.coe_mul_top_of_pos (lt_of_le_of_ne hb (Ne.symm hb0)),
        EReal.add_top_of_ne_bot (hmul a ha x)]
      exact le_top
    have hx' := EReal.coe_toReal hx (hbot x)
    have hy' := EReal.coe_toReal hy (hbot y)
    have h := le_of_mem_realEpigraph hI hx'.symm.le hy'.symm.le ha hb hab
    simpa only [EReal.coe_add, EReal.coe_mul, hx', hy'] using h
  · intro hI p hp q hq a b ha hb hab
    have hp' : I p.1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hp
    have hq' : I q.1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hq
    have hpcoe := EReal.coe_toReal hp' (hbot p.1)
    have hqcoe := EReal.coe_toReal hq' (hbot q.1)
    have hpReal : (I p.1).toReal ≤ p.2 := by
      exact EReal.coe_le_coe_iff.1 (hpcoe.le.trans hp)
    have hqReal : (I q.1).toReal ≤ q.2 := by
      exact EReal.coe_le_coe_iff.1 (hqcoe.le.trans hq)
    change I (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
    refine (hI p.1 q.1 a b ha hb hab).trans ?_
    rw [← hpcoe, ← hqcoe, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2
      (add_le_add (mul_le_mul_of_nonneg_left hpReal ha)
        (mul_le_mul_of_nonneg_left hqReal hb))

/-- Adding a real convex function preserves convexity of the extended epigraph. -/
theorem convex_realEpigraph_add_real {I : E → EReal} (hbot : ∀ x, I x ≠ ⊥)
    (hI : Convex ℝ (realEpigraph I)) {q : E → ℝ} (hq : ConvexOn ℝ Set.univ q) :
    Convex ℝ (realEpigraph (fun x ↦ I x + (q x : EReal))) := by
  intro p hp s hs a b ha hb hab
  have hpfin : I p.1 ≠ ⊤ := by
    intro h
    have := hp
    change I p.1 + (q p.1 : EReal) ≤ (p.2 : EReal) at this
    rw [h, EReal.top_add_coe] at this
    exact EReal.coe_ne_top _ (top_le_iff.1 this)
  have hsfin : I s.1 ≠ ⊤ := by
    intro h
    have := hs
    change I s.1 + (q s.1 : EReal) ≤ (s.2 : EReal) at this
    rw [h, EReal.top_add_coe] at this
    exact EReal.coe_ne_top _ (top_le_iff.1 this)
  have hpcoe := EReal.coe_toReal hpfin (hbot p.1)
  have hscoe := EReal.coe_toReal hsfin (hbot s.1)
  have hpReal : (I p.1).toReal + q p.1 ≤ p.2 := by
    change I p.1 + (q p.1 : EReal) ≤ (p.2 : EReal) at hp
    rw [← hpcoe, ← EReal.coe_add] at hp
    exact EReal.coe_le_coe_iff.1 hp
  have hsReal : (I s.1).toReal + q s.1 ≤ s.2 := by
    change I s.1 + (q s.1 : EReal) ≤ (s.2 : EReal) at hs
    rw [← hscoe, ← EReal.coe_add] at hs
    exact EReal.coe_le_coe_iff.1 hs
  have henergy := le_of_mem_realEpigraph hI hpcoe.symm.le hscoe.symm.le ha hb hab
  have hqcomb := hq.2 (Set.mem_univ p.1) (Set.mem_univ s.1) ha hb hab
  change I (a • p.1 + b • s.1) + (q (a • p.1 + b • s.1) : EReal) ≤
    ((a * p.2 + b * s.2 : ℝ) : EReal)
  refine (add_le_add henergy (le_refl (q (a • p.1 + b • s.1) : EReal))).trans ?_
  rw [← EReal.coe_add]
  apply EReal.coe_le_coe_iff.2
  have hpbound := mul_le_mul_of_nonneg_left hpReal ha
  have hsbound := mul_le_mul_of_nonneg_left hsReal hb
  simp only [smul_eq_mul] at hqcomb
  linarith

/-- The real epigraph of a convex real-valued function remains convex when its values are
viewed in the extended reals. -/
theorem convex_realEpigraph_coeReal {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    Convex ℝ (realEpigraph (fun x ↦ (f x : EReal))) := by
  apply (convex_realEpigraph_iff (fun x ↦ EReal.coe_ne_bot (f x))).2
  intro x y a b ha hb hab
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.2 (hf.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab)

end PDE.Analysis.Convex
