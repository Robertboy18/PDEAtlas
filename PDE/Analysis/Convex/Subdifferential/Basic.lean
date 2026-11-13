/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.Topology
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# The Hilbert subdifferential of a signed extended energy

The subdifferential is a set of supporting vectors, rather than a chosen gradient. Its defining
inequality uses the extended energy at every competitor, including competitors with
infinite energy. For a proper energy the existence of a supporting vector forces finiteness
at the base point. Each nonempty fiber is closed and convex, and the relation is monotone.

The subdifferential is Evans's (1) in §9.6.1. Parts (i), (ii) and (iii) of his Theorem 1 are
`ne_top_of_mem_subdifferential`, `subdifferential_monotone` and `zero_mem_subdifferential_iff`;
they use properness at most, and neither convexity nor lower semicontinuity. Part (iv) is
`existsUnique_subdifferential_resolvent`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, the definition (1) of the subdifferential,
  p. 560, and Theorem 1(i)-(iii) and steps 1-3 of its proof, p. 561.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Supporting vectors for an extended energy at a point. -/
def subdifferential (I : H → EReal) (u : H) : Set H :=
  {v | ∀ w, I u + (inner ℝ v (w - u) : EReal) ≤ I w}

/-- Points with at least one supporting vector. This can be smaller than the finite domain. -/
def subdifferentialDomain (I : H → EReal) : Set H :=
  {u | (subdifferential I u).Nonempty}

/-- A proper energy is finite wherever a supporting vector exists. -/
theorem ne_top_of_mem_subdifferential {I : H → EReal} (hI : IsProper I)
    {u v : H} (hv : v ∈ subdifferential I u) : I u ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hI.2
  intro hu
  have h := hv w
  rw [hu, EReal.top_add_coe] at h
  exact hw (top_le_iff.1 h)

/-- At a finite base point the supporting inequality may be checked on finite competitors. -/
theorem mem_subdifferential_iff {I : H → EReal} (hI : IsProper I) {u v : H} :
    v ∈ subdifferential I u ↔ I u ≠ ⊤ ∧
      ∀ w, I w ≠ ⊤ → (I u).toReal + inner ℝ v (w - u) ≤ (I w).toReal := by
  constructor
  · intro hv
    have hu := ne_top_of_mem_subdifferential hI hv
    refine ⟨hu, fun w hw ↦ ?_⟩
    have h := hv w
    rw [← EReal.coe_toReal hu (hI.1 u), ← EReal.coe_toReal hw (hI.1 w),
      ← EReal.coe_add] at h
    exact EReal.coe_le_coe_iff.1 h
  · rintro ⟨hu, hv⟩ w
    by_cases hw : I w = ⊤
    · rw [hw]
      exact le_top
    rw [← EReal.coe_toReal hu (hI.1 u), ← EReal.coe_toReal hw (hI.1 w),
      ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (hv w hw)

/-- Zero is a subgradient exactly at a global minimum, with extended values retained. -/
theorem zero_mem_subdifferential_iff {I : H → EReal} {u : H} :
    (0 : H) ∈ subdifferential I u ↔ ∀ w, I u ≤ I w := by
  simp [subdifferential]

/-- The Hilbert subdifferential is a monotone relation. -/
theorem subdifferential_monotone {I : H → EReal} (hI : IsProper I)
    {u₁ u₂ v₁ v₂ : H} (h₁ : v₁ ∈ subdifferential I u₁)
    (h₂ : v₂ ∈ subdifferential I u₂) :
    0 ≤ inner ℝ (v₁ - v₂) (u₁ - u₂) := by
  obtain ⟨hu₁, hv₁⟩ := (mem_subdifferential_iff hI).1 h₁
  obtain ⟨hu₂, hv₂⟩ := (mem_subdifferential_iff hI).1 h₂
  have h12 := hv₁ u₂ hu₂
  have h21 := hv₂ u₁ hu₁
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

/-- Each fiber of the proper-energy subdifferential is a closed set. -/
theorem isClosed_subdifferential {I : H → EReal} (hI : IsProper I) (u : H) :
    IsClosed (subdifferential I u) := by
  by_cases hu : I u = ⊤
  · have hset : subdifferential I u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      exact fun v hv ↦ ne_top_of_mem_subdifferential hI hv hu
    rw [hset]
    exact isClosed_empty
  have hset : subdifferential I u =
      ⋂ (w : H) (_ : I w ≠ ⊤),
        {v | (I u).toReal + inner ℝ v (w - u) ≤ (I w).toReal} := by
    ext v
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_subdifferential_iff hI]
    exact and_iff_right hu
  rw [hset]
  exact isClosed_iInter fun w ↦ isClosed_iInter fun _ ↦
    isClosed_le (continuous_const.add (continuous_id.inner continuous_const)) continuous_const

/-- Each fiber of the proper-energy subdifferential is convex. -/
theorem convex_subdifferential {I : H → EReal} (hI : IsProper I) (u : H) :
    Convex ℝ (subdifferential I u) := by
  intro v₁ h₁ v₂ h₂ a b ha hb hab
  obtain ⟨hu, hv₁⟩ := (mem_subdifferential_iff hI).1 h₁
  obtain ⟨_, hv₂⟩ := (mem_subdifferential_iff hI).1 h₂
  apply (mem_subdifferential_iff hI).2
  refine ⟨hu, fun w hw ↦ ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (hv₁ w hw) ha
  have h2 := mul_le_mul_of_nonneg_left (hv₂ w hw) hb
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith [congrArg (fun t : ℝ ↦ t * (I u).toReal) hab,
    congrArg (fun t : ℝ ↦ t * (I w).toReal) hab]

end PDE.Analysis.Convex
