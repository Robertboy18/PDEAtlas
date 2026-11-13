/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Volterra
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Globally Lipschitz time-dependent equations in Banach spaces

Joint continuity makes every Picard integrand continuous without a measurable-space
or separability assumption on the state space. A factorial Volterra estimate constructs
solutions on arbitrary finite intervals with an interior initial time. Uniqueness on
intersections then gives a solution on the whole real line.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A jointly continuous field, uniformly Lipschitz in the state, has a solution
on any prescribed finite interval.
The chosen extension has an ordinary derivative even at the two interval endpoints. -/
theorem exists_eq_hasDerivAt_on_Icc_of_lipschitz {F : ℝ → E → E} {K : NNReal}
    (hF : Continuous (uncurry F)) {a b : ℝ}
    (hLip : ∀ t ∈ Icc a b, LipschitzWith K (F t)) (t₀ : Icc a b) (x₀ : E) :
    ∃ u : ℝ → E, Continuous u ∧ u t₀ = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivAt u (F t (u t)) t := by
  have hab : a ≤ b := t₀.2.1.trans t₀.2.2
  let g : C(Icc a b, E) → ℝ → E := fun u t ↦ F t (IccExtend hab u t)
  have hg (u : C(Icc a b, E)) : Continuous (g u) :=
    hF.comp (continuous_id.prodMk (u.continuous.Icc_extend' (h := hab)))
  let P : C(Icc a b, E) → C(Icc a b, E) := fun u ↦
    ⟨fun t ↦ x₀ + ∫ s in t₀.1..t.1, g u s,
      continuous_const.add
        ((intervalIntegral.differentiable_integral_of_continuous (hg u)).continuous.comp
          continuous_subtype_val)⟩
  obtain ⟨v, hv, _⟩ := PDE.Analysis.ODE.existsUnique_isFixedPt_volterra t₀ P g x₀ K
    (fun u ↦ (hg u).continuousOn.integrableOn_compact isCompact_Icc)
    (fun _ _ ↦ rfl) (fun u v t ↦ by
      simpa only [g, IccExtend_of_mem hab u t.2, IccExtend_of_mem hab v t.2,
        dist_eq_norm] using (hLip t t.2).dist_le_mul (u t) (v t))
  let u : ℝ → E := fun t ↦ x₀ + ∫ s in t₀.1..t, g v s
  have heq (t : ℝ) (ht : t ∈ Icc a b) : u t = v ⟨t, ht⟩ :=
    congrArg (fun w : C(Icc a b, E) ↦ w ⟨t, ht⟩) hv
  refine ⟨u, continuous_const.add
    (intervalIntegral.differentiable_integral_of_continuous (hg v)).continuous,
    by simp [u], ?_⟩
  intro t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right
    ((hg v).intervalIntegrable t₀.1 t)
    (hg v).aestronglyMeasurable.stronglyMeasurableAtFilter
    (hg v).continuousAt).const_add x₀
  simpa only [g, IccExtend_of_mem hab v ht, heq t ht] using hd

/-- A jointly continuous field with a uniform global state Lipschitz constant has a
solution on the whole real line through any initial state at any initial time.
The state space can be any real Banach space, without separability assumptions. -/
theorem exists_eq_hasDerivAt_of_lipschitz {F : ℝ → E → E} {K : NNReal}
    (hF : Continuous (uncurry F)) (hLip : ∀ t, LipschitzWith K (F t))
    (t₀ : ℝ) (x₀ : E) :
    ∃ u : ℝ → E, u t₀ = x₀ ∧ ∀ t, HasDerivAt u (F t (u t)) t := by
  have hlocal (R : ℝ) (hR : 0 < R) :
      ∃ u : ℝ → E, u t₀ = x₀ ∧
        ∀ t ∈ Icc (t₀ - R) (t₀ + R), HasDerivAt u (F t (u t)) t := by
    obtain ⟨u, _, hu, hd⟩ := exists_eq_hasDerivAt_on_Icc_of_lipschitz
      (a := t₀ - R) (b := t₀ + R)
      hF (fun t _ ↦ hLip t) ⟨t₀, by constructor <;> linarith⟩ x₀
    exact ⟨u, hu, hd⟩
  choose v hv₀ hvd using hlocal
  let u : ℝ → E := fun t ↦ v (|t - t₀| + 1) (by positivity) t
  have hagree (R : ℝ) (hR : 0 < R) :
      EqOn u (v R hR) (Ioo (t₀ - R) (t₀ + R)) := by
    intro s hs
    let R' := |s - t₀| + 1
    have hR' : 0 < R' := by dsimp [R']; positivity
    let B := min R R'
    have hB : 0 < B := lt_min hR hR'
    have hBR : B ≤ R := min_le_left _ _
    have hBR' : B ≤ R' := min_le_right _ _
    have hzero : t₀ ∈ Ioo (t₀ - B) (t₀ + B) := by constructor <;> linarith
    have hsB : s ∈ Ioo (t₀ - B) (t₀ + B) := by
      have hsmall : |s - t₀| < B := by
        apply lt_min
        · exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
        · dsimp [R']; linarith
      obtain ⟨hl, hr⟩ := abs_lt.mp hsmall
      constructor <;> linarith
    have heq := ODE_solution_unique_of_mem_Ioo (v := F) (s := fun _ ↦ (univ : Set E))
      (fun t _ ↦ (hLip t).lipschitzOnWith) hzero
      (fun t ht ↦ ⟨hvd R hR t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (fun t ht ↦ ⟨hvd R' hR' t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (by rw [hv₀ R hR, hv₀ R' hR'])
    exact (heq hsB).symm
  refine ⟨u, hv₀ (|t₀ - t₀| + 1) (by positivity), ?_⟩
  intro t
  let R := |t - t₀| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have ht : t ∈ Ioo (t₀ - R) (t₀ + R) := by
    have hsmall : |t - t₀| < R := by dsimp [R]; linarith
    obtain ⟨hl, hr⟩ := abs_lt.mp hsmall
    constructor <;> linarith
  have heq : u =ᶠ[𝓝 t] v R hR :=
    eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) (fun s hs ↦ hagree R hR hs)
  rw [hagree R hR ht]
  exact (hvd R hR t (Ioo_subset_Icc_self ht)).congr_of_eventuallyEq heq

end PDE.Analysis.Evolution
