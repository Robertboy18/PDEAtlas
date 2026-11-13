/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Subspaces with nowhere zero continuous representatives

If every nonzero vector in a subspace has a continuous representative which never vanishes
on a fixed nonempty open set, that subspace has dimension at most one. A linear combination
can be chosen to vanish at one point. Continuity identifies its representative everywhere
on the open set, contradicting nonvanishing unless the combination is zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Submodule

/-- A subspace whose nonzero vectors admit nowhere zero continuous representatives is
spanned by any of its nonzero vectors. The representing linear map need not be injective. -/
theorem exists_eq_smul_of_nonvanishing_representatives
    {X V : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    [AddCommGroup V] [Module ℝ V] {p : ℝ≥0∞}
    (W : Submodule ℝ V) {Ω : Set X} (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (j : V →ₗ[ℝ] Lp ℝ p (μ.restrict Ω))
    (hrep : ∀ w ∈ W, w ≠ 0 → ∃ f : X → ℝ,
      (j w : X → ℝ) =ᵐ[μ.restrict Ω] f ∧ ContinuousOn f Ω ∧
      ∀ x ∈ Ω, f x ≠ 0)
    {u v : V} (hu : u ∈ W) (hune : u ≠ 0) (hv : v ∈ W) :
    ∃ c : ℝ, v = c • u := by
  classical
  by_cases hvzero : v = 0
  · exact ⟨0, by simp [hvzero]⟩
  obtain ⟨f, hf, hfcont, hfne⟩ := hrep u hu hune
  obtain ⟨g, hg, hgcont, _⟩ := hrep v hv hvzero
  obtain ⟨x₀, hx₀⟩ := hne
  let c := g x₀ / f x₀
  have hwzero : v - c • u = 0 := by
    by_contra hwne
    obtain ⟨h, hh, hhcont, hhne⟩ := hrep (v - c • u) (W.sub_mem hv (W.smul_mem c hu)) hwne
    have hcombo : (j (v - c • u) : X → ℝ) =ᵐ[μ.restrict Ω]
        fun x ↦ g x - c * f x := by
      rw [map_sub, map_smul]
      filter_upwards [Lp.coeFn_sub (j v) (c • j u), Lp.coeFn_smul c (j u), hf, hg]
        with x hsub hsm hfx hgx
      simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsm, hfx, hgx] using hsub
    have hsame := Measure.eqOn_open_of_ae_eq (hh.symm.trans hcombo) hΩ hhcont
      (hgcont.sub (hfcont.const_mul c))
    apply hhne x₀ hx₀
    rw [hsame hx₀]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (g x₀) (hfne x₀ hx₀)).symm
  exact ⟨c, sub_eq_zero.mp hwzero⟩

end Submodule
