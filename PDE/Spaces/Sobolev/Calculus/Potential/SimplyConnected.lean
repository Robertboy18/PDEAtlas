/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Potential.Local
public import PDE.Spaces.Sobolev.Calculus.Potential.Cover

/-!
# Weak potentials on simply connected open sets

A locally L² field with commuting distributional coordinate derivatives is a
weak gradient on any simply connected open Euclidean domain. Local potentials
are constructed on nested balls by mollification and the closed range of the
Sobolev gradient. A countable ball cover and additive-constant gluing
then produce the global locally L² potential. No convexity or regularity of
the domain boundary is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal Distributions Sobolev

namespace SobolevSpace

open GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A locally L² weakly closed field on a simply connected open domain has
a locally L² scalar potential. The weak derivatives are tested against
all compactly supported smooth functions in the original domain. -/
theorem exists_weak_potential_of_weakly_closed
    (hΩ : IsOpen Ω) (hsc : IsSimplyConnected Ω) (F : ℝ^n → ℝ^n)
    (hF : ∀ i : Fin n, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
      MemLp (fun x ↦ F x i) 2 (volume.restrict K))
    (hweak : ∀ i j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ Ω →
      (∫ x in Ω, F x j * (∂[i] (φ : ℝ^n → ℝ)) x) =
        ∫ x in Ω, F x i * (∂[j] (φ : ℝ^n → ℝ)) x) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        MemLp p 2 (domainMeasure n K)) ∧
      ∀ j : Fin n, HasWeakDerivativeOn Ω [j] p (fun x ↦ F x j) := by
  classical
  have := hsc.simplyConnectedSpace
  have := hΩ.locallyPathConnectedSpace
  choose r hr hsub w hw using exists_local_weak_potential hΩ F hF hweak
  obtain ⟨c, hc, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
      (fun x : Ω ↦ ball x.val (r x)) (fun _ ↦ isOpen_ball)
      (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  have : Countable c := hc.to_subtype
  let U (i : c) : Set (ℝ^n) := ball i.val.val (r i.val)
  have hcov : Ω ⊆ ⋃ i : c, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  exact exists_weak_potential_of_native_cover hΩ U (fun _ ↦ isOpen_ball)
    (fun i ↦ (convex_ball _ _).isPreconnected)
    (fun i j ↦ ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected)
    (fun _ ↦ isBounded_ball) (fun i ↦ hsub i.val) hcov
    (fun i ↦ w i.val) F (fun i ↦ hw i.val)

end SobolevSpace
