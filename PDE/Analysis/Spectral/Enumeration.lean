/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.CompactOperator
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Order.Monotone.MonovaryOrder

/-!
# Enumerating eigenmodes with multiplicity

A compact operator has finitely many nonzero eigenvalues above any positive norm
threshold. Each corresponding eigenspace is finite-dimensional, so a linearly
independent family has only finitely many eigenvectors above that threshold,
including multiplicities.

For positive variational eigenvalues, taking reciprocals turns this into finite
sublevels. Any infinite family of real numbers with finite sublevels admits a
nondecreasing enumeration tending to infinity. Mathlib supplies the ordering of
the index type and the classification of the resulting locally finite order.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Spectral

open Filter Module.End

/-- Only finitely many vectors in a linearly independent eigenfamily of a compact
operator can have eigenvalue norm at least `ε > 0`. This counts multiplicity;
neither symmetry nor completeness of the eigenfamily is assumed. -/
theorem finite_eigenvector_indices_norm_ge
    {𝕜 H ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) (hT : IsCompactOperator T)
    (μ : ι → 𝕜) (v : ι → H) (hv : LinearIndependent 𝕜 v)
    (heigen : ∀ i, HasEigenvector (T : Module.End 𝕜 H) (μ i) (v i))
    {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ ‖μ i‖}.Finite := by
  classical
  refine Set.Finite.of_finite_fibers μ ?_ ?_
  · refine (PDE.Analysis.finite_eigenvalues_norm_ge T hT hε).subset ?_
    rintro a ⟨i, hi, rfl⟩
    exact ⟨hasEigenvalue_of_hasEigenvector (heigen i), hi⟩
  · intro a ha
    have ha0 : a ≠ 0 := by
      obtain ⟨i, hi, rfl⟩ := ha
      intro hzero
      change ε ≤ ‖μ i‖ at hi
      rw [hzero, norm_zero] at hi
      exact (not_le_of_gt hε) hi
    have : FiniteDimensional 𝕜 (eigenspace T.toLinearMap a) :=
      ContinuousLinearMap.finite_dimensional_eigenspace hT a ha0
    let S : Set ι := {i | ε ≤ ‖μ i‖} ∩ μ ⁻¹' {a}
    let w : S → eigenspace T.toLinearMap a := fun i ↦
      ⟨v i, by
        have hi : μ (i : ι) = a := i.property.2
        simpa only [hi] using (heigen (i : ι)).1⟩
    have hw : LinearIndependent 𝕜 w := by
      apply LinearIndependent.of_comp (eigenspace T.toLinearMap a).subtype
      exact hv.comp (fun i : S ↦ (i : ι)) Subtype.val_injective
    have : Finite S := hw.finite
    exact Set.toFinite S

/-- An infinite family in a linear order with finite sublevels can be listed in
nondecreasing order, retaining every index exactly once. Its values tend to
infinity; repeated values are allowed because each sublevel is finite. -/
theorem exists_equiv_nat_monotone_of_finite_sublevel
    {ι α : Type*} [Infinite ι] [LinearOrder α] (f : ι → α)
    (hfinite : ∀ r, {i | f i ≤ r}.Finite) :
    ∃ e : ℕ ≃ ι, Monotone (fun n ↦ f (e n)) ∧
      Tendsto (fun n ↦ f (e n)) atTop atTop := by
  classical
  obtain ⟨instOrder, hmono, _⟩ := (monovary_self f).exists_monotone
  have hIic (a : ι) : (Set.Iic a).Finite :=
    (hfinite (f a)).subset fun _ hi ↦ hmono hi
  let : LocallyFiniteOrder ι :=
    LocallyFiniteOrder.ofFiniteIcc fun _ b ↦ (hIic b).subset fun _ hi ↦ hi.2
  let : NoMaxOrder ι := ⟨fun a ↦ by
    obtain ⟨b, hb⟩ := (hIic a).exists_notMem
    exact ⟨b, lt_of_not_ge hb⟩⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty ι)
  let s := (hIic a).toFinset
  have hs : s.Nonempty := ⟨a, by simp [s]⟩
  have hmin (i : ι) : s.min' hs ≤ i := by
    by_cases hi : i ≤ a
    · exact s.min'_le i (by simpa [s] using hi)
    · exact (s.min'_le a (by simp [s])).trans (le_of_not_ge hi)
  let : OrderBot ι := { bot := s.min' hs, bot_le := hmin }
  let : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  let : PredOrder ι := LinearLocallyFiniteOrder.predOrder ι
  let e : ℕ ≃o ι := (orderIsoNatOfLinearSuccPredArch (ι := ι)).symm
  refine ⟨e.toEquiv, hmono.comp e.monotone, tendsto_atTop.2 fun r ↦ ?_⟩
  have hpre : {n : ℕ | f (e n) ≤ r}.Finite :=
    (hfinite r).preimage e.injective.injOn
  obtain ⟨N, hN⟩ := hpre.bddAbove
  filter_upwards [eventually_gt_atTop N] with n hn
  exact (lt_of_not_ge fun h ↦ (not_le_of_gt hn) (hN h)).le

end PDE.Analysis.Spectral
