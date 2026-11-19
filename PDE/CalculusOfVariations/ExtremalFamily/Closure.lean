/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.Comparison

/-!
# Extremal-family comparison for a parameter defined on the closure

Finite-order extension supplies a smooth representative of the parameter without
changing its prescribed closure values. Locality of the action then transfers the
comparison back to the original parameter graph.

The main theorem, `lagrangianAction_le_parameter_graph`, is Evans, §8.2.5, Theorem 10 (local
minimizers), for vector-valued maps; Evans states it for scalar functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.5, Theorem 10.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis SobolevSpace

private theorem exists_interval_in_open_ordConnected {K J : Set ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hKJ : K ⊆ J)
    (hJ : IsOpen J) (hJc : OrdConnected J) :
    ∃ a b, a < b ∧ Icc a b ⊆ J ∧ K ⊆ Ioo a b := by
  obtain ⟨l, hl⟩ := hK.exists_isLeast hne
  obtain ⟨r, hr⟩ := hK.exists_isGreatest hne
  obtain ⟨a₀, a₁, ha, hIa⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds (hKJ hl.1))
  obtain ⟨b₀, b₁, hb, hIb⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds (hKJ hr.1))
  obtain ⟨a, haa, hal⟩ := exists_between ha.1
  obtain ⟨b, hrb, hbb⟩ := exists_between hb.2
  have hlr : l ≤ r := hl.2 hr.1
  refine ⟨a, b, hal.trans_le (hlr.trans hrb.le), ?_, ?_⟩
  · exact hJc.out (hIa ⟨haa, hal.trans ha.2⟩) (hIb ⟨hb.1.trans hrb, hbb⟩)
  · intro t ht
    exact ⟨hal.trans_le (hl.2 ht), (hr.2 ht).trans_lt hrb⟩

/-- Raw closure data suffice for the extremal-family comparison. Family jets are
required only on compact parameter subintervals inside the open interval; no
regularity at its endpoints, velocity sign, or competitor closeness is assumed.
This is Evans, §8.2.5, Theorem 10, for vector-valued maps. -/
theorem lagrangianAction_le_parameter_graph
    {d m : ℕ} {Ω : Set (ℝ^(d + 1))} {J : Set ℝ}
    {L : Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ^m → ℝ^(d + 1) → ℝ}
    {U : ℝ → ℝ^(d + 1) → ℝ^m} {θ : ℝ^(d + 1) → ℝ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hJ : IsOpen J) (hJc : OrdConnected J) (h0 : 0 ∈ J)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin (d + 1)) ℝ × (ℝ^m × ℝ^(d + 1)) ↦
        L a.1 a.2.1 a.2.2) {a | a.2.2 ∈ Ω})
    (hU : ∀ a b : ℝ, a < b → Icc a b ⊆ J →
      ContinuousSecondJetOn (fun p : ℝ^(d + 1) × ℝ ↦ U p.2 p.1) (Ω ×ˢ Ioo a b))
    (hθ : ContDiffUpToBoundary 2 θ Ω) (hθc : ContinuousOn θ (closure Ω))
    (hθJ : MapsTo θ (closure Ω) J)
    (hboundary : ∀ x ∈ frontier Ω, θ x = 0)
    (hEL : ∀ t ∈ J, ∀ x ∈ Ω, ∀ k, classicalEulerLagrange L (U t) x k = 0)
    (hconvex : ∀ x ∈ Ω, ∀ z, ConvexOn ℝ univ (fun P ↦ L P z x)) :
    lagrangianAction Ω L (U 0) ≤ lagrangianAction Ω L (fun x ↦ U (θ x) x) := by
  obtain ⟨Θ, hΘ, _, heq⟩ := hθ.exists_contDiff_succ_extension 1 hopen hbounded hgraph
  have heqC : EqOn Θ θ (closure Ω) :=
    heq.of_subset_closure hΘ.continuous.continuousOn hθc subset_closure Subset.rfl
  let K := insert 0 (θ '' closure Ω)
  have hK : IsCompact K := (hbounded.isCompact_closure.image_of_continuousOn hθc).insert 0
  have hKJ : K ⊆ J := insert_subset h0 (image_subset_iff.mpr hθJ)
  obtain ⟨a, b, hab, hIJ, hKI⟩ := exists_interval_in_open_ordConnected
    hK ⟨0, mem_insert _ _⟩ hKJ hJ hJc
  have hθI : MapsTo Θ (closure Ω) (Ioo a b) := by
    intro x hx
    rw [heqC hx]
    exact hKI (mem_insert_of_mem _ (mem_image_of_mem θ hx))
  have hcmp := lagrangianAction_le_parameter_graph_of_closureJets hopen hbounded
    (hgraph.hasC1GraphBoundary (by norm_num)) isOpen_Ioo ordConnected_Ioo
    (hKI (mem_insert _ _)) hL (hU a b hab hIJ) (hΘ.of_le (by norm_num)) hθI
    (fun x hx ↦ (heqC (frontier_subset_closure hx)).trans (hboundary x hx))
    (fun t ht ↦ hEL t (hIJ (Ioo_subset_Icc_self ht))) hconvex
  exact hcmp.trans_eq (lagrangianAction_congr hopen
    (fun x hx ↦ congrArg (fun t ↦ U t x) (heq hx)))

end PDE.CalculusOfVariations.ExtremalFamily
