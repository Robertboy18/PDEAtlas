/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.HigherOrder.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Slicing.FirstJetReconstruction

/-!
# Higher Sobolev time regularity for arbitrary trajectories

For every `m`, an `L²(H^{m+2})` trajectory `u` whose `Hᵐ` reading has weak time derivative
`g ∈ L²(Hᵐ)` has a representative `v` continuous from the closed interval into `H^{m+1}`, with
`‖v t‖ ≤ C (‖u‖ + ‖g‖)` for a constant `C` that does not depend on `u` and `g`
(`exists_continuous_higher_sobolev_representative`). This is Evans §5.9.2, Theorem 4, which assumes
`∂U` smooth; we assume a bounded open set with C² graph boundary.

## How it works

We follow step 3 of Evans's proof. For each multi-index `α` of order at most `m` (an element of
`DerivIndex n m`), the derivative `D^α u`, taken by `derivativeWordCLM`, is an `L²(H²)` trajectory
whose `L²` coordinate has weak time derivative `D^α g`, the coordinate `wkpCoordinateCLM α` of `g`.
The case `m = 0`, `exists_continuous_h1_representative`, gives it a continuous `H¹` representative
bounded by `C (‖u‖ + ‖g‖)`, since neither map increases norms. Where Evans sums these estimates over
`α`, we collect the fields into one continuous map into `DerivIndex n m → W^{1,2}(Ω)` and apply the
bounded map `firstJetReconstructionCLM`, which selects coordinates and projects orthogonally onto
the closed graph `W^{m+1,2}(Ω)`. It inverts the first jet map `firstJetCLM`
(`firstJetReconstructionCLM_firstJetCLM`), so the result agrees with `u` almost everywhere, and the
constant becomes `‖firstJetReconstructionCLM‖ * C`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 4 and step 3 of its proof, estimate (16),
  pp. 304-305.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set PDE.Analysis.Evolution
open scoped ENNReal Sobolev

/-- Evans §5.9.2, Theorem 4, for a bounded open `Ω ⊆ ℝ^n` with C² graph boundary and `a < b`:
there is `C ≥ 0` such that whenever `u ∈ L²(a, b; H^{m+2}(Ω))`, read in `Hᵐ`, has weak time
derivative `g ∈ L²(a, b; Hᵐ(Ω))` on `(a, b)`, some `v` continuous from `[a, b]` into
`H^{m+1}(Ω)` agrees with `u` almost everywhere and satisfies `‖v t‖ ≤ C (‖u‖ + ‖g‖)` on
`[a, b]`. The weak derivative is taken in Hᵐ using smooth compactly supported time tests. No
boundary condition is required. -/
theorem exists_continuous_higher_sobolev_representative {n : ℕ} [Fact (0 < n)]
    (m : ℕ) {Ω : Set ℝ^n} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Lp (W^{m + 2,2}(Ω)) 2 (volume.restrict (Ioc a b)))
        (g : Lp (W^{m,2}(Ω)) 2 (volume.restrict (Ioc a b))),
        HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ lowerOrderCLM (show m ≤ m + 2 by omega) (u t)) (fun t ↦ g t) →
        ∃ v : ℝ → W^{m + 1,2}(Ω), ContinuousOn v (Icc a b) ∧
          v =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ lowerOrderCLM (by omega) (u t)) ∧
          ∀ t ∈ Icc a b, ‖v t‖ ≤ C * (‖u‖ + ‖g‖) := by
  obtain ⟨C, hC, hfirst⟩ := exists_continuous_h1_representative hopen hbounded hgraph hab
  let R := firstJetReconstructionCLM (n := n) (m := m) (Ω := Ω)
  refine ⟨‖R‖ * C, mul_nonneg (norm_nonneg R) hC, ?_⟩
  intro u g hweak
  let D (α : DerivIndex n m) : W^{m + 2,2}(Ω) →L[ℝ] W^{2,2}(Ω) :=
    derivativeWordCLM α.toList (Nat.add_le_add_right α.toList_length_le 2)
  let G (α : DerivIndex n m) : W^{m,2}(Ω) →L[ℝ] DerivLp n 2 Ω :=
    wkpCoordinateCLM α
  have hbase (α : DerivIndex n m) (U : W^{m + 2,2}(Ω)) :
      wkpBaseCoordinateCLM (D α U) = G α (lowerOrderCLM (by omega) U) := by
    dsimp only [D, G]
    simp only [wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply,
      derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply, lowerOrderCLM_apply]
    have hlen := α.toList_length_le
    rw [show derivIndexOfList α.toList (by omega) = α.castOrder (by omega) from
      derivIndexOfList_toList (α.castOrder (show m ≤ m + 2 by omega))
        (α.castOrder (show m ≤ m + 2 by omega)).toList_length_le]
  have hfields (α : DerivIndex n m) :
      ∃ v : ℝ → W^{1,2}(Ω), ContinuousOn v (Icc a b) ∧
        v =ᵐ[volume.restrict (Ioc a b)]
          (fun t ↦ firstJetCLM (lowerOrderCLM (show m + 1 ≤ m + 2 by omega) (u t)) α) ∧
        ∀ t ∈ Icc a b, ‖v t‖ ≤ C * (‖u‖ + ‖g‖) := by
    let ua := (D α).compLp u
    let ga := (G α).compLp g
    have hua := ((D α).coeFn_compLp' u).filter_mono
      (ae_mono (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
    have hga := ((G α).coeFn_compLp' g).filter_mono
      (ae_mono (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
    have ha : HasWeakTimeDerivativeOn (Ioo a b)
        (fun t ↦ wkpBaseCoordinateCLM (ua t)) (fun t ↦ ga t) := by
      apply (hweak.map (G α)).congr_ae_restrict measurableSet_Ioo _ hga.symm
      filter_upwards [hua] with t ht
      exact (hbase α (u t)).symm.trans (congrArg wkpBaseCoordinateCLM ht.symm)
    obtain ⟨v, hv, hae, hnorm⟩ := hfirst ua ga ha
    have hunorm : ‖ua‖ ≤ ‖u‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(D α).coeFn_compLp' u] with t ht
      rw [ht]
      exact norm_derivativeWordCLM_apply_le _ _ _
    have hgnorm : ‖ga‖ ≤ ‖g‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(G α).coeFn_compLp' g] with t ht
      rw [ht]
      exact wkpCoordinateCLM_norm_le _ _
    refine ⟨v, hv, ?_, fun t ht ↦ (hnorm t ht).trans
      (mul_le_mul_of_nonneg_left (add_le_add hunorm hgnorm) hC)⟩
    filter_upwards [hae, (D α).coeFn_compLp' u] with t ht hut
    rw [ht]
    change lowerOrderCLM (show 1 ≤ 2 by omega) (ua t) = _
    rw [hut]
    apply Subtype.ext
    apply PiLp.ext
    intro b
    rfl
  choose v hv hae hnorm using hfields
  let w : ℝ → (DerivIndex n m → W^{1,2}(Ω)) := fun t a ↦ v a t
  have hw : ContinuousOn w (Icc a b) := continuousOn_pi.mpr hv
  refine ⟨fun t ↦ R (w t), R.continuous.comp_continuousOn hw, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hae] with t ht
    have heq : w t = firstJetCLM (lowerOrderCLM (show m + 1 ≤ m + 2 by omega) (u t)) :=
      funext ht
    rw [heq]
    exact firstJetReconstructionCLM_firstJetCLM _
  · intro t ht
    have hn : ‖w t‖ ≤ C * (‖u‖ + ‖g‖) :=
      (pi_norm_le_iff_of_nonneg (mul_nonneg hC (by positivity))).mpr fun a ↦ hnorm a t ht
    calc
      ‖R (w t)‖ ≤ ‖R‖ * ‖w t‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (C * (‖u‖ + ‖g‖)) := mul_le_mul_of_nonneg_left hn (norm_nonneg R)
      _ = ‖R‖ * C * (‖u‖ + ‖g‖) := (mul_assoc _ _ _).symm

end SobolevSpace.GraphSpace
