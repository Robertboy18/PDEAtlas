/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.HigherOrder.WholeSpaceTriple
public import PDE.Spaces.Sobolev.Extension.HigherOrder.Geometric
public import PDE.Analysis.Evolution.LionsMagenes.Factorization

/-!
# H¹ time continuity on a bounded C² domain

Let `Ω ⊆ ℝⁿ` be a bounded open set with C² graph boundary and let `a < b`. There is `C ≥ 0` such
that every `u ∈ L²(a, b; H²(Ω))` whose `L²` coordinate has weak time derivative
`g ∈ L²(a, b; L²(Ω))` on `(a, b)` agrees almost everywhere with some `v` continuous from `[a, b]`
into `H¹(Ω)` with `‖v t‖ ≤ C (‖u‖ + ‖g‖)` (`exists_continuous_h1_representative`). This is the case
`m = 0` of Evans §5.9.2, Theorem 4, which assumes `∂U` smooth. The trajectory is arbitrary; no
differential equation or boundary condition is imposed.

## How it works

As in step 1 of Evans's proof, we extend to the whole space:
`Extension.HigherOrder.exists_extension_with_L2_base` gives bounded extensions `E` on `H²(Ω)` and
`E₀` on `L²(Ω)` that agree on the `L²` coordinate and restrict to the identity, so the `L²`
coordinate of `E u` has weak time derivative `E₀ g`. On `ℝⁿ` the inclusion `H²(ℝⁿ) → H¹(ℝⁿ)` is a
Gelfand triple (`hTwoHOneTriple`) whose energy pairing factors through `L²` as
`⟪U, V⟫_{H¹} = ⟪U, V - ΔV⟫_{L²}` (`hTwoHOneTriple_energyToDual`); this is the integration by parts
of step 2 of Evans's proof, done on all of `ℝⁿ`. The abstract theorem
`GelfandTriple.exists_continuous_representative_of_factorization` then gives a continuous `H¹(ℝⁿ)`
representative of `E u` with a uniform bound, and restricting it to `Ω` gives `v`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 4, the case `m = 0` (steps 1 and 2 of the
  proof, estimates (14)-(16)), pp. 304-305.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set PDE.Analysis.Evolution
open scoped ENNReal Sobolev

/-- Evans §5.9.2, Theorem 4, case `m = 0`, for a bounded open `Ω ⊆ ℝ^n` with C² graph boundary
and `a < b`: there is `C ≥ 0` such that whenever `u ∈ L²(a, b; H²(Ω))` has `L²` coordinate with
weak time derivative `g ∈ L²(a, b; L²(Ω))` on `(a, b)`, some `v` continuous from `[a, b]` into
`H¹(Ω)` agrees with `u` almost everywhere and satisfies `‖v t‖ ≤ C (‖u‖ + ‖g‖)` on `[a, b]`. -/
theorem exists_continuous_h1_representative {n : ℕ} [Fact (0 < n)]
    {Ω : Set ℝ^n} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc a b)))
        (g : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))),
        HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t) →
        ∃ v : ℝ → W^{1,2}(Ω), ContinuousOn v (Icc a b) ∧
          v =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ lowerOrderCLM (by omega) (u t)) ∧
           ∀ t ∈ Icc a b, ‖v t‖ ≤ C * (‖u‖ + ‖g‖) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
  let n := m + 1
  let : MeasurableSpace (W^{2,2}(ℝ^n)) := borel _
  have : BorelSpace (W^{2,2}(ℝ^n)) := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ (W^{2,2}(ℝ^n))) := borel _
  have : BorelSpace (StrongDual ℝ (W^{2,2}(ℝ^n))) := ⟨rfl⟩
  obtain ⟨E, E₀, hbase, _, hres⟩ :=
    Extension.HigherOrder.exists_extension_with_L2_base (k := 2) hopen hbounded hgraph
  obtain ⟨C, hC, hwhole⟩ := (hTwoHOneTriple n).exists_continuous_representative_of_factorization
    wkpBaseCoordinateCLM (lTwoToHTwoDual n) hTwoHOneTriple_energyToDual hab
  refine ⟨C * (‖E‖ + ‖E₀‖), mul_nonneg hC (by positivity), ?_⟩
  intro u g hweak
  let uE := E.compLp u
  let gE := E₀.compLp g
  have huE := (E.coeFn_compLp' u).filter_mono
    (ae_mono (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
  have hgE := (E₀.coeFn_compLp' g).filter_mono
    (ae_mono (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
  have hext : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (uE t)) (fun t ↦ gE t) := by
    apply (hweak.map E₀).congr_ae_restrict measurableSet_Ioo _ hgE.symm
    filter_upwards [huE] with t ht
    exact (hbase (u t)).symm.trans (congrArg wkpBaseCoordinateCLM ht.symm)
  obtain ⟨v, hv, hae, hnorm⟩ := hwhole uE gE hext
  let R : W^{1,2}(ℝ^n) →L[ℝ] W^{1,2}(Ω) :=
    restrictCLM hopen.measurableSet (subset_univ Ω)
  refine ⟨fun t ↦ R (v t), R.continuous.comp_continuousOn hv, ?_, ?_⟩
  · filter_upwards [hae, E.coeFn_compLp' u] with t ht hut
    change R (v t) = lowerOrderCLM (by omega) (u t)
    rw [ht]
    change R (lowerOrderCLM (show 1 ≤ 2 by omega) (uE t)) = _
    rw [hut]
    dsimp only [R]
    rw [restrictCLM_lowerOrderCLM_apply, hres]
  · intro t ht
    have hsum : ‖uE‖ + ‖gE‖ ≤ (‖E‖ + ‖E₀‖) * (‖u‖ + ‖g‖) := by
      calc
        ‖uE‖ + ‖gE‖ ≤ ‖E‖ * ‖u‖ + ‖E₀‖ * ‖g‖ :=
          add_le_add (E.norm_compLp_le u) (E₀.norm_compLp_le g)
        _ ≤ (‖E‖ + ‖E₀‖) * (‖u‖ + ‖g‖) := by
          nlinarith [mul_nonneg (norm_nonneg E) (norm_nonneg g),
            mul_nonneg (norm_nonneg E₀) (norm_nonneg u)]
    calc
      ‖R (v t)‖ ≤ ‖v t‖ := norm_restrictCLM_apply_le _ _ _
      _ ≤ C * (‖uE‖ + ‖gE‖) := hnorm t ht
      _ ≤ C * ((‖E‖ + ‖E₀‖) * (‖u‖ + ‖g‖)) := mul_le_mul_of_nonneg_left hsum hC
      _ = C * (‖E‖ + ‖E₀‖) * (‖u‖ + ‖g‖) := (mul_assoc _ _ _).symm

end SobolevSpace.GraphSpace
