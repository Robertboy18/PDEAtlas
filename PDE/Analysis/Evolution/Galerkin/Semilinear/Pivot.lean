/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Galerkin.Measurable.AEBounds
import PDE.Analysis.Evolution.Integrated.Energy.Pivot
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Semilinear evolution with a coercive pivot response

The linear Galerkin theorem constructs the response to each `L²(H)` load.
If the form controls `μ ‖i v‖²` and the nonlinear load has Lipschitz constant
strictly below `μ`, the response is a contraction in `L²(H)`.

Its fixed point lies in the pivot space, where the nonlinear estimate is
available. Solving once more at that load recovers the energy-space state.
The result satisfies the integrated weak equation, including its initial
trace.

The nonlinear load may depend on the entire pivot trajectory. Pointwise
reaction terms are a special case, after their action on Bochner `L²` has
been established. There is no zero-at-zero assumption on the load. The fixed point comes
from Banach's theorem, Mathlib's `ContractingWith.fixedPoint`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.1, Theorem 1 (Banach's fixed point theorem) and
  the proof of Theorem 2. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis.Evolution

/-- Let `B` be measurable and bounded with a Gårding inequality almost everywhere, and assume
`μ ‖ι v‖² ≤ B(t)(v, v)` almost everywhere. If `F : L²(a, b; H) → L²(a, b; H)` is Lipschitz with
constant `L < μ`, then `u' + B(t) u = F(ι u)` has exactly one integrated weak solution with
initial value `uInit`. The Gårding bound and the stable trial system give each linear response,
and the pivot bound makes the response map a contraction. -/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_lipschitz_pivot
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : StableTrialSystem T)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b theta gamma : ℝ}
    (hab : a < b) (htheta : 0 < theta) (hgamma : 0 ≤ gamma)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Ioc a b)))
    (MB : ℝ≥0)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      theta * ‖v‖ ^ 2 ≤ B t v v + gamma * ‖T.inclusion v‖ ^ 2)
    {L μ : ℝ≥0}
    (hcoercive : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      (μ : ℝ) * ‖T.inclusion v‖ ^ 2 ≤ B t v v)
    (F : Lp H 2 (volume.restrict (Ioc a b)) →
      Lp H 2 (volume.restrict (Ioc a b)))
    (hF : LipschitzWith L F) (hsmall : L < μ) (uInit : H) :
    ∃! u : Lp V 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution T B
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
          (F (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) u))) u uInit := by
  classical
  let ν := volume.restrict (Ioc a b)
  let J := T.inclusion.compLpL 2 ν
  let Q := T.pivotToDual.compLpL 2 ν
  have hexists (f : Lp H 2 ν) :
      Nonempty (GardingWeakSolutionOn T B (Q f) uInit a b theta gamma) :=
    GardingWeakSolutionOn.nonempty_of_ae_garding T S.space S.finiteDimensional S.projection
      S.denseEnergy B (Q f) hab htheta hgamma hB MB hbound hGarding uInit
  let R (f : Lp H 2 ν) := (hexists f).some
  let Φ (v : Lp H 2 ν) := J (R (F v)).state
  have hμ : 0 < μ := lt_of_le_of_lt (by positivity) hsmall
  have hμreal : 0 < (μ : ℝ) := hμ
  have hcontract : ContractingWith (L / μ) Φ := by
    refine ⟨(div_lt_one hμ).2 hsmall, LipschitzWith.of_dist_le_mul ?_⟩
    intro v w
    have hresponse := (R (F v)).properties.solution.mul_norm_pivot_sub_le
      hB MB hbound hcoercive (R (F w)).properties.solution
    have hnonlinear : ‖F v - F w‖ ≤ (L : ℝ) * ‖v - w‖ := by
      simpa only [dist_eq_norm] using hF.dist_le_mul v w
    have hestimate : (μ : ℝ) * ‖Φ v - Φ w‖ ≤ (L : ℝ) * ‖v - w‖ := by
      change (μ : ℝ) * ‖J (R (F v)).state - J (R (F w)).state‖ ≤ _
      rw [← map_sub]
      exact hresponse.trans hnonlinear
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_div]
    calc
      ‖Φ v - Φ w‖ ≤ ((L : ℝ) * ‖v - w‖) / μ :=
        (le_div_iff₀ hμreal).2 (by simpa only [mul_comm] using hestimate)
      _ = ((L : ℝ) / μ) * ‖v - w‖ := by ring
  let z := hcontract.fixedPoint Φ
  have hz : J (R (F z)).state = z := hcontract.fixedPoint_isFixedPt
  refine ⟨(R (F z)).state, ?_, ?_⟩
  · change IsGelfandIntegratedWeakSolution T B (Q (F (J (R (F z)).state)))
      (R (F z)).state uInit
    rw [hz]
    exact (R (F z)).properties.solution
  · intro v hv
    have hvlinear : v = (R (F (J v))).state :=
      (R (F (J v))).properties.unique v hv
    have hvfixed : Function.IsFixedPt Φ (J v) := by
      change J (R (F (J v))).state = J v
      rw [← hvlinear]
    have hvz : J v = z := hcontract.fixedPoint_unique hvfixed
    apply (R (F z)).properties.unique v
    change IsGelfandIntegratedWeakSolution T B (Q (F (J v))) v uInit at hv
    simpa only [hvz] using hv

end PDE.Analysis.Evolution
