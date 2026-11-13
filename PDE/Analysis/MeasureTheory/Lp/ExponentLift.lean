/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Changing the target exponent of an Lp-valued linear map

Let `E` and `F` be Banach spaces over a nontrivially normed field. Suppose a
continuous linear map from `E` to `Lp F p μ` takes all its values in `Lp F q μ`,
with `p,q ≥ 1`. The same representatives define a continuous linear map into
`Lp F q μ`.

Convergence in either norm implies convergence in measure. Uniqueness of that
limit closes the graph of the lifted map, so the closed graph theorem supplies
continuity. The measure is arbitrary, and either exponent may be infinite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ContinuousLinearMap

variable {α 𝕜 E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Lift an `Lᵖ`-valued linear map to `Lᵠ` when all its values lie in `Lᵠ`.
The closed graph theorem supplies continuity; it is not an extra hypothesis. -/
def liftLpExponent (J : E →L[𝕜] Lp F p μ)
    (hmem : ∀ x : E, MemLp (J x : α → F) q μ) :
    E →L[𝕜] Lp F q μ := by
  let L : E →ₗ[𝕜] Lp F q μ :=
    { toFun := fun x ↦ (hmem x).toLp (J x)
      map_add' := by
        intro x y
        apply Lp.ext
        filter_upwards [(hmem (x + y)).coeFn_toLp,
          Lp.coeFn_add ((hmem x).toLp (J x)) ((hmem y).toLp (J y)),
          (hmem x).coeFn_toLp, (hmem y).coeFn_toLp,
          Lp.coeFn_add (J x) (J y)] with a hleft hright hx hy hJ
        rw [hleft, hright, Pi.add_apply, hx, hy, map_add, hJ, Pi.add_apply]
      map_smul' := by
        intro c x
        apply Lp.ext
        filter_upwards [(hmem (c • x)).coeFn_toLp,
          Lp.coeFn_smul c ((hmem x).toLp (J x)),
          (hmem x).coeFn_toLp, Lp.coeFn_smul c (J x)] with a hleft hright hx hJ
        change ((hmem (c • x)).toLp (J (c • x)) : α → F) a =
          (c • (hmem x).toLp (J x) : Lp F q μ) a
        rw [hleft, hright, Pi.smul_apply, hx, map_smul, hJ, Pi.smul_apply] }
  refine ContinuousLinearMap.ofSeqClosedGraph (g := L) ?_
  intro u x y hux huy
  have hbase := tendstoInMeasure_of_tendsto_Lp ((J.continuous.tendsto x).comp hux)
  have htarget := tendstoInMeasure_of_tendsto_Lp huy
  have htarget' : TendstoInMeasure μ (fun k ↦ (J (u k) : α → F)) atTop y := by
    apply htarget.congr_left
    intro k
    exact (hmem (u k)).coeFn_toLp
  apply Lp.ext
  exact (tendstoInMeasure_ae_unique hbase htarget').symm.trans
    (hmem x).coeFn_toLp.symm

/-- Changing the exponent preserves the original representative almost
everywhere. -/
theorem coeFn_liftLpExponent (J : E →L[𝕜] Lp F p μ)
    (hmem : ∀ x : E, MemLp (J x : α → F) q μ) (x : E) :
    liftLpExponent J hmem x =ᵐ[μ] (J x : α → F) :=
  (hmem x).coeFn_toLp

end ContinuousLinearMap
