/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Regularity

/-!
# Extending the Hopf–Lax potential across its initial face

Clamping time at zero extends the forward value to a globally Lipschitz
function. It preserves the prescribed primitive on the initial face and agrees
with the forward value on an open neighborhood of every positive-time point.
The continuation allows global integration by parts to retain the initial term.

In the proof of Evans, §3.4.2, Theorem 2, the potential `w` of (34) is integrated against `v_x`
over `ℝ × (0, ∞)` in (35); `forwardValue` continues it by `w = h` for `t ≤ 0`, so that the
integration by parts produces the initial term.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, Theorem 2 and its proof, equations
  (34)-(35).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology NNReal

namespace HamiltonJacobi.HopfLax

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hopf–Lax value, continued to negative time by its initial value. -/
def forwardValue (L h : E → ℝ) (p : E × ℝ) : ℝ :=
  value L h (max p.2 0) p.1

/-- On the initial face the continuation is the original datum. -/
@[simp] theorem forwardValue_zero (L h : E → ℝ) (x : E) :
    forwardValue L h (x, 0) = h x := by
  simp [forwardValue]

/-- At every positive-time point the continuation and the formula have
the same germ, so all derivatives agree there. -/
theorem forwardValue_eventuallyEq (L h : E → ℝ) {p : E × ℝ} (hp : 0 < p.2) :
    forwardValue L h =ᶠ[𝓝 p] (fun q ↦ value L h q.2 q.1) := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
  exact congrArg (fun t ↦ value L h t q.1) (max_eq_left hq.le)

private theorem lipschitzWith_forwardValue_of_forward {L h : E → ℝ} {A : ℝ≥0}
    (hforward : LipschitzOnWith A (fun z : E × ℝ ↦ value L h z.2 z.1) {z | 0 ≤ z.2}) :
    LipschitzWith A (forwardValue L h) := by
  have hclip : LipschitzWith 1 (fun p : E × ℝ ↦ (p.1, max p.2 0)) := by
    have hf : LipschitzWith 1 (Prod.fst : E × ℝ → E) := LipschitzWith.prod_fst
    have ht : LipschitzWith 1 (Prod.snd : E × ℝ → ℝ) := LipschitzWith.prod_snd
    simpa only [max_self] using hf.prodMk (ht.max_const 0)
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  have hdist : dist (p.1, max p.2 0) (q.1, max q.2 0) ≤ dist p q := by
    simpa only [NNReal.coe_one, one_mul] using hclip.dist_le_mul p q
  exact (hforward.dist_le_mul (p.1, max p.2 0) (show 0 ≤ max p.2 0 from le_max_right _ _)
    (q.1, max q.2 0) (show 0 ≤ max q.2 0 from le_max_right _ _)).trans
    (mul_le_mul_of_nonneg_left hdist A.2)

/-- Lipschitz data give a globally Lipschitz continuation, without a bound on
the datum itself. Only the forward values are used. -/
theorem exists_lipschitzWith_forwardValue [FiniteDimensional ℝ E] {L h : E → ℝ}
    (hL : Superlinear L) (hconv : ConvexOn ℝ univ L) {K : ℝ≥0} (hh : LipschitzWith K h) :
    ∃ C : ℝ≥0, LipschitzWith C (forwardValue L h) := by
  have hcont : Continuous L := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨C, hC, hLC, hbound⟩ := exists_trace_constant hL K
  refine ⟨K + ⟨C, hC⟩, lipschitzWith_forwardValue_of_forward ?_⟩
  exact lipschitzOnWith_forward hcont hL hconv hh hC hLC hbound

end HamiltonJacobi.HopfLax
