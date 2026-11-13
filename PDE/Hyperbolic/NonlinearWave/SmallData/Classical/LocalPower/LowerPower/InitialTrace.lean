/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.Cone
public import PDE.Analysis.Calculus.SphericalMean.Regularity

/-!
# Initial traces from the regular nonlinear remainder

The factor `t²` in the retarded term gives zero initial displacement and the
prescribed ordinary velocity trace for the constructed C¹ field. These traces
hold from both sides of the initial slice.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis
open scoped Topology

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- A C¹ remainder multiplied by `t²` does not change either Cauchy trace
of the zero-displacement Kirchhoff potential. -/
theorem cauchy_traces_of_remainder {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 1 h) {T : ℝ} (hT : 0 < T)
    {v a : ℝ × ℝ^3 → ℝ} (ha : ContDiffOn ℝ 1 a {p | |p.1| < T})
    (heq : ∀ p : ℝ × ℝ^3, |p.1| < T → v p = p.1 * unitSphereAverage 3 h p.2 p.1 + p.1 ^ 2 * a p) :
    (∀ x, v (0, x) = 0) ∧ ∀ x, HasDerivAt (fun t ↦ v (t, x)) (h x) 0 := by
  have hzero (x : ℝ^3) : v (0, x) = 0 := by
    simpa using heq (0, x) (by simpa using hT)
  refine ⟨hzero, fun x ↦ ?_⟩
  have hnear : {p : ℝ × ℝ^3 | |p.1| < T} ∈ 𝓝 (0, x) :=
    (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simpa using hT)
  have hac : ContDiffAt ℝ 1 (fun t : ℝ ↦ a (t, x)) 0 :=
    (ha.contDiffAt hnear).comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hd := ((hasDerivAt_id (0 : ℝ)).fun_mul (hasDerivAt_unitSphereAverage h x 0 hh)).fun_add
    (((hasDerivAt_id (0 : ℝ)).fun_pow 2).fun_mul (hac.differentiableAt one_ne_zero).hasDerivAt)
  have htrace : HasDerivAt
      (fun t : ℝ ↦ t * unitSphereAverage 3 h x t + t ^ 2 * a (t, x)) (h x) 0 := by
    simpa [unitSphereAverage_zero] using hd
  apply htrace.congr_of_eventuallyEq
  filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear] with t ht
  exact heq (t, x) ht

/-- If the reaction fixes zero, the normalized nonlinear remainder also
vanishes on the initial slice. -/
theorem remainder_initial_zero {f : ℝ → ℝ} (hf : f 0 = 0) {T : ℝ} (hT : 0 < T) {v a : ℝ × ℝ^3 → ℝ}
    (hv : ∀ x, v (0, x) = 0)
    (ha : ∀ p : ℝ × ℝ^3, |p.1| < T → a p = ∫ s : unitInterval,
      (1 - (s : ℝ)) * ((∫ ω : Direction, f (v (p.1 * (s : ℝ),
      p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
      ∂((MeasureTheory.volume : MeasureTheory.Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) :
    ∀ x, a (0, x) = 0 := by
  intro x
  simpa [hv, hf] using ha (0, x) (by simpa using hT)

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
