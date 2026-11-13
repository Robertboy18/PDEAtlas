/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.ClassicalStrip

/-!
# Global forward classical nonlinear waves on the real line

Compatible strip fields agree locally with fixed classical extensions. This gives
a single C² spacetime field solving the nonlinear PDE at every nonnegative time.
The negative-time extension is used for regularity and traces only.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter Function
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- The classical extensions agree wherever both forward strips are defined. -/
theorem classicalStripExtension_eq_of_mem {L S T : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) {p : ℝ^2} (hpS : p 0 ∈ Icc (0 : ℝ) (S : ℝ)) (hpT : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) :
    classicalStripExtension hf g h S p = classicalStripExtension hf g h T p := by
  have he {S T : NNReal} (hST : S ≤ T) (hpS : p 0 ∈ Icc (0 : ℝ) (S : ℝ))
      (hpT : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) :
      classicalStripExtension hf g h S p = classicalStripExtension hf g h T p := by
    rw [classicalStripExtension_eq_on_strip hf g h hpS,
      classicalStripExtension_eq_on_strip hf g h hpT]
    have hproj : stripEmbedding hST (stripProjection S p) = stripProjection T p := by
      change stripEmbedding hST (projIcc (0 : ℝ) S S.coe_nonneg (p 0), p 1) =
        (projIcc (0 : ℝ) T T.coe_nonneg (p 0), p 1)
      rw [projIcc_of_mem S.coe_nonneg hpS, projIcc_of_mem T.coe_nonneg hpT]
      rfl
    have hres := congrArg (fun u : ForwardStrip S →ᵇ ℝ ↦ u (stripProjection S p))
      (stripRestriction_nonlinearStripSolution hf g h hST)
    change nonlinearStripSolution hf g h T (stripEmbedding hST (stripProjection S p)) =
      nonlinearStripSolution hf g h S (stripProjection S p) at hres
    rw [hproj] at hres
    exact hres.symm
  rcases le_total S T with hST | hTS
  · exact he hST hpS hpT
  · exact (he hTS hpT hpS).symm

/-- Compatible finite-strip solutions define one field for every forward time.
For negative times this chooses a smooth extension from the unit strip. -/
def nonlinearClassicalSolution {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (p : ℝ^2) : ℝ :=
  classicalStripExtension hf g h ⟨max 0 (p 0) + 1, by positivity⟩ p

/-- The global field agrees with every classical extension on its forward strip. -/
theorem nonlinearClassicalSolution_eq_on_strip {L T : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) {p : ℝ^2} (hp : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) :
    nonlinearClassicalSolution hf g h p = classicalStripExtension hf g h T p := by
  apply classicalStripExtension_eq_of_mem hf g h _ hp
  exact ⟨hp.1, (le_max_right 0 (p 0)).trans (le_add_of_nonneg_right zero_le_one)⟩

/-- Near the initial slice the global field is the fixed unit-strip extension. -/
theorem nonlinearClassicalSolution_eq_one_of_lt {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) {p : ℝ^2} (hp : p 0 < 1) :
    nonlinearClassicalSolution hf g h p = classicalStripExtension hf g h 1 p := by
  by_cases ht : 0 ≤ p 0
  · exact nonlinearClassicalSolution_eq_on_strip hf g h ⟨ht, hp.le⟩
  · have hT : (⟨max 0 (p 0) + 1, by positivity⟩ : NNReal) = 1 := by
      apply Subtype.ext
      simp [max_eq_left (le_of_not_ge ht)]
    exact congrArg (fun T : NNReal ↦ classicalStripExtension hf g h T p) hT

/-- Every spacetime point has a neighborhood represented by one fixed smooth strip extension. -/
theorem nonlinearClassicalSolution_locally_eq_extension {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (p : ℝ^2) :
    ∃ T : NNReal, nonlinearClassicalSolution hf g h =ᶠ[𝓝 p] classicalStripExtension hf g h T ∧
      (0 ≤ p 0 → p 0 ≤ T) := by
  have hc : Continuous (fun q : ℝ^2 ↦ q 0) := PiLp.continuous_apply 2 _ 0
  by_cases hp : p 0 < 1
  · refine ⟨1, ?_, fun _ ↦ hp.le⟩
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hp)] with q hq
    exact nonlinearClassicalSolution_eq_one_of_lt hf g h hq
  · have hp0 : 0 < p 0 := lt_of_lt_of_le zero_lt_one (le_of_not_gt hp)
    let T : NNReal := ⟨p 0 + 1, by positivity⟩
    have hpT : p 0 < T := by
      change p 0 < p 0 + 1
      linarith
    refine ⟨T, ?_, fun _ ↦ hpT.le⟩
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hp0),
      hc.continuousAt.eventually (gt_mem_nhds hpT)] with q hq0 hqT
    exact nonlinearClassicalSolution_eq_on_strip hf g h ⟨hq0.le, hqT.le⟩

/-- The compatible field is jointly classical on spacetime, including the initial slice. -/
theorem contDiff_two_nonlinearClassicalSolution {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 2 (nonlinearClassicalSolution hf g h) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨T, he, _⟩ := nonlinearClassicalSolution_locally_eq_extension hf g h p
  have hreg := (contDiff_two_classicalStripExtension hf hf₁ hg hh T).contDiffAt (x := p)
  exact hreg.congr_of_eventuallyEq he

/-- The global field solves `u_tt - u_xx = -f(u)` at every nonnegative time. -/
theorem waveOperator_nonlinearClassicalSolution {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {p : ℝ^2}
    (hp : 0 ≤ p 0) :
    waveOperator (n := 1) (nonlinearClassicalSolution hf g h) p =
      -f (nonlinearClassicalSolution hf g h p) := by
  obtain ⟨T, he, hpT⟩ := nonlinearClassicalSolution_locally_eq_extension hf g h p
  have hj (i : Fin 2) : (∂[i] (∂[i] (nonlinearClassicalSolution hf g h))) p =
        (∂[i] (∂[i] (classicalStripExtension hf g h T))) p := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero, id_eq] using
      PDE.iterate_partialDeriv_congr_nhds i 2 he
  have hop : waveOperator (n := 1) (nonlinearClassicalSolution hf g h) p =
      waveOperator (n := 1) (classicalStripExtension hf g h T) p := by
    simp only [waveOperator, hj]
  rw [hop, waveOperator_classicalStripExtension hf hf₁ hg hh ⟨hp, hpT hp⟩, he.eq_of_nhds]

/-- The global field attains the bounded initial displacement. -/
theorem nonlinearClassicalSolution_initial_position {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (x : ℝ^1) :
    nonlinearClassicalSolution hf g h (timeSpaceCons 0 x) = g (x 0) := by
  rw [nonlinearClassicalSolution_eq_one_of_lt hf g h (by simp),
    classicalStripExtension_initial_position]

/-- The global field attains the bounded initial velocity. -/
theorem nonlinearClassicalSolution_initial_velocity {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) (x : ℝ^1) :
    (∂[0] (nonlinearClassicalSolution hf g h)) (timeSpaceCons 0 x) = h (x 0) := by
  obtain ⟨T, he, _⟩ := nonlinearClassicalSolution_locally_eq_extension hf g h (timeSpaceCons 0 x)
  have hj : (∂[0] (nonlinearClassicalSolution hf g h)) (timeSpaceCons 0 x) =
      (∂[0] (classicalStripExtension hf g h T)) (timeSpaceCons 0 x) :=
    congrArg (fun A : ℝ^2 →L[ℝ] ℝ ↦ A (EuclideanSpace.single 0 1)) he.fderiv_eq
  rw [hj, classicalStripExtension_initial_velocity hf hf₁ hg hh T x]

/-- Displacement has the prescribed joint spacetime trace at every initial point. -/
theorem tendsto_nonlinearClassicalSolution_initial {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (x : ℝ^1) :
    Tendsto (nonlinearClassicalSolution hf g h) (𝓝 (timeSpaceCons 0 x)) (𝓝 (g (x 0))) := by
  simpa only [ContinuousAt, nonlinearClassicalSolution_initial_position] using
    (contDiff_two_nonlinearClassicalSolution hf hf₁ hg hh).continuous.continuousAt
      (x := timeSpaceCons 0 x)

/-- Velocity has the prescribed joint spacetime trace at every initial point. -/
theorem tendsto_partialDeriv_nonlinearClassicalSolution_initial {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) (x : ℝ^1) :
    Tendsto (∂[0] (nonlinearClassicalSolution hf g h)) (𝓝 (timeSpaceCons 0 x)) (𝓝 (h (x 0))) := by
  have hc := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0)
    (contDiff_two_nonlinearClassicalSolution hf hf₁ hg hh)
  simpa only [ContinuousAt, nonlinearClassicalSolution_initial_velocity hf hf₁ hg hh] using
    hc.continuous.continuousAt (x := timeSpaceCons 0 x)

end WaveEquation
