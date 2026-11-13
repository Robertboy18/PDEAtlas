/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Terminal
public import PDE.Spaces.Sobolev.Approximation.Density.SmallNorm
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.SmoothData

/-!
# Arbitrarily small smooth data with terminal higher Sobolev norm blowup

Positive multiples of a fixed compact smooth bump provide the initial velocity.
The canonical H⁵ norm of that velocity can be arbitrarily small, hence so can
the initial H⁵ × H⁴ state norm with zero displacement. The constructed
quadratic evolution has a positive finite higher lifetime, a jointly C²
classical observation with both Cauchy traces, and a state norm tending to
infinity at that lifetime.

No solution, amplitude estimate, continuation criterion, or lifespan conclusion
is an assumption. Maximality is in the higher mild class. The result does not
identify the endpoint with the supremum over all C² competitors.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Common Set SobolevSpace SobolevSpace.GraphSpace TopologicalSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped Distributions ENNReal NNReal Sobolev Topology

namespace WaveEquation.SmallData.Classical.NormBlowup

/-- Arbitrarily small nonnegative compact smooth velocity and zero displacement
produce a quadratic classical wave, represented by the constructed
maximal H⁵ × H⁴ trajectory, whose natural Sobolev norm tends to infinity at a
positive finite terminal time. All witnesses are constructed from the size bound. -/
theorem exists_small_data_quadratic_norm_blowup {ε : ℝ} (hε : 0 < ε) :
    ∃ h : 𝓓((⊤ : Opens (ℝ^3)), ℝ),
      (∀ x, 0 ≤ h x) ∧
      (∀ x, 2 ≤ ‖x‖ → h x = 0) ∧
      0 < ∫ x, h x ∧
      let H := globalTestFunctionToWkpOn (k := 5) (p := 2) (Ω := univ) h
      let U := quadraticTrajectory H
      let T := (quadraticLifespan H).toReal
      ‖H‖ < ε ∧ ‖U 0‖ < ε ∧ 0 < T ∧
      U 0 = (0, lowerOrderCLM (by omega : 4 ≤ 5) H) ∧
      (higherLinearSemigroup 3 4).IsMildSolutionBefore quadraticStateMap
        (0, lowerOrderCLM (by omega : 4 ≤ 5) H) T U ∧
      Tendsto (fun t ↦ ‖(U t).1‖ + ‖(U t).2‖) (𝓝[<] T) atTop ∧
      (¬ ∃ τ : ℝ≥0, T ≤ (τ : ℝ) ∧
        ∃ V : C(Icc (0 : ℝ) (τ : ℝ), W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3)),
          (higherLinearSemigroup 3 4).IsMildSolutionOn quadraticStateMap
            (0, lowerOrderCLM (by omega : 4 ≤ 5) H) τ V) ∧
      ∃ u : ℝ^4 → ℝ,
        IsSolutionBefore (fun z ↦ -(z ^ 2)) (fun _ ↦ 0) h T u ∧
        ∀ t ∈ Ico 0 T, ∀ x,
          u (timeSpaceCons t x) = classicalRepresentativeCLM (by norm_num) (U t).1 x ∧
          (∂[0] u) (timeSpaceCons t x) =
            classicalRepresentativeCLM (by norm_num) (U t).2 x := by
  obtain ⟨h, hhn, hs, hpositive, hnorm⟩ := exists_nonneg_testFunction_sobolevNorm_lt 3 5 2 hε
  let H := globalTestFunctionToWkpOn (k := 5) (p := 2) (Ω := univ) h
  have he : (classicalRepresentativeCLM (by norm_num) H : ℝ^3 → ℝ) = h :=
    classicalRepresentative_mkWkpSpaceOnOfContDiff (by norm_num) h.contDiff h.hasCompactSupport
  have hs' : ∀ x, (2 : ℝ) < ‖x‖ →
      classicalRepresentativeCLM (by norm_num) H x = 0 := by
    intro x hx
    rw [congrFun he x]
    exact hs x hx.le
  have hp' : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x := by
    simpa only [he] using hpositive
  have hfinite := quadraticLifespan_ne_top H hs' (by norm_num) hp'
  have hsmall : ‖quadraticTrajectory H 0‖ < ε := by
    rw [quadraticTrajectory_zero, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    exact (norm_lowerOrderCLM_apply_le (by omega : 4 ≤ 5) H).trans_lt hnorm
  obtain ⟨u, hu, hrep⟩ := exists_classical_quadratic_terminal H hs' hp'
  refine ⟨h, hhn, hs, hpositive, hnorm, hsmall,
    quadratic_terminalTime_pos H hs' (by norm_num) hp', quadraticTrajectory_zero H,
    isMildSolutionBefore_quadraticTrajectory H hfinite,
    tendsto_norm_sum_quadraticTrajectory H hs' (by norm_num) hp',
    not_exists_quadratic_mild_at_terminal H hs' (by norm_num) hp', u, ?_, hrep⟩
  simpa only [he] using hu

end WaveEquation.SmallData.Classical.NormBlowup
