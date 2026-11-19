/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Classical.Lifespan
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.SmallData

/-!
# Small smooth data with norm blowup at the maximal classical time

The constructed quadratic H⁵ × H⁴ wave has the greatest duration among all
same-data C² competitors. Its Sobolev norm tends to infinity at that
positive finite classical endpoint. All data and solution witnesses are
constructed from a positive size bound.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Common Set SobolevSpace SobolevSpace.GraphSpace TopologicalSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped Distributions ENNReal NNReal Sobolev Topology

namespace WaveEquation.SmallData.Classical.NormBlowup

/-- Arbitrarily small smooth nonnegative compact velocity produces a
quadratic classical wave whose linked H⁵ × H⁴ norm diverges at the supremum of
all same-data C² existence durations. -/
theorem exists_small_data_maximal_classical_norm_blowup {ε : ℝ} (hε : 0 < ε) :
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
      existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0) h = Ioc 0 T ∧
      T = sSup (existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0) h) ∧
      ∃ u : ℝ^4 → ℝ,
        IsMaximalSolutionBefore (fun z ↦ -(z ^ 2)) (fun _ ↦ 0) h T u ∧
        ∀ t ∈ Ico 0 T, ∀ x,
          u (timeSpaceCons t x) = classicalRepresentativeCLM (by norm_num) (U t).1 x ∧
          (∂[0] u) (timeSpaceCons t x) =
            classicalRepresentativeCLM (by norm_num) (U t).2 x := by
  obtain ⟨h, hhn, hs, hp, hHsmall, hsmall, hT, hinit, hmild, hdiv, _hmax, u, hu, hrep⟩ :=
    exists_small_data_quadratic_norm_blowup hε
  let H := globalTestFunctionToWkpOn (k := 5) (p := 2) (Ω := univ) h
  have he : (classicalRepresentativeCLM (by norm_num) H : ℝ^3 → ℝ) = h :=
    classicalRepresentative_mkWkpSpaceOnOfContDiff (by norm_num) h.contDiff h.hasCompactSupport
  have hs' : ∀ x, (2 : ℝ) < ‖x‖ →
      classicalRepresentativeCLM (by norm_num) H x = 0 := by
    intro x hx
    rw [congrFun he x]
    exact hs x hx.le
  have hp' : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x := by
    simpa only [he] using hp
  have hE : existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0) h =
      Ioc 0 (quadraticLifespan H).toReal := by
    simpa only [he] using quadratic_existenceTimes_eq H hs' (by norm_num) hp'
  have hsup : (quadraticLifespan H).toReal =
      sSup (existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0) h) := by
    simpa only [he] using quadratic_terminalTime_eq_csSup H hs' (by norm_num) hp'
  refine ⟨h, hhn, hs, hp, hHsmall, hsmall, hT, hinit, hmild, hdiv, hE, hsup, u, ⟨hu, ?_⟩, hrep⟩
  intro S v hS hv _
  have hmem : S ∈ existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0) h := ⟨v, hv⟩
  rw [hE] at hmem
  exact (not_lt_of_ge hmem.2) hS

end WaveEquation.SmallData.Classical.NormBlowup
