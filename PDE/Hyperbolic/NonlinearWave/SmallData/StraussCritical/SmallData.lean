/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.Lifespan
public import PDE.Spaces.Sobolev.Approximation.Density.SmallNorm

/-!
# Arbitrarily small smooth data at the critical Strauss exponent

The data are nonnegative test functions with positive integral, fixed
support, and arbitrarily small canonical integer-order `L²` Sobolev norm.
All classical solutions for these data have a common finite duration bound.
The construction uses the small-norm mollifier family.

The data class is nonempty.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set SobolevSpace.GraphSpace TopologicalSpace
open scoped Distributions Sobolev

namespace WaveEquation.SmallData

/-- Smooth compact velocities of arbitrarily small Sobolev norm have a
common finite classical duration bound at `p=1+√2`, with zero displacement. -/
theorem exists_small_data_classical_duration_bound_three_at_strauss (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : 𝓓((⊤ : Opens (ℝ^3)), ℝ),
      (∀ x, 0 ≤ h x) ∧
      (∀ x, 2 ≤ ‖x‖ → h x = 0) ∧
      0 < ∫ x, h x ∧
      ‖globalTestFunctionToWkpOn (k := k) (p := 2) (Ω := univ) h‖ < ε ∧
      ∃ B : ℝ, 0 < B ∧ ∀ T : ℝ, 0 < T → ∀ u : ℝ^4 → ℝ,
        ContDiffOn ℝ 2 u {z | z 0 < T} →
        (∀ z, z 0 ∈ Ico 0 T → waveOperator u z = |u z| ^ (1 + Real.sqrt 2)) →
        (∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0) →
        (∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) → T ≤ B := by
  obtain ⟨h, hhn, hsupport, hpositive, hnorm⟩ := exists_nonneg_testFunction_sobolevNorm_lt 3 k 2 hε
  exact ⟨h, hhn, hsupport, hpositive, hnorm,
    Classical.exists_classical_duration_bound_three_at_strauss
      (h.contDiff.of_le (by simp)) hhn (fun x hx ↦ hsupport x hx.le)
      (by norm_num) hpositive⟩

end WaveEquation.SmallData
