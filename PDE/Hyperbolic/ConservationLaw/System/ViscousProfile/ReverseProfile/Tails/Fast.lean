/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Connection
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.FastLogCosh

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import CAS.ExactTactic

/-!
# A fast log-cosh tail through section one

A smooth taper beyond state two lets the scalar connection theorem
construct an orbit through one. Monotonicity keeps its nonpositive-time branch
in `(0,1]`, where the tapered field is exactly the physical scalar field.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter Set
open scoped Topology

/-- A nonnegative log-cosh perturbation has an incoming tail through one
for every speed below two. The equation holds with an ordinary derivative at
all nonpositive times, including zero. The C² extension at positive times is auxiliary. -/
theorem exists_fastLogCosh_tail_at_one {δ μ : ℝ} (hδ : 0 ≤ δ) (hμ : μ < 2) :
    ∃ z : ℝ → ℝ, z 0 = 1 ∧ ContDiff ℝ 2 z ∧
      (∀ t ≤ 0, z t ∈ Ioc 0 1 ∧ HasDerivAt z (fastLogCosh δ (z t) - μ * z t) t) ∧
      Tendsto z atBot (𝓝 0) ∧ Tendsto (deriv z) atBot (𝓝 0) := by
  let f : ℝ → ℝ := fun s ↦ fastLogCosh δ s - μ * s
  let F : ℝ → ℝ := fun s ↦ (1 - Real.smoothTransition (s - 2)) * f s
  have hf : ContDiff ℝ 1 f :=
    ((contDiff_fastLogCosh δ).of_le (by simp)).sub (contDiff_const.mul contDiff_id)
  have hF : ContDiff ℝ 1 F := (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (contDiff_id.sub contDiff_const))).mul hf
  have hfzero : f 0 = 0 := by simp [f, fastLogCosh]
  have hFzero : F 0 = 0 := by simp only [F, hfzero, mul_zero]
  have hFthree : F 3 = 0 := by
    have hstep : Real.smoothTransition ((3 : ℝ) - 2) = 1 :=
      Real.smoothTransition.one_of_one_le (by cas)
    simp only [F, hstep, sub_self, zero_mul]
  have hfpos (s : ℝ) (hs : 0 < s) : 0 < f s := by
    have hlinear : 0 < (2 - μ) * s := mul_pos (sub_pos.mpr hμ) hs
    have hlog : 0 ≤ δ * Real.log (Real.cosh s) :=
      mul_nonneg hδ (Real.log_nonneg (Real.one_le_cosh s))
    have heq : f s = (2 - μ) * s + δ * Real.log (Real.cosh s) := by
      dsimp only [f, fastLogCosh]
      generalize Real.log (Real.cosh s) = ell
      cas
    rw [heq]
    exact add_pos_of_pos_of_nonneg hlinear hlog
  have hFpos : ∀ s ∈ Ioo (0 : ℝ) 3, 0 < F s := by
    intro s hs
    have hslt : s - 2 < 1 := by
      have h := hs.2
      cas
    exact mul_pos (sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one hslt)) (hfpos s hs.1)
  have hFeq (s : ℝ) (hs : s ≤ 1) : F s = f s := by
    have hstep : Real.smoothTransition (s - 2) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by cas)
    simp only [F, hstep, sub_zero, one_mul]
  obtain ⟨z, hz0, hzC2, hzd, hzrange, hzmono, hzlimit, _, hdlimit, _⟩ :=
    Evolution.Scalar.exists_heteroclinic_of_pos (a := 0) (b := 3) (x₀ := 1)
      hF.contDiffOn hFzero hFthree hFpos (by constructor <;> cas)
  refine ⟨z, hz0, hzC2, ?_, hzlimit, hdlimit⟩
  intro t ht
  have hzle : z t ≤ 1 := by
    simpa only [hz0] using hzmono.monotone ht
  exact ⟨⟨(hzrange t).1, hzle⟩, (hzd t).congr_deriv (hFeq (z t) hzle)⟩

end PDE.Analysis
