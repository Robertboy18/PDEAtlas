/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.ConeSolution
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.TimeExtension
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Solution

/-!
# Local classical existence with a C² reaction in three dimensions

The uniform cone construction supplies the nonlinear field. Its normalized
integral equation identifies it, at short nonnegative times, with a free
Kirchhoff wave plus the classical Duhamel potential. This representative
has joint C² regularity across time zero and the ordinary Cauchy traces.
Only C² regularity of the scalar reaction and bounded C² velocity are used.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common BoundedContinuousFunction
open PDE (partialDeriv)
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower

/-- A C² scalar source and bounded C² initial velocity construct a
local solution in three dimensions. The displacement is zero, and the
representative is jointly C² even across the initial slice. -/
theorem exists_solutionBefore_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h : ℝ^3 →ᵇ ℝ) (hh : ContDiff ℝ 2 h) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧ IsSolutionBefore (fun z ↦ -f z) (fun _ ↦ 0) h T u := by
  obtain ⟨T, hT, v, hv, hveq⟩ := exists_cone_solution hf h hh
  obtain ⟨S, hS, hST, V, hV, hVeq⟩ := exists_time_extension hT hv
  let F : ℝ^4 → ℝ := f ∘ V ∘ timeSpaceContinuousLinearEquiv 3
  have hF : ContDiff ℝ 2 F := hf.comp (hV.comp (timeSpaceContinuousLinearEquiv 3).contDiff)
  have hD := contDiff_two_oddDuhamelSolution 0 hF.contDiffOn
  have hH := contDiff_kirchhoffPotential hh
  let u : ℝ^4 → ℝ := fun p ↦ kirchhoffPotential h p + oddDuhamelSolution 0 F p
  have hu : ContDiff ℝ 2 u := hH.add hD
  have hidentify {t : ℝ} (ht : t ∈ Ico 0 S) (x : ℝ^3) :
      u (timeSpaceCons t x) = v (t, x) := by
    rw [hveq (t, x) (by simpa only [abs_of_nonneg ht.1] using ht.2.trans hST)]
    change kirchhoffPotential h (timeSpaceCons t x) + oddDuhamelSolution 0 F (timeSpaceCons t x) = _
    rw [kirchhoffPotential_timeSpaceCons, oddDuhamelSolution_zero_eq_normalized F x ht.1]
    congr 2
    congr 1 with s
    congr 3 with ω
    have hs : |t * (s : ℝ)| < S := by
      rw [abs_of_nonneg (mul_nonneg ht.1 s.2.1)]
      exact (mul_le_of_le_one_right ht.1 s.2.2).trans_lt ht.2
    change f (V (timeSpaceContinuousLinearEquiv 3 (timeSpaceCons (t * (s : ℝ))
      (x + t • ((1 - (s : ℝ)) • (ω : ℝ^3)))))) = _
    simp only [timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons]
    rw [hVeq _ hs]
  refine ⟨S, u, hu, hS, hu.contDiffOn, ?_, ?_, ?_⟩
  · intro p hp
    change waveOperator (fun q ↦ kirchhoffPotential h q + oddDuhamelSolution 0 F q) p = - -f (u p)
    rw [waveOperator_add hH.contDiffAt hD.contDiffAt,
      waveOperator_kirchhoffPotential_nonneg hh hp.1,
      waveOperator_oddDuhamelSolution 0 hF.contDiffOn hp.1, zero_add, neg_neg]
    change f (V (p 0, spatialPart p)) = f (u p)
    rw [hVeq _ (by simpa only [abs_of_nonneg hp.1] using hp.2)]
    exact congrArg f (by
      simpa only [timeSpaceCons_spatialPart] using (hidentify hp (spatialPart p)).symm)
  · intro x
    simp only [u, kirchhoffPotential_timeSpaceCons, zero_mul, oddDuhamelSolution_initial, add_zero]
  · intro x
    rw [show u = fun p ↦ kirchhoffPotential h p + oddDuhamelSolution 0 F p from rfl,
      PDE.partialDeriv_add (hH.differentiable (by norm_num) _)
        (hD.differentiable (by norm_num) _),
      partialDeriv_kirchhoffPotential_initial (hh.of_le (by norm_num)),
      partialDeriv_oddDuhamelSolution_initial 0 hF.contDiffOn, add_zero]

end WaveEquation.SmallData.Classical.LocalPower
