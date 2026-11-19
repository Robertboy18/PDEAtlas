/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Statement
public import PDE.Fluid.NavierStokes.Nonuniqueness.UnstableProfile
import PDE.Fluid.NavierStokes.ClassicalEnergy.LerayHopf
import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalSolution

/-!
# Nonuniqueness from an unstable profile

Every unstable profile gives the conclusion of Theorem 1 of Hou, Wang and Yang
(`of_unstableProfile`).

## How it works

We take the cutoff radius `R` equal to the threshold of the ancient family and the datum
`u_loc`, the far field `‖x‖⁻¹ A(x)` localized at radius `R`. It is compactly supported,
distributionally divergence free, smooth away from the origin and in `Lᵠ` for `q < 3`. For
`s ∈ [0, 1]` the physical velocity `u_s` and the Riesz pressure `p_s` of its slices form a
classical solution of the unforced problem with datum `u_loc` on `(0, 1) × ℝ³`
(`physical_classical`), in the classical energy class (`physical_classicalEnergyClass`), with
`L²` initial trace `u_loc` (`physical_trace`), and `suitableLerayHopf_of_classical` makes it a
suitable Leray–Hopf solution with horizon one. Its `L²` velocity class at time one is the class
of `u_s(1)`, and the slices `u_s(1)` of distinct parameters differ on a set of positive measure
(`eq_of_velocitySlice_physicalVelocity_one_ae_eq`), so the classes are pairwise distinct. The
`Lʳ(0, 1; Lᵠ)` bounds are those of the physical velocity (`physical_memLp_LsLq`). The steps
follow Section 2.2 of Hou, Wang and Yang; the ancient family, the cutoff and the energy
estimates behind them are proved in the imported modules.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Theorem 1, p. 1, and Section 2.2,
  pp. 11-15.
  <https://arxiv.org/abs/2509.25116v2>
-/

public section

open MeasureTheory Set

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- **Nonuniqueness from an unstable profile** (Hou, Wang and Yang, Theorem 1 and
Section 2.2). For every unstable profile there are a compactly supported
divergence-free datum, smooth away from the origin and in every `Lᵠ` with `q < 3`, and a family
of suitable Leray–Hopf solutions on `[0, 1]` with this datum, indexed by `s ∈ [0, 1]`, whose
velocities at time one are pairwise distinct `L²` classes. Each solution is smooth on
`(0, 1) × ℝ³` and lies in `Lʳ(0, 1; Lᵠ)` for `q ≥ 2`, `r ≥ 1` and `3/q + 2/r > 1`.

The datum is the far field `‖x‖⁻¹ A(x)` localized at the threshold radius of the ancient
family, and the solution of parameter `s` is the physical velocity of the ancient correction
with unstable terminal coordinate proportional to `s`, with the Riesz pressure of its slices. -/
theorem of_unstableProfile (D : UnstableProfile) : NonuniquenessConclusion := by
  set R := D.ancientThreshold
  have hR : D.ancientThreshold ≤ R := le_rfl
  have hR0 : 0 < R := lt_of_lt_of_le one_pos D.one_le_ancientThreshold
  have hhom : ∀ x (c : ℝ), 0 < c → ‖c • x‖⁻¹ • D.A (c • x) = c⁻¹ • (‖x‖⁻¹ • D.A x) :=
    fun x _ hc ↦ D.farField_smul x hc
  have hsmooth : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ ‖y‖⁻¹ • D.A y) x :=
    fun _ hx ↦ D.contDiffAt_farField hx
  have hu₀ := distributionallyDivergenceFree_localizedDatum hR0 hhom hsmooth
    D.datum_divergenceFree
  have hsol (s : Icc (0 : ℝ) 1) : ∃ sol : SuitableLerayHopfSolution
      (unforcedProblem (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) hu₀),
      sol.u = physicalVelocity D R s ∧ sol.p = physicalPressure D R s ∧ (sol.T : ℝ) = 1 := by
    have h := physical_classical hR s.2 hu₀
    exact suitableLerayHopf_of_classical hu₀ _ _ 1 (fun z hz ↦ ⟨(h z hz).1, (h z hz).2.1⟩)
      (fun z hz ↦ (h z hz).2.2.2) (fun z hz ↦ (h z hz).2.2.1)
      (physical_classicalEnergyClass hR s.2)
      (fun x ↦ physicalVelocity_timeSpaceCons_of_nonpos D R s le_rfl x) (physical_trace hR0)
  choose sol hu hp hT using hsol
  refine ⟨_, hu₀, hasCompactSupport_localizedDatum hR0,
    fun x hx ↦ contDiffAt_localizedDatum (hsmooth x hx),
    fun q hq ↦ D.memLp_localizedDatum hR0 hq, sol, hT, ?_, ?_, ?_⟩
  · intro s s' h
    have hslice (s : Icc (0 : ℝ) 1) :
        ((sol s).toPressureRepresentativeLerayHopfSolution.toLerayHopfSolution.toWeakSolution
          |>.velocityL2Slice 1 : ℝ^3 → ℝ^3) =ᵐ[volume]
          IncompressibleFlow.velocitySlice (physicalVelocity D R s) 1 := by
      rw [← hu s]
      exact WeakSolution.velocityL2Slice_apply_ae _
        (show (1 : ℝ) ∈ Icc 0 ((sol s).T : ℝ) by rw [hT s]; exact right_mem_Icc.mpr zero_le_one)
    have h1 := hslice s
    simp only at h
    rw [h] at h1
    exact Subtype.ext
      (eq_of_velocitySlice_physicalVelocity_one_ae_eq hR s.2 s'.2 (h1.symm.trans (hslice s')))
  · intro s z hz
    rw [hu s, hp s]
    exact ⟨(physical_classical hR s.2 hu₀ z hz).1, (physical_classical hR s.2 hu₀ z hz).2.1⟩
  · intro s q r hq hr hqr
    rw [hu s]
    exact physical_memLp_LsLq D s hR0 hq hr hqr

end NavierStokes.Nonuniqueness
