/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakFiniteTrace
public import PDE.Fluid.DeGregorio.Iteration.Picard.CoupledShapeRepresentative

/-!
# Picard restart from the constructed weak terminal state

The finite-time weak energy estimate constructs the terminal H² graph.
Oddness survives its locally uniform trace. The Picard existence theorem then
constructs a new coupled output from that graph, and every spatial trace of the
trajectory at the terminal time agrees with the initial slice of the new output.

The new output solves the physical equation in its own local time; the endpoint
normalization is applied to it afterwards. At radius ten its odd supported datum has
the shape required by the normalized local-trajectory construction.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio

/-- A locally H²-bounded normalized rescaled trajectory with uniform H¹ control can be
restarted by the Picard theorem at its terminal time. The initial datum of the restart
is odd and has the original support, so the same endpoint normalization can be applied
to this output. -/
theorem IsClassicalRescaledSolutionOn.exists_terminal_picard_restart_of_local_h2_h1
    {fields : Fields} {ρ : ℝ → ℝ} {a t₀ T R M : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T) (hR : 0 < R)
    {F : ℝ → DerivLp 1 2 univ}
    (hlocal : ∀ c d : ℝ, Icc c d ⊆ Ioo a T →
      ∃ B : NNReal, ∀ t ∈ Icc c d, F t ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hH1 : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ M)
    (hodd : ∀ t ∈ Ioo a T, Function.Odd (fun x ↦ fields.vorticity x t)) :
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (D : NNReal)
      (G : C(Icc (0 : ℝ) S, supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
          Icc (-(R * Real.exp 2)) (R * Real.exp 2)) D))
      (d z : ℝ → ℝ → ℝ),
      ContDiff ℝ 1 v ∧ Function.Odd v ∧ tsupport v ⊆ Icc (-R) R ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ) =ᵐ[volume] v ∧
      Iteration.IsHkFrozenOutput hS.le G G U v d z ∧
      IsClassicalSolutionOn 1 ⟨z, Iteration.hkCurveHilbertVelocity hS.le G⟩ (Ioo 0 S) ∧
      Tendsto F (𝓝[<] T) (𝓝 (G ⟨0, le_rfl, hS.le⟩).val) ∧
      (∀ A : Set ℝ, IsCompact A →
        TendstoUniformlyOn (fun t x ↦ fields.vorticity x t)
          (fun x ↦ z x 0) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ fields.vorticity x t))
          (deriv (fun x ↦ z x 0)) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ fields.velocity x t))
          (fun x ↦ d x 0) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t x ↦ fields.velocity x t)
          (fun x ↦ Iteration.hkCurveHilbertVelocity hS.le G x 0) (𝓝[<] T) A) ∧
      Tendsto ρ (𝓝[<] T)
        (𝓝 (-Iteration.hkCurveHilbertVelocity hS.le G R 0 / R)) := by
  obtain ⟨_, U, v, _, _, _, hv, hs, hUrep, hlim, _, htraces, hρ, _⟩ :=
    hsol.exists_h2_terminal_of_local_h2_h1 ht₀ hR isCompact_Icc
      hlocal hrep hzero hnormalized hH1
  have hvodd : Function.Odd v := by
    intro x
    have hx := (htraces {x} isCompact_singleton).1.tendsto_at (mem_singleton x)
    have hneg := (htraces {-x} isCompact_singleton).1.tendsto_at (mem_singleton (-x))
    apply tendsto_nhds_unique hneg
    apply hx.neg.congr'
    filter_upwards [Ioo_mem_nhdsLT (ht₀.1.trans ht₀.2)] with t ht
    exact (hodd t ht x).symm
  have hout (x : ℝ) (hx : R < |x|) : v x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ (not_le_of_gt hx) (abs_le.mpr (hs h))
  obtain ⟨S, hS, D, G, d, z, hG, hphysical, _⟩ :=
    Iteration.exists_hkCurve_local_solution_unique_in_ball hR.le U hv.continuous hUrep hout
  have hz : (fun x ↦ z x 0) = v := funext hG.initial
  have hd : (fun x ↦ d x 0) = hilbertPV v := by
    rw [hG.coefficient_eq_hilbertPV_on_Icc (left_mem_Icc.mpr hS.le), hz]
  have hu : (fun x ↦ Iteration.hkCurveHilbertVelocity hS.le G x 0) =
      hilbertPVVelocity v := by
    rw [hG.velocity_eq_hilbertPVVelocity_on_Icc (left_mem_Icc.mpr hS.le), hz]
  refine ⟨U, v, S, hS, D, G, d, z, hv, hvodd, hs, hUrep, hG, hphysical, ?_, ?_, ?_⟩
  · simpa only [hG.initial_base] using hlim
  · intro A hA
    simpa only [hz, hd, hu] using htraces A hA
  · simpa only [congrFun hu R] using hρ

end DeGregorio
