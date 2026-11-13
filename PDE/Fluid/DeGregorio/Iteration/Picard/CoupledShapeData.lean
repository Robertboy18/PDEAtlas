/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.CoupledShapeOddness
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SmoothData

/-!
# Smooth odd supported data give a coupled solution with shape

Only the initial smooth function, its oddness, and a support interval are
prescribed. The Sobolev initial graph, positive lifespan, uniform graph bound,
Hilbert coefficient, classical representative, and their closed traces all
come from the Picard construction. The solution lies in the supported H² class.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The same H¹ graphs used by the closed-slab and weak-limit theorems inherit
oddness, a common compact support, and the stored L² derivative bound. -/
theorem IsHkFrozenOutput.exists_odd_supported_h1_trace
    {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
    {F : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
    {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hodd : Function.Odd w₀) :
    ∃ g : Icc (0 : ℝ) T → W^{1,2}((Set.univ : Set (ℝ^1))),
      (∀ t, ‖g t‖ ≤ B) ∧
      (∀ t, realLineRepresentative (g t) = fun x ↦ w x t) ∧
      (∀ t, realLineCoordinateCLM (baseIndex 1 1) (g t) =
        oneDimensionalPushforwardL2 (F t).val) ∧
      Continuous (fun t ↦ realLineCoordinateCLM (baseIndex 1 1) (g t)) ∧
      ∀ t, Function.Odd (realLineRepresentative (g t)) ∧
        tsupport (realLineRepresentative (g t)) ⊆ Icc (-R) R ∧
        MemLp (deriv (realLineRepresentative (g t))) 2 volume ∧
        (∫ x, deriv (realLineRepresentative (g t)) x ^ 2) ≤ (B : ℝ) ^ 2 := by
  obtain ⟨g, hg, hrep, hbase, hc⟩ := h.exists_h1_trace
  refine ⟨g, hg, hrep, hbase, hc, fun t ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [hrep t]
    exact h.odd_vorticity_on_Icc hodd t.property
  · rw [hrep t]
    exact h.tsupport_on_Icc t.property
  · have hd := deriv_realLineRepresentative_L2_bound (g t)
    exact ⟨hd.1, hd.2.trans (pow_le_pow_left₀ (norm_nonneg _) (hg t) 2)⟩

/-- Smooth odd data supported in `[-S,S]` have a coupled local solution, unique among
coupled outputs in the same supported H² ball. The closed-slab representatives have
odd vorticity and velocity, an even principal-value coefficient, and support in
`[-S exp 2,S exp 2]`.
The same H¹ graphs give the L²-continuous trace used by the stationary limit theorem. -/
theorem exists_odd_supported_local_solution_of_contDiff
    {S : ℝ} (hS : 0 ≤ S) {w₀ : ℝ → ℝ}
    (hw₀ : ContDiff ℝ (⊤ : ℕ∞) w₀) (hodd : Function.Odd w₀)
    (hsupp : Function.support w₀ ⊆ Icc (-S) S) :
    ∃ (T : ℝ) (hT : 0 < T) (B : NNReal) (W₀ : W^{2,2}((Set.univ : Set (ℝ^1))))
      (F : C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
            Icc (-(S * Real.exp 2)) (S * Real.exp 2)) B))
      (c w : ℝ → ℝ → ℝ),
      IsHkFrozenOutput hT.le F F W₀ w₀ c w ∧
      IsClassicalSolutionOn 1
        ⟨w, fun x t ↦ hilbertPVVelocity (fun y ↦ w y t) x⟩ (Ioo 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Function.Odd (fun x ↦ w x t) ∧
        Function.Odd (fun x ↦ hkCurveHilbertVelocity hT.le F x t) ∧
        Function.Even (fun x ↦ c x t) ∧
        tsupport (fun x ↦ w x t) ⊆ Icc (-(S * Real.exp 2)) (S * Real.exp 2) ∧
        HasCompactSupport (fun x ↦ w x t) ∧
        (fun x ↦ c x t) = hilbertPV (fun x ↦ w x t) ∧
        (fun x ↦ hkCurveHilbertVelocity hT.le F x t) =
          hilbertPVVelocity (fun x ↦ w x t)) ∧
      (∃ g : Icc (0 : ℝ) T → W^{1,2}((Set.univ : Set (ℝ^1))),
        (∀ t, ‖g t‖ ≤ B) ∧
        (∀ t, realLineRepresentative (g t) = fun x ↦ w x t) ∧
        (∀ t, realLineCoordinateCLM (baseIndex 1 1) (g t) =
          oneDimensionalPushforwardL2 (F t).val) ∧
        Continuous (fun t ↦ realLineCoordinateCLM (baseIndex 1 1) (g t))) ∧
      ∀ (G : C(Icc (0 : ℝ) T,
          supportedHkBaseBall 1 2 univ
            (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
              Icc (-(S * Real.exp 2)) (S * Real.exp 2)) B))
        (d z : ℝ → ℝ → ℝ), IsHkFrozenOutput hT.le G G W₀ w₀ d z → G = F := by
  have hcompact : HasCompactSupport w₀ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hsupp isClosed_Icc)
  obtain ⟨_, f₀, _, hf₀⟩ :=
    exists_supportedHkBaseBall_real_of_contDiff (k := 2) hw₀ hcompact measurableSet_Icc hsupp
  obtain ⟨W₀, _, hW₀⟩ := f₀.property.1
  have hrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀ := by
    rw [hW₀]
    exact hf₀
  have hzero (x : ℝ) (hx : S < |x|) : w₀ x = 0 := by
    by_contra hn
    exact (not_le_of_gt hx) (abs_le.mpr (hsupp hn))
  obtain ⟨T, hT, B, F, c, w, h, _, huniq⟩ :=
    exists_hkCurve_local_solution_unique_in_ball hS W₀ hw₀.continuous hrep hzero
  refine ⟨T, hT, B, W₀, F, c, w, h, h.isClassicalSolutionOn_hilbertPVVelocity,
    ?_, h.exists_h1_trace, huniq⟩
  intro t ht
  obtain ⟨hu, hc⟩ := h.odd_velocity_even_coefficient_on_Icc hodd ht
  exact ⟨h.odd_vorticity_on_Icc hodd ht, hu, hc, h.tsupport_on_Icc ht,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (h.tsupport_on_Icc ht),
    h.coefficient_eq_hilbertPV_on_Icc ht, h.velocity_eq_hilbertPVVelocity_on_Icc ht⟩

end DeGregorio.Iteration
