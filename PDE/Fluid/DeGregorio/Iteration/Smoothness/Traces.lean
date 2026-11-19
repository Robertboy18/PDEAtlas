/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Smoothness.Bootstrap
import PDE.Analysis.Integration.Primitive.Basic

/-!
# Joint continuity of the spatial derivatives

For a coupled De Gregorio output with smooth compact datum, every spatial derivative
`∂ₓᵏ ω` is jointly continuous on `ℝ × [0, T]`. Along a characteristic, `∂ₓᵏ ω` is its initial value
plus the time integral of a bounded integrand: for `k ≥ 1` by the derivative tower of height `k`,
and for `k = 0` by the stretching identity. So it is Lipschitz in time uniformly in the label; in
the label it is continuous because every slice is smooth. Composing with the inverse
characteristics gives joint continuity in Eulerian coordinates.

## Main results

* `IsHkFrozenOutput.continuous_iterate_deriv`: joint continuity of every spatial derivative.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev ContDiff NNReal
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {T : ℝ} {B : NNReal} {R : ℝ} {hT : 0 ≤ T}
  {F : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}(ℝ^1)} {w₀ : ℝ → ℝ} {c w X Y : ℝ → ℝ → ℝ}

/-- Every spatial derivative of a coupled H² output of the De Gregorio equation with smooth
compactly supported datum is jointly continuous on `ℝ × [0, T]`. -/
theorem IsHkFrozenOutput.continuous_iterate_deriv (h : IsHkFrozenOutput hT F F W₀ w₀ c w)
    (hw₀ : ContDiff ℝ ∞ w₀) (hc₀ : HasCompactSupport w₀) (k : ℕ) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ deriv^[k] (fun y ↦ w y p.2) p.1) := by
  obtain ⟨W, hW, hWb, hWbase, hWrep⟩ := h.exists_measurable_h2_graph
  obtain ⟨X, Y, hX₀, hX', hXc, hYc, hYX, hXY, hYLip, _⟩ :=
    exists_hkCurve_hilbert_eulerian_coordinates hT F
  have hchar : HkCharacteristics hT F c X Y :=
    ⟨⟨h.coefficient_continuous, h.hilbert_pair, h.velocity_derivative,
      h.coefficient_bound, hX₀, hX', hXc⟩, hYc, hYX, hXY, hYLip⟩
  have hc := h.coefficient_eq_realHilbertH1 hWbase
  have hsmooth (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (fun x ↦ w x t) :=
    h.contDiff_vorticity hw₀ hc₀ t.property
  -- The characteristic identity of the `k`-th derivative with a bounded measurable integrand.
  have hident : ∃ (G : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)) (M : ℝ), StronglyMeasurable G ∧
      (∀ t, ‖G t‖ ≤ M) ∧ ∀ a (t : Icc (0 : ℝ) T),
        deriv^[k] (fun y ↦ w y t) (X a t) = deriv^[k] (fun y ↦ w y 0) a +
          ∫ s in 0..(t : ℝ), realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
            (G (projIcc 0 T hT s))) (X a s) := by
    have hk : 0 ≤ 36 * succOrderAssemblyNormBound 1 1 :=
      mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg
    rcases k with _ | n
    · refine ⟨fun t ↦ firstDerivativeSourceH2CLM (W t) (W t),
        36 * succOrderAssemblyNormBound 1 1 * B * B,
        firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable (hW.prodMk hW),
        fun t ↦ ?_, fun a t ↦ ?_⟩
      · exact (norm_firstDerivativeSourceH2CLM_apply_le _ _).trans (by gcongr <;> exact hWb t)
      · simpa only [hWrep, Function.iterate_zero, id] using
          h.integral_eq_source hchar hWrep hc a t
    · obtain ⟨q, hq0, htower⟩ := h.exists_derivTower hchar hW hWb hWrep hc hw₀ hc₀ n
      have hrep := htower.realLineRepresentative_eq (w := w) (by rw [hq0]; exact hWrep)
      obtain ⟨C, hC⟩ := htower.bounded
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by omega) ⟨0, le_rfl, hT⟩)
      have hmeas := htower.measurable
      have hlist {e : ℕ × ℕ × ℝ} (he : e ∈ forcingList (n + 1)) :
          e.1 < n + 1 ∧ e.2.1 < n + 1 := by
        have := mem_forcingList he
        omega
      obtain ⟨D, hD⟩ := exists_norm_sourceSum_le (q := q) (l := forcingList (n + 1)) (C := C)
        fun e he t ↦ ⟨hC _ (hlist he).1.le t, hC _ (hlist he).2.le t⟩
      refine ⟨levelSource q (n + 1),
        36 * succOrderAssemblyNormBound 1 1 * C * C +
          |1 - ((n + 1 : ℕ) : ℝ)| * (36 * succOrderAssemblyNormBound 1 1 * C * C) + D,
        ?_, fun t ↦ ?_, fun a t ↦ ?_⟩
      · have h1 := firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable
          ((hmeas 0 (by omega)).prodMk (hmeas (n + 1) le_rfl))
        have h2 := firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable
          ((hmeas (n + 1) le_rfl).prodMk (hmeas 0 (by omega)))
        have h3 := stronglyMeasurable_sourceSum (q := q) (l := forcingList (n + 1)) fun e he ↦
          ⟨hmeas _ (hlist he).1.le, hmeas _ (hlist he).2.le⟩
        exact (h1.add (h2.const_smul (1 - ((n + 1 : ℕ) : ℝ)))).add h3
      · simp only [levelSource]
        apply (norm_add_le _ _).trans
        gcongr
        · apply (norm_add_le _ _).trans
          gcongr
          · apply (norm_firstDerivativeSourceH2CLM_apply_le _ _).trans
            gcongr
            exacts [hC 0 (by omega) t, hC (n + 1) le_rfl t]
          · rw [norm_smul, Real.norm_eq_abs]
            gcongr
            apply (norm_firstDerivativeSourceH2CLM_apply_le _ _).trans
            gcongr
            exacts [hC (n + 1) le_rfl t, hC 0 (by omega) t]
        · exact hD t
      · have h0 : (fun y ↦ w y 0) = fun y ↦ w y ((⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) : ℝ) := rfl
        rw [h0, ← hrep (n + 1) le_rfl t, ← hrep (n + 1) le_rfl ⟨0, le_rfl, hT⟩]
        exact htower.integral_eq a t
  obtain ⟨G, M, hGm, hGb, hGeq⟩ := hident
  have hM : 0 ≤ 2 * M := by linarith [(norm_nonneg _).trans (hGb ⟨0, le_rfl, hT⟩)]
  have hGl : StronglyMeasurable (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (G t)) :=
    (lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable hGm
  have hGlb (t : Icc (0 : ℝ) T) : ‖lowerOrderCLM (by decide : 1 ≤ 2) (G t)‖ ≤ M :=
    (norm_lowerOrderCLM_apply_le _ _).trans (hGb t)
  -- Joint continuity along the characteristics.
  let Φ : ℝ × Icc (0 : ℝ) T → ℝ := fun p ↦ deriv^[k] (fun y ↦ w y p.2) (X p.1 p.2)
  have hΦ : Continuous Φ :=
    continuous_prod_of_continuous_lipschitzWith' Φ ⟨2 * M, hM⟩
      (fun a ↦ lipschitzWith_of_eq_integral hM
        (fun t ↦ intervalIntegrable_h1_along_flow (hT := hT) hchar.flow_continuous hGl hGlb a t)
        (fun s _ ↦ by
          rw [← Real.norm_eq_abs]
          exact (norm_realLineRepresentative_le _ _).trans (by gcongr; exact hGlb _))
        (hGeq a))
      fun t ↦ ((hsmooth t).iterate_deriv k).continuous.comp
        (hchar.flow_continuous.comp (continuous_id.prodMk continuous_const))
  have heq : (fun p : ℝ × Icc (0 : ℝ) T ↦ deriv^[k] (fun y ↦ w y p.2) p.1) =
      fun p ↦ Φ (Y p.1 p.2, p.2) :=
    funext fun p ↦ by simp only [Φ, hchar.flow_inverse p.1 p.2 p.2.property]
  rw [heq]
  exact hΦ.comp (hchar.inverse_continuous.prodMk continuous_snd)

end DeGregorio.Iteration
