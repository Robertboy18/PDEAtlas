/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.RegularityTransfer

/-!
# Smooth local flows and their first variations

Start with one local C¹ flow and its first variation. The regularity-transfer
theorem makes that flow smooth on its existing cylinder, without shrinking the
domain for each derivative order. Its state derivative is then smooth as well.
Derivative uniqueness identifies it with the original first variation, retaining
both the variational equation and the uniform initial-state Lipschitz estimate.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Metric Set
open scoped ContDiff NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth finite-dimensional vector field constructs a jointly smooth local
flow and first variation on one cylinder, with a uniform initial-state Lipschitz bound. -/
theorem exists_local_contDiff_infty_family
    (v : E → E) (hv : ContDiff ℝ ∞ v) (q₀ : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 < T ∧
      ∃ flow : E × ℝ → E, ∃ variation : E × ℝ → (E →L[ℝ] E),
        ContDiffOn ℝ ∞ flow (ball q₀ r ×ˢ Ioo (-T) T) ∧
        ContDiffOn ℝ ∞ variation (ball q₀ r ×ˢ Ioo (-T) T) ∧
        (∃ C : ℝ≥0, ∀ t ∈ Icc (-T) T,
          LipschitzOnWith C (fun q ↦ flow (q, t)) (ball q₀ r)) ∧
        ∀ q ∈ ball q₀ r,
          flow (q, 0) = q ∧ variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
          ∀ t ∈ Ioo (-T) T,
            HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t ∧
            HasDerivAt (fun s ↦ variation (q, s))
              ((fderiv ℝ v (flow (q, t))).comp (variation (q, t))) t ∧
            HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q := by
  obtain ⟨r, hr, T, hT, flow, variation, _hf, _hJ, hLip, hsolve⟩ :=
    exists_local_contDiff_one_family_of_contDiff_one v (hv.of_le (by simp)) q₀
  have hflow : ContDiffOn ℝ ∞ flow (ball q₀ r ×ˢ Ioo (-T) T) :=
    contDiffOn_infty_of_solution_family v hv flow (ball q₀ r) isOpen_ball hT
      (fun q hq ↦ (hsolve q hq).1)
      (fun q hq t ht ↦ ((hsolve q hq).2.2 t ht).1)
  refine ⟨r, hr, T, hT, flow, variation, hflow, ?_, hLip, hsolve⟩
  let ι : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod 0
  have hD : ContDiffOn ℝ ∞ (fun p ↦ (fderiv ℝ flow p).comp ι)
      (ball q₀ r ×ˢ Ioo (-T) T) :=
    (hflow.fderiv_of_isOpen (isOpen_ball.prod isOpen_Ioo) (by simp)).clm_comp
      contDiffOn_const
  apply hD.congr
  rintro ⟨q, t⟩ ⟨hq, ht⟩
  have hjoint := (hflow.contDiffAt
    ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hq, ht⟩)).differentiableAt (by simp)
  have hinsert : HasFDerivAt (fun w : E ↦ (w, t)) ι q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const t q)
  exact ((hsolve q hq).2.2 t ht).2.2.unique (hjoint.hasFDerivAt.comp q hinsert)

end

end PDE.Analysis.ODE
