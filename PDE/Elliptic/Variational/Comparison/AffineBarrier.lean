/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Comparison.Dirichlet
import PDE.Analysis.MeasureTheory.ContinuousBounds

/-!
# Comparison with an affine multiple of a weak barrier

A nonnegative multiple of a weak supersolution, plus a constant, is again a
weak supersolution for the Dirichlet form. Its continuous representative
identifies its trace. Unshifted weak comparison then bounds the continuous
interior representative of a subsolution at every interior point.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open Boundary Approximation.UpToBoundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal InnerProductSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- An affine multiple of a continuous weak supersolution bounds a continuous
interior subsolution whenever the same inequality holds for its trace. -/
theorem leOn_of_trace_le_affine_dirichlet_supersolution
    (P : InwardPartition Ω) (hbounded : Bornology.IsBounded Ω)
    (U B : H¹(Ω)) {u b : ℝ^(m + 1) → ℝ}
    (hu : ContinuousOn u Ω) (hb : ContinuousOn b (closure Ω))
    (hU : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] u)
    (hB : baseRepresentative B =ᵐ[domainMeasure (m + 1) Ω] b)
    (hsub : ∀ t : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM t x) →
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) ≤ 0)
    (hsuper : ∀ t : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM t x) →
      0 ≤ ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) B)
        (derivCoordCLM i t))
    (d : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (htrace : ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace U x ≤ d + C * b x) :
    ∀ x ∈ Ω, u x ≤ d + C * b x := by
  let : IsFiniteMeasure (domainMeasure (m + 1) Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  let D : H¹(Ω) := wkpConstant d
  let V : H¹(Ω) := D + C • B
  have hD (i : Fin (m + 1)) :
      wkpCoordinateCLM (singleDerivIndex (m + 1) i) D = 0 := by
    apply Lp.ext
    exact (wkpConstant_deriv_ae d i).trans
      (Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
        (μ := domainMeasure (m + 1) Ω)).symm
  have hV : baseRepresentative V =ᵐ[domainMeasure (m + 1) Ω]
      fun x ↦ d + C * b x := by
    filter_upwards [baseRepresentative_add_ae D (C • B),
      baseRepresentative_smul_ae C B,
      wkpConstant_base_ae (n := m + 1) (p := 2) (Ω := Ω) d, hB]
      with x hx hs hd hb
    change baseRepresentative D x = d at hd
    simpa only [V, hs, hd, hb, smul_eq_mul] using hx
  have hVcont : ContinuousOn (fun x ↦ d + C * b x) (closure Ω) :=
    continuousOn_const.add (continuousOn_const.mul hb)
  have hVtrace := Trace.C1.trace_eq_ae_of_continuousOn P V hVcont hV
  have hUV := base_le_ae_of_trace_le_of_dirichlet_inequality P hbounded U V
    (by filter_upwards [htrace, hVtrace] with x hx hv; simpa only [hv] using hx) (by
      intro t ht
      apply (hsub t ht).trans
      have heq :
          (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) V)
            (derivCoordCLM i t)) =
            C * ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) B)
              (derivCoordCLM i t) := by
        simp only [V, map_add, map_smul, hD, zero_add,
          real_inner_smul_left, Finset.mul_sum]
      rw [heq]
      exact mul_nonneg hC (hsuper t ht))
  apply PDE.Analysis.leOn_open_of_ae_le (μ := volume) hΩ.isOpen hu
    (hVcont.mono subset_closure)
  filter_upwards [hUV, hU, hV] with x hx hu hv
  change baseRepresentative U x ≤ baseRepresentative V x at hx
  simpa only [hu, hv] using hx

end SobolevSpace.GraphSpace
