/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.SubSupersolution.Laplacian
import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore
import CAS.ExactTactic

/-!
# Nonzero constant barriers

The H¹ functions `-1` and `2` bound a zero-boundary solution of
`-Δu = 1 - u`. Their geometric traces are those same constants, so the barriers
have nonzero boundary values, and the reaction has a nonzero offset. The solution
comes from `exists_weak_laplacian_solution_between_H1_barriers`.
The dimension may be one.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Elliptic.Semilinear
open SobolevSpace.Boundary SobolevSpace.Approximation.UpToBoundary
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

namespace PDE.Examples.Semilinear

/-- The nonzero constant barriers `-1` and `2` enclose a solution of `-Δu = 1 - u`. -/
theorem exists_solution_between_nonzero_constant_barriers
    {m : ℕ} {Ω : Set ℝ^(m + 1)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, -1 ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, baseCoordCLM u x ≤ 2) ∧
      MemLp (fun x ↦ 1 - baseCoordCLM u x) 2 (domainMeasure (m + 1) Ω) ∧
      ∀ v : H¹₀(Ω),
        (∑ i, ∫ x, derivCoordCLM i u x * derivCoordCLM i v x
          ∂domainMeasure (m + 1) Ω) =
          ∫ x, (1 - baseCoordCLM u x) * baseCoordCLM v x
            ∂domainMeasure (m + 1) Ω := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hb
  let := hgraph.c1ExtensionAtlas hΩ hb
  obtain ⟨P⟩ := exists_inwardPartition hΩ hb (hasC1Boundary_of_local_graph hgraph)
  let w (c : ℝ) : H¹(Ω) := wkpConstant c
  have hbase (c : ℝ) :
      wkpBaseCoordinateCLM (w c) =ᵐ[domainMeasure (m + 1) Ω] fun _ ↦ c :=
    wkpConstant_base_ae c
  have htrace (c : ℝ) :
      Trace.C1.trace (w c) =ᵐ[surfaceMeasure Ω] fun _ ↦ c :=
    Trace.C1.trace_eq_ae_of_continuousOn P (w c) continuousOn_const (hbase c)
  have hgrad (c : ℝ) (v : H¹₀(Ω)) :
      (∑ i, ∫ x, wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w c) x *
        derivCoordCLM i v x ∂domainMeasure (m + 1) Ω) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    calc
      _ = ∫ _ : ℝ^(m + 1), (0 : ℝ) ∂domainMeasure (m + 1) Ω := by
        apply integral_congr_ae
        filter_upwards [wkpConstant_deriv_ae
          (n := m + 1) (p := 2) (Ω := Ω) c i] with x hx
        simp only [show wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w c) x = 0
          from hx, zero_mul]
      _ = 0 := integral_zero _ _
  have hg : Differentiable ℝ (fun s : ℝ ↦ 1 - s) := by
    intro s
    cas
  have hderiv (s : ℝ) : |deriv (fun t : ℝ ↦ 1 - t) s| ≤ 1 := by
    have hd : deriv (fun t : ℝ ↦ 1 - t) s = -1 := by cas
    rw [hd]
    norm_num
  have htlo : ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace (w (-1)) x ≤ 0 := by
    filter_upwards [htrace (-1)] with x hx
    rw [hx]
    norm_num
  have hthi : ∀ᵐ x ∂surfaceMeasure Ω, 0 ≤ Trace.C1.trace (w 2) x := by
    filter_upwards [htrace 2] with x hx
    rw [hx]
    norm_num
  have hlr : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      wkpBaseCoordinateCLM (w (-1)) x ≤ wkpBaseCoordinateCLM (w 2) x := by
    filter_upwards [hbase (-1), hbase 2] with x hl hu
    rw [hl, hu]
    norm_num
  have hlo : ∀ v : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM v x) →
      (∑ i, ∫ x, wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w (-1)) x *
        derivCoordCLM i v x ∂domainMeasure (m + 1) Ω) ≤
        ∫ x, (1 - wkpBaseCoordinateCLM (w (-1)) x) * baseCoordCLM v x
          ∂domainMeasure (m + 1) Ω := by
    intro v hv
    rw [hgrad]
    apply integral_nonneg_of_ae
    filter_upwards [hbase (-1), hv] with x hx hvx
    rw [hx]
    exact mul_nonneg (by norm_num) hvx
  have hhi : ∀ v : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM v x) →
      (∫ x, (1 - wkpBaseCoordinateCLM (w 2) x) * baseCoordCLM v x
        ∂domainMeasure (m + 1) Ω) ≤
        ∑ i, ∫ x, wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w 2) x *
          derivCoordCLM i v x ∂domainMeasure (m + 1) Ω := by
    intro v hv
    rw [hgrad]
    apply integral_nonpos_of_ae
    filter_upwards [hbase 2, hv] with x hx hvx
    rw [hx]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hvx
  obtain ⟨u, hlu, huu, hmem, heq⟩ :=
    exists_weak_laplacian_solution_between_H1_barriers hΩ hb hgraph
      (fun s ↦ 1 - s) hg hderiv (w (-1)) (w 2) htlo hthi hlr hlo hhi
  refine ⟨u, ?_, ?_, hmem, heq⟩
  · filter_upwards [hbase (-1), hlu] with x hx hu
    simpa only [hx] using hu
  · filter_upwards [hbase 2, huu] with x hx hu
    simpa only [hx] using hu

end PDE.Examples.Semilinear
