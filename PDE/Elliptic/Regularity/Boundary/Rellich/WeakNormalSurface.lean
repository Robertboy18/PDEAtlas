/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Rellich.LocalSurfaceBound
public import PDE.Elliptic.Regularity.Interior.PoissonLocalization
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteCoverBound
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.WeakNormalLocalization

/-!
# Surface L² normal derivatives of zero-trace weak Poisson fields

On a bounded C¹ graph domain, a zero-trace H¹ field with L² Laplacian has
a weak normal derivative represented by a surface L² function.

The proof chooses a finite graph cover and localizes the field with cutoffs
equal to one near the supports of its boundary partition. The local Poisson
construction and local surface estimate apply to these localized fields.
Locality of the Green pairing transfers their estimates to the original field.
The boundary partition and smooth trace density then give the bound on the
whole Hilbert trace space, and Hilbert space duality supplies the density.
-/

@[expose] public noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions Sobolev InnerProductSpace Topology

namespace SobolevSpace.Trace.C1

open GraphSpace GraphSpace.Rellich Approximation.UpToBoundary
open Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
  [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The surface L² norm of an ambient smooth test is the literal square-integral norm. -/
theorem norm_trace_globalTestFunctionToWkpOn
    (φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ)) :
    ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖ =
      Real.sqrt (∫ x, φ.toFun x ^ 2 ∂surfaceMeasure Ω) := by
  rw [norm_eq_sqrt_real_inner, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [trace_globalTestFunctionToWkpOn_apply_ae (Ω := Ω) φ] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial, pow_two, TestFunction.toFun_eq_coe]

/-- A zero-trace H¹ field with L² Laplacian has a surface-L² bound on its weak normal trace.
The finite constant is independent of the boundary trace class and its lifting. -/
theorem exists_norm_weakNormalTrace_le_surface_of_H10
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (w : H¹₀(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w : H¹(Ω)))
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : HilbertTraceSpace (Ω := Ω),
      ‖weakNormalTrace (w : H¹(Ω)) f huf q‖ ≤ C * ‖boundaryValue q‖ := by
  classical
  obtain ⟨cover⟩ := hgraph.nonempty_c1GraphBoundaryCover H.isOpen H.bounded
  obtain ⟨P⟩ := exists_inwardPartition H.isOpen H.bounded
    (Boundary.hasC1Boundary_of_local_graph hgraph)
  let c := cover.toFiniteBoundaryCover
  have hweak := integral_laplacian_eq_of_weakForm (w : H¹(Ω)) f huf
  have hlocal (i : Fin c.N) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ),
        tsupport φ ⊆ tsupport (c.boundaryCutoff i) →
        ‖weakNormalTrace (w : H¹(Ω)) f huf
          (traceClass (globalTestFunctionToWkpOn φ))‖ ≤
            C * ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖ := by
    obtain ⟨η, hηsupport, _, hηone, _⟩ := TestFunction.exists_eq_one_on_compact
      (cover.boundaryPatch_open i) (c.boundaryCutoff i).hasCompactSupport
      (c.boundaryCutoff_support i)
    obtain ⟨g, hg, hgweak⟩ := exists_laplacian_cutoffH10 H.isOpen w f hweak η
    have hug (v : H¹₀(Ω)) :
        (∑ j, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) j)
          (cutoffH10 H.isOpen η w : H¹(Ω))) (derivCoordCLM j v)) =
            -inner ℝ g (baseCoordCLM v) := by
      simpa only [inner_neg_left, wkpCoordinateCLM_apply] using
        poisson_weakForm_of_integral_laplacian_eq
          (cutoffH10 H.isOpen η w : H¹(Ω)) g hgweak v
    obtain ⟨u, hu, -, hsupport⟩ :=
      exists_compact_representative_cutoffH10 H.isOpen η w
    obtain ⟨C, hC, hbound⟩ := exists_greenPairing_surface_bound P cover i
      (cutoffH10 H.isOpen η w) u hu (hsupport.trans hηsupport)
      g hgweak (c.boundaryCutoff i).hasCompactSupport (c.boundaryCutoff_support i)
    refine ⟨C, hC, ?_⟩
    intro φ hφ
    have hηφ : ∀ x ∈ tsupport φ.toFun, η.toFun =ᶠ[𝓝 x] (fun _ ↦ 1) := by
      intro x hx
      exact hηone x (hφ hx)
    rw [← weakNormalTrace_cutoffH10_eq H.isOpen w f g η φ hηφ hg huf hug,
      weakNormalTrace_globalTestFunctionToWkpOn, Real.norm_eq_abs,
      norm_trace_globalTestFunctionToWkpOn]
    exact hbound φ.toFun (φ.contDiff.of_le (by simp)) hφ
  choose C hC hbound using hlocal
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ hC i), ?_⟩
  exact norm_le_of_finiteBoundaryCover_bound hgraph c
    (weakNormalTrace (w : H¹(Ω)) f huf) C hC hbound

/-- The outward weak normal derivative of a zero-trace weak Poisson field has a
surface L² density. The equality holds on every Hilbert trace class. -/
theorem exists_surfaceDensity_weakNormalTrace_of_H10
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (w : H¹₀(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w : H¹(Ω)))
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v)) :
    ∃ q : BoundaryL2 (Ω := Ω), ∀ z : HilbertTraceSpace (Ω := Ω),
      weakNormalTrace (w : H¹(Ω)) f huf z =
        ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_weakNormalTrace_le_surface_of_H10 hgraph w f huf
  obtain ⟨q, _, hq⟩ :=
    exists_surfaceDensity_of_norm_le (weakNormalTrace (w : H¹(Ω)) f huf) hC hbound
  exact ⟨q, hq⟩

end SobolevSpace.Trace.C1
