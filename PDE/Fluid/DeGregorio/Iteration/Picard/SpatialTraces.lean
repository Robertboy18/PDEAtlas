/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder.Convergence
public import PDE.Fluid.DeGregorio.Iteration.Picard.Output

/-!
# Closed-time spatial derivatives of the transport output

The bounded H² output and its L² time topology determine continuous first
spatial derivatives up to both endpoints. The interior transport equation
then determines the one-sided time-derivative traces.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
  {f G : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}

/-- The output's first spatial derivative is jointly continuous on the
closed time slab. -/
theorem IsHkFrozenOutput.continuous_spatial_deriv
    (h : IsHkFrozenOutput hT f G W₀ w₀ c w) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ deriv (fun y ↦ w y p.2) p.1) :=
  (continuous_representative_and_deriv_of_hkBaseBall
    (continuous_subtype_val.comp G.continuous) (fun t ↦ (G t).property.1)
    (fun _ ↦ h.continuous.comp (continuous_id.prodMk continuous_const))
    h.representative).2

/-- At every closed time, including either endpoint, the vorticity and
its first spatial derivative converge uniformly on each compact spatial set. -/
theorem IsHkFrozenOutput.tendstoUniformlyOn_spatial_traces
    (h : IsHkFrozenOutput hT f G W₀ w₀ c w)
    (t : Icc (0 : ℝ) T) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun s : Icc (0 : ℝ) T ↦ fun x ↦ w x s)
      (fun x ↦ w x t) (𝓝 t) K ∧
      TendstoUniformlyOn (fun s : Icc (0 : ℝ) T ↦ deriv (fun x ↦ w x s))
        (deriv (fun x ↦ w x t)) (𝓝 t) K :=
  tendstoUniformlyOn_representative_and_deriv_of_hkBaseBall
    (fun s ↦ (G s).property.1) (G t).property.1
    ((continuous_subtype_val.comp G.continuous).tendsto t)
    (fun _ ↦ h.continuous.comp (continuous_id.prodMk continuous_const))
    (h.continuous.comp (continuous_id.prodMk continuous_const))
    h.representative (h.representative t) hK

/-- The transport right-hand side is jointly continuous on the closed time slab. -/
theorem IsHkFrozenOutput.continuous_transport_rhs
    (h : IsHkFrozenOutput hT f G W₀ w₀ c w) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦
      c p.1 p.2 * w p.1 p.2 -
        hkCurveHilbertVelocity hT f p.1 p.2 * deriv (fun y ↦ w y p.2) p.1) :=
  ((h.coefficient_continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).mul h.continuous).sub
      (((continuous_hkCurveHilbertVelocity hT f).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).mul
          h.continuous_spatial_deriv)

/-- The interior classical time derivative has the transport value as its trace
at each closed time. The derivative itself is only evaluated at interior times. -/
theorem IsHkFrozenOutput.tendsto_time_deriv_from_interior
    (h : IsHkFrozenOutput hT f G W₀ w₀ c w) (x : ℝ) (t : Icc (0 : ℝ) T) :
    Tendsto (fun s : Ioo (0 : ℝ) T ↦ deriv (w x) s)
      (comap ((↑) : Ioo (0 : ℝ) T → ℝ) (𝓝 (t : ℝ)))
      (𝓝 (c x t * w x t -
        hkCurveHilbertVelocity hT f x t * deriv (fun y ↦ w y t) x)) := by
  have hsub : Tendsto
      (fun s : Ioo (0 : ℝ) T ↦ (⟨(s : ℝ), Ioo_subset_Icc_self s.property⟩ : Icc 0 T))
      (comap ((↑) : Ioo (0 : ℝ) T → ℝ) (𝓝 (t : ℝ))) (𝓝 t) :=
    tendsto_subtype_rng.mpr tendsto_comap
  have hlim := (h.continuous_transport_rhs.tendsto (x, t)).comp
    (tendsto_const_nhds.prodMk_nhds hsub)
  apply hlim.congr'
  apply Eventually.of_forall
  intro s
  exact (eq_sub_iff_add_eq.mpr (h.transport x s s.property)).symm

end DeGregorio.Iteration
