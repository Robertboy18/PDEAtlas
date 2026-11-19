/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTimeScalar
public import PDE.Fluid.DeGregorio.DynamicRescaling.OriginNormalization
import CAS.ExactTactic
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.TimeDerivative

/-!
# Time differentiation of the rescaled transport equation

Joint `C²` germs justify the mixed derivatives. Differentiating the
equation gives its linearization at the current fields, with the derivatives
of the two rates. Endpoint normalization differentiates to the normalization
for the time-dependent perturbation, and equal total rates force its origin
slope to vanish.

## References

* J. Chen, T. Y. Hou, and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), no. 6, 1282-1350; numbering of
  arXiv:1905.06387v3, supplementary material, Section 12, (12.1)-(12.3), p. 20 of the supplement.
  <https://doi.org/10.1002/cpa.21991>
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace DeGregorio

/-- Time derivatives of the real vorticity and normalized velocity. -/
def timeDifferentiatedFields (fields : Fields) : Fields where
  vorticity x t := deriv (fields.vorticity x) t
  velocity x t := deriv (fields.velocity x) t

/-- Differentiation of the rescaled PDE gives the linearization at
the current fields. -/
theorem hasDerivAt_time_vorticity_of_rescaledTransport
    {a x t cL cW : ℝ} {fields : Fields} {spatialRate vorticityRate : ℝ → ℝ}
    {times : Set ℝ} (htimes : times ∈ 𝓝 t)
    (htransport :
      SatisfiesRescaledTransportEquationOn a fields spatialRate vorticityRate times)
    (hω : ContDiffAt ℝ 2 (Function.uncurry fields.vorticity) (x, t))
    (hu : ContDiffAt ℝ 2 (Function.uncurry fields.velocity) (x, t))
    (hL : HasDerivAt spatialRate cL t) (hW : HasDerivAt vorticityRate cW t) :
    HasDerivAt ((timeDifferentiatedFields fields).vorticity x)
      (linearizedTransport a (spatialRate t) (vorticityRate t) cL cW
        (fun y ↦ fields.vorticity y t) (fun y ↦ fields.velocity y t)
        (fun y ↦ (timeDifferentiatedFields fields).vorticity y t)
        (fun y ↦ (timeDifferentiatedFields fields).velocity y t) x) t := by
  have hωt := ((hω.comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    two_ne_zero).hasDerivAt
  have hut := ((hu.comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    two_ne_zero).hasDerivAt
  change HasDerivAt (fields.vorticity x) (deriv (fields.vorticity x) t) t at hωt
  change HasDerivAt (fields.velocity x) (deriv (fields.velocity x) t) t at hut
  have hωxt := PDE.Analysis.Calculus.hasDerivAt_spatial_deriv hω
  have huxt := PDE.Analysis.Calculus.hasDerivAt_spatial_deriv hu
  have hproduction :=
    ((hW.add huxt).mul hωt).sub (((hL.mul_const x).add (hut.const_mul a)).mul hωxt)
  have hderiv := hproduction.congr_of_eventuallyEq (show
      (fun s ↦ deriv (fields.vorticity x) s) =ᶠ[𝓝 t]
        (fun s ↦ (vorticityRate s + deriv (fun y ↦ fields.velocity y s) x) *
          fields.vorticity x s -
          (spatialRate s * x + a * fields.velocity x s) *
            deriv (fun y ↦ fields.vorticity y s) x) from
    (show ∀ᶠ s in 𝓝 t, s ∈ times from htimes).mono
      fun s hs ↦ eq_sub_of_add_eq (htransport (x := x) hs))
  apply hderiv.congr_deriv
  simp only [linearizedTransport, timeDifferentiatedFields, Pi.add_apply]
  ring

/-- The boundary normalization has the derivative prescribed in §12.
Equality with the normalization is only needed on a time neighborhood. -/
theorem hasDerivAt_boundary_normalization
    {fields : Fields} {rate : ℝ → ℝ} {L t : ℝ}
    (hu : DifferentiableAt ℝ (fields.velocity L) t)
    (hnormalization : ∀ᶠ s in 𝓝 t, rate s = -fields.velocity L s / L) :
    HasDerivAt rate (-(timeDifferentiatedFields fields).velocity L t / L) t :=
  (hu.hasDerivAt.neg.div_const L).congr_of_eventuallyEq hnormalization

/-- The differentiated rate makes the transport velocity vanish at the
fixed support endpoint. -/
theorem boundary_normalization_time_cancellation
    {fields : Fields} {rate : ℝ → ℝ} {L t : ℝ} (hL : L ≠ 0)
    (hu : DifferentiableAt ℝ (fields.velocity L) t)
    (hnormalization : ∀ᶠ s in 𝓝 t, rate s = -fields.velocity L s / L) :
    deriv rate t * L + (timeDifferentiatedFields fields).velocity L t = 0 := by
  rw [(hasDerivAt_boundary_normalization hu hnormalization).deriv]
  cas using hL

/-- Equal total rates preserve the origin slope, so the time-differentiated
vorticity has zero spatial slope at the origin. -/
theorem time_vorticity_origin_slope_eq_zero
    {fields : Fields} {rate : ℝ → ℝ} {times : Set ℝ} {t : ℝ}
    (ht : t ∈ times)
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields rate rate times)
    (hω : ContDiffAt ℝ 2 (Function.uncurry fields.vorticity) (0, t))
    (hu : ContDiffAt ℝ 2 (fun x ↦ fields.velocity x t) 0)
    (hωzero : fields.vorticity 0 t = 0) (huzero : fields.velocity 0 t = 0) :
    deriv (fun x ↦ (timeDifferentiatedFields fields).vorticity x t) 0 = 0 :=
  (PDE.Analysis.Calculus.hasDerivAt_spatial_deriv hω).unique
    (hasDerivAt_origin_slope_zero htransport ht hω hu hωzero huzero)

/-- The Biot–Savart law differentiates in time under common `L²`
majorants. Mixed derivatives identify the resulting velocity gradient. -/
theorem isHilbertPair_timeDerivatives_of_biotSavart
    {fields : Fields} {times : Set ℝ} {t : ℝ} {B C : ℝ → ℝ}
    (htimes : times ∈ 𝓝 t) (hconvex : Convex ℝ times)
    (hbiot : SatisfiesBiotSavartOn fields times)
    (hf : ∀ s, MemLp (fun x ↦ fields.vorticity x s) 2 volume)
    (hg : ∀ s, MemLp (deriv (fun x ↦ fields.velocity x s)) 2 volume)
    (hq : MemLp (fun x ↦ (timeDifferentiatedFields fields).vorticity x t) 2 volume)
    (hr : MemLp (deriv (fun x ↦ (timeDifferentiatedFields fields).velocity x t)) 2 volume)
    (hB : MemLp B 2 volume) (hC : MemLp C 2 volume)
    (hω : ∀ᵐ x, ∀ s ∈ times, DifferentiableAt ℝ (fields.vorticity x) s)
    (hu : ∀ᵐ x, ∀ s ∈ times,
      ContDiffAt ℝ 2 (Function.uncurry fields.velocity) (x, s))
    (hqb : ∀ᵐ x, ∀ s ∈ times, ‖(timeDifferentiatedFields fields).vorticity x s‖ ≤ B x)
    (hrb : ∀ᵐ x, ∀ s ∈ times,
      ‖deriv (fun y ↦ (timeDifferentiatedFields fields).velocity y s) x‖ ≤ C x) :
    IsHilbertPair (fun x ↦ (timeDifferentiatedFields fields).vorticity x t)
      (deriv (fun x ↦ (timeDifferentiatedFields fields).velocity x t)) := by
  apply IsHilbertPair.timeDerivative_of_memLp_bounds hf hg hq hr hB hC
    htimes hconvex (fun s hs ↦ hbiot hs) ?_ ?_ hqb hrb
  · filter_upwards [hω] with x hx
    exact fun s hs ↦ (hx s hs).hasDerivAt
  · filter_upwards [hu] with x hx
    exact fun s hs ↦ PDE.Analysis.Calculus.hasDerivAt_spatial_deriv (hx s hs)

end DeGregorio
