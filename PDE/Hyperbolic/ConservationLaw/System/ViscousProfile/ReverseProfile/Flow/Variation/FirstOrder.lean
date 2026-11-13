/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

import PDE.Analysis.ODE.SmoothDependence.Variation

/-!
# Physical variations of the supplied full prescribed flow

The full parameters are `((δ,c),(μ,a))`, with Euclidean three-dimensional state
and a Pi space of gate coefficients. Differentiation in `(μ,a)` keeps `δ,c` and
the feedback thresholds fixed. The initial section gives the variation
`!₂[0,ξ.2,0]`; the physical damping contributes `-ξ.1 • γ` in all state coordinates.

The variational germ theorem gives ordinary time derivatives at every
point of the supplied closed time interval.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The physical-parameter derivative at `(μ,a)=(0,0)`, with `(δ,c)` fixed. -/
def prescribedClockFullVariation
    (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
    (σ : ℝ × (Fin 3 → ℝ)) (ξ : ℝ × ℝ) (t : ℝ) : ℝ^3 :=
  fderiv ℝ (fun p ↦ Ψ (t, (σ, p))) (0, 0) ξ

/-- The variation is jointly smooth in time and the fixed-flux parameters. -/
theorem contDiff_prescribedClockFullVariation {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) (ξ : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun u : ℝ × (ℝ × (Fin 3 → ℝ)) ↦ prescribedClockFullVariation Ψ u.2 ξ u.1) := by
  have hfamily : ContDiff ℝ ∞ (fun z : (ℝ × (ℝ × (Fin 3 → ℝ))) × (ℝ × ℝ) ↦
        Ψ (z.1.1, (z.1.2, z.2))) :=
    hΨ.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hD : ContDiff ℝ ∞ (fun u : ℝ × (ℝ × (Fin 3 → ℝ)) ↦
      fderiv ℝ (fun p : ℝ × ℝ ↦ Ψ (u.1, (u.2, p))) (0, 0)) := ContDiff.fderiv
      (f := fun (u : ℝ × (ℝ × (Fin 3 → ℝ))) (p : ℝ × ℝ) ↦ Ψ (u.1, (u.2, p)))
      (g := fun _ : ℝ × (ℝ × (Fin 3 → ℝ)) ↦ ((0 : ℝ), (0 : ℝ)))
      hfamily contDiff_const (by simp)
  exact hD.clm_apply contDiff_const

/-- The supplied initial section has zero speed variation and middle displacement `ξ.2`. -/
theorem prescribedClockFullVariation_initial {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hinit : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3)) (σ : ℝ × (Fin 3 → ℝ)) (ξ : ℝ × ℝ) :
    prescribedClockFullVariation Ψ σ ξ 0 = (!₂[0, ξ.2, 0] : ℝ^3) := by
  have hsection : (fun p : ℝ × ℝ ↦ Ψ (0, (σ, p))) =
      fun p : ℝ × ℝ ↦ p.2 • (!₂[0, 1, 0] : ℝ^3) + !₂[0, 0, 1] := by
    funext p
    rw [hinit (σ, p)]
    ext i
    fin_cases i <;> simp
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := hasFDerivAt_snd
  have hsection' := (hsnd.smul_const (!₂[0, 1, 0] : ℝ^3)).add_const (!₂[0, 0, 1] : ℝ^3)
  unfold prescribedClockFullVariation
  rw [hsection, hsection'.fderiv]
  ext i
  fin_cases i <;> simp

/-- The full physical variation satisfies its ordinary ODE on the closed time slab.
The state differential is that of the concrete flux with `δ,c,A,B` fixed. -/
theorem hasDerivAt_prescribedClockFullVariation {A B : ℝ} {b : (Fin 3 → ℝ) × ℝ → ℝ}
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} {H : ℝ}
    (hb : ContDiff ℝ ∞ b) (hΨ : ContDiff ℝ ∞ Ψ) (hN : IsOpen N) {σ : ℝ × (Fin 3 → ℝ)}
    (hbase : (σ, (0, 0)) ∈ N)
    (hode : ∀ θ ∈ N, ∀ t ∈ Icc (0 : ℝ) H, HasDerivAt (fun s ↦ Ψ (s, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (t, θ)) - θ.2.1 •
      Ψ (t, θ)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (ξ : ℝ × ℝ) :
    HasDerivAt (prescribedClockFullVariation Ψ σ ξ) (fderiv ℝ
      (concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y))) (Ψ (t, (σ, (0, 0))))
      (prescribedClockFullVariation Ψ σ ξ t) - ξ.1 • Ψ (t, (σ, (0, 0)))) t := by
  let f : ℝ^3 → ℝ^3 := concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y))
  let q : ℝ^3 := Ψ (t, (σ, (0, 0)))
  let v : (ℝ × ℝ) × ℝ^3 → ℝ^3 := fun u ↦ f u.2 - u.1.1 • u.2
  have hbσ : ContDiff ℝ ∞ (fun y : ℝ ↦ b (σ.2, y)) := hb.comp (contDiff_const.prodMk contDiff_id)
  have hf : Differentiable ℝ f :=
    (contDiff_concreteGatedFlux σ.1 (contDiff_clockFeedback A B) hbσ).differentiable
      (by simp)
  have hstate : HasFDerivAt (fun u : (ℝ × ℝ) × ℝ^3 ↦ u.2)
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ^3)) ((0, 0), q) := hasFDerivAt_snd
  have hμ : HasFDerivAt (fun u : (ℝ × ℝ) × ℝ^3 ↦ u.1.1) ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ^3))) ((0, 0), q) := hasFDerivAt_fst.fst
  have hfield := ((hf q).hasFDerivAt.comp ((0, 0), q) hstate).fun_sub (hμ.fun_smul hstate)
  have hfamily : ContDiff ℝ ∞ (fun u : ℝ × (ℝ × ℝ) ↦ Ψ (u.1, (σ, u.2))) :=
    hΨ.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))
  let U : Set (ℝ × ℝ) := (fun p : ℝ × ℝ ↦ (σ, p)) ⁻¹' N
  have hU : IsOpen U := hN.preimage (continuous_const.prodMk continuous_id)
  have hbaseU : ((0, 0) : ℝ × ℝ) ∈ U := hbase
  have hodeσ : ∀ᶠ p in 𝓝 ((0, 0) : ℝ × ℝ),
      HasDerivAt (fun s ↦ Ψ (s, (σ, p))) (v (p, Ψ (t, (σ, p)))) t := by
    filter_upwards [hU.mem_nhds hbaseU] with p hp using hode (σ, p) hp t ht
  have h := PDE.Analysis.ODE.hasDerivAt_parameterVariation_of_contDiffAt
    (F := fun s p ↦ Ψ (s, (σ, p))) (v := v) (p := (0, 0)) (t := t)
    (hfamily.contDiffAt.of_le (by simp)) hfield.differentiableAt hodeσ ξ
  apply h.congr_deriv
  simpa [v, f, q, prescribedClockFullVariation, Function.comp_def] using
    congrArg (fun D : ((ℝ × ℝ) × ℝ^3) →L[ℝ] ℝ^3 ↦
      D (ξ, prescribedClockFullVariation Ψ σ ξ t)) hfield.fderiv

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
