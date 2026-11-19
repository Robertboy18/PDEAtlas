/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.Variation.SecondOrder
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder

/-!
# Second speed variation of the prescribed-clock flow

The general second-variation identity applies to the same supplied flow and
fixed flux parameters used for the full first variation. Its prescribed initial
section makes the second speed derivative zero initially.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The second speed derivative of the supplied prescribed flow has zero
initial value and the second variational ODE on the same closed slab. All flux
parameters are fixed, and `W` is the already defined full first speed variation. -/
theorem prescribedClockSecondVariation_initial_and_hasDerivAt {A B : ℝ} {b : (Fin 3 → ℝ) × ℝ → ℝ}
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} {H : ℝ}
    (hb : ContDiff ℝ ∞ b) (hΨ : ContDiff ℝ ∞ Ψ) (hN : IsOpen N) {σ : ℝ × (Fin 3 → ℝ)}
    (hbase : (σ, (0, 0)) ∈ N) (hinit : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3))
    (hode : ∀ θ ∈ N, ∀ t ∈ Icc (0 : ℝ) H, HasDerivAt (fun s ↦ Ψ (s, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (t, θ)) - θ.2.1 •
      Ψ (t, θ)) t) :
    let f : ℝ^3 → ℝ^3 :=
      concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y))
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, (σ, (0, 0)))
    let W : ℝ → ℝ^3 := prescribedClockFullVariation Ψ σ (1, 0)
    let Z : ℝ → ℝ^3 := fun t ↦
      deriv (deriv (fun μ : ℝ ↦ Ψ (t, (σ, (μ, 0))))) 0
    Z 0 = 0 ∧ ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt Z
        (fderiv ℝ f (γ t) (Z t) +
          fderiv ℝ (fderiv ℝ f) (γ t) (W t) (W t) - (2 : ℝ) • W t) t := by
  dsimp only
  let F : ℝ → ℝ → ℝ^3 := fun s μ ↦ Ψ (s, (σ, (μ, 0)))
  let f : ℝ^3 → ℝ^3 :=
    concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y))
  have hfamily : ContDiff ℝ ∞ F.uncurry :=
    hΨ.comp (contDiff_fst.prodMk
      (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_const)))
  have hbσ : ContDiff ℝ ∞ (fun y : ℝ ↦ b (σ.2, y)) :=
    hb.comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ 2 f :=
    (contDiff_concreteGatedFlux σ.1 (contDiff_clockFeedback A B) hbσ).of_le (by simp)
  have hW (s : ℝ) : deriv (F s) 0 = prescribedClockFullVariation Ψ σ (1, 0) s := by
    have hphysical : ContDiff ℝ ∞
        (fun p : ℝ × ℝ ↦ Ψ (s, (σ, p))) :=
      hΨ.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
    have haxis : HasDerivAt (fun μ : ℝ ↦ (μ, (0 : ℝ))) (1, 0) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    simpa only [F, prescribedClockFullVariation, Function.comp_def, id_eq] using
      ((hphysical.differentiable (by simp) (0, 0)).hasFDerivAt.comp_hasDerivAt_of_eq
        (0 : ℝ) haxis rfl).deriv
  constructor
  · have hsection : F 0 = fun _ : ℝ ↦ (!₂[0, 0, 1] : ℝ^3) := by
      funext μ
      exact hinit (σ, (μ, 0))
    change deriv (deriv (F 0)) 0 = 0
    rw [hsection]
    simp only [deriv_const', deriv_const]
  · intro t ht
    let U : Set ℝ := (fun μ : ℝ ↦ (σ, (μ, (0 : ℝ)))) ⁻¹' N
    have hU : IsOpen U :=
      hN.preimage (continuous_const.prodMk (continuous_id.prodMk continuous_const))
    have hzero : (0 : ℝ) ∈ U := hbase
    have hodeσ : ∀ᶠ μ in 𝓝 (0 : ℝ),
        HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t := by
      filter_upwards [hU.mem_nhds hzero] with μ hμ
      exact hode (σ, (μ, 0)) hμ t ht
    have h := PDE.Analysis.ODE.hasDerivAt_secondSpeedVariation_sub_smul
      (F := F) (f := f) (t := t) (μ₀ := 0)
      (hfamily.of_le (by simp)) hf hodeσ
    simpa only [hW, zero_smul, sub_zero] using h

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
