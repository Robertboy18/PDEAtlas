/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Solution.Coordinates
public import PDE.Parabolic.Systems.Transport.Energy.Velocity

/-!
# Hilbert energy bounds for strong matrix diffusion solutions

The component energy identities control the finite-Hilbert Bochner
norms. The initial value and the forcing enter only through their H¹ norms.
For viscosity at most one, the L²(L²) norm of the weak velocity is
bounded by the same data, independently of viscosity.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev
open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {ε a b K M : ℝ}
  {B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ}
  {f : Fin m → ℝ × ℝ^n → ℝ}
  {q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}
  {U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}

/-- The Hilbert-valued state and velocity satisfy quadratic bounds
whose constants depend only on the interval and coefficient bounds. -/
theorem energy_squares
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hab : a < b) (hK0 : 0 ≤ K)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p))
    (hK : ∀ t ∈ Icc a b, transportDerivativeSum (A t) ≤ K)
    (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Icc a b,
      ‖vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q))‖ ≤ M)
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
      (volume.restrict (Ioc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F t p) x = f p (t, x)) :
    (∀ t ∈ Icc a b,
      ‖z t‖ ^ 2 ≤ (‖q‖ ^ 2 + ‖F‖ ^ 2) * Real.exp ((K + 1) * (t - a))) ∧
    ‖(ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
        (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ))).compLpL
          2 (volume.restrict (Ioc a b)) G‖ ^ 2 ≤
      3 * ((n : ℝ) * (1 + (K + 1) * (b - a) * Real.exp ((K + 1) * (b - a))) +
        1 + (m : ℝ) * M ^ 2 * (b - a) * Real.exp ((K + 1) * (b - a))) *
        (‖q‖ ^ 2 + ‖F‖ ^ 2) := by
  let μ := volume.restrict (Ioc a b)
  let P₃ (p : Fin m) :
      PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ] W^{3,2}(ℝ^n) :=
    PiLp.proj 2 _ p
  let P₁ (p : Fin m) :
      PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ] W^{1,2}(ℝ^n) :=
    PiLp.proj 2 _ p
  let u (p : Fin m) := (P₃ p).compLpL 2 μ U
  let g (p : Fin m) := (P₁ p).compLpL 2 μ G
  let f (p : Fin m) := (P₁ p).compLpL 2 μ F
  have hu : ∀ᵐ t ∂μ, ∀ p, u p t = U t p :=
    ae_all_iff.mpr fun p ↦ (P₃ p).coeFn_compLpL U
  have hg : ∀ᵐ t ∂μ, ∀ p, g p t = G t p :=
    ae_all_iff.mpr fun p ↦ (P₁ p).coeFn_compLpL G
  have hF : ∀ᵐ t ∂μ, ∀ p, f p t = F t p :=
    ae_all_iff.mpr fun p ↦ (P₁ p).coeFn_compLpL F
  have heq (p : Fin m) : (fun t ↦ g p t) =ᵐ[μ] fun t ↦
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (u p t) + f p t +
        vectorTransportH1CLM isOpen_univ (A t)
          (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (u q t)) p := by
    filter_upwards [h.native_equation A hB (fun p t ↦ F t p) hf, hu, hg, hF]
      with t ht hut hgt hft
    simpa only [hut, hgt, hft] using ht p
  have hz : ContinuousOn (fun t p ↦ z t p) (Icc a b) :=
    continuousOn_pi.mpr fun p ↦ (P₁ p).continuous.comp_continuousOn h.continuousOn
  have hFint : (∫ t in a..b, ∑ p, ‖f p t‖ ^ 2) = ‖F‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le, Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hF] with t ht
    simp only [PiLp.norm_sq_eq_of_L2, ht]
  have henergy := (transport_diffusion_energy_estimates hε hab hK0 A hA hK
    u g f heq h.coordinate_weakTimeDerivative _ hz h.coordinate_representative).1
  have hvelocity := transport_diffusion_velocity_estimate hε hε1 hab hK0 A hA hK
    hM0 hM u g f heq h.coordinate_weakTimeDerivative _ hz h.coordinate_representative
  let V : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ) :=
    ContinuousLinearMap.piLpMap 2 (fun _ ↦ wkpBaseCoordinateCLM)
  have hGint : ‖V.compLpL 2 μ G‖ ^ 2 =
      ∫ t in a..b, ∑ p, ‖wkpBaseCoordinateCLM (g p t)‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq, intervalIntegral.integral_of_le hab.le]
    apply integral_congr_ae
    filter_upwards [V.coeFn_compLpL G, hg] with t ht hgt
    rw [ht, PiLp.norm_sq_eq_of_L2]
    simp only [V, ContinuousLinearMap.piLpMap_apply, hgt]
  constructor
  · intro t ht
    simpa only [← PiLp.norm_sq_eq_of_L2, h.initial_eq, hFint] using henergy t ht
  · change ‖V.compLpL 2 μ G‖ ^ 2 ≤ _
    rw [hGint]
    simpa only [← PiLp.norm_sq_eq_of_L2, h.initial_eq, hFint] using hvelocity

end PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution
