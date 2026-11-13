/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Solution.Coordinates
public import PDE.Parabolic.Systems.Transport.Uniqueness

/-!
# Uniqueness of arbitrary strong matrix diffusion solutions

Coordinate projections of the finite Hilbert-valued state and velocity
recover the component trajectories. The pointwise equation determines their
H¹ equation, so the symmetric energy estimate applies to any two strong
solutions. Equality holds for the Bochner classes and at every point of
their closed time traces.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution

open MeasureTheory Set
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n m : ℕ} {ε a b K : ℝ}
  {B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ}
  {f : Fin m → ℝ × ℝ^n → ℝ}
  {q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}

/-- Strong solutions of the same equation with the same initial value are equal.
The coefficient derivative bound gives the energy estimate, so neither
competitor is assumed to satisfy one. -/
theorem unique
    (hε : 0 ≤ ε) (hab : a < b) (hK0 : 0 ≤ K)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p))
    (hK : ∀ t ∈ Icc a b, transportDerivativeSum (A t) ≤ K)
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F p t) x = f p (t, x))
    (U V : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
      (volume.restrict (Ioc a b)))
    (G H : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
      (volume.restrict (Ioc a b)))
    (z w : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
    (hU : IsStrongTransportDiffusionSolution ε a b B f q U G z)
    (hV : IsStrongTransportDiffusionSolution ε a b B f q V H w) :
    U = V ∧ G = H ∧ EqOn z w (Icc a b) := by
  -- Fix the `PiLp` normed-space structures before elaborating the Bochner maps.
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{3,2}(ℝ^n))
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{1,2}(ℝ^n))
  let μ := volume.restrict (Ioc a b)
  let P₃ (p : Fin m) :
      PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ] W^{3,2}(ℝ^n) :=
    PiLp.proj 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) p
  let P₁ (p : Fin m) :
      PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ] W^{1,2}(ℝ^n) :=
    PiLp.proj 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) p
  let u (p : Fin m) := (P₃ p).compLpL 2 μ U
  let v (p : Fin m) := (P₃ p).compLpL 2 μ V
  let g (p : Fin m) := (P₁ p).compLpL 2 μ G
  let h (p : Fin m) := (P₁ p).compLpL 2 μ H
  have hu : ∀ᵐ t ∂μ, ∀ p, u p t = U t p :=
    ae_all_iff.mpr fun p ↦ (P₃ p).coeFn_compLpL U
  have hv : ∀ᵐ t ∂μ, ∀ p, v p t = V t p :=
    ae_all_iff.mpr fun p ↦ (P₃ p).coeFn_compLpL V
  have hg : ∀ᵐ t ∂μ, ∀ p, g p t = G t p :=
    ae_all_iff.mpr fun p ↦ (P₁ p).coeFn_compLpL G
  have hh : ∀ᵐ t ∂μ, ∀ p, h p t = H t p :=
    ae_all_iff.mpr fun p ↦ (P₁ p).coeFn_compLpL H
  have heqU (p : Fin m) : (fun t ↦ g p t) =ᵐ[μ] fun t ↦
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (u p t) + F p t +
        vectorTransportH1CLM isOpen_univ (A t)
          (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (u q t)) p := by
    filter_upwards [hU.native_equation A hB (fun p t ↦ F p t) hf, hu, hg] with t ht hut hgt
    simpa only [hut, hgt] using ht p
  have heqV (p : Fin m) : (fun t ↦ h p t) =ᵐ[μ] fun t ↦
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (v p t) + F p t +
        vectorTransportH1CLM isOpen_univ (A t)
          (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (v q t)) p := by
    filter_upwards [hV.native_equation A hB (fun p t ↦ F p t) hf, hv, hh] with t ht hvt hht
    simpa only [hvt, hht] using ht p
  obtain ⟨huv, hgh, hzw⟩ := transport_diffusion_unique hε hab hK0 A hA hK
    u v g h F heqU heqV hU.coordinate_weakTimeDerivative hV.coordinate_weakTimeDerivative
    (fun t p ↦ z t p) (fun t p ↦ w t p)
    (continuousOn_pi.mpr fun p ↦ (P₁ p).continuous.comp_continuousOn hU.continuousOn)
    (continuousOn_pi.mpr fun p ↦ (P₁ p).continuous.comp_continuousOn hV.continuousOn)
    hU.coordinate_representative hV.coordinate_representative
    (by rw [hU.initial_eq, hV.initial_eq])
  refine ⟨?_, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [hu, hv] with t hut hvt
    exact PiLp.ext fun p ↦ by rw [← hut p, ← hvt p, huv]
  · apply Lp.ext
    filter_upwards [hg, hh] with t hgt hht
    exact PiLp.ext fun p ↦ by rw [← hgt p, ← hht p, hgh]
  · intro t ht
    exact PiLp.ext fun p ↦ congrFun (hzw ht) p

end PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution
