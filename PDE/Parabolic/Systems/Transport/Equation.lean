/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Transport
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian.HigherOrder
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# The representative equation for matrix diffusion

The native H¹ equation is equivalent to the almost-everywhere pointwise
matrix PDE. Weak-derivative uniqueness on an open set gives the converse:
equality of the base L² coordinates determines the complete H¹ identity.
So a competitor with the stated H³/H¹ regularity that satisfies the pointwise
PDE also satisfies the H¹ equation used in the estimates.
-/

@[expose] public noncomputable section

open scoped Laplacian Sobolev

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal

variable {n m : ℕ} {Ω : Set ℝ^n} {ε : ℝ}

/-- The H¹-valued diffusion and drift are represented by their weak
coordinates. All rows and spatial directions share one exceptional set. -/
theorem transport_diffusion_rhs_ae
    (hΩ : IsOpen Ω) (A : Fin n → Fin m → Fin m → W^{1,∞}(Ω))
    (U : Fin m → W^{3,2}(Ω)) (F : Fin m → W^{1,2}(Ω)) :
    ∀ᵐ x ∂domainMeasure n Ω, ∀ p,
      wkpBaseCoordinateCLM
        (ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p) + F p +
          vectorTransportH1CLM hΩ A
            (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U q)) p) x =
        ε * (∑ j, wkpCoordinateCLM (pairDerivIndex n j j)
          (lowerOrderCLM (by decide : 2 ≤ 3) (U p)) x) +
          wkpBaseCoordinateCLM (F p) x -
            ∑ j, ∑ q, wkpBaseCoordinateCLM (A j p q) x *
              wkpCoordinateCLM (singleDerivIndex n j)
                (lowerOrderCLM (by decide : 1 ≤ 3) (U q)) x := by
  let L (p : Fin m) := Δ (lowerOrderCLM (by decide : 2 ≤ 3) (U p))
  let B (p : Fin m) := vectorTransportCLM
    (fun j p q ↦ wkpBaseCoordinateCLM (A j p q))
    (fun q ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U q)) p
  have hB := vectorTransportCLM_apply_ae
    (fun j p q ↦ wkpBaseCoordinateCLM (A j p q))
    (fun q ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U q))
  apply ae_all_iff.mpr
  intro p
  have hbase :
      wkpBaseCoordinateCLM
        (ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p) + F p +
          vectorTransportH1CLM hΩ A
            (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U q)) p) =
      ε • L p + wkpBaseCoordinateCLM (F p) + B p := by
    simp only [map_add, map_smul, higherOrderLaplacianCLM_base,
      vectorTransportH1CLM_base, lowerOrderCLM_trans_apply, L, laplacian_eq_wkpLaplacianCLM, B]
  rw [hbase]
  filter_upwards [Lp.coeFn_add (ε • L p + wkpBaseCoordinateCLM (F p)) (B p),
    Lp.coeFn_add (ε • L p) (wkpBaseCoordinateCLM (F p)),
    Lp.coeFn_smul ε (L p),
    wkpLaplacianCLM_coeFn (lowerOrderCLM (by decide : 2 ≤ 3) (U p)), hB]
      with x hs ha he hL hb
  simp only [L, laplacian_eq_wkpLaplacianCLM] at hs ha he ⊢
  simp only [hs, Pi.add_apply, ha, he, Pi.smul_apply, smul_eq_mul, hL,
    B, hb, wkpCoordinateCLM_apply, sub_eq_add_neg]

/-- For H³ states and H¹ forcing and velocity, the pointwise matrix PDE is
equivalent to the native H¹ equation. The open-domain hypothesis is used only to recover
the derivative coordinates from equality of the base functions. -/
theorem transport_diffusion_equation_iff_ae
    (hΩ : IsOpen Ω) (A : Fin n → Fin m → Fin m → W^{1,∞}(Ω))
    (U : Fin m → W^{3,2}(Ω)) (G F : Fin m → W^{1,2}(Ω)) :
    (∀ p, G p =
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p) + F p +
        vectorTransportH1CLM hΩ A
          (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U q)) p) ↔
    ∀ᵐ x ∂domainMeasure n Ω, ∀ p,
      wkpBaseCoordinateCLM (G p) x -
        ε * (∑ j, wkpCoordinateCLM (pairDerivIndex n j j)
          (lowerOrderCLM (by decide : 2 ≤ 3) (U p)) x) +
        (∑ j, ∑ q, wkpBaseCoordinateCLM (A j p q) x *
          wkpCoordinateCLM (singleDerivIndex n j)
            (lowerOrderCLM (by decide : 1 ≤ 3) (U q)) x) =
        wkpBaseCoordinateCLM (F p) x := by
  have hrhs := transport_diffusion_rhs_ae (ε := ε) hΩ A U F
  constructor
  · intro h
    filter_upwards [hrhs] with x hx
    intro p
    rw [h p, hx p]
    abel
  · intro h p
    apply wkpBaseCoordinateCLM_injective hΩ
    apply Lp.ext
    filter_upwards [h, hrhs] with x hx hr
    rw [hr p]
    linear_combination hx p

end PDE.Parabolic.Systems
