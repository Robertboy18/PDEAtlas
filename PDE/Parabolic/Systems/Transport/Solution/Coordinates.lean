/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Solution
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Recovering the native equation from a strong solution

The literal almost-everywhere equation determines the H¹ equation because
the Sobolev base coordinate is injective. This allows the energy and
uniqueness results to apply to any strong solution, whatever its
construction and whichever pointwise coefficient representatives are chosen.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution

open MeasureTheory Set
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev
open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {ε a b : ℝ}
  {B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ}
  {f : Fin m → ℝ × ℝ^n → ℝ}
  {q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}
  {U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}

/-- Coordinate projections recover the scalar Bochner weak
derivatives, with the H³ state lowered to H¹ before differentiating. -/
theorem coordinate_weakTimeDerivative
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z) (p : Fin m) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3)
        ((PiLp.proj 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) p :
          PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ] W^{3,2}(ℝ^n)).compLpL
            2 (volume.restrict (Ioc a b)) U t))
      ((PiLp.proj 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) p :
        PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ] W^{1,2}(ℝ^n)).compLpL
          2 (volume.restrict (Ioc a b)) G) := by
  let P₃ : PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ] W^{3,2}(ℝ^n) :=
    PiLp.proj 2 _ p
  let P₁ : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ] W^{1,2}(ℝ^n) :=
    PiLp.proj 2 _ p
  apply (h.weakTimeDerivative.map P₁).congr_ae_restrict measurableSet_Ioo
  · filter_upwards [(P₃.coeFn_compLpL U).filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    simp only [Function.comp_def, ht, P₁, P₃, PiLp.proj_apply,
      ContinuousLinearMap.piLpMap_apply]
  · exact (P₁.coeFn_compLpL G).symm.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))

/-- Each component of the closed H¹ trace represents the corresponding
projected H³ Bochner trajectory. -/
theorem coordinate_representative
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z) (p : Fin m) :
    (fun t ↦ z t p) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      lowerOrderCLM (by decide : 1 ≤ 3)
        ((PiLp.proj 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) p :
          PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ] W^{3,2}(ℝ^n)).compLpL
            2 (volume.restrict (Ioc a b)) U t) := by
  let P : PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ] W^{3,2}(ℝ^n) :=
    PiLp.proj 2 _ p
  filter_upwards [h.representative, P.coeFn_compLpL U] with t ht hUt
  rw [hUt, ht]
  rfl

/-- The pointwise PDE of a strong solution implies the native H¹ equation. -/
theorem native_equation
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Fin m → ℝ → W^{1,2}(ℝ^n))
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F p t) x = f p (t, x)) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ p,
      G t p = ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U t p) +
        F p t + vectorTransportH1CLM isOpen_univ (A t)
          (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U t q)) p := by
  filter_upwards [h.equation, hB, hf] with t ht hBt hft
  apply (transport_diffusion_equation_iff_ae isOpen_univ (A t)
    (fun p ↦ U t p) (fun p ↦ G t p) (fun p ↦ F p t)).mpr
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [ht, hBt, hft] with x hx hBx hfx
  intro p
  simpa only [← hBx, ← hfx, wkpCoordinateCLM_apply, lowerOrderCLM_apply] using hx p

end PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution
