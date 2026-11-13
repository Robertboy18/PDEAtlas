/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Existence
public import PDE.Parabolic.Systems.Transport.Solution
import PDE.Analysis.Evolution.Time.WeakDerivative.FiniteProduct
import PDE.Analysis.MeasureTheory.Lp.FiniteCoordinates.Hilbert

/-!
# Finite Hilbert-valued strong matrix diffusion solutions

The constructed component trajectories assemble into Bochner classes
in the finite Hilbert product. Their coordinate weak derivatives give the
vector weak derivative, and the H² trace gives the closed H¹ trace required
by the strong solution predicate. The equation is transferred to the pointwise
matrix entries and forcing representatives on one common exceptional set.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n m : ℕ} {ε a b : ℝ}

/-- Continuous W¹,∞ matrix coefficients, an H² initial value and L²(H¹)
forcing produce a strong solution for every positive viscosity and finite
interval. Pointwise representatives of the coefficients and forcing occur in
the equation, with no regularity assumed on those representatives. -/
theorem exists_strongTransportDiffusionSolution
    (hε : 0 < ε) (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b))
    (B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ)
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (f : Fin m → ℝ × ℝ^n → ℝ)
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F p t) x = f p (t, x))
    (q : PiLp 2 (fun _ : Fin m ↦ W^{2,2}(ℝ^n))) :
    ∃ (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
        (volume.restrict (Ioc a b)))
      (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
        (volume.restrict (Ioc a b)))
      (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      IsStrongTransportDiffusionSolution ε a b B f
        (ContinuousLinearMap.piLpMap 2
          (fun _ : Fin m ↦ lowerOrderCLM (by decide : 1 ≤ 2)) q) U G z := by
  -- Fix the `PiLp` normed-space structures before elaborating the Bochner maps.
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{3,2}(ℝ^n))
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{1,2}(ℝ^n))
  let μ := volume.restrict (Ioc a b)
  obtain ⟨u, g, Z, hZ, hZa, hu⟩ := exists_transport_diffusion_solution hε hab A hA F q
  obtain ⟨U, hU, _⟩ := Lp.exists_piLp_L2 u
  obtain ⟨G, hG, _⟩ := Lp.exists_piLp_L2 g
  let z (t : ℝ) : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) :=
    WithLp.toLp 2 (fun p ↦ lowerOrderCLM (by decide : 1 ≤ 2) (Z t p))
  let P : PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) :=
    ContinuousLinearMap.piLpMap 2 (fun _ ↦ lowerOrderCLM (by decide))
  refine ⟨U, G, z, ?_⟩
  constructor
  · apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    exact continuousOn_pi.mpr fun p ↦
      (lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_continuousOn
        ((continuous_apply p).comp_continuousOn hZ)
  · change WithLp.toLp 2 (fun p ↦ lowerOrderCLM (by decide : 1 ≤ 2) (Z a p)) = _
    rw [hZa]
    rfl
  · filter_upwards [hU, ae_all_iff.mpr (fun p ↦ (hu p).2.2)] with t ht hzt
    apply PiLp.ext
    intro p
    change lowerOrderCLM (by decide : 1 ≤ 2) (Z t p) =
      lowerOrderCLM (by decide : 1 ≤ 3) (U t p)
    rw [ht p, hzt p, lowerOrderCLM_trans_apply]
  · apply HasWeakTimeDerivativeOn.of_piLp_coordinates
    · have hi : IntegrableOn (fun t ↦ P (U t)) (Ioc a b) :=
        (P.comp_memLp U).integrable (by norm_num)
      exact hi.locallyIntegrableOn.mono_set Ioo_subset_Ioc_self
    · have hi : IntegrableOn (fun t ↦ G t) (Ioc a b) :=
        (Lp.memLp G).integrable (by norm_num)
      exact hi.locallyIntegrableOn.mono_set Ioo_subset_Ioc_self
    · intro p
      apply (hu p).2.1.congr_ae_restrict measurableSet_Ioo
      · filter_upwards [hU.filter_mono
          (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
        simp only [ContinuousLinearMap.piLpMap_apply, ht]
      · filter_upwards [hG.filter_mono
          (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
        exact (ht p).symm
  · filter_upwards [hU, hG, hB, hf, ae_all_iff.mpr (fun p ↦ (hu p).1)]
      with t hUt hGt hBt hft heqt
    have heq := (transport_diffusion_equation_iff_ae isOpen_univ (A t)
      (fun p ↦ u p t) (fun p ↦ g p t) (fun p ↦ F p t)).mp heqt
    simp only [domainMeasure, Measure.restrict_univ] at heq
    filter_upwards [heq, hBt, hft] with x hx hBx hfx
    intro p
    simpa only [hUt, hGt, ← hBx, ← hfx, wkpCoordinateCLM_apply,
      lowerOrderCLM_apply] using hx p

open SobolevSpace.Approximation

/-- Mollifying an H¹ datum gives the H² initial value needed for H³
regularity. Its H¹ trace is the graph mollifier `mollifierHkCLM` of the
datum, for any positive smoothing scale. -/
theorem exists_strongTransportDiffusionSolution_mollified
    (hε : 0 < ε) (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b))
    (B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ)
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (f : Fin m → ℝ × ℝ^n → ℝ)
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F p t) x = f p (t, x))
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (g : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :
    ∃ (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
        (volume.restrict (Ioc a b)))
      (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
        (volume.restrict (Ioc a b)))
      (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      IsStrongTransportDiffusionSolution ε a b B f
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM μ hδ) g) U G z := by
  let q : PiLp 2 (fun _ : Fin m ↦ W^{2,2}(ℝ^n)) :=
    WithLp.toLp 2 (fun p ↦ mollifierSmoothingCLM 2 μ hδ (wkpBaseCoordinateCLM (g p)))
  obtain ⟨U, G, z, hz⟩ :=
    exists_strongTransportDiffusionSolution hε hab A hA B hB F f hf q
  have hq : ContinuousLinearMap.piLpMap 2
      (fun _ : Fin m ↦ lowerOrderCLM (by decide : 1 ≤ 2)) q =
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM μ hδ) g := by
    apply PiLp.ext
    intro p
    change lowerOrderCLM (by decide : 1 ≤ 2)
        (mollifierSmoothingCLM 2 μ hδ (wkpBaseCoordinateCLM (g p))) = _
    rw [lowerOrderCLM_mollifierSmoothingCLM, mollifierSmoothingCLM_baseCoordinate]
    rfl
  rw [hq] at hz
  exact ⟨U, G, z, hz⟩

end PDE.Parabolic.Systems
