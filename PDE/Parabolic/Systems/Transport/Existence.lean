/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Regularity.HigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Transport
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Parabolic.Heat.Sobolev.LinearPerturbation

/-!
# Whole-space diffusion with matrix transport

Continuous W¹,∞ matrix coefficients and H¹ forcing give an H³ state
and H¹ weak time derivative on every finite interval. The construction first
solves in C(H¹) using the causal heat response. The resulting L²(H²) state
makes its transport term an L²(H¹) forcing, so heat regularity
upgrades the same trajectory. No symmetry is needed for this existence result.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open PDE.Analysis.Evolution PDE.Parabolic.Heat
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Laplacian Sobolev

variable {n m : ℕ} {ε a b : ℝ}

/-- Diffusion with the full variable matrix first-order term, with a continuous
closed-interval H² trace. The Sobolev regularity and time derivative are
constructed from the coefficients and data. -/
theorem exists_transport_diffusion_solution
    (hε : 0 < ε) (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b))
    (F : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (q : Fin m → W^{2,2}(ℝ^n)) :
    ∃ (U : Fin m → Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (G : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (Z : ℝ → Fin m → W^{2,2}(ℝ^n)),
      ContinuousOn Z (Icc a b) ∧ Z a = q ∧
      ∀ i,
        (fun t ↦ G i t) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦
          ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U i t) + F i t +
            vectorTransportH1CLM isOpen_univ (A t)
              (fun j ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U j t)) i) ∧
        HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U i t)) (fun t ↦ G i t) ∧
        (fun t ↦ Z t i) =ᵐ[volume.restrict (Ioc a b)]
          (fun t ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U i t)) := by
  classical
  let μ := volume.restrict (Ioc a b)
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  let B₀ (t : ℝ) := vectorTransportCLM
    (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q))
  let B₁ (t : ℝ) := vectorTransportH1CLM isOpen_univ (A t)
  have hB₀ : ContinuousOn B₀ (Icc a b) :=
    continuous_vectorTransportCLM.comp_continuousOn (by fun_prop)
  obtain ⟨u, g, z, hz, hza, hu⟩ :=
    exists_heat_solution_of_continuous_linear_perturbation hε hab B₀ hB₀
      (fun i ↦ P.compLpL 2 μ (F i)) (fun i ↦ lowerOrderCLM (by decide : 1 ≤ 2) (q i))
  have hentry (j : Fin n) (p q : Fin m) : MemLp (fun t ↦ A t j p q) ∞ μ :=
    (by fun_prop : ContinuousOn (fun t ↦ A t j p q) (Icc a b)).memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hH (i : Fin m) : MemLp (fun t ↦ F i t + B₁ t (fun j ↦ u j t) i) 2 μ :=
    (Lp.memLp (F i)).add (memLp_vectorTransportH1CLM isOpen_univ A hentry u i)
  let H (i : Fin m) := (hH i).toLp (fun t ↦ F i t + B₁ t (fun j ↦ u j t) i)
  have heq (i : Fin m) : g i =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 μ (u i) + P.compLpL 2 μ (H i) := by
    apply Lp.ext
    filter_upwards [(hu i).1, P.coeFn_compLpL (F i), P.coeFn_compLpL (H i),
      (hH i).coeFn_toLp,
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).coeFn_compLpL
        (u i), Lp.coeFn_add
          ((ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
            2 μ (u i)) (P.compLpL 2 μ (H i)),
      ae_all_iff.mpr (fun j ↦ (hu j).2.2)] with t ht hFt hHt hHval hLap hsum hzt
    rw [ht, hsum, Pi.add_apply, hLap, hHt, hHval, map_add]
    change ε • Δ (u i t) + P.compLpL 2 μ (F i) t + B₀ t (z t) i = _
    rw [hFt]
    dsimp only [P, B₁, B₀]
    rw [vectorTransportH1CLM_base, laplacian_eq_wkpLaplacianCLM]
    rw [show z t = (fun j ↦ lowerOrderCLM (by decide : 1 ≤ 2) (u j t)) from funext hzt]
    simp only [smul_apply]
    abel
  choose U G Z hU hG hGeq hw hZ hZU hZa hZz using fun i ↦
    heat_solution_higherOrder hε hab (q i) (H i) (u i) (g i) (heq i)
      (hu i).2.1 (fun t ↦ z t i) ((continuous_apply i).comp_continuousOn hz)
      (hu i).2.2 (congrFun hza i)
  refine ⟨U, G, (fun t i ↦ Z i t), continuousOn_pi.mpr hZ, funext hZa,
    fun i ↦ ⟨?_, hw i, hZU i⟩⟩
  have huU (j : Fin m) : (fun t ↦ u j t) =ᵐ[μ]
      fun t ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U j t) := by
    rw [← hU j]
    exact (lowerOrderCLM (by decide) : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n)).coeFn_compLpL (U j)
  rw [hGeq i]
  filter_upwards [Lp.coeFn_add
    ((ε • (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) :
      W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n))).compLpL 2 μ (U i)) (H i),
    (ε • (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) :
      W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n))).coeFn_compLpL (U i),
    (hH i).coeFn_toLp, ae_all_iff.mpr huU] with t ht hLt hHt hUt
  rw [ht, Pi.add_apply, hLt, hHt]
  change ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U i t) +
    (F i t + B₁ t (fun j ↦ u j t) i) = _
  rw [show (fun j ↦ u j t) = (fun j ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U j t)) from
    funext hUt]
  exact (add_assoc _ _ _).symm

end PDE.Parabolic.Systems
