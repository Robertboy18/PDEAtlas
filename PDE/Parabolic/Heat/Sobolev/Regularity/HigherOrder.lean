/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Regularity.Derivative
import PDE.Analysis.Evolution.Compactness.MollifiedOperators
import PDE.Analysis.MeasureTheory.Lp.Composition.LinearMap

/-!
# Higher Sobolev graphs for the heat state

The constructed first-derivative heat solutions bound the H³ norms of the
mollifications. Weak compactness then recovers the measurable H³
graph of the original heat state. The unordered multi-index norm enters
through the first-derivative norm comparison.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open Filter MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- H² initial data and H¹ forcing give an H³ Bochner state for every
heat trajectory in the natural H² energy class. The higher graph is derived
from the equation and its closed-interval trace. -/
theorem exists_heat_higherOrder_state
    (hε : 0 < ε) (hab : a < b)
    (q : W^{2,2}(ℝ^n))
    (F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u +
      (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ).compLpL
        2 (volume.restrict (Ioc a b)) F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (z : ℝ → W^{1,2}(ℝ^n)) (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (u t))
    (hinit : z a = lowerOrderCLM (by decide : 1 ≤ 2) q) :
    ∃ U : Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)),
      (lowerOrderCLM (n := n) (p := 2) (by decide : 2 ≤ 3)).compLpL
        2 (volume.restrict (Ioc a b)) U = u := by
  classical
  let ν := volume.restrict (Ioc a b)
  let μ := standardMollifier n
  choose v hv using
    fun i ↦ exists_heat_firstDerivative_mollification hε hab q F u g heq hweak z hz hzu hinit i
  let δ (j : ℕ) : ℝ := 1 / (j + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let S (j : ℕ) : W^{2,2}(ℝ^n) →L[ℝ] W^{3,2}(ℝ^n) :=
    (mollifierSmoothingCLM 3 μ (hδ j)).comp wkpBaseCoordinateCLM
  let y (j : ℕ) : Lp (W^{3,2}(ℝ^n)) 2 ν := (S j).compLpL 2 ν u
  let P : W^{3,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  let D (i : Fin n) : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) :=
    partialDerivCLM i
  have hP (j : ℕ) : ‖P.compLpL 2 ν (y j)‖ ≤ ‖u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [P.coeFn_compLpL (y j), (S j).coeFn_compLpL u] with t hPt hSt
    rw [hPt]
    change ‖P ((S j).compLpL 2 ν u t)‖ ≤ _
    rw [hSt]
    change ‖wkpBaseCoordinateCLM
      (mollifierSmoothingCLM 3 μ (hδ j) (wkpBaseCoordinateCLM (u t)))‖ ≤ _
    rw [mollifierSmoothingCLM_base]
    exact (norm_mollifierRowCLM_apply_le μ (hδ j) _).trans
      (wkpBaseCoordinateCLM_norm_le (u t))
  have hD (j : ℕ) (i : Fin n) :
      (D i).compLpL 2 ν (y j) =
        (mollifierHkCLM (k := 2) μ (hδ j)).compLpL 2 ν (v i) := by
    rw [← hv i (δ j) (hδ j)]
    let Q : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ :=
      wkpCoordinateCLM (derivIndexOfList [i] (by simp))
    let R : W^{2,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) :=
      (mollifierSmoothingCLM 2 μ (hδ j)).comp Q
    apply Lp.ext
    filter_upwards [(D i).coeFn_compLpL (y j), (S j).coeFn_compLpL u,
      R.coeFn_compLpL u] with t hDt hSt hRt
    rw [hDt]
    change D i ((S j).compLpL 2 ν u t) = R.compLpL 2 ν u t
    rw [hSt, hRt]
    exact derivativeWordCLM_mollifierSmoothingCLM [i] (by simp) (by simp)
      μ (hδ j) (u t)
  have hC : 0 ≤ succOrderAssemblyNormBound n 2 := by
    unfold succOrderAssemblyNormBound
    positivity
  have hbound : Bornology.IsBounded (range y) := by
    refine (isBounded_iff_forall_norm_le (s := range y)).mpr
      ⟨succOrderAssemblyNormBound n 2 * (‖u‖ + ∑ i, ‖v i‖), ?_⟩
    rintro _ ⟨j, rfl⟩
    refine (norm_Lp_le_base_add_firstDerivatives (k := 2) isOpen_univ (y j)).trans ?_
    gcongr with i
    · exact hP j
    change ‖(D i).compLpL 2 ν (y j)‖ ≤ _
    rw [hD]
    exact norm_compLpL_apply_le_of_contraction ν (mollifierHkCLM μ (hδ j))
      (norm_mollifierHkCLM_apply_le μ (hδ j)) (v i)
  exact exists_higherOrder_Lp_of_bounded_mollifications (by decide : 2 ≤ 3)
    μ δ hδ hδ0 u hbound

/-- Higher-order regularity belongs to every heat trajectory with H²
initial data and H¹ forcing. The stronger state and velocity have precisely
the original lower-order coordinates, and the closed traces agree. -/
theorem heat_solution_higherOrder
    (hε : 0 < ε) (hab : a < b)
    (q : W^{2,2}(ℝ^n))
    (F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u +
      (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ).compLpL
        2 (volume.restrict (Ioc a b)) F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (z : ℝ → W^{1,2}(ℝ^n)) (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (u t))
    (hinit : z a = lowerOrderCLM (by decide : 1 ≤ 2) q) :
    ∃ (U : Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (G : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (Z : ℝ → W^{2,2}(ℝ^n)),
      (lowerOrderCLM (n := n) (p := 2) (by decide : 2 ≤ 3)).compLpL
        2 (volume.restrict (Ioc a b)) U = u ∧
      (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ).compLpL
        2 (volume.restrict (Ioc a b)) G = g ∧
      G = (ε • (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) :
        W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n))).compLpL
          2 (volume.restrict (Ioc a b)) U + F ∧
      HasWeakTimeDerivativeOn (Ioo a b)
        (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U t)) (fun t ↦ G t) ∧
      ContinuousOn Z (Icc a b) ∧
      Z =ᵐ[volume.restrict (Ioc a b)]
        (fun t ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U t)) ∧
      Z a = q ∧
      EqOn (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (Z t)) z (Icc a b) := by
  let ν := volume.restrict (Ioc a b)
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  obtain ⟨U, hU⟩ := exists_heat_higherOrder_state hε hab q F u g heq hweak z hz hzu hinit
  let B : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) := lowerOrderCLM (by decide)
  let B₁ : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by decide)
  let A : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) :=
    ε • higherOrderLaplacianCLM (by decide)
  let A₂ : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  let G : Lp (W^{1,2}(ℝ^n)) 2 ν := A.compLpL 2 ν U + F
  have huU : (fun t ↦ u t) =ᵐ[ν] fun t ↦ B (U t) := by rw [← hU]; exact B.coeFn_compLpL U
  have hPA : P.comp A = A₂.comp B := by
    ext1 V
    simp only [ContinuousLinearMap.comp_apply, P, A, A₂, B, smul_apply, map_smul,
      higherOrderLaplacianCLM_base, laplacian_eq_wkpLaplacianCLM]
  have hPG : P.compLpL 2 ν G = g := by
    change P.compLpL 2 ν (A.compLpL 2 ν U + F) = g
    rw [map_add]
    change (P.compLpL 2 ν).comp (A.compLpL 2 ν) U + P.compLpL 2 ν F = g
    rw [← ContinuousLinearMap.comp_compLpL, hPA, ContinuousLinearMap.comp_compLpL]
    change A₂.compLpL 2 ν (B.compLpL 2 ν U) + P.compLpL 2 ν F = g
    rw [show B.compLpL 2 ν U = u from hU]
    exact heq.symm
  have hstate : (fun t ↦ wkpBaseCoordinateCLM (u t)) =ᵐ[ν] fun t ↦ P (B₁ (U t)) := by
    filter_upwards [huU] with t ht
    rw [ht]
    rfl
  have hvelocity : (fun t ↦ g t) =ᵐ[ν] fun t ↦ P (G t) := by
    rw [← hPG]; exact P.coeFn_compLpL G
  have hweakP : HasWeakTimeDerivativeOn (Ioo a b)
      (P ∘ fun t ↦ B₁ (U t)) (P ∘ fun t ↦ G t) :=
    hweak.congr_ae_restrict measurableSet_Ioo
      (hstate.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      (hvelocity.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
  have huInt : IntegrableOn (fun t ↦ B₁ (U t)) (Ioc a b) volume :=
    (B₁.comp_memLp U).integrable (by norm_num)
  have hgInt : IntegrableOn (fun t ↦ G t) (Ioc a b) volume :=
    (Lp.memLp G).integrable (by norm_num)
  have hw := HasWeakTimeDerivativeOn.of_map P
    (wkpBaseCoordinateCLM_injective isOpen_univ)
    (huInt.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
    (hgInt.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn hweakP
  have hzU : z =ᵐ[ν] fun t ↦ B₁ (U t) := by
    filter_upwards [hzu, huU] with t hzt hut
    rw [hzt, hut]
    exact lowerOrderCLM_trans_apply (by decide : 1 ≤ 2) (by decide : 2 ≤ 3) (U t)
  obtain ⟨Z, hZ, hZU, hZz⟩ :=
    exists_continuous_hTwo_representative_eq_lowerOrder hab U G hw z hz hzU
  refine ⟨U, G, Z, hU, hPG, rfl, hw, hZ, hZU, ?_, hZz⟩
  exact lowerOrderCLM_injective (by decide : 1 ≤ 2) isOpen_univ
    ((hZz (left_mem_Icc.mpr hab.le)).trans hinit)


/-- The heat equation has an H³ state and an H¹ weak time derivative
for H² initial data and H¹ forcing. Its continuous H² representative attains
the prescribed initial value on the closed time interval. -/
theorem exists_heat_solution_higherOrder
    (hε : 0 < ε) (hab : a < b) (q : W^{2,2}(ℝ^n))
    (F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b))) :
    ∃ (U : Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (G : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (z : ℝ → W^{2,2}(ℝ^n)),
      G = (ε • (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) :
        W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n))).compLpL
          2 (volume.restrict (Ioc a b)) U + F ∧
      HasWeakTimeDerivativeOn (Ioo a b)
        (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U t)) (fun t ↦ G t) ∧
      ContinuousOn z (Icc a b) ∧
      z =ᵐ[volume.restrict (Ioc a b)]
        (fun t ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U t)) ∧
      z a = q := by
  let ν := volume.restrict (Ioc a b)
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  obtain ⟨u, g, z, heq, _, hweak, hz, hzu, hinit, _⟩ :=
    exists_heat_solution hε hab (P.compLpL 2 ν F) (lowerOrderCLM (by decide : 1 ≤ 2) q)
  obtain ⟨U, G, Z, _, _, hG, hw, hZ, hZU, hZa, _⟩ :=
    heat_solution_higherOrder hε hab q F u g heq hweak z hz hzu hinit
  exact ⟨U, G, Z, hG, hw, hZ, hZU, hZa⟩

end PDE.Parabolic.Heat
