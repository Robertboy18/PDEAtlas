/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Construction.RegularizedFamily
public import PDE.Analysis.Evolution.Compactness.InitialTrace
import PDE.Analysis.WeakCompactness.Operators
import PDE.Analysis.Evolution.Compactness.MollifiedOperators
import PDE.Analysis.Evolution.Compactness.Lp.PointwiseBounds

/-!
# Heat evolution as a joint weak limit

The uniformly bounded H¹ trajectories, smoothed H² states, and L² velocities
have a common weak limit. Self-adjoint mollifiers disappear against strongly
convergent test vectors. This identifies the weak Laplacian of the limit and preserves
the integrated initial identity. The argument is on all of ℝⁿ and uses no
compact spatial embedding.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open Filter MeasureTheory Set
open PDE.Analysis PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal InnerProductSpace Topology Sobolev

variable {n : ℕ} {ε δ a b : ℝ}

/-- The two Bochner states satisfy the graph relation: restricting
the smoothed H² state gives the H¹ mollifier of the original H¹ state. -/
theorem lowerOrder_compLpL_regularized_heat_state
    (hδ : 0 < δ)
    (u : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (z : ℝ → W^{1,2}(ℝ^n))
    (hu : (u : ℝ → W^{1,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] z)
    (hv : (v : ℝ → W^{2,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      mollifierSmoothingCLM 2 (standardMollifier n) hδ (wkpBaseCoordinateCLM (z t))) :
    (lowerOrderCLM (n := n) (p := 2) (by omega : 1 ≤ 2)).compLpL
      2 (volume.restrict (Ioc a b)) v =
      (mollifierHkCLM (k := 1) (standardMollifier n) hδ).compLpL
        2 (volume.restrict (Ioc a b)) u := by
  apply Lp.ext
  filter_upwards [hu, hv,
    (lowerOrderCLM (n := n) (p := 2) (by omega : 1 ≤ 2)).coeFn_compLpL v,
    (mollifierHkCLM (k := 1) (standardMollifier n) hδ).coeFn_compLpL u]
    with t hut hvt hlow hJ
  rw [hlow, hJ, hvt, hut, lowerOrderCLM_mollifierSmoothingCLM,
    mollifierSmoothingCLM_baseCoordinate]

/-- The projected velocity equals the mollified weak Laplacian of
the smoothed state plus the mollified original forcing, as Bochner classes. -/
theorem regularized_heat_velocity_eq
    (hδ : 0 < δ)
    (v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (z : ℝ → W^{1,2}(ℝ^n))
    (hv : (v : ℝ → W^{2,2}(ℝ^n)) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      mollifierSmoothingCLM 2 (standardMollifier n) hδ (wkpBaseCoordinateCLM (z t)))
    (hg : (g : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM 1 hδ (z t) +
        mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t))) :
    g = (mollifierRowCLM (standardMollifier n) hδ).compLpL 2
        (volume.restrict (Ioc a b))
        ((ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
          2 (volume.restrict (Ioc a b)) v) +
      (mollifierRowCLM (standardMollifier n) hδ).compLpL
        2 (volume.restrict (Ioc a b)) F := by
  let μ := volume.restrict (Ioc a b)
  let A : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  let J := mollifierRowCLM (standardMollifier n) hδ
  apply Lp.ext
  filter_upwards [hv, hg, A.coeFn_compLpL v, J.coeFn_compLpL (A.compLpL 2 μ v),
    J.coeFn_compLpL F, Lp.coeFn_add (J.compLpL 2 μ (A.compLpL 2 μ v))
      (J.compLpL 2 μ F)] with t hvt hgt hA hJv hJF hadd
  rw [hadd, Pi.add_apply, hJv, hJF, hA, hgt, map_add, map_smul,
    regularizedLaplacianCLM_base,
    mollifierSmoothingCLM_base]
  simp only [A, J, smul_apply, map_smul, hvt, laplacian_eq_wkpLaplacianCLM]

/-- Weak limits remove both mollifiers and preserve the graph linking the
H¹ trajectory to the H² state. All three limits use the same ultrafilter. -/
theorem exists_heat_weak_limits
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) (hδ0 : Tendsto δ atTop (𝓝 0))
    (u : ℕ → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (v : ℕ → Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g : ℕ → Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (hu : Bornology.IsBounded (range u)) (hv : Bornology.IsBounded (range v))
    (hg : Bornology.IsBounded (range g))
    (hB : ∀ k, (lowerOrderCLM (n := n) (p := 2) (by omega : 1 ≤ 2)).compLpL
        2 (volume.restrict (Ioc a b)) (v k) =
      (mollifierHkCLM (k := 1) (standardMollifier n) (hδ k)).compLpL
        2 (volume.restrict (Ioc a b)) (u k))
    (hG : ∀ k, g k =
      (mollifierRowCLM (standardMollifier n) (hδ k)).compLpL
        2 (volume.restrict (Ioc a b))
        ((ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
          2 (volume.restrict (Ioc a b)) (v k)) +
      (mollifierRowCLM (standardMollifier n) (hδ k)).compLpL
        2 (volume.restrict (Ioc a b)) F) :
    ∃ (uLimit : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (vLimit : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (gLimit : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
      (W : Ultrafilter ℕ),
      (W : Filter ℕ) ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (u k)) W (𝓝 (toWeakSpace ℝ _ uLimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (v k)) W (𝓝 (toWeakSpace ℝ _ vLimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (g k)) W (𝓝 (toWeakSpace ℝ _ gLimit)) ∧
      (lowerOrderCLM (n := n) (p := 2) (by omega : 1 ≤ 2)).compLpL
        2 (volume.restrict (Ioc a b)) vLimit = uLimit ∧
      gLimit = (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) vLimit + F := by
  let μ := volume.restrict (Ioc a b)
  let QX (k : ℕ) : Lp (W^{1,2}(ℝ^n)) 2 μ →L[ℝ] Lp (W^{1,2}(ℝ^n)) 2 μ :=
    (mollifierHkCLM (standardMollifier n) (hδ k)).compLpL 2 μ
  let QZ (k : ℕ) : Lp (DerivLp n 2 univ) 2 μ →L[ℝ] Lp (DerivLp n 2 univ) 2 μ :=
    (mollifierRowCLM (standardMollifier n) (hδ k)).compLpL 2 μ
  have hQX (x : Lp (W^{1,2}(ℝ^n)) 2 μ) :
      Tendsto (fun k ↦ QX k x) atTop (𝓝 x) := by
    apply tendsto_compLpL_of_tendsto_strongly
      (fun k ↦ mollifierHkCLM (standardMollifier n) (hδ k)) 1 zero_le_one
    · intro k y
      simpa only [one_mul] using norm_mollifierHkCLM_apply_le _ (hδ k) y
    · exact tendsto_mollifierHkCLM _ δ hδ hδ0
  have hQZ (z : Lp (DerivLp n 2 univ) 2 μ) :
      Tendsto (fun k ↦ QZ k z) atTop (𝓝 z) :=
    tendsto_mollifierRowCLM_compLpL μ _ δ hδ hδ0 z
  have hQXself (k : ℕ) (x y : Lp (W^{1,2}(ℝ^n)) 2 μ) :
      ⟪QX k x, y⟫_ℝ = ⟪x, QX k y⟫_ℝ :=
    inner_compLpL_left_of_self_adjoint μ
      (mollifierHkCLM (k := 1) (standardMollifier n) (hδ k))
      (inner_standardMollifierHkCLM_left (n := n) (r := 1) (hδ k)) x y
  have hQZself (k : ℕ) (x y : Lp (DerivLp n 2 univ) 2 μ) :
      ⟪QZ k x, y⟫_ℝ = ⟪x, QZ k y⟫_ℝ :=
    inner_compLpL_left_of_self_adjoint μ
      (mollifierRowCLM (standardMollifier n) (hδ k))
      (inner_standardMollifierRowCLM_left (n := n) (hδ k)) x y
  let B : W^{2,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by omega)
  let A : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  have : CompleteSpace (Lp (W^{1,2}(ℝ^n)) 2 μ) := inferInstance
  have : CompleteSpace (Lp (W^{2,2}(ℝ^n)) 2 μ) := inferInstance
  have : CompleteSpace (Lp (DerivLp n 2 univ) 2 μ) := inferInstance
  have hB' (k : ℕ) : B.compLpL 2 μ (v k) = QX k (u k) := hB k
  have hG' (k : ℕ) : g k = QZ k (A.compLpL 2 μ (v k)) + QZ k F := hG k
  have hcompact := WeakCompactness.exists_weak_limit_regularized_graph
    (X := Lp (W^{1,2}(ℝ^n)) 2 μ) (Y := Lp (W^{2,2}(ℝ^n)) 2 μ)
    (Z := Lp (DerivLp n 2 univ) 2 μ) (ι := ℕ) (l := atTop)
  have hcompactQ := hcompact QX QZ hQX hQZ hQXself hQZself
  have hcompactBA := hcompactQ (B.compLpL 2 μ) (A.compLpL 2 μ)
  have hcompactSeq := hcompactBA u v g F hu hv hg
  obtain ⟨uLimit, vLimit, gLimit, W, hW, huw, hvw, hgw, hBu, hGlim⟩ :=
    hcompactSeq hB' hG'
  exact ⟨uLimit, vLimit, gLimit, W, hW, huw, hvw, hgw, hBu, hGlim⟩

/-- The heat equation has an H² Bochner state and an L² velocity
with the full integrated initial identity and an H¹ energy envelope. The
initial datum and forcing are arbitrary in H¹ and L²(L²), respectively. -/
theorem exists_heat_integrated_solution
    (hε : 0 < ε) (hab : a ≤ b)
    (F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b))) (q : W^{1,2}(ℝ^n)) :
    ∃ (v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b))),
      g = (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) v + F ∧
      ε * ‖v‖ ^ 2 ≤ (1 + (1 + ε) * (b - a) * Real.exp (b - a)) *
        (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        ‖lowerOrderCLM (by omega : 1 ≤ 2) (v t)‖ ^ 2 ≤
          (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) *
            Real.exp (t - a)) ∧
      ∀ (w : DerivLp n 2 univ) (τ : TimeTest a b),
        -(∫ t, ⟪wkpBaseCoordinateCLM (v t), w⟫_ℝ * τ.derivToLp t
          ∂volume.restrict (Ioc a b)) =
        (∫ t, ⟪g t, w⟫_ℝ * τ.toLp t ∂volume.restrict (Ioc a b)) +
          ⟪wkpBaseCoordinateCLM q, w⟫_ℝ * τ.toFun a := by
  let μ := volume.restrict (Ioc a b)
  let δ (k : ℕ) : ℝ := 1 / (k + 1)
  have hδ (k : ℕ) : 0 < δ k := by positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨U, u, v, g, huB, hvB, hgB, hu, hv, hg⟩ :=
    exists_bounded_regularized_heat_family hε hab δ hδ F (Lp.memLp F) q
  let B : W^{2,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by omega)
  obtain ⟨uLimit, vLimit, gLimit, W, _, huweak, hvweak, hgweak, hBu, hGlim⟩ :=
    exists_heat_weak_limits δ hδ hδ0 u v g F huB hvB hgB
      (fun k ↦ lowerOrder_compLpL_regularized_heat_state
        (hδ k) (u k) (v k) (U k).trajectory (hu k) (hv k))
      (fun k ↦ regularized_heat_velocity_eq
        (hδ k) (v k) (g k) F (U k).trajectory (hv k) (hg k))
  have henergy : ∀ᵐ t ∂μ, ‖uLimit t‖ ^ 2 ≤
      (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) *
        Real.exp (t - a) := by
    refine ae_norm_sq_le_of_tendsto_weak_Lp _ huweak (.of_forall fun k ↦ ?_)
    filter_upwards [hu k, ae_restrict_mem measurableSet_Ioc] with t hut ht
    rw [hut]
    exact regularized_heat_norm_sq_le hε (hδ k) hab (Lp.memLp F) (U k)
      t (Ioc_subset_Icc_self ht)
  have hBv : (uLimit : ℝ → W^{1,2}(ℝ^n)) =ᵐ[μ] fun t ↦ B (vLimit t) := by
    rw [← hBu]; exact B.coeFn_compLpL vLimit
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  have hPweak : Tendsto (fun k ↦ toWeakSpace ℝ _ (P.compLpL 2 μ (u k))) W
      (𝓝 (toWeakSpace ℝ _ (P.compLpL 2 μ uLimit))) :=
    (WeakSpace.map (P.compLpL 2 μ)).continuous.continuousAt.tendsto.comp huweak
  have hid (w : DerivLp n 2 univ) (τ : TimeTest a b) :
      -(∫ t, ⟪P.compLpL 2 μ uLimit t, w⟫_ℝ * τ.derivToLp t ∂μ) =
      (∫ t, ⟪gLimit t, w⟫_ℝ * τ.toLp t ∂μ) + ⟪P q, w⟫_ℝ * τ.toFun a := by
    apply integrated_initial_identity_of_weak_state_velocity_limits (P q) hPweak hgweak
    intro k w τ
    apply integrated_initial_identity_of_absolutelyContinuous hab
      (fun t ↦ P ((U k).trajectory t)) (P.compLpL 2 μ (u k)) (g k) (P q)
    · exact P.lipschitzWith.comp_absolutelyContinuousOnInterval (U k).absolutely_continuous
    · filter_upwards [P.coeFn_compLpL (u k), hu k] with t hPt hut
      rw [hPt, hut]
    · filter_upwards [(U k).hasDerivAt_comp_ae P, hg k] with t hdt hgt
      simpa only [hgt, P, map_add, smul_apply] using hdt
    · rw [(U k).initial_value]
  refine ⟨vLimit, gLimit, hGlim, ?_, ?_, ?_⟩
  · rw [mul_comm ε, ← le_div_iff₀ hε]
    refine WeakCompactness.norm_sq_le_of_tendsto_of_norm_sq_le
      (E := Lp (W^{2,2}(ℝ^n)) 2 μ) (u := v) (uLimit := vLimit) hvweak (.of_forall fun k ↦ ?_)
    rw [le_div_iff₀ hε, mul_comm]
    exact regularized_heat_smoothing_norm_sq_le hε hab (hδ k) (Lp.memLp F) (U k) (v k) (hv k)
  · filter_upwards [henergy, hBv] with t ht hvt
    simpa only [hvt] using ht
  · intro w τ
    have heq : (∫ t, ⟪P.compLpL 2 μ uLimit t, w⟫_ℝ * τ.derivToLp t ∂μ) =
        ∫ t, ⟪wkpBaseCoordinateCLM (vLimit t), w⟫_ℝ * τ.derivToLp t ∂μ := by
      apply integral_congr_ae
      filter_upwards [P.coeFn_compLpL uLimit, hBv] with t hPt hvt
      rw [hPt, hvt]
      simp only [P, B, wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
        DerivIndex.castOrder_baseIndex]
    exact heq ▸ hid w τ

end PDE.Parabolic.Heat
