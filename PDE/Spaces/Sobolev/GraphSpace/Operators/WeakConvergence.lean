/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness.Identification
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.Analysis.MeasureTheory.Lp.ContinuousExtension

/-!
# Weak convergence of bounded Sobolev graphs

On an open set, the base L2 coordinate determines the Sobolev graph. Therefore
a uniform Hk bound and weak convergence of the base coordinate imply weak Hk
convergence along the same filter. For a jointly continuous field on a spatial
ball, compact restriction gives the required strong L2 continuity of its base.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Uniformly bounded Sobolev graphs converge weakly when their base L2
coordinates converge weakly to the base of the prescribed graph. -/
theorem tendsto_weak_hk_of_base
    (hΩ : IsOpen Ω) {ι : Type*} {l : Filter ι}
    (u : ι → W^{k,2}(Ω)) (v : W^{k,2}(Ω))
    (hbounded : Bornology.IsBounded (range u))
    (hbase : Tendsto
      (fun i ↦ toWeakSpace ℝ (DerivLp n 2 Ω) (wkpBaseCoordinateCLM (u i))) l
      (𝓝 (toWeakSpace ℝ (DerivLp n 2 Ω) (wkpBaseCoordinateCLM v)))) :
    Tendsto (fun i ↦ toWeakSpace ℝ (W^{k,2}(Ω)) (u i)) l
      (𝓝 (toWeakSpace ℝ (W^{k,2}(Ω)) v)) :=
  PDE.Analysis.WeakCompactness.tendsto_of_injective_map
    (H := W^{k,2}(Ω)) (E := DerivLp n 2 Ω)
    wkpBaseCoordinateCLM (wkpBaseCoordinateCLM_injective hΩ) u v hbounded hbase

/-- A bounded family of local Sobolev graphs is weakly continuous if its
base representatives form a jointly continuous field. The ball may
cross any coordinate axis. -/
theorem continuous_weak_hk_of_joint_continuous
    {T : Type*} [TopologicalSpace T] (r : ℝ)
    (u : T → W^{k,2}(Metric.ball (0 : ℝ^n) r)) (f : T → ℝ^n → ℝ)
    (hf : Continuous (fun z : T × ℝ^n ↦ f z.1 z.2))
    (hbase : ∀ t, baseRepresentative (u t)
      =ᵐ[domainMeasure n (Metric.ball 0 r)] f t)
    (hbounded : Bornology.IsBounded (range u)) :
    Continuous (fun t ↦ toWeakSpace ℝ (W^{k,2}(Metric.ball (0 : ℝ^n) r)) (u t)) := by
  let K := Metric.closedBall (0 : ℝ^n) r
  have hK : IsCompact K := isCompact_closedBall (0 : ℝ^n) r
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasure ((domainMeasure n (Metric.ball 0 r)).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let G : C(T, C(K, ℝ)) := (⟨fun z : T × K ↦ f z.1 z.2,
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩ :
      C(T × K, ℝ)).curry
  let L : C(K, ℝ) →L[ℝ] DerivLp n 2 (Metric.ball 0 r) :=
    (BoundedContinuousFunction.subtypeToLp (p := 2)
      (μ := domainMeasure n (Metric.ball 0 r)) hK.isClosed.measurableSet).comp
        ((ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ).toContinuousLinearEquiv
          |>.toContinuousLinearMap)
  have hLG (t : T) : (L (G t) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Metric.ball 0 r)] f t := by
    have hL : (L (G t) : ℝ^n → ℝ) =ᵐ[domainMeasure n (Metric.ball 0 r)]
        Function.extend Subtype.val (G t) (fun _ ↦ 0) :=
      BoundedContinuousFunction.coeFn_subtypeToLp (p := 2)
        (μ := domainMeasure n (Metric.ball 0 r)) hK.isClosed.measurableSet
        (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (G t))
    filter_upwards [hL, ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    have hxK : x ∈ K := Metric.ball_subset_closedBall hball
    exact Subtype.coe_injective.extend_apply _ _ (⟨x, hxK⟩ : K)
  have heq : (fun t ↦ wkpBaseCoordinateCLM (u t)) = fun t ↦ L (G t) := by
    funext t
    apply Lp.ext
    exact (hbase t).trans (hLG t).symm
  apply PDE.Analysis.WeakCompactness.continuous_of_injective_map
    (H := W^{k,2}(Metric.ball (0 : ℝ^n) r)) (E := DerivLp n 2 (Metric.ball 0 r))
    wkpBaseCoordinateCLM (wkpBaseCoordinateCLM_injective Metric.isOpen_ball) u hbounded
  have hcontinuous : Continuous (fun t ↦ wkpBaseCoordinateCLM (u t)) := by
    rw [heq]
    exact L.continuous.comp G.continuous
  exact (toWeakSpaceCLM ℝ _).continuous.comp hcontinuous

/-- Joint base continuity on bounded weak sets identifies the weak limits of
the uniformly bounded local Sobolev graphs selected by a recovery estimate. -/
theorem exists_local_graph_tendsto_weak
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n k : ℕ}
    (f : E → (ℝ^n) → ℝ) (r : ℝ)
    (hSob : ∃ C : ℝ, 0 ≤ C ∧ ∀ V : E, ∃ G : W^{k,2}(Metric.ball (0 : ℝ^n) r),
      baseRepresentative G =ᵐ[domainMeasure n (Metric.ball 0 r)] f V ∧
      ‖G‖ ≤ C * (1 + ‖V‖ + ‖V‖ ^ 2))
    (hjoint : ∀ B : ℝ, Continuous
      (fun z : {v : WeakSpace ℝ E // ‖(toWeakSpace ℝ E).symm v‖ ≤ B} × (ℝ^n) ↦
        f ((toWeakSpace ℝ E).symm z.1.val) z.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ G : E → W^{k,2}(Metric.ball (0 : ℝ^n) r),
      (∀ V, baseRepresentative (G V) =ᵐ[domainMeasure n (Metric.ball 0 r)] f V ∧
        ‖G V‖ ≤ C * (1 + ‖V‖ + ‖V‖ ^ 2)) ∧
      ∀ {ι : Type*} {l : Filter ι} [l.NeBot] (u : ι → E) (v : E) (B : ℝ),
        (∀ i, ‖u i‖ ≤ B) →
        Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E v)) →
        Tendsto (fun i ↦ toWeakSpace ℝ (W^{k,2}(Metric.ball (0 : ℝ^n) r)) (G (u i))) l
          (𝓝 (toWeakSpace ℝ (W^{k,2}(Metric.ball (0 : ℝ^n) r)) (G v))) := by
  obtain ⟨C, hC, hSob⟩ := hSob
  choose G hG using hSob
  refine ⟨C, hC, G, hG, ?_⟩
  intro ι l hl u v B hbound hweak
  have hv : ‖v‖ ≤ B :=
    PDE.Analysis.WeakCompactness.norm_le_of_tendsto_of_norm_le hweak
      (Eventually.of_forall hbound)
  let T := {w : WeakSpace ℝ E // ‖(toWeakSpace ℝ E).symm w‖ ≤ B}
  let uT : ι → T := fun i ↦ ⟨toWeakSpace ℝ E (u i), hbound i⟩
  let vT : T := ⟨toWeakSpace ℝ E v, hv⟩
  have huT : Tendsto uT l (𝓝 vT) := tendsto_subtype_rng.mpr hweak
  have hbounded : Bornology.IsBounded
      (range (fun w : T ↦ G ((toWeakSpace ℝ E).symm w.val))) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C * (1 + B + B ^ 2), ?_⟩
    rintro _ ⟨w, rfl⟩
    apply (hG _).2.trans
    have hw : ‖(toWeakSpace ℝ E).symm w.val‖ ≤ B := w.property
    gcongr
  have hcont := continuous_weak_hk_of_joint_continuous r
    (fun w : T ↦ G ((toWeakSpace ℝ E).symm w.val))
    (fun w : T ↦ f ((toWeakSpace ℝ E).symm w.val))
    (hjoint B) (fun w ↦ (hG _).1) hbounded
  exact hcont.tendsto vT |>.comp huT

/-- The weak H4 source limit also determines the weak H3 limits of all
first weak derivative graphs. -/
theorem exists_local_scalar_graph_tendsto_weak
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (f : E → (ℝ^n) → ℝ) (r : ℝ)
    (hSob : ∃ C : ℝ, 0 ≤ C ∧ ∀ V : E, ∃ G : W^{4,2}(Metric.ball (0 : ℝ^n) r),
      baseRepresentative G =ᵐ[domainMeasure n (Metric.ball 0 r)] f V ∧
      ‖G‖ ≤ C * (1 + ‖V‖ + ‖V‖ ^ 2))
    (hjoint : ∀ B : ℝ, Continuous
      (fun z : {v : WeakSpace ℝ E // ‖(toWeakSpace ℝ E).symm v‖ ≤ B} × (ℝ^n) ↦
        f ((toWeakSpace ℝ E).symm z.1.val) z.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ G : E → W^{4,2}(Metric.ball (0 : ℝ^n) r),
      (∀ V, baseRepresentative (G V) =ᵐ[domainMeasure n (Metric.ball 0 r)] f V ∧
        ‖G V‖ ≤ C * (1 + ‖V‖ + ‖V‖ ^ 2)) ∧
      ∀ {ι : Type*} {l : Filter ι} [l.NeBot] (u : ι → E) (v : E) (B : ℝ),
        (∀ i, ‖u i‖ ≤ B) →
        Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E v)) →
        Tendsto (fun j ↦ toWeakSpace ℝ (W^{4,2}(Metric.ball (0 : ℝ^n) r)) (G (u j))) l
            (𝓝 (toWeakSpace ℝ (W^{4,2}(Metric.ball (0 : ℝ^n) r)) (G v))) ∧
          ∀ i : Fin n, Tendsto
            (fun j ↦ toWeakSpace ℝ (W^{3,2}(Metric.ball (0 : ℝ^n) r))
              (∂[i] (G (u j)))) l
            (𝓝 (toWeakSpace ℝ (W^{3,2}(Metric.ball (0 : ℝ^n) r))
              (∂[i] (G v)))) := by
  obtain ⟨C, hC, G, hG, hweakG⟩ := exists_local_graph_tendsto_weak f r hSob hjoint
  refine ⟨C, hC, G, hG, ?_⟩
  intro ι l hl u v B hbound hweak
  have hlim := hweakG u v B hbound hweak
  refine ⟨hlim, fun i ↦ ?_⟩
  exact (WeakSpace.map (partialDerivCLM (n := n) (k := 3) (p := 2)
    (Ω := Metric.ball 0 r) i)).continuous.tendsto
      (toWeakSpace ℝ (W^{4,2}(Metric.ball (0 : ℝ^n) r)) (G v)) |>.comp hlim

end SobolevSpace.GraphSpace
