/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.AllOrders
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.ReversibleScale

/-!
# Smooth wave trajectories through the initial time

Solve the forward equation also with opposite initial velocity and reflect
that solution in time. The reversible Sobolev scale makes the glued curves
smooth at zero, so their common displacement is smooth on the closed forward
halfspace. This constructs boundary regularity from the initial data.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

omit [NeZero n] in
private theorem mkWkpSpaceOnOfContDiff_neg {k : ℕ} (h : ℝ^n → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhc : HasCompactSupport h) :
    mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) (fun x ↦ -h x) hh.neg hhc.neg =
      -mkWkpSpaceOnOfContDiff h hh hhc := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [map_neg]
  apply Lp.ext
  filter_upwards [wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae hh.neg hhc.neg,
    wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae hh hhc, Lp.coeFn_neg (wkpBaseCoordinateCLM
      (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) h hh hhc))] with x hx hy hz
  simp only [Pi.neg_apply] at hz
  rw [hx, hz, hy]

private theorem contDiff_higherScaleField (hk : ∀ j : ℕ, (n : ℝ) < 2 * (((j + 3 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : W^{(j + 1) + 4,2}(ℝ^n) × W^{(j + 1) + 3,2}(ℝ^n) ↦
      (z.2, higherSmoothAcceleration (hk j) hs hf0 z.1)) := by
  let Q : (W^{(j + 1) + 4,2}(ℝ^n) × W^{(j + 1) + 3,2}(ℝ^n)) →L[ℝ]
      W^{(j + 3) + 2,2}(ℝ^n) := ContinuousLinearMap.fst ℝ _ _
  let A : W^{(j + 3) + 2,2}(ℝ^n) →L[ℝ] W^{j + 3,2}(ℝ^n) := higherOrderLaplacianCLM le_rfl
  let B : W^{(j + 3) + 2,2}(ℝ^n) →L[ℝ] W^{j + 3,2}(ℝ^n) :=
    lowerOrderCLM (by omega)
  exact contDiff_snd.prodMk ((A.contDiff.sub
    ((contDiff_higherComposition (hk j) hs hf0).comp B.contDiff)).comp Q.contDiff)

omit [NeZero n] in
/-- Time reversal preserves displacement and negates velocity at each scale level. -/
def higherVelocityReflection (n j : ℕ) :
    (W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)) →L[ℝ]
      (W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod (-(ContinuousLinearMap.snd ℝ _ _))

private theorem contDiff_reversible_higher_lifts
    (hk : ∀ j : ℕ, (n : ℝ) < 2 * (((j + 3 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    {x y : H¹(ℝ^n) × DerivLp n 2 univ}
    {e d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (he : IsEnergySolution hf hf0 x e) (hd : IsEnergySolution hf hf0 y d)
    (U V : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)))
    (hU : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
        wkpBaseCoordinateCLM (U j t).2) = e t)
    (hV : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (V j t).1,
        wkpBaseCoordinateCLM (V j t).2) = d t)
    (hz : ∀ j, U j 0 = higherVelocityReflection n j (V j 0)) :
    ∀ j, ContDiff ℝ (⊤ : ℕ∞)
      (reversibleGluing (higherVelocityReflection n j) (U j) (V j) (hz j)) := by
  let R := higherVelocityReflection n
  let F (j : ℕ) (z : W^{(j + 1) + 4,2}(ℝ^n) × W^{(j + 1) + 3,2}(ℝ^n)) :
      W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n) := (z.2, higherSmoothAcceleration (hk j) hs hf0 z.1)
  have hF (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (F j) := contDiff_higherScaleField hk hs hf0 j
  refine contDiff_reversibleGluing (E := fun j ↦ W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n))
    (fun j ↦ j + 1) R F hF ?_ U V hz ?_ ?_
  · intro j z
    change (-z.2, higherSmoothAcceleration (hk j) hs hf0 z.1) =
      (-z.2, - -higherSmoothAcceleration (hk j) hs hf0 z.1)
    rw [neg_neg]
  · intro j t ht
    exact he.hasDerivAt_higher_lifts hk hs hf hf0 U hU j ht
  · intro j t ht
    exact hd.hasDerivAt_higher_lifts hk hs hf hf0 V hV j ht

/-- Smooth compact Cauchy data have compatible higher forward lifts which are
restrictions of smooth time curves at every Sobolev order. -/
theorem exists_smooth_higher_lifts_of_smoothCompact
    (hn : n < 4) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ e : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      IsEnergySolution hf hf0
        (mkWkpSpaceOnOfContDiff g hg hgc,
          wkpBaseCoordinateCLM (mkWkpSpaceOnOfContDiff (k := 3) h hh hhc)) e ∧
      ∃ U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)),
        (∀ j, U j 0 = (mkWkpSpaceOnOfContDiff g hg hgc,
          mkWkpSpaceOnOfContDiff h hh hhc)) ∧
        (∀ j t, 0 ≤ t →
          (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
            wkpBaseCoordinateCLM (U j t).2) = e t) ∧
        ∀ j, ContDiff ℝ (⊤ : ℕ∞) (U j) := by
  obtain ⟨e, he, U, hU0, hU⟩ :=
    exists_global_higher_lifts_of_smoothCompact hn hs hf hf0 g h hg hh hgc hhc
  obtain ⟨d, hd, V, hV0, hV⟩ := exists_global_higher_lifts_of_smoothCompact hn hs hf hf0
      g (fun x ↦ -h x) hg hh.neg hgc hhc.neg
  have hn' : (n : ℝ) < 4 := by exact_mod_cast hn
  have hk (j : ℕ) : (n : ℝ) < 2 * (((j + 3 : ℕ) : ℝ) - 1) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  let R := higherVelocityReflection n
  have hz (j : ℕ) : U j 0 = R j (V j 0) := by
    rw [hU0, hV0, mkWkpSpaceOnOfContDiff_neg h hh hhc]
    simp only [R, higherVelocityReflection, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', neg_apply, neg_neg]
  let Z (j : ℕ) := reversibleGluing (R j) (U j) (V j) (hz j)
  have hsmooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Z j) :=
    contDiff_reversible_higher_lifts hk hs hf hf0 he hd U V hU hV hz
  refine ⟨e, he, Z, ?_, ?_, hsmooth⟩
  · intro j
    rw [show Z j 0 = U j 0 from reversibleGluing_of_nonneg _ _ _ _ le_rfl]
    exact hU0 j
  · intro j t ht
    rw [show Z j t = U j t from reversibleGluing_of_nonneg _ _ _ _ ht]
    exact hU j t ht

omit [NeZero n] in
/-- Smooth extensions of every higher lift give joint smoothness of their
continuous common representative up to the initial boundary. -/
theorem contDiffOn_closed_of_smooth_higher_lifts (hn : n < 4)
    (U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)))
    {e : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hU : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
        wkpBaseCoordinateCLM (U j t).2) = e t)
    (hs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (U j))
    {q : C(ℝ × ℝ^n, ℝ)}
    (hq : ∀ t, 0 ≤ t → (fun y ↦ q (t, y)) =ᵐ[volume] baseRepresentative (e t).1) :
    ContDiffOn ℝ (⊤ : ℕ∞) q (Ici 0 ×ˢ univ) := by
  have hn' : (n : ℝ) < 4 := by exact_mod_cast hn
  apply contDiffOn_infty.mpr
  intro r
  have hkr : (n : ℝ) < 2 * (((r + 4 : ℕ) : ℝ) - 1) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hrr : (n : ℝ) < 2 * (((r + 4 : ℕ) : ℝ) - r - 1) := by push_cast; linarith
  have htime : ContDiffOn ℝ r (fun t ↦ (U r t).1) univ :=
    (contDiff_fst.comp ((hs r).of_le (by simp))).contDiffOn
  have hfield := contDiffOn_joint_classicalRepresentative isOpen_univ hkr hrr htime
  apply (hfield.mono (prod_mono (subset_univ _) Subset.rfl)).congr
  intro p hp
  have ha := hq p.1 hp.1
  rw [← hU r p.1 hp.1] at ha
  exact congrFun (eq_classicalRepresentativeCLM_of_ae_eq hkr (U r p.1).1
    (q.continuous.comp (continuous_const.prodMk continuous_id)) ha) p.2

end PDE.Hyperbolic.NonlinearWave.Cauchy
