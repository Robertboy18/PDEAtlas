/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.SectionProjection
public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.Hessian

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import PDE.Analysis.Calculus.LocalExtension.Zero
import CAS.ExactTactic

/-!
# A GN-neutral bilinear family with prescribed projected integral

The trajectory, fundamental solution, terminal projection, frame and transverse
vector are supplied once. One time arc and one normalized bump work for every
projected target. The tensor is the `bilinearCorrection` formula,
including away from the arc, where its target is zero.

Only the two used frame columns need smoothness. Invertibility of their projected
pair persists by continuity and forces the omitted tangent coordinate to remain
nonzero.

The result is a tensor along the supplied curve.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped ContDiff Topology Matrix

namespace PDE.Analysis.GNNeutralHessian

/-- The converse needed for persistence, without differentiating the dual basis. -/
private theorem repr_ne_zero_of_isInvertible_projectedPair (r : Module.Basis (Fin 3) ℝ (ℝ^3))
    (v : ℝ^3) (π : (ℝ^3) →L[ℝ] (ℝ^2))
    (hker : LinearMap.ker π.toLinearMap = Submodule.span ℝ ({v} : Set (ℝ^3))) (hv : v ≠ 0)
    (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hM : (projectedPair (π (r i)) (π (r j))).IsInvertible) :
    r.repr v k ≠ 0 := by
  classical
  intro hk
  have hsplit : v = r.repr v i • r i + r.repr v j • r j := by
    apply r.repr.injective
    ext m
    have hm : m = i ∨ m = j ∨ m = k := by omega
    rcases hm with rfl | rfl | rfl
    · simp [map_add, map_smul, hij.symm]
    · simp [map_add, map_smul, hij]
    · simp [map_add, map_smul, hki.symm, hkj.symm, hk]
  have hvπ : π v = 0 := show v ∈ LinearMap.ker π.toLinearMap from
    hker ▸ Submodule.subset_span (mem_singleton v)
  let c : ℝ^2 := WithLp.toLp 2 ![r.repr v i, r.repr v j]
  have hc : projectedPair (π (r i)) (π (r j)) c = 0 := by
    change r.repr v i • π (r i) + r.repr v j • π (r j) = 0
    simpa only [map_add, map_smul] using (congrArg π hsplit).symm.trans hvπ
  have hc0 : c = 0 := hM.injective (hc.trans (map_zero _).symm)
  have hci : r.repr v i = 0 := congrArg (fun z : ℝ^2 ↦ z 0) hc0
  have hcj : r.repr v j = 0 := congrArg (fun z : ℝ^2 ↦ z 1) hc0
  exact hv (by simpa only [hci, hcj, zero_smul, zero_add] using hsplit)

/-- For one supplied autonomous orbit and fundamental solution, local determinant
and tangent-coordinate data give a compactly supported smooth GN-neutral tensor
with any prescribed integrated terminal projection.

The arc and scalar bump precede `target` in the quantifiers. The same explicit
formula is globally smooth because its closed support lies strictly inside the
arc. The GN condition uses the dual frame coordinate, not an inner product.
`W` need only be smooth on `J`. -/
theorem exists_integrated_bilinearCorrection_of_autonomous {f : (ℝ^3) → ℝ^3} {γ : ℝ → ℝ^3}
    {Ω : Set (ℝ^3)} {a b t₀ tStar : ℝ} (htStar : tStar ∈ Ioo a b) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hmem : MapsTo γ (Icc a b) Ω)
    (hode : ∀ t ∈ Icc a b, HasDerivAt γ (f (γ t)) t)
    (S : Evolution.FundamentalSolution (fun t ↦ fderiv ℝ f (γ t)) t₀ (Icc a b))
    (L : (ℝ^3) →L[ℝ] (ℝ^2))
    (hL : LinearMap.ker L.toLinearMap = Submodule.span ℝ ({f (γ b)} : Set (ℝ^3)))
    (r : ℝ → Module.Basis (Fin 3) ℝ (ℝ^3)) (W : ℝ → ℝ^3) {J : Set ℝ} (hJ : IsOpen J)
    (htJ : tStar ∈ J) (i j : Fin 3) (hij : i ≠ j) (hiSmooth : ContDiffOn ℝ ∞ (fun t ↦ r t i) J)
    (hjSmooth : ContDiffOn ℝ ∞ (fun t ↦ r t j) J) (hW : ContDiffOn ℝ ∞ W J)
    (hi : Matrix.det ![⇑(f (γ tStar)), ⇑(r tStar i), ⇑(W tStar)] ≠ 0)
    (hj : Matrix.det ![⇑(f (γ tStar)), ⇑(r tStar j), ⇑(W tStar)] ≠ 0)
    (hcoeff : ∀ k, k ≠ i → k ≠ j → (r tStar).repr (f (γ tStar)) k ≠ 0) :
    let v := fun t ↦ f (γ t)
    let π := fun t ↦ L.comp (S.propagator b t)
    ∃ l u : ℝ, ∃ χ : ℝ → ℝ,
      tStar ∈ Ioo l u ∧ Ioo l u ⊆ J ∩ Ioo a b ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo l u ∧
      (∀ t, 0 ≤ χ t) ∧ (∫ t, χ t) = 1 ∧
      (∀ t ∈ Ioo l u,
        Matrix.det ![⇑(v t), ⇑(r t i), ⇑(W t)] ≠ 0 ∧
        Matrix.det ![⇑(v t), ⇑(r t j), ⇑(W t)] ≠ 0 ∧
        ∀ k, k ≠ i → k ≠ j → (r t).repr (v t) k ≠ 0) ∧
      ∀ target : ℝ^2,
        let B := fun t ↦ bilinearCorrection (v t) (r t i) (r t j) (W t)
          (π t) (χ t • target)
        ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧ tsupport B ⊆ Ioo l u ∧
        (∀ t,
          (∀ x y, B t x y = B t y x) ∧
          (∀ y, B t (deriv γ t) y = 0) ∧
          (∀ m, (r t).repr (B t (r t m) (r t m)) m = 0) ∧
          L (S.propagator b t (B t (W t) (W t))) = χ t • target) ∧
        Integrable (fun t ↦ L (S.propagator b t (B t (W t) (W t)))) ∧
        (∫ t in a..b, L (S.propagator b t (B t (W t) (W t)))) = target := by
  classical
  intro v π
  obtain ⟨_, hvOn, hπOn, _, _, hsection⟩ :=
    Evolution.finite_section_projection_of_autonomous (htStar.1.trans htStar.2).le
      hΩ hf hmem hode S L hL
  have hker (t : ℝ) (ht : t ∈ Icc a b) :
      LinearMap.ker (π t).toLinearMap = Submodule.span ℝ ({v t} : Set (ℝ^3)) :=
    (hsection t ht).2.2.2.1
  have hvne (t : ℝ) (ht : t ∈ Icc a b) : v t ≠ 0 := (hsection t ht).2.2.2.2.1
  have hvAt : ContDiffAt ℝ ∞ v tStar := hvOn.contDiffAt (Icc_mem_nhds htStar.1 htStar.2)
  have hπAt : ContDiffAt ℝ ∞ π tStar := hπOn.contDiffAt (Icc_mem_nhds htStar.1 htStar.2)
  have hiAt := hiSmooth.contDiffAt (hJ.mem_nhds htJ)
  have hjAt := hjSmooth.contDiffAt (hJ.mem_nhds htJ)
  have hWAt := hW.contDiffAt (hJ.mem_nhds htJ)
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  let M := fun t ↦ projectedPair (π t (r t i)) (π t (r t j))
  have hMbase : (M tStar).IsInvertible := isInvertible_projectedPair (r tStar) (v tStar) (π tStar)
      (hker tStar ⟨htStar.1.le, htStar.2.le⟩) i j k hij hki hkj (hcoeff k hki hkj)
  have hMAt : ContDiffAt ℝ ∞ M tStar := by
    dsimp only [M, projectedPair]
    exact (contDiffAt_const.smulRight (hπAt.clm_apply hiAt)).add
      (contDiffAt_const.smulRight (hπAt.clm_apply hjAt))
  have hdet (w : ℝ → ℝ^3) (hw : ContinuousAt w tStar) :
      ContinuousAt (fun t ↦ Matrix.det ![⇑(v t), ⇑(w t), ⇑(W t)]) tStar := by fun_prop
  have hnear : ∀ᶠ t in 𝓝 tStar, t ∈ J ∩ Ioo a b ∧ Matrix.det ![⇑(v t), ⇑(r t i), ⇑(W t)] ≠ 0 ∧
      Matrix.det ![⇑(v t), ⇑(r t j), ⇑(W t)] ≠ 0 ∧ (M t).IsInvertible := by
    filter_upwards [(hJ.inter isOpen_Ioo).mem_nhds ⟨htJ, htStar⟩,
      (hdet (fun t ↦ r t i) hiAt.continuousAt).eventually_ne hi,
      (hdet (fun t ↦ r t j) hjAt.continuousAt).eventually_ne hj,
      hMAt.continuousAt.eventually hMbase.eventually_nhds] with t ht hdi hdj hMt
    exact ⟨ht, hdi, hdj, hMt⟩
  obtain ⟨l, u, htArc, hArc⟩ := hnear.exists_Ioo_subset
  have hArc_sub : Ioo l u ⊆ J ∩ Ioo a b := fun _ ht ↦ (hArc ht).1
  have hArcIcc : Ioo l u ⊆ Icc a b := fun _ ht ↦ ⟨(hArc_sub ht).2.1.le, (hArc_sub ht).2.2.le⟩
  have hArcRank (t : ℝ) (ht : t ∈ Ioo l u) : Matrix.det ![⇑(v t), ⇑(r t i), ⇑(W t)] ≠ 0 ∧
      Matrix.det ![⇑(v t), ⇑(r t j), ⇑(W t)] ≠ 0 ∧ ∀ m, m ≠ i → m ≠ j → (r t).repr (v t) m ≠ 0 :=
    ⟨(hArc ht).2.1, (hArc ht).2.2.1, fun m hmi hmj ↦ repr_ne_zero_of_isInvertible_projectedPair
      (r t) (v t) (π t) (hker t (hArcIcc ht)) (hvne t (hArcIcc ht)) i j m hij hmi hmj
      (hArc ht).2.2.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds htArc)
  let φ : ContDiffBump tStar :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by cas using hε
      rIn_lt_rOut := by cas using hε }
  let χ : ℝ → ℝ := φ.normed volume
  have hχsupport : tsupport χ ⊆ Ioo l u := (φ.tsupport_normed_eq (μ := volume)).trans_subset
    ((Metric.closedBall_subset_ball (by cas using hε)).trans hball)
  have hχsmooth : ContDiff ℝ ∞ χ := φ.contDiff_normed
  have hχcompact : HasCompactSupport χ := φ.hasCompactSupport_normed
  have hχone : (∫ t, χ t) = 1 := φ.integral_normed
  have hχinterval : (∫ t in a..b, χ t) = 1 :=
    (intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) fun t ht ↦
      Ioo_subset_Ioc_self (hArc_sub (hχsupport (subset_tsupport χ ht))).2).trans hχone
  refine ⟨l, u, χ, htArc, hArc_sub, hχsmooth, hχcompact, hχsupport,
    φ.nonneg_normed, hχone, hArcRank, fun target ↦ ?_⟩
  let B : ℝ → (ℝ^3) →L[ℝ] (ℝ^3) →L[ℝ] (ℝ^3) := fun t ↦
    bilinearCorrection (v t) (r t i) (r t j) (W t) (π t) (χ t • target)
  obtain ⟨hBOn, hBOnSpec⟩ := contDiffOn_bilinearCorrection_of_ker
    (s := Ioo l u) (n := ∞) r v W π (fun t ↦ χ t • target) i j k hij hki hkj
    (hiSmooth.mono (fun _ ht ↦ (hArc_sub ht).1)) (hjSmooth.mono (fun _ ht ↦ (hArc_sub ht).1))
    (hvOn.mono hArcIcc) (hW.mono (fun _ ht ↦ (hArc_sub ht).1))
    (hπOn.mono hArcIcc) (hχsmooth.contDiffOn.smul contDiffOn_const) (fun t ht ↦ hker t (hArcIcc ht))
    (fun t ht ↦ (hArcRank t ht).2.2 k hki hkj)
    (fun t ht ↦ (hArcRank t ht).1) (fun t ht ↦ (hArcRank t ht).2.1)
  change ContDiffOn ℝ ∞ B (Ioo l u) at hBOn
  have hBzero (t : ℝ) (hχ0 : χ t = 0) : B t = 0 := by
    ext x y
    simp [B, bilinearCorrection_apply, hχ0]
  have hBsupport : Function.support B ⊆ Function.support χ := fun t ht hχ0 ↦ ht (hBzero t hχ0)
  have hBtsupport : tsupport B ⊆ Ioo l u := (closure_mono hBsupport).trans hχsupport
  have hBcompact : HasCompactSupport B := hχcompact.mono hBsupport
  have hext : (Ioo l u).indicator B = B :=
    indicator_eq_self.mpr (hBsupport.trans ((subset_tsupport χ).trans hχsupport))
  have hBsmooth : ContDiff ℝ ∞ B := by
    simpa only [hext] using hBOn.indicator_of_tsupport_subset isOpen_Ioo
      (show tsupport ((Ioo l u).indicator B) ⊆ Ioo l u by simpa only [hext] using hBtsupport)
  have hBspec (t : ℝ) : (∀ x y, B t x y = B t y x) ∧ (∀ y, B t (deriv γ t) y = 0) ∧
      (∀ m, (r t).repr (B t (r t m) (r t m)) m = 0) ∧
      L (S.propagator b t (B t (W t) (W t))) = χ t • target := by
    by_cases ht : t ∈ Ioo l u
    · obtain ⟨hsym, htangent, hdiag, hproject⟩ := hBOnSpec t ht
      exact ⟨hsym, fun y ↦ (hode t (hArcIcc ht)).deriv ▸ htangent y, hdiag, hproject⟩
    · have hχ0 : χ t = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ ht (hχsupport h)
      simp [hBzero t hχ0, hχ0]
  have hprojected : (fun t ↦ L (S.propagator b t (B t (W t) (W t)))) = fun t ↦ χ t • target :=
    funext fun t ↦ (hBspec t).2.2.2
  refine ⟨hBsmooth, hBcompact, hBtsupport, hBspec,
    hprojected ▸ φ.integrable_normed.smul_const target, ?_⟩
  rw [hprojected, intervalIntegral.integral_smul_const, hχinterval, one_smul]

end PDE.Analysis.GNNeutralHessian
