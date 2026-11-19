/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.Spectral.Semigroup
public import PDE.Analysis.Evolution.Semigroup.Semilinear.Basic

/-!
# Integrated equations for spectral wave trajectories

Energy-norm eigenfunction expansions identify continuous functionals by their
coordinates. Applied to spectral wave trajectories, this gives the two integrated
wave equations without differentiating the orbit in the energy norm.

For continuous forcing, the scalar mode calculation and the Duhamel integral give
the forced equations. The scalar calculation permits any real eigenvalue and time;
the semigroup applications use nonnegative time.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology InnerProductSpace Interval BigOperators ENNReal

namespace Hyperbolic.Variational

variable {V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A semigroup with the constructed spectral coordinates satisfies both
integrated wave equations for arbitrary energy data. The comparison with finite
spectral approximations avoids differentiating the orbit in the energy norm. -/
theorem waveSemigroup_integral_equations
    (B : V →L[ℝ] StrongDual ℝ V) (hsymm : ∀ v w, B v w = B w v)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (K : H →L[ℝ] StrongDual ℝ V) (hK : ∀ p w, K p w = ⟪p, J w⟫_ℝ)
    (basis : HilbertBasis ℕ ℝ H)
    (lambda : ℕ → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)
    (e : ℕ → V) (he : ∀ i, J (e i) = basis i)
    (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ)
    (S : PDE.Analysis.Evolution.StronglyContinuousSemigroup (V × H))
    (hcoordinate : ∀ t i x, waveCoordinate J basis i (S t x) =
      waveModeEvolution (lambda i) (t : ℝ) (waveCoordinate J basis i x))
    (x : V × H) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, (S s.toNNReal x).2) =
        J (S t.toNNReal x).1 - J x.1 ∧
      (∫ s in (0 : ℝ)..t, -(B (S s.toNNReal x).1)) =
        K (S t.toNNReal x).2 - K x.2 := by
  obtain ⟨u, _, hu, _, _, hq, hp⟩ :=
    exists_energy_wave_of_weakEigenbasis
      B hsymm hc hcoercive J hJ K hK basis lambda hlambda e he hweak x.1 x.2 ht
  have heq (s : ℝ) (hs : s ∈ Icc 0 t) : u s = S s.toNNReal x := by
    apply waveCoordinates_injective J hJ basis
    funext i
    change waveCoordinate J basis i (u s) = waveCoordinate J basis i (S s.toNNReal x)
    have hui := waveCoordinate_eq_of_tendsto_finiteSpectralWave
      J basis lambda e he
      (fun i ↦ (⟪basis i, J x.1⟫_ℝ, ⟪basis i, x.2⟫_ℝ))
      (hu.tendsto_at hs) i
    rw [hcoordinate]
    simpa only [waveCoordinate_apply, Real.coe_toNNReal _ hs.1] using hui
  constructor
  · calc
      (∫ s in (0 : ℝ)..t, (S s.toNNReal x).2) =
          ∫ s in (0 : ℝ)..t, (u s).2 := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact congrArg Prod.snd (heq s hs).symm
      _ = J (u t).1 - J x.1 := hq t ⟨ht, le_rfl⟩
      _ = J (S t.toNNReal x).1 - J x.1 := by rw [heq t ⟨ht, le_rfl⟩]
  · calc
      (∫ s in (0 : ℝ)..t, -(B (S s.toNNReal x).1)) =
          ∫ s in (0 : ℝ)..t, -(B (u s).1) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact congrArg (fun y : V × H ↦ -(B y.1)) (heq s hs).symm
      _ = K (u t).2 - K x.2 := hp t ⟨ht, le_rfl⟩
      _ = K (S t.toNNReal x).2 - K x.2 := by rw [heq t ⟨ht, le_rfl⟩]

omit [CompleteSpace V] in
/-- The two time-integrated wave equations are equivalent to their scalar
eigenmode equations. The forcing is continuous with values in the pivot space. -/
theorem wave_integral_equations_iff_coordinates
    (B : V →L[ℝ] StrongDual ℝ V) (hsymm : ∀ v w, B v w = B w v)
    (J : V →L[ℝ] H)
    (K : H →L[ℝ] StrongDual ℝ V) (hK : ∀ p w, K p w = ⟪p, J w⟫_ℝ)
    (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ) (e : ℕ → V)
    (he : ∀ i, J (e i) = basis i)
    (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ)
    (hexpansion : ∀ v : V, HasSum (fun i ↦ ⟪basis i, J v⟫_ℝ • e i) v)
    {u : ℝ → V × H} (hu : Continuous u)
    {f : ℝ → H} (hf : Continuous f) (x : V × H) (t : ℝ) :
    ((∫ s in (0 : ℝ)..t, (u s).2) = J (u t).1 - J x.1 ∧
      (∫ s in (0 : ℝ)..t, K (f s) - B (u s).1) = K (u t).2 - K x.2) ↔
    ∀ i,
      (∫ s in (0 : ℝ)..t, ⟪basis i, (u s).2⟫_ℝ) =
        ⟪basis i, J (u t).1⟫_ℝ - ⟪basis i, J x.1⟫_ℝ ∧
      (∫ s in (0 : ℝ)..t,
          ⟪basis i, f s⟫_ℝ - lambda i * ⟪basis i, J (u s).1⟫_ℝ) =
        ⟪basis i, (u t).2⟫_ℝ - ⟪basis i, x.2⟫_ℝ := by
  have hp := hu.snd.intervalIntegrable (μ := volume) 0 t
  have hr : IntervalIntegrable (fun s ↦ K (f s) - B (u s).1) volume 0 t :=
    ((K.continuous.comp hf).sub
      (B.continuous.comp hu.fst)).intervalIntegrable (μ := volume) 0 t
  have htest (s : ℝ) (i : ℕ) :
      (K (f s) - B (u s).1) (e i) =
        ⟪basis i, f s⟫_ℝ - lambda i * ⟪basis i, J (u s).1⟫_ℝ := by
    rw [sub_apply, hK, he, hsymm, hweak, real_inner_comm]
  have hqintegral (i : ℕ) :
      ⟪basis i, (∫ s in (0 : ℝ)..t, (u s).2)⟫_ℝ =
        ∫ s in (0 : ℝ)..t, ⟪basis i, (u s).2⟫_ℝ :=
    ((innerSL ℝ (basis i)).intervalIntegral_comp_comm hp).symm
  have hpintegral (i : ℕ) :
      (∫ s in (0 : ℝ)..t, K (f s) - B (u s).1) (e i) =
        ∫ s in (0 : ℝ)..t,
          ⟪basis i, f s⟫_ℝ - lambda i * ⟪basis i, J (u s).1⟫_ℝ := by
    rw [ContinuousLinearMap.intervalIntegral_apply hr]
    exact intervalIntegral.integral_congr fun s _ ↦ htest s i
  have hright (i : ℕ) :
      (K (u t).2 - K x.2) (e i) =
        ⟪basis i, (u t).2⟫_ℝ - ⟪basis i, x.2⟫_ℝ := by
    simp only [sub_apply, hK, he]
    rw [real_inner_comm (u t).2, real_inner_comm x.2]
  constructor
  · rintro ⟨hq, hv⟩ i
    constructor
    · rw [← hqintegral, hq, inner_sub_right]
    · rw [← hpintegral, hv, hright]
  · intro h
    constructor
    · apply basis.repr.injective
      apply lp.ext
      funext i
      simpa only [basis.repr_apply_apply, inner_sub_right, hqintegral] using (h i).1
    · apply PDE.Analysis.Variational.eq_of_apply_weakEigenfunctions_eq
        J basis e hexpansion
      intro i
      rw [hpintegral, hright]
      exact (h i).2

/-- Every spectral coordinate of the forced mild curve is the scalar
variation-of-constants formula. The force enters only the velocity component. -/
theorem waveCoordinate_forced_mild
    (J : V →L[ℝ] H) (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ)
    (S : PDE.Analysis.Evolution.StronglyContinuousSemigroup (V × H))
    (hcoordinate : ∀ t i x, waveCoordinate J basis i (S t x) =
      waveModeEvolution (lambda i) (t : ℝ) (waveCoordinate J basis i x))
    {f : ℝ → H} (hf : Continuous f) (x : V × H) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) :
    waveCoordinate J basis i
        (S t.toNNReal x + S.duhamel (fun s ↦ (0, f s)) t) =
      waveModeEvolution (lambda i) t (waveCoordinate J basis i x) +
        ∫ s in (0 : ℝ)..t,
          waveModeEvolution (lambda i) (t - s) (0, ⟪basis i, f s⟫_ℝ) := by
  have hforce : Continuous (fun s ↦ ((0 : V), f s)) := continuous_const.prodMk hf
  have hint :=
    (S.continuous_duhamelIntegrand hforce t).intervalIntegrable (μ := volume) 0 t
  rw [map_add, hcoordinate, Real.coe_toNNReal _ ht]
  congr 1
  unfold PDE.Analysis.Evolution.StronglyContinuousSemigroup.duhamel
  rw [← (waveCoordinate J basis i).intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  change waveCoordinate J basis i (S (t - s).toNNReal (0, f s)) =
    waveModeEvolution (lambda i) (t - s) (0, ⟪basis i, f s⟫_ℝ)
  rw [hcoordinate, Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
  simp only [waveCoordinate_apply, map_zero, inner_zero_right]

/-- The scalar wave variation-of-constants formula satisfies the integrated
first-order system. An integrating factor differentiates the primitive, so no
derivative of the forcing is needed. -/
theorem waveMode_forced_integral_equation
    (lambda : ℝ) {g : ℝ → ℝ × ℝ} (hg : Continuous g) (x : ℝ × ℝ) (t : ℝ) :
    let z := fun r ↦ waveModeEvolution lambda r x +
      ∫ s in (0 : ℝ)..r, waveModeEvolution lambda (r - s) (g s)
    Continuous z ∧
      (∫ s in (0 : ℝ)..t, waveModeGenerator lambda (z s) + g s) = z t - x := by
  let W := waveModeEvolution lambda
  let z := fun r ↦ W r x + ∫ s in (0 : ℝ)..r, W (r - s) (g s)
  change Continuous z ∧
    (∫ s in (0 : ℝ)..t, waveModeGenerator lambda (z s) + g s) = z t - x
  let k := fun s ↦ W (-s) (g s)
  have hk : Continuous k := by
    have hW : Continuous (fun s : ℝ ↦ W (-s)) :=
      (differentiable_exp_smul_const ℝ
        (waveModeGenerator lambda)).continuous.comp continuous_neg
    have h := hW.clm_apply hg
    have hfst := (ContinuousLinearMap.fst ℝ ℝ ℝ).continuous.comp h
    have hsnd := (ContinuousLinearMap.snd ℝ ℝ ℝ).continuous.comp h
    exact hfst.prodMk hsnd
  have hrepr (r : ℝ) :
      z r = W r (x + ∫ s in (0 : ℝ)..r, k s) := by
    change W r x + (∫ s in (0 : ℝ)..r, W (r - s) (g s)) =
      W r (x + ∫ s in (0 : ℝ)..r, k s)
    rw [map_add,
      ← (W r).intervalIntegral_comp_comm (hk.intervalIntegrable (μ := volume) 0 r)]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    change W (r - s) (g s) = W r (W (-s) (g s))
    simpa only [W, sub_eq_add_neg, ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun (waveModeEvolution_add lambda r (-s)) (g s)
  have hinverse (r : ℝ) (y : ℝ × ℝ) : W r (W (-r) y) = y := by
    have h := DFunLike.congr_fun (waveModeEvolution_add lambda r (-r)) y
    simpa only [W, add_neg_cancel, waveModeEvolution_zero,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] using h.symm
  have hzderiv (r : ℝ) :
      HasDerivAt z (waveModeGenerator lambda (z r) + g r) r := by
    have hprimitive := (intervalIntegral.integral_hasDerivAt_right
      (hk.intervalIntegrable (μ := volume) 0 r)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter
      hk.continuousAt).const_add x
    have hproduct :=
      (hasDerivAt_exp_smul_const' (waveModeGenerator lambda) r).clm_apply hprimitive
    change HasDerivAt (fun s ↦ W s (x + ∫ q in (0 : ℝ)..s, k q))
      (waveModeGenerator lambda (W r (x + ∫ q in (0 : ℝ)..r, k q)) +
        W r (k r)) r at hproduct
    have hcancel : W r (k r) = g r := hinverse r (g r)
    rw [← hrepr r, hcancel] at hproduct
    exact hproduct.congr_of_eventuallyEq (Eventually.of_forall hrepr)
  have hz : Continuous z :=
    continuous_iff_continuousAt.mpr fun r ↦ (hzderiv r).continuousAt
  refine ⟨hz, ?_⟩
  have hzero : z 0 = x := by
    simp only [z, W, waveModeEvolution_zero, ContinuousLinearMap.id_apply,
      intervalIntegral.integral_same, add_zero]
  simpa only [hzero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hzderiv s)
    ((((waveModeGenerator lambda).continuous.comp hz).add hg).intervalIntegrable
      (μ := volume) 0 t)

/-- Continuous pivot forcing produces a mild curve satisfying the two
time-integrated weak wave equations. Spectral testing passes from each forced mode to the full
energy dual. -/
theorem forced_waveSemigroup_integral_equations
    (B : V →L[ℝ] StrongDual ℝ V) (hsymm : ∀ v w, B v w = B w v)
    (J : V →L[ℝ] H)
    (K : H →L[ℝ] StrongDual ℝ V) (hK : ∀ p w, K p w = ⟪p, J w⟫_ℝ)
    (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ) (e : ℕ → V)
    (he : ∀ i, J (e i) = basis i)
    (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ)
    (hexpansion : ∀ v : V, HasSum (fun i ↦ ⟪basis i, J v⟫_ℝ • e i) v)
    (S : PDE.Analysis.Evolution.StronglyContinuousSemigroup (V × H))
    (hcoordinate : ∀ t i x, waveCoordinate J basis i (S t x) =
      waveModeEvolution (lambda i) (t : ℝ) (waveCoordinate J basis i x))
    {f : ℝ → H} (hf : Continuous f) (x : V × H) {t : ℝ} (ht : 0 ≤ t) :
    let u := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ (0, f r)) s
    (∫ s in (0 : ℝ)..t, (u s).2) = J (u t).1 - J x.1 ∧
      (∫ s in (0 : ℝ)..t, K (f s) - B (u s).1) = K (u t).2 - K x.2 := by
  let u := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ ((0 : V), f r)) s
  change (∫ s in (0 : ℝ)..t, (u s).2) = J (u t).1 - J x.1 ∧
    (∫ s in (0 : ℝ)..t, K (f s) - B (u s).1) = K (u t).2 - K x.2
  have hu : Continuous u :=
    ((S.continuous_orbit x).comp continuous_real_toNNReal).add
      (S.continuous_duhamel (continuous_const.prodMk hf))
  apply (wave_integral_equations_iff_coordinates
    B hsymm J K hK basis lambda e he hweak hexpansion hu hf x t).mpr
  intro i
  let g := fun s ↦ ((0 : ℝ), ⟪basis i, f s⟫_ℝ)
  have hg : Continuous g := continuous_const.prodMk ((innerSL ℝ (basis i)).continuous.comp hf)
  let z := fun r ↦ waveModeEvolution (lambda i) r (waveCoordinate J basis i x) +
    ∫ s in (0 : ℝ)..r, waveModeEvolution (lambda i) (r - s) (g s)
  have hmode := waveMode_forced_integral_equation
    (lambda i) hg (waveCoordinate J basis i x) t
  change Continuous z ∧
    (∫ s in (0 : ℝ)..t, waveModeGenerator (lambda i) (z s) + g s) =
      z t - waveCoordinate J basis i x at hmode
  have hpoint (s : ℝ) (hs : 0 ≤ s) : waveCoordinate J basis i (u s) = z s :=
    waveCoordinate_forced_mild J basis lambda S hcoordinate hf x hs i
  have hcomponents (s : ℝ) (hs : 0 ≤ s) :
      ⟪basis i, J (u s).1⟫_ℝ = (z s).1 ∧
        ⟪basis i, (u s).2⟫_ℝ = (z s).2 := by
    exact ⟨congrArg Prod.fst (hpoint s hs), congrArg Prod.snd (hpoint s hs)⟩
  have hint : IntervalIntegrable
      (fun s ↦ waveModeGenerator (lambda i) (z s) + g s) volume 0 t :=
    (((waveModeGenerator (lambda i)).continuous.comp hmode.1).add
      hg).intervalIntegrable (μ := volume) 0 t
  have hfirst := congrArg (ContinuousLinearMap.fst ℝ ℝ ℝ) hmode.2
  have hsecond := congrArg (ContinuousLinearMap.snd ℝ ℝ ℝ) hmode.2
  rw [← (ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hint] at hfirst
  rw [← (ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hint] at hsecond
  simp only [ContinuousLinearMap.coe_fst', waveModeGenerator_apply, Prod.fst_add,
    Prod.fst_sub, g, add_zero, waveCoordinate_apply] at hfirst
  simp only [ContinuousLinearMap.coe_snd', waveModeGenerator_apply, Prod.snd_add,
    Prod.snd_sub, g, waveCoordinate_apply] at hsecond
  constructor
  · rw [(hcomponents t ht).1]
    rw [← hfirst]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact (hcomponents s hs.1).2
  · rw [(hcomponents t ht).2]
    rw [← hsecond]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    change ⟪basis i, f s⟫_ℝ - lambda i * ⟪basis i, J (u s).1⟫_ℝ =
      -lambda i * (z s).1 + ⟪basis i, f s⟫_ℝ
    rw [(hcomponents s hs.1).1]
    simp only [sub_eq_add_neg, neg_mul, add_comm]

end Hyperbolic.Variational
