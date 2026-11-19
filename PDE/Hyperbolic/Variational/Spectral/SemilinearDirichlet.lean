/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Maximal
public import PDE.Hyperbolic.Variational.Spectral.Dirichlet

/-!
# Maximal semilinear Dirichlet waves

On a nonempty bounded open domain, autonomous, essentially bounded, symmetric,
uniformly elliptic principal coefficients determine the homogeneous wave semigroup.
A locally Lipschitz map from `H¹₀ × L²` to `L²` then gives a maximal forward mild wave.
Every compact interval before its lifetime has a Bochner weak wave represented by
that trajectory, including both initial displacement and initial velocity.

The nonlinear forcing is extended continuously from each compact initial interval.
Finite lifetime forces norm blowup when the nonlinearity is Lipschitz on each bounded energy ball.

Two energy-continuous weak waves with the same initial data agree: the weak equations
identify each curve with its Duhamel representation, and mild uniqueness applies.
The conserved quadratic energy belongs to the homogeneous semigroup. No boundary
smoothness or spatial `H²` regularity is assumed.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology InnerProductSpace Interval BigOperators ENNReal

namespace SobolevSpace.GraphSpace

open Hyperbolic.Variational PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- The Dirichlet semigroup turns each continuous semilinear mild curve on a
positive finite interval into a Bochner weak wave. Any trajectory agreeing
with that curve on the interval represents the same load, displacement,
velocity, and acceleration classes. Continuity of the nonlinearity suffices
for this passage; both initial terms come from the linear forced-wave theorem.
The same semigroup retains its integrated displacement equation. -/
private theorem exists_dirichlet_waveSemigroup_mild_prefix (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let T := h10L2GelfandTriple hΩopen
    ∃ S : StronglyContinuousSemigroup (H¹₀(Ω) × L2),
      (∀ (t : NNReal) (x : H¹₀(Ω) × L2),
        autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t : NNReal, ‖S t‖ ≤ C) ∧
      (∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
        let u := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ ((0 : H¹₀(Ω)), f r)) s
        (∫ s in (0 : ℝ)..t, (u s).2) =
          baseCoordCLM (n := n) (Ω := Ω) (u t).1 - baseCoordCLM (n := n) (Ω := Ω) x.1) ∧
      ∀ (N : C(H¹₀(Ω) × L2, L2)) (x : H¹₀(Ω) × L2) (τ : NNReal), 0 < τ →
        ∀ (v : C(Icc (0 : ℝ) (τ : ℝ), H¹₀(Ω) × L2)),
          S.IsMildSolutionOn ((ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N) x τ v →
          ∀ (u : ℝ → H¹₀(Ω) × L2), EqOn (IccExtend τ.coe_nonneg v) u (Icc 0 (τ : ℝ)) →
            ∃ (ell : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
              (q : Lp H¹₀(Ω) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
              (p : Lp L2 2 (volume.restrict (Ioc 0 (τ : ℝ))))
              (acc : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))),
              (ell : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
                (fun t ↦ T.pivotToDual (N (u t))) ∧
              (q : ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] (fun t ↦ (u t).1) ∧
              (p : ℝ → L2) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] (fun t ↦ (u t).2) ∧
              (acc : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
                (fun t ↦ T.pivotToDual (N (u t)) - B (u t).1) ∧
              IsGelfandWeakWaveSolution T (fun _ ↦ B) ell q p acc x.1 x.2 := by
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  let T := h10L2GelfandTriple hΩopen
  obtain ⟨S, henergy, hbound, hkin, hforced⟩ :=
    exists_forced_dirichlet_weakWave hn hΩopen hΩbounded hΩne a ha hsymm
  refine ⟨S, henergy, hbound, hkin, fun N x τ hτpos v hv u heq ↦ ?_⟩
  let f : ℝ → L2 := fun t ↦ N (IccExtend τ.coe_nonneg v t)
  let w : ℝ → H¹₀(Ω) × L2 := fun t ↦ S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) t
  have hwuAE : w =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ((hv ⟨t, Ioc_subset_Icc_self ht⟩).symm.trans
      (IccExtend_of_mem τ.coe_nonneg v (Ioc_subset_Icc_self ht)).symm).trans
      (heq (Ioc_subset_Icc_self ht))
  have hfAE : f =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] (fun t ↦ N (u t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact congrArg N (heq (Ioc_subset_Icc_self ht))
  obtain ⟨ell, q, p, acc, hell, hq, hp, hacc, hweak⟩ :=
    hforced f (N.continuous.comp v.continuous.Icc_extend') x τ (NNReal.coe_pos.mpr hτpos)
  exact ⟨ell, q, p, acc, hell.trans (hfAE.fun_comp T.pivotToDual),
    hq.trans (hwuAE.fun_comp Prod.fst), hp.trans (hwuAE.fun_comp Prod.snd),
    hacc.trans (hfAE.comp₂ (fun (g : L2) (z : H¹₀(Ω) × L2) ↦ T.pivotToDual g - B z.1) hwuAE), hweak⟩

/-- A locally Lipschitz map from the energy space to `L²` gives a maximal
semilinear Dirichlet wave. Every compact initial interval before its lifetime
has Bochner displacement, velocity, load, and acceleration classes represented
by the constructed trajectory and its nonlinear dual residual. The chosen
semigroup also satisfies the integrated displacement equation for continuous
forcing, as needed to differentiate source potentials along these trajectories.

The nonlinearity is evaluated along a continuous extension of each compact
prefix. The final norm-blowup implication requires Lipschitz bounds on every bounded energy ball;
local Lipschitz continuity alone is not used to obtain those bounds. -/
theorem exists_maximal_semilinear_dirichlet_weakWave (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let T := h10L2GelfandTriple hΩopen
    ∃ S : StronglyContinuousSemigroup (H¹₀(Ω) × L2),
      (∀ (t : NNReal) (x : H¹₀(Ω) × L2),
        autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t : NNReal, ‖S t‖ ≤ C) ∧
      (∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
        let u := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ ((0 : H¹₀(Ω)), f r)) s
        (∫ s in (0 : ℝ)..t, (u s).2) =
          baseCoordCLM (n := n) (Ω := Ω) (u t).1 - baseCoordCLM (n := n) (Ω := Ω) x.1) ∧
      ∀ (N : C(H¹₀(Ω) × L2, L2)) (hN : LocallyLipschitz N) (x : H¹₀(Ω) × L2),
        let F := (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
        let hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hN
        let u := S.maximalMildSolution hF x
        0 < S.mildLifespan F x ∧ u 0 = x ∧
        ContinuousOn u {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < S.mildLifespan F x} ∧
        (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < S.mildLifespan F x →
          u t = S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), N (u s))) t) ∧
        (∀ τ : NNReal, 0 < τ → (τ : ℝ≥0∞) < S.mildLifespan F x →
          ∃ (ell : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
            (q : Lp H¹₀(Ω) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
            (p : Lp L2 2 (volume.restrict (Ioc 0 (τ : ℝ))))
            (acc : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))),
            (ell : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
              (fun t ↦ T.pivotToDual (N (u t))) ∧
            (q : ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] (fun t ↦ (u t).1) ∧
            (p : ℝ → L2) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] (fun t ↦ (u t).2) ∧
            (acc : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
              (fun t ↦ T.pivotToDual (N (u t)) - B (u t).1) ∧
            IsGelfandWeakWaveSolution T (fun _ ↦ B) ell q p acc x.1 x.2) ∧
        ((∀ R : ℝ, 0 < R →
            ∃ L : NNReal, LipschitzOnWith L N (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) →
          S.mildLifespan F x ≠ ∞ →
          ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧
            ∀ t ∈ Ico 0 (S.mildLifespan F x).toReal,
              (S.mildLifespan F x).toReal - t < ε → R < ‖u t‖) := by
  obtain ⟨S, henergy, hbound, hkin, hprefix⟩ :=
    exists_dirichlet_waveSemigroup_mild_prefix hn hΩopen hΩbounded hΩne a ha hsymm
  refine ⟨S, henergy, hbound, hkin, fun N hN x ↦ ?_⟩
  let F : C(H¹₀(Ω) × L2, H¹₀(Ω) × L2) := (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
  have hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hN
  refine ⟨S.mildLifespan_pos hF x, S.maximalMildSolution_zero hF x,
    S.continuousOn_maximalMildSolution hF x,
    fun t ht hlt ↦ S.maximalMildSolution_equation hF x ht hlt, fun τ hτpos hτlife ↦ ?_,
    fun hNballs hfinite ↦ ?_⟩
  · obtain ⟨v, hv, heq⟩ := S.exists_mildSolutionOn_eqOn_maximalMildSolution
      (E := H¹₀(Ω) × L2) (F := F) hF x (τ := τ) hτlife
    exact hprefix N x τ hτpos v hv _ heq
  refine S.maximalMildSolution_norm_eventually_gt_of_lifespan_ne_top (fun R hR ↦ ?_) x hfinite
  obtain ⟨L, hL⟩ := hNballs R hR
  refine ⟨L, ?_⟩
  change LipschitzOnWith L (fun z : H¹₀(Ω) × L2 ↦ ((0 : H¹₀(Ω)), N z))
    (Metric.closedBall (0 : H¹₀(Ω) × L2) R)
  simpa only [max_eq_right (show (0 : NNReal) ≤ L from bot_le)] using
    (LipschitzWith.const (0 : H¹₀(Ω))).lipschitzOnWith.prodMk hL

/-- Energy-continuous semilinear weak Dirichlet waves with the same initial
data agree throughout their common compact interval. Each curve is continuous
in `H¹₀ × L²` and represents the displacement and velocity Bochner classes;
its load represents the nonlinearity evaluated along that curve.

Continuous nonlinear forcing gives the linear weak-to-mild identification.
Continuity upgrades that almost-everywhere identity to every point, including
the endpoints. Locally Lipschitz mild uniqueness then applies.
No uniqueness assertion is made for arbitrary nonlinear Bochner trajectories
without energy-continuous representatives. -/
theorem eq_of_semilinear_dirichlet_weakWave_energyContinuous (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) {τ : NNReal} (hτ : 0 < τ)
    (N : C(H¹₀(Ω) × L2, L2)) (hN : LocallyLipschitz N) (x : H¹₀(Ω) × L2)
    (u v : C(Icc (0 : ℝ) (τ : ℝ), H¹₀(Ω) × L2)) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let T := h10L2GelfandTriple hΩopen
    (∃ (ell : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (q : Lp H¹₀(Ω) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (p : Lp L2 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (acc : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))),
      (ell : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ T.pivotToDual (N (IccExtend τ.coe_nonneg u t))) ∧
      (q : ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ (IccExtend τ.coe_nonneg u t).1) ∧
      (p : ℝ → L2) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] (fun t ↦ (IccExtend τ.coe_nonneg u t).2) ∧
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ell q p acc x.1 x.2) →
    (∃ (ell : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (q : Lp H¹₀(Ω) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (p : Lp L2 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (acc : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))),
      (ell : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ T.pivotToDual (N (IccExtend τ.coe_nonneg v t))) ∧
      (q : ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ (IccExtend τ.coe_nonneg v t).1) ∧
      (p : ℝ → L2) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] (fun t ↦ (IccExtend τ.coe_nonneg v t).2) ∧
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ell q p acc x.1 x.2) →
    u = v := by
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  let T := h10L2GelfandTriple hΩopen
  dsimp only
  rintro ⟨ellU, qU, pU, accU, hellU, hqU, hpU, hweakU⟩ ⟨ellV, qV, pV, accV, hellV, hqV, hpV, hweakV⟩
  obtain ⟨S, _, _, hidentify⟩ := exists_dirichlet_waveSemigroup_weak_identification
      hn hΩopen hΩbounded hΩne a ha hsymm
  let F : C(H¹₀(Ω) × L2, H¹₀(Ω) × L2) := (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
  have hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hN
  have htoMild (w : C(Icc (0 : ℝ) (τ : ℝ), H¹₀(Ω) × L2))
      (ell : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (q : Lp H¹₀(Ω) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (p : Lp L2 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (acc : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (hell : (ell : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ T.pivotToDual (N (IccExtend τ.coe_nonneg w t))))
      (hq : (q : ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ (IccExtend τ.coe_nonneg w t).1))
      (hp : (p : ℝ → L2) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ (IccExtend τ.coe_nonneg w t).2))
      (hweak : IsGelfandWeakWaveSolution T (fun _ ↦ B) ell q p acc x.1 x.2) :
      S.IsMildSolutionOn F x τ w := by
    let f : ℝ → L2 := fun t ↦ N (IccExtend τ.coe_nonneg w t)
    have hf : Continuous f := N.continuous.comp w.continuous.Icc_extend'
    obtain ⟨hqD, hpD, _⟩ := hidentify f hf x (τ : ℝ) (NNReal.coe_pos.mpr hτ) ell q p acc hell hweak
    have hwD : IccExtend τ.coe_nonneg w =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        fun t ↦ S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) t := by
      filter_upwards [hq, hp, hqD, hpD] with t hqt hpt hqDt hpDt
      exact Prod.ext (hqt.symm.trans hqDt) (hpt.symm.trans hpDt)
    have heq := Measure.eqOn_Icc_of_ae_eq volume (NNReal.coe_pos.mpr hτ).ne
      ((ae_restrict_congr_set Ioc_ae_eq_Icc).1 hwD) w.continuous.Icc_extend'.continuousOn
      (((S.continuous_orbit x).comp continuous_real_toNNReal).add
        (S.continuous_duhamel (continuous_const.prodMk hf))).continuousOn
    exact fun t ↦ (IccExtend_val τ.coe_nonneg w t).symm.trans (heq t.property)
  exact StronglyContinuousSemigroup.IsMildSolutionOn.eq_of_locallyLipschitz
    (E := H¹₀(Ω) × L2) (T := S) (F := F) (x₀ := x) (τ := τ) (u := u) (v := v) hF
    (htoMild u ellU qU pU accU hellU hqU hpU hweakU)
    (htoMild v ellV qV pV accV hellV hqV hpV hweakV)

end SobolevSpace.GraphSpace
