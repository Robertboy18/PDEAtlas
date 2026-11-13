/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.SignedPower
public import PDE.Hyperbolic.Variational.Spectral.SemilinearDirichlet
public import PDE.Hyperbolic.Variational.DefocusingPowerEnergy
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.ZeroTrace

/-!
# Dirichlet waves with an odd-power source

On a measurable domain of finite measure, the zero-trace Sobolev embedding and
Hölder's inequality construct the source `|u|^(r-1) u` as a locally Lipschitz
map from `H¹₀ × L²` to `L²`, with bounds on every bounded energy ball.
The range is `1 ≤ r ≤ n/(n-2)` in dimensions above two and every finite `r ≥ 1`
in dimensions one and two.

For a nonempty bounded open domain, autonomous, essentially bounded real principal
coefficients that are almost everywhere symmetric and uniformly elliptic give a
maximal semilinear Dirichlet wave. Its continuous energy trajectory represents a
Bochner weak wave on every compact initial interval before the maximal lifetime.
If that lifetime is finite, the energy-space norm tends to infinity.

The source construction needs only finite domain measure. Boundedness is kept
in the wave theorem for its spectral construction. No boundary smoothness or
spatial `H²` regularity is assumed. Along the nonlinear trajectory, half the
quadratic energy minus the power potential is constant. This focusing energy
need not bound the energy-space norm, so conservation does not give global existence
for the focusing source. For the negative source, the positive total energy controls
both components; the final theorem proves global existence for every energy initial state.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology InnerProductSpace Interval BigOperators ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- On a measurable domain of finite measure, the scalar power source is locally
Lipschitz from the Dirichlet energy space to `L²`, with a Lipschitz bound on
every bounded energy ball.

For `n ≥ 3`, the supported range is `1 ≤ r ≤ n/(n-2)`, including the
endpoint. For `n = 1, 2`, every finite real `r ≥ 1` is supported. The
embedding is derived from zero extension and the canonical Sobolev theory;
no smoothness of the boundary is required. The source depends only on
the displacement, and its representative is `|u|^(r-1) u`. -/
theorem exists_powerSource (hn : 0 < n) (hΩ : MeasurableSet Ω) [IsFiniteMeasure (domainMeasure n Ω)]
    {r : ℝ} (hr : 1 ≤ r) (hrange : 2 < n → r ≤ (n : ℝ) / ((n : ℝ) - 2)) :
    ∃ N : C(H¹₀(Ω) × L2, L2),
      (∀ z : H¹₀(Ω) × L2, (N z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun y ↦ Real.signedPower r (baseCoordCLM z.1 y)) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ L : NNReal, LipschitzOnWith L N (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) ∧
      LocallyLipschitz N := by
  have hq : 2 ≤ 2 * r := by linarith
  have hnq : 2 < n → 2 * r ≤ 2 * (n : ℝ) / ((n : ℝ) - 2) := fun hn2 ↦ by
    rw [mul_div_assoc]
    linarith [hrange hn2]
  have : Fact (1 ≤ ENNReal.ofReal (2 * r)) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let K : (H¹₀(Ω) × L2) →L[ℝ] DerivLp n (ENNReal.ofReal (2 * r)) Ω :=
    (h10LpEmbedding hn hΩ hq hnq).comp (ContinuousLinearMap.fst ℝ H¹₀(Ω) L2)
  let N : H¹₀(Ω) × L2 → L2 := fun z ↦ Lp.signedPower hr (K z)
  have hNae (z : H¹₀(Ω) × L2) : (N z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun y ↦ Real.signedPower r (baseCoordCLM z.1 y) := by
    filter_upwards [Lp.coeFn_signedPower hr (K z), h10LpEmbedding_ae hn hΩ hq hnq z.1] with y hN hJ
    exact hN.trans (congrArg (Real.signedPower r) hJ)
  have hballs : ∀ R : ℝ, 0 ≤ R →
      ∃ L : NNReal, LipschitzOnWith L N (Metric.closedBall (0 : H¹₀(Ω) × L2) R) := by
    intro R hR
    rcases eq_or_lt_of_le hr with hr1 | hr1
    · let K2 : (H¹₀(Ω) × L2) →L[ℝ] L2 :=
        (baseCoordCLM (n := n) (Ω := Ω)).comp (ContinuousLinearMap.fst ℝ H¹₀(Ω) L2)
      have hNK2 : N = K2 := funext fun z ↦ Lp.ext <| by
        change (N z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM z.1 : ℝ^n → ℝ)
        simpa only [← hr1, Real.signedPower_one] using hNae z
      exact ⟨‖K2‖₊, hNK2 ▸ K2.lipschitzWith.lipschitzOnWith⟩
    let C : ℝ := (2 * r) * (2 * (‖K‖ * R)) ^ (r - 1) * ‖K‖
    have hC : 0 ≤ C :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)) (norm_nonneg _)
    refine ⟨⟨C, hC⟩, LipschitzOnWith.of_dist_le_mul fun z hz w hw ↦ ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hz hw
    simp only [dist_eq_norm]
    have hzK : ‖K z‖ ≤ ‖K‖ * R := (K.le_opNorm z).trans (by gcongr)
    have hwK : ‖K w‖ ≤ ‖K‖ * R := (K.le_opNorm w).trans (by gcongr)
    calc
      ‖N z - N w‖ ≤ (2 * r) * (‖K z‖ + ‖K w‖) ^ (r - 1) * ‖K z - K w‖ :=
        Lp.norm_signedPower_sub_le hr1 (K z) (K w)
      _ ≤ (2 * r) * (2 * (‖K‖ * R)) ^ (r - 1) * (‖K‖ * ‖z - w‖) := by
        rw [← map_sub]
        gcongr
        · linarith
        · exact K.le_opNorm _
      _ = C * ‖z - w‖ := by ring
  have hlocal : LocallyLipschitz N := fun z ↦ by
    obtain ⟨L, hL⟩ := hballs (‖z‖ + 1) (by positivity)
    exact ⟨L, _, Metric.closedBall_mem_nhds_of_mem (mem_ball_zero_iff.2 (lt_add_one _)), hL⟩
  exact ⟨⟨N, hlocal.continuous⟩, hNae, hballs, hlocal⟩

end SobolevSpace.GraphSpace

namespace SobolevSpace.GraphSpace

open Hyperbolic.Variational PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- Almost-everywhere symmetry of the coefficients and the integrated displacement
equation give conservation of the power energy along this semigroup's Picard trajectory. -/
private theorem powerWave_conservation (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (S : StronglyContinuousSemigroup (H¹₀(Ω) × L2))
    (henergy : ∀ t x, autonomousWaveEnergy (variableCoeffForm (multiplicationCoefficientOperator a))
      (S t x) = autonomousWaveEnergy (variableCoeffForm (multiplicationCoefficientOperator a)) x)
    (hkin : ∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) s;
      (∫ s in (0 : ℝ)..t, (z s).2) = baseCoordCLM (n := n) (Ω := Ω) (z t).1 - baseCoordCLM x.1)
    {r : ℝ} (hr : 1 ≤ r) (N : C(H¹₀(Ω) × L2, L2)) (hN : LocallyLipschitz N)
    (hNae : ∀ z : H¹₀(Ω) × L2, (N z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun y ↦
      Real.signedPower r (baseCoordCLM z.1 y))
    (x : H¹₀(Ω) × L2) {t : ℝ} (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t <
      S.mildLifespan ((ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N) x) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let F := (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
    let hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hN
    let u := S.maximalMildSolution hF x
    (1 / 2 : ℝ) * autonomousWaveEnergy B (u t) -
        (∫ y, |baseCoordCLM (u t).1 y| ^ (r + 1) ∂domainMeasure n Ω) / (r + 1) =
      (1 / 2 : ℝ) * autonomousWaveEnergy B x -
        (∫ y, |baseCoordCLM x.1 y| ^ (r + 1) ∂domainMeasure n Ω) / (r + 1) := by
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω)
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  have hBsymm (v w : H¹₀(Ω)) : B v w = B w v :=
    variableCoeffForm_symm (symmetricCoefficientOperator_multiplication_of_ae a hsymm) v w
  exact power_energy_maximalMildSolution (V := H¹₀(Ω)) (μ := domainMeasure n Ω) S B hBsymm henergy
    (baseCoordCLM (n := n) (Ω := Ω)) hkin hr N hN hNae x ht hlt

/-- A locally Lipschitz realization of the power source gives maximal weak waves
with conserved nonlinear energy. Bounds on each energy ball give the finite-lifetime
norm blowup alternative. All conclusions use the same Dirichlet semigroup. -/
private theorem exists_powerWave_of_source (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) {r : ℝ} (hr : 1 ≤ r)
    (N : C(H¹₀(Ω) × L2, L2)) (hN : LocallyLipschitz N)
    (hNae : ∀ z : H¹₀(Ω) × L2, (N z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun y ↦
      Real.signedPower r (baseCoordCLM z.1 y))
    (hNballs : ∀ R : ℝ, 0 ≤ R → ∃ L : NNReal,
      LipschitzOnWith L N (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let T := h10L2GelfandTriple hΩopen
    ∃ S : StronglyContinuousSemigroup (H¹₀(Ω) × L2),
      (∀ (t : NNReal) (z : H¹₀(Ω) × L2),
        autonomousWaveEnergy B (S t z) = autonomousWaveEnergy B z) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t : NNReal, ‖S t‖ ≤ C) ∧
      ∀ x : H¹₀(Ω) × L2,
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
        (S.mildLifespan F x ≠ ∞ →
          ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧
            ∀ t ∈ Ico 0 (S.mildLifespan F x).toReal,
              (S.mildLifespan F x).toReal - t < ε → R < ‖u t‖) ∧
        (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < S.mildLifespan F x →
          (1 / 2 : ℝ) * autonomousWaveEnergy B (u t) -
              (∫ y, |baseCoordCLM (u t).1 y| ^ (r + 1) ∂domainMeasure n Ω) / (r + 1) =
            (1 / 2 : ℝ) * autonomousWaveEnergy B x -
              (∫ y, |baseCoordCLM x.1 y| ^ (r + 1) ∂domainMeasure n Ω) / (r + 1)) := by
  obtain ⟨S, hS⟩ := exists_maximal_semilinear_dirichlet_weakWave (n := n) (Ω := Ω)
    hn hΩopen hΩbounded hΩne a ha hsymm
  refine ⟨S, hS.1, hS.2.1, fun x ↦ ?_⟩
  -- Project the weak-wave clauses without constructing nested elimination motives.
  have h := hS.2.2.2 N hN x
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2 fun R hR ↦ hNballs R hR.le,
    fun t ht hlt ↦ powerWave_conservation a hsymm S hS.1 hS.2.2.1 hr N hN hNae x ht hlt⟩

/-- Maximal Dirichlet waves with the concrete scalar source
`|u|^(r-1) u`, in the energy-to-`L²` Sobolev range.

The domain is any nonempty bounded open subset of `ℝⁿ`, `n ≥ 1`.
The principal coefficients are bounded, symmetric, and uniformly elliptic.
For `n ≥ 3` the range is `1 ≤ r ≤ n/(n-2)`; in dimensions one and two
every finite real `r ≥ 1` is allowed. No boundary regularity or assumed
Sobolev estimate is part of the statement.

Every compact preterminal interval has a Bochner weak wave represented
by the constructed energy trajectory. Finite lifetime forces its energy
norm to tend to infinity. This is the maximal lifetime in the continuous
energy mild class. The earlier weak-wave uniqueness theorem applies to
energy-continuous representatives with this nonlinear load, rather than
to arbitrary Bochner trajectories.

The same constructed trajectory conserves
`(B(u,u) + ‖u_t‖²)/2 - ∫ |u|^(r+1)/(r+1)` before its lifetime. The semigroup's integrated
displacement equation supplies the kinematics needed for the potential chain rule. -/
theorem exists_maximal_power_dirichlet_weakWave (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) {r : ℝ} (hr : 1 ≤ r)
    (hrange : 2 < n → r ≤ (n : ℝ) / ((n : ℝ) - 2)) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let T := h10L2GelfandTriple hΩopen
    ∃ (S : StronglyContinuousSemigroup (H¹₀(Ω) × L2))
      (N : C(H¹₀(Ω) × L2, L2)) (hN : LocallyLipschitz N),
      (∀ z : H¹₀(Ω) × L2, (N z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun y ↦ Real.signedPower r (baseCoordCLM z.1 y)) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ L : NNReal, LipschitzOnWith L N (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) ∧
      (∀ (t : NNReal) (z : H¹₀(Ω) × L2),
        autonomousWaveEnergy B (S t z) = autonomousWaveEnergy B z) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t : NNReal, ‖S t‖ ≤ C) ∧
      ∀ x : H¹₀(Ω) × L2,
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
        (S.mildLifespan F x ≠ ∞ →
          ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧
            ∀ t ∈ Ico 0 (S.mildLifespan F x).toReal,
              (S.mildLifespan F x).toReal - t < ε → R < ‖u t‖) ∧
        (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < S.mildLifespan F x →
          (1 / 2 : ℝ) * autonomousWaveEnergy B (u t) -
              (∫ y, |baseCoordCLM (u t).1 y| ^ (r + 1) ∂domainMeasure n Ω) / (r + 1) =
            (1 / 2 : ℝ) * autonomousWaveEnergy B x -
              (∫ y, |baseCoordCLM x.1 y| ^ (r + 1) ∂domainMeasure n Ω) / (r + 1)) := by
  have : IsFiniteMeasure (domainMeasure n Ω) := isFiniteMeasure_domainMeasure_of_isBounded hΩbounded
  obtain ⟨N, hNae, hNballs, hN⟩ := exists_powerSource hn hΩopen.measurableSet hr hrange
  obtain ⟨S, hS⟩ := exists_powerWave_of_source (n := n) (Ω := Ω)
    hn hΩopen hΩbounded hΩne a ha hsymm hr N hN hNae hNballs
  exact ⟨S, N, hN, hNae, hNballs, hS⟩

section Defocusing

/-- The Sobolev power source and its negative have the same bounds on energy balls.
Their scalar potential is integrable because the displacement and source both lie in `L²`. -/
private theorem exists_signed_powerSource (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {r : ℝ} (hr : 1 ≤ r)
    (hrange : 2 < n → r ≤ (n : ℝ) / ((n : ℝ) - 2)) :
    ∃ P : C(H¹₀(Ω) × L2, L2), LocallyLipschitz P ∧
      (∀ z : H¹₀(Ω) × L2, (P z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun y ↦ Real.signedPower r (baseCoordCLM z.1 y)) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ L : NNReal, LipschitzOnWith L P (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) ∧
      (∀ z : H¹₀(Ω) × L2, ((-P) z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun y ↦ -Real.signedPower r (baseCoordCLM z.1 y)) ∧
      (∀ v : H¹₀(Ω), Integrable (fun y ↦ |baseCoordCLM v y| ^ (r + 1)) (domainMeasure n Ω)) ∧
      (∀ R : ℝ, 0 ≤ R →
        ∃ L : NNReal, LipschitzOnWith L (-P) (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) := by
  obtain ⟨P, hPae, hPballs, hP⟩ := exists_powerSource (n := n) (Ω := Ω) hn hΩ hr hrange
  refine ⟨P, hP, hPae, hPballs, fun z ↦ ?_, fun v ↦
    PDE.Analysis.Calculus.integrable_abs_rpow_of_L2_signedPower hr (baseCoordCLM v) (P (v, 0))
      (hPae (v, 0)), fun R hR ↦ (hPballs R hR).imp fun _ hL ↦ hL.neg⟩
  filter_upwards [Lp.coeFn_neg (P z), hPae z] with y hneg hpower
  exact hneg.trans (congrArg Neg.neg hpower)

/-- For a fixed Dirichlet semigroup and power source, the positive conserved energy
bounds both components of the trajectory and rules out a finite forward lifetime. -/
private theorem defocusingPowerWave_global (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (S : StronglyContinuousSemigroup (H¹₀(Ω) × L2))
    (henergy : ∀ t x, autonomousWaveEnergy (variableCoeffForm (multiplicationCoefficientOperator a))
      (S t x) = autonomousWaveEnergy (variableCoeffForm (multiplicationCoefficientOperator a)) x)
    (hkin : ∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) s;
      (∫ s in (0 : ℝ)..t, (z s).2) = baseCoordCLM (n := n) (Ω := Ω) (z t).1 - baseCoordCLM x.1)
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v : H¹₀(Ω), c * ‖v‖ ^ 2 ≤
      variableCoeffForm (multiplicationCoefficientOperator a) v v)
    {r : ℝ} (hr : 1 ≤ r) (P : C(H¹₀(Ω) × L2, L2))
    (hPae : ∀ z : H¹₀(Ω) × L2, (P z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun y ↦
      Real.signedPower r (baseCoordCLM z.1 y))
    (hPballs : ∀ R : ℝ, 0 ≤ R → ∃ L : NNReal,
      LipschitzOnWith L P (Metric.closedBall (0 : H¹₀(Ω) × L2) R))
    (x : H¹₀(Ω) × L2) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let E := defocusingPowerEnergy B (baseCoordCLM (n := n) (Ω := Ω)) r
    let N : C(H¹₀(Ω) × L2, L2) := -P
    let F := (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
    let u := S.maximalMildSolution
      (locallyLipschitz_defocusingWaveSource P (fun R hR ↦ hPballs R hR.le)) x
    S.mildLifespan F x = ∞ ∧
      ∀ t : ℝ, 0 ≤ t → E (u t) = E x ∧ c * ‖(u t).1‖ ^ 2 + ‖(u t).2‖ ^ 2 ≤ 2 * E x ∧
        ‖u t‖ ≤ Real.sqrt (2 * E x / min c 1) := by
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω)
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  have hBsymm (v w : H¹₀(Ω)) : B v w = B w v :=
    variableCoeffForm_symm (symmetricCoefficientOperator_multiplication_of_ae a hsymm) v w
  exact defocusing_power_global (V := H¹₀(Ω)) (μ := domainMeasure n Ω)
    S B hBsymm henergy (baseCoordCLM (n := n) (Ω := Ω)) hkin hc hcoercive hr P hPae
    (fun R hR ↦ hPballs R hR.le) x

/-- The displacement, velocity and acceleration of a weak wave on a finite initial interval. -/
private def powerWaveWeakPrefix (hΩopen : IsOpen Ω) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (N : C(H¹₀(Ω) × L2, L2)) (u : ℝ → H¹₀(Ω) × L2) (x : H¹₀(Ω) × L2) (τ : NNReal) : Prop :=
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let T := h10L2GelfandTriple hΩopen
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
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ell q p acc x.1 x.2

/-- A global maximal trajectory with its finite-interval weak traces and conserved energy. -/
private def isGlobalDefocusingPowerWave (hΩopen : IsOpen Ω) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (r c : ℝ) (S : StronglyContinuousSemigroup (H¹₀(Ω) × L2))
    (P : C(H¹₀(Ω) × L2, L2)) (hP : LocallyLipschitz P) (x : H¹₀(Ω) × L2) : Prop :=
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let E := defocusingPowerEnergy B (baseCoordCLM (n := n) (Ω := Ω)) r
    let N : C(H¹₀(Ω) × L2, L2) := -P
    let hN : LocallyLipschitz N := hP.neg
    let F := (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
    let hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hN
    let u := S.maximalMildSolution hF x
    S.mildLifespan F x = ∞ ∧ u 0 = x ∧ ContinuousOn u (Ici 0) ∧
    (∀ t : ℝ, 0 ≤ t → u t = S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), N (u s))) t) ∧
    (∀ τ : NNReal, 0 < τ → powerWaveWeakPrefix hΩopen a N u x τ) ∧
    (∀ t : ℝ, 0 ≤ t → E (u t) = E x ∧ c * ‖(u t).1‖ ^ 2 + ‖(u t).2‖ ^ 2 ≤ 2 * E x ∧
      ‖u t‖ ≤ Real.sqrt (2 * E x / min c 1))

/-- The global energy bound extends the weak prefixes of this same semigroup to every
finite initial interval. The initial trace and mild equation remain those of its maximal curve. -/
private theorem defocusingPowerWave_of_semigroup (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (S : StronglyContinuousSemigroup (H¹₀(Ω) × L2))
    (henergy : ∀ t x,
      autonomousWaveEnergy (variableCoeffForm (multiplicationCoefficientOperator a)) (S t x) =
        autonomousWaveEnergy (variableCoeffForm (multiplicationCoefficientOperator a)) x)
    (hkin : ∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) s
      (∫ s in (0 : ℝ)..t, (z s).2) = baseCoordCLM (n := n) (Ω := Ω) (z t).1 - baseCoordCLM x.1)
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v : H¹₀(Ω), c * ‖v‖ ^ 2 ≤
      variableCoeffForm (multiplicationCoefficientOperator a) v v)
    {r : ℝ} (hr : 1 ≤ r) (P : C(H¹₀(Ω) × L2, L2)) (hP : LocallyLipschitz P)
    (hPae : ∀ z : H¹₀(Ω) × L2, (P z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun y ↦ Real.signedPower r (baseCoordCLM z.1 y))
    (hPballs : ∀ R : ℝ, 0 ≤ R →
      ∃ L : NNReal, LipschitzOnWith L P (Metric.closedBall (0 : H¹₀(Ω) × L2) R))
    (hweak :
      let N : C(H¹₀(Ω) × L2, L2) := -P
      let F : C(H¹₀(Ω) × L2, H¹₀(Ω) × L2) :=
        (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
      let hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hP.neg
      ∀ (x : H¹₀(Ω) × L2) (τ : NNReal), 0 < τ → (τ : ℝ≥0∞) < S.mildLifespan F x →
        powerWaveWeakPrefix hΩopen a N (S.maximalMildSolution (F := F) hF x) x τ)
    (x : H¹₀(Ω) × L2) : isGlobalDefocusingPowerWave hΩopen a r c S P hP x := by
  unfold isGlobalDefocusingPowerWave
  have hF : LocallyLipschitz ((ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk (-P)) :=
    (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hP.neg
  obtain ⟨hglobal, hconserve⟩ :=
    defocusingPowerWave_global a hsymm S henergy hkin hc hcoercive hr P hPae hPballs x
  have hglobal' : S.mildLifespan _ x = ∞ := hglobal
  exact ⟨hglobal', S.maximalMildSolution_zero hF x,
    (S.maximalMildSolution_global_of_lifespan_eq_top hF x hglobal').1,
    fun t ht ↦ S.maximalMildSolution_equation hF x ht (hglobal' ▸ ENNReal.ofReal_lt_top),
    fun τ hτ ↦ hweak x τ hτ (hglobal' ▸ ENNReal.coe_lt_top), hconserve⟩

/-- The coefficient form supplies coercivity and the Dirichlet semigroup.
Its weak prefixes satisfy the global conclusion by the fixed-semigroup energy argument. -/
private theorem exists_defocusingPowerWave_of_source (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) {r : ℝ} (hr : 1 ≤ r)
    (P : C(H¹₀(Ω) × L2, L2)) (hP : LocallyLipschitz P)
    (hPae : ∀ z : H¹₀(Ω) × L2, (P z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun y ↦
      Real.signedPower r (baseCoordCLM z.1 y))
    (hPballs : ∀ R : ℝ, 0 ≤ R → ∃ L : NNReal,
      LipschitzOnWith L P (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    ∃ c : ℝ, 0 < c ∧ ∃ S : StronglyContinuousSemigroup (H¹₀(Ω) × L2),
      (∀ v : H¹₀(Ω), c * ‖v‖ ^ 2 ≤ B v v) ∧
      ∀ x : H¹₀(Ω) × L2, isGlobalDefocusingPowerWave hΩopen a r c S P hP x := by
  obtain ⟨S, henergy, _, hkin, hsemilinear⟩ :=
    exists_maximal_semilinear_dirichlet_weakWave hn hΩopen hΩbounded hΩne a ha hsymm
  obtain ⟨c, hc, hcoercive⟩ :=
    variableCoeffForm_isCoercive hn hΩbounded _ (integratedElliptic_multiplication_of_ae a ha)
  have hcoercive' (v : H¹₀(Ω)) :
      c * ‖v‖ ^ 2 ≤ variableCoeffForm (multiplicationCoefficientOperator a) v v := by
    simpa only [pow_two, mul_assoc] using hcoercive v
  refine ⟨c, hc, S, hcoercive', fun x ↦ defocusingPowerWave_of_semigroup hΩopen a hsymm S henergy
    hkin hc hcoercive' hr P hP hPae hPballs ?_ x⟩
  intro N F hF y τ hτ hτlife
  exact (hsemilinear (-P) hP.neg y).2.2.2.2.1 τ hτ hτlife

/-- The negative odd-power Dirichlet source gives a global forward wave for every
energy initial state. The coefficients are autonomous, essentially bounded,
almost everywhere symmetric and uniformly elliptic on a nonempty bounded open
domain. The exponent range is `1 ≤ r ≤ n/(n-2)` for `n ≥ 3`, and every finite
real `r ≥ 1` for `n = 1, 2`.

The same maximal mild trajectory represents the displacement and velocity of
a Bochner weak wave on every finite initial interval. Its positive total energy
is constant and controls both energy-space components. The source and its integrable scalar
potential are constructed from the zero-trace Sobolev embedding. -/
theorem exists_global_defocusing_power_dirichlet_weakWave (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) {r : ℝ} (hr : 1 ≤ r)
    (hrange : 2 < n → r ≤ (n : ℝ) / ((n : ℝ) - 2)) :
    let B := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    let T := h10L2GelfandTriple hΩopen
    let E := defocusingPowerEnergy B (baseCoordCLM (n := n) (Ω := Ω)) r
    ∃ c : ℝ, 0 < c ∧
      ∃ (S : StronglyContinuousSemigroup (H¹₀(Ω) × L2))
        (N : C(H¹₀(Ω) × L2, L2)) (hN : LocallyLipschitz N), (∀ v : H¹₀(Ω), c * ‖v‖ ^ 2 ≤ B v v) ∧
        (∀ z : H¹₀(Ω) × L2, (N z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
          fun y ↦ -Real.signedPower r (baseCoordCLM z.1 y)) ∧
        (∀ v : H¹₀(Ω), Integrable (fun y ↦ |baseCoordCLM v y| ^ (r + 1)) (domainMeasure n Ω)) ∧
        (∀ R : ℝ, 0 ≤ R →
          ∃ L : NNReal, LipschitzOnWith L N (Metric.closedBall (0 : H¹₀(Ω) × L2) R)) ∧
        ∀ x : H¹₀(Ω) × L2,
          let F := (ContinuousMap.const (H¹₀(Ω) × L2) (0 : H¹₀(Ω))).prodMk N
          let hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : H¹₀(Ω))).prodMk hN
          let u := S.maximalMildSolution hF x
          S.mildLifespan F x = ∞ ∧ u 0 = x ∧ ContinuousOn u (Ici 0) ∧
          (∀ t : ℝ, 0 ≤ t → u t = S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), N (u s))) t) ∧
          (∀ τ : NNReal, 0 < τ →
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
          (∀ t : ℝ, 0 ≤ t → E (u t) = E x ∧ c * ‖(u t).1‖ ^ 2 + ‖(u t).2‖ ^ 2 ≤ 2 * E x ∧
            ‖u t‖ ≤ Real.sqrt (2 * E x / min c 1)) := by
  have : IsFiniteMeasure (domainMeasure n Ω) := isFiniteMeasure_domainMeasure_of_isBounded hΩbounded
  obtain ⟨P, hP, hPae, hPballs, hNae, hintegrable, hNballs⟩ :=
    exists_signed_powerSource (n := n) (Ω := Ω) hn hΩopen.measurableSet hr hrange
  obtain ⟨c, hc, S, hcoercive, hS⟩ := exists_defocusingPowerWave_of_source
    (n := n) (Ω := Ω) hn hΩopen hΩbounded hΩne a ha hsymm hr P hP hPae hPballs
  exact ⟨c, hc, S, -P, hP.neg, hcoercive, hNae, hintegrable, hNballs, hS⟩

end Defocusing

end SobolevSpace.GraphSpace
