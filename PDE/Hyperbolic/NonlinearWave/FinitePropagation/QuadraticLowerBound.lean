/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.EnergyGrowth
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Vanishing

/-!
# Finite propagation for semilinear waves

Let `V` be `C¹` with `V 0 = 0` and `V z ≥ -C z²` near zero. Adding a positive quadratic term
makes the cone energy nonnegative. The added term contributes a source bounded by the modified
energy, so Gronwall propagates zero Cauchy data. The reaction `deriv V` need not be locally
Lipschitz.

A nonnegative potential satisfies the bound with `C = 0`, which gives the finite propagation
theorem of Evans, §12.1.2, Theorem 2(ii), on the closed and on the open backward cone.
Continuity extends zero Cauchy data from the open base ball to its closure, so the closed-cone
conclusion holds for zero Cauchy data on the open base ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(ii) and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- A local quadratic lower bound extends to every compact scalar range. -/
private theorem exists_quadratic_lower_bound_on_Icc
    {V : ℝ → ℝ} {C : ℝ} (hV : Continuous V)
    (hbound : ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z) (M : ℝ) :
    ∃ K ≥ 0, ∀ z ∈ Icc (-M) M, -K * z ^ 2 ≤ V z := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff_ball.mp hbound
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hV.norm.continuousOn
  let K := max 0 (max C (B / δ ^ 2))
  have hK : 0 ≤ K := le_max_left _ _
  refine ⟨K, hK, ?_⟩
  intro z hz
  by_cases hsmall : |z| < δ
  · have hlocal : -C * z ^ 2 ≤ V z := hnear z (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hsmall)
    have hCK : C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    exact (mul_le_mul_of_nonneg_right (neg_le_neg hCK) (sq_nonneg z)).trans hlocal
  · have hb : |V z| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB (mem_image_of_mem (fun z ↦ ‖V z‖) hz)
    have hBK : B ≤ K * δ ^ 2 := (div_le_iff₀ (sq_pos_of_pos hδ)).mp
        ((le_max_right _ _).trans (le_max_right _ _))
    have hδz : δ ≤ |z| := le_of_not_gt hsmall
    have hsquare : δ ^ 2 ≤ z ^ 2 := by
      nlinarith [sq_abs z, sq_nonneg (|z| - δ)]
    have hlarge := hBK.trans (mul_le_mul_of_nonneg_left hsquare hK)
    linarith [(neg_le_abs (V z)).trans hb]

/-- The extra quadratic potential pays for its own contribution to the energy source. -/
private theorem energyBalanceResidual_le_of_quadratic_lower_bound {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {K : ℝ} {p : ℝ^(n + 1)} (hV : ContDiff ℝ 1 V) (hu : ContDiffAt ℝ 2 u p) (hK : 0 ≤ K)
    (hbound : -K * (u p) ^ 2 ≤ V (u p)) (hwave : semilinearWaveOperator V u p = 0) :
    semilinearWaveEnergyBalanceResidual (fun z ↦ V z + (K + 1) * z ^ 2) u p ≤
      (2 * (K + 1)) * semilinearWaveEnergyDensity (fun z ↦ V z + (K + 1) * z ^ 2) u p := by
  have hW : ContDiff ℝ 1 (fun z ↦ V z + (K + 1) * z ^ 2) := by fun_prop
  have hd : deriv (fun z ↦ V z + (K + 1) * z ^ 2) (u p) =
      deriv V (u p) + (K + 1) * (2 * u p) := by
    exact ((hV.differentiable (by norm_num)).differentiableAt.hasDerivAt.add
      (((hasDerivAt_id (u p)).pow 2).const_mul (K + 1))).deriv.trans (by simp)
  rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator hW hu]
  simp only [semilinearWaveOperator, hd] at hwave ⊢
  have hsource : (∂[0] u) p * (waveOperator u p + (deriv V (u p) + (K + 1) * (2 * u p))) =
      (K + 1) * (2 * (∂[0] u) p * u p) := by rw [← add_assoc, hwave]; ring
  rw [hsource]
  have hprod : 2 * (∂[0] u) p * u p ≤ (∂[0] u) p ^ 2 + (u p) ^ 2 := by
    nlinarith [sq_nonneg ((∂[0] u) p - u p)]
  have hcoercive : (∂[0] u) p ^ 2 + (u p) ^ 2 ≤
      2 * semilinearWaveEnergyDensity (fun z ↦ V z + (K + 1) * z ^ 2) u p := by
    unfold semilinearWaveEnergyDensity classicalWaveEnergyDensity
    nlinarith [sq_nonneg (u p), sq_nonneg (‖classicalWaveSpatialGradient u p‖)]
  calc
    _ ≤ (K + 1) * ((∂[0] u) p ^ 2 + (u p) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (by linarith)
    _ ≤ (K + 1) * (2 * _) := mul_le_mul_of_nonneg_left hcoercive (by linarith)
    _ = _ := by ring

/-- Let `V` be `C¹` with `V 0 = 0` and `V z ≥ -C z²` near zero. A `C²` solution of the
semilinear wave equation in a backward cone whose Cauchy data vanish on the base
vanishes on the closed cone. The reaction `deriv V` need not be locally Lipschitz. -/
theorem eq_zero_on_closed_backwardCone_of_quadratic_lower_bound [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {C : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hbound : ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z) (hu : ContDiff ℝ 2 u) (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (timeSpaceCons a x) = 0) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  obtain ⟨M, _, hM⟩ := exists_norm_le_on_timeSpaceCylinder u hu.continuous a T c (T - a)
  obtain ⟨K, hK, hKV⟩ := exists_quadratic_lower_bound_on_Icc hV.continuous hbound M
  let W : ℝ → ℝ := fun z ↦ V z + (K + 1) * z ^ 2
  have hW : ContDiff ℝ 1 W := by dsimp only [W]; fun_prop
  have hWzero : W 0 = 0 := by simp only [W, hVzero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, add_zero]
  have hcone (t : ℝ) (ht : t ∈ Icc a T) (x : ℝ^n) (hx : x ∈ Metric.closedBall c (T - t)) :
      -K * (u (timeSpaceCons t x)) ^ 2 ≤ V (u (timeSpaceCons t x)) := by
    apply hKV
    apply abs_le.mp
    simpa only [Real.norm_eq_abs] using hM t ht x
      (Metric.closedBall_subset_closedBall (sub_le_sub_left ht.1 T) hx)
  have hWnonneg (t : ℝ) (ht : t ∈ Icc a T) (x : ℝ^n)
      (hx : x ∈ Metric.closedBall c (T - t)) : 0 ≤ W (u (timeSpaceCons t x)) := by
    have hp := hcone t ht x hx
    dsimp only [W]
    nlinarith [sq_nonneg (u (timeSpaceCons t x))]
  have hres (t : ℝ) (ht : t ∈ Ico a T) (x : ℝ^n) (hx : x ∈ Metric.ball c (T - t)) :
      semilinearWaveEnergyBalanceResidual W u (timeSpaceCons t x) ≤
        (2 * (K + 1)) * semilinearWaveEnergyDensity W u (timeSpaceCons t x) :=
    energyBalanceResidual_le_of_quadratic_lower_bound hV hu.contDiffAt hK
      (hcone t (Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall hx)) (hwave t ht x hx)
  have hinitial := semilinearBackwardConeEnergy_initial_eq_zero hWzero hu c hpos hvel
  apply eq_zero_on_closed_backwardCone_of_energy_eq_zero hu c hpos
  intro t ht
  have he := semilinearBackwardConeEnergy_le_exp hW hu c hWnonneg hres ht
  rw [hinitial, zero_mul] at he
  have hp : 0 ≤ ballIntegral n (fun x ↦ W (u (timeSpaceCons t x))) c (T - t) :=
    setIntegral_nonneg measurableSet_ball (fun x hx ↦
      hWnonneg t (Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall hx))
  have hn := backwardConeEnergy_nonneg u c T t
  unfold semilinearBackwardConeEnergy at he
  linarith

/-- Finite propagation for semilinear waves on the closed backward cone (Evans, §12.1.2,
Theorem 2(ii)).

Let `V` be a nonnegative `C¹` potential with `V(0)=0`. A classical solution
of `uₜₜ - Δu + V'(u)=0` whose displacement and velocity vanish on the closed base
ball vanishes throughout the closed backward cone. -/
theorem eq_zero_on_closed_backwardCone_semilinear [Fact (0 < n)] {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z) (hVzero : V 0 = 0) (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (timeSpaceCons a x) = 0) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 :=
  eq_zero_on_closed_backwardCone_of_quadratic_lower_bound (C := 0) hV hVzero
    (Eventually.of_forall fun z ↦ by simpa only [neg_zero, zero_mul] using hVnonneg z)
    hu c hwave hpos hvel

/-- Zero displacement and velocity on the open base ball force vanishing on the
closed backward cone, including its lateral boundary and vertex. Continuity of
both Cauchy traces supplies the closed-ball data required by the energy argument.
Evans, §12.1.2, Theorem 2(ii), assumes zero data on the closed ball `B(x₀, t₀)`. -/
theorem eq_zero_on_closed_backwardCone_semilinear_of_open_ball [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z) (hVzero : V 0 = 0)
    (hu : ContDiff ℝ 2 u) (c : ℝ^n) {a T : ℝ} (haT : a < T)
    (hwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.ball c (T - a), u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Metric.ball c (T - a), (∂[0] u) (timeSpaceCons a x) = 0) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  have hslice := (contDiff_timeSpaceCons_spatial n a (m := 1)).continuous
  have hp := Set.EqOn.closure hpos (hu.continuous.comp hslice) continuous_const
  have hv := Set.EqOn.closure hvel
    ((PDE.contDiff_partialDeriv_of_succ (m := 1) hu).continuous.comp hslice) continuous_const
  rw [closure_ball _ (sub_ne_zero.mpr haT.ne')] at hp hv
  exact eq_zero_on_closed_backwardCone_semilinear hV hVnonneg hVzero hu c hwave hp hv

/-- Finite propagation for semilinear waves on the open backward cone (Evans, §12.1.2,
Theorem 2(ii)).

Let `V` be a nonnegative `C¹` potential with `V(0) = 0`. A classical solution
of `uₜₜ - Δu + V'(u) = 0` whose displacement and velocity vanish on the open
base ball vanishes in the open backward cone. Each point of the open cone lies in a
strictly smaller closed backward cone whose base is inside the open base ball. -/
theorem eq_zero_on_open_backwardCone_semilinear [Fact (0 < n)] {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z) (hVzero : V 0 = 0) (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.ball c (T - a), u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Metric.ball c (T - a), (∂[0] u) (timeSpaceCons a x) = 0) :
    ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), u (timeSpaceCons t x) = 0 := by
  intro t ht x hx
  let T' : ℝ := (t + dist x c + T) / 2
  have htxT : t + dist x c < T := by
    rw [Metric.mem_ball] at hx
    linarith
  have hsmall : t + dist x c < T' := by
    dsimp [T']
    linarith
  have hlarge : T' < T := by
    dsimp [T']
    linarith
  apply eq_zero_on_closed_backwardCone_semilinear hV hVnonneg hVzero hu c
    (fun s hs y hy ↦ hwave s ⟨hs.1, hs.2.trans hlarge⟩ y
      (Metric.ball_subset_ball (sub_le_sub_right hlarge.le s) hy))
    (fun y hy ↦ hpos y (Metric.closedBall_subset_ball (sub_lt_sub_right hlarge a) hy))
    (fun y hy ↦ hvel y (Metric.closedBall_subset_ball (sub_lt_sub_right hlarge a) hy))
    t ⟨ht.1, (le_add_of_nonneg_right dist_nonneg).trans hsmall.le⟩ x
  rw [Metric.mem_closedBall]
  linarith

end WaveEquation
