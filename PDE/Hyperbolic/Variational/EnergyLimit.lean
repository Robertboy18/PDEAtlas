/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.UniformLimit
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strong energy limits of autonomous wave approximations

For a coercive bounded spatial form, conservation of the energy of differences
turns convergence of initial states into uniform convergence in the energy space.
This argument uses neither compactness of the spatial inclusion nor finite
dimension. In a spectral wave construction, the approximants are finite sums of
weak eigenfunctions, and the classical equation proves the required conservation
of differences.

The limit theorem constructs a strongly continuous energy-space trajectory,
passes the exact energy identity to it, and recovers both time-integrated wave
equations by uniform convergence. None of these properties is assumed.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology InnerProductSpace

namespace Hyperbolic.Variational

variable {V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H]

/-- Twice the physical wave energy of a displacement in `V` and velocity in `H`.
The form is not required to be positive until a coercive estimate is used. -/
def autonomousWaveEnergy (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V × H) : ℝ :=
  B x.1 x.1 + ‖x.2‖ ^ 2

/-- The wave energy is continuous in the product energy topology. -/
theorem continuous_autonomousWaveEnergy (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Continuous (autonomousWaveEnergy (H := H) B) := by
  unfold autonomousWaveEnergy
  fun_prop

/-- Coercivity of the spatial form controls the product norm of both wave
components, with no relation assumed between the norms of `V` and `H`. -/
theorem min_mul_norm_sq_le_autonomousWaveEnergy (B : V →L[ℝ] V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (x : V × H) :
    min c 1 * ‖x‖ ^ 2 ≤ autonomousWaveEnergy B x := by
  have hB := hcoercive x.1
  have hBnonneg : 0 ≤ B x.1 x.1 := (mul_nonneg hc.le (sq_nonneg _)).trans hB
  unfold autonomousWaveEnergy
  rw [Prod.norm_def]
  rcases le_total ‖x.1‖ ‖x.2‖ with h | h
  · rw [max_eq_right h]
    have hmin := mul_le_mul_of_nonneg_right (min_le_right c 1) (sq_nonneg ‖x.2‖)
    nlinarith [sq_nonneg ‖x.2‖]
  · rw [max_eq_left h]
    have hmin := mul_le_mul_of_nonneg_right (min_le_left c 1) (sq_nonneg ‖x.1‖)
    nlinarith [sq_nonneg ‖x.2‖]

/-- Boundedness of the form bounds the energy by the squared product norm. -/
theorem autonomousWaveEnergy_le_mul_norm_sq (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V × H) :
    autonomousWaveEnergy B x ≤ (‖B‖ + 1) * ‖x‖ ^ 2 := by
  have hB : B x.1 x.1 ≤ ‖B‖ * ‖x.1‖ * ‖x.1‖ := (le_abs_self _).trans (B.le_opNorm₂ x.1 x.1)
  have hq : ‖x.1‖ ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (le_max_left _ _)
  have hp : ‖x.2‖ ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (le_max_right _ _)
  have hscaled := mul_le_mul_of_nonneg_left hq (norm_nonneg B)
  unfold autonomousWaveEnergy
  nlinarith

/-- Comparing two coercive wave energies gives a uniform comparison of their
state norms. This constant depends only on the form bound and coercivity. -/
theorem exists_pos_norm_le_of_autonomousWaveEnergy_le (B : V →L[ℝ] V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : V × H,
      autonomousWaveEnergy B x ≤ autonomousWaveEnergy B y → ‖x‖ ≤ K * ‖y‖ := by
  let d := min c 1
  have hd : 0 < d := lt_min hc zero_lt_one
  let K := Real.sqrt ((‖B‖ + 1) / d)
  have hratio : 0 < (‖B‖ + 1) / d := div_pos (by positivity) hd
  have hK : 0 < K := Real.sqrt_pos.2 hratio
  have hKsq : K ^ 2 = (‖B‖ + 1) / d := Real.sq_sqrt hratio.le
  refine ⟨K, hK, fun x y hxy ↦ ?_⟩
  have hbound : d * ‖x‖ ^ 2 ≤ (‖B‖ + 1) * ‖y‖ ^ 2 :=
    (min_mul_norm_sq_le_autonomousWaveEnergy B hc hcoercive x).trans
      (hxy.trans (autonomousWaveEnergy_le_mul_norm_sq B y))
  have hsq : ‖x‖ ^ 2 ≤ (K * ‖y‖) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hd).mp
    calc
      ‖x‖ ^ 2 * d ≤ (‖B‖ + 1) * ‖y‖ ^ 2 := by
        simpa only [mul_comm] using hbound
      _ = (K * ‖y‖) ^ 2 * d := by
        rw [mul_pow, hKsq, mul_right_comm ((‖B‖ + 1) / d) (‖y‖ ^ 2) d, div_mul_cancel₀ _ hd.ne']
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK.le (norm_nonneg _))).1 hsq

/-- Energy control of differences propagates the Cauchy property of the initial
states uniformly over the whole time set. The set need not be compact. -/
theorem uniformCauchySeqOn_of_autonomousWaveEnergy_difference_le {X : Type*} (B : V →L[ℝ] V →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (z : ℕ → X → V × H) (s : Set X)
    (a : X) (hinit : CauchySeq fun n ↦ z n a)
    (henergy : ∀ n m t, t ∈ s → autonomousWaveEnergy B (z n t - z m t) ≤
      autonomousWaveEnergy B (z n a - z m a)) :
    UniformCauchySeqOn z atTop s := by
  obtain ⟨K, hK, hbound⟩ := exists_pos_norm_le_of_autonomousWaveEnergy_le (H := H) B hc hcoercive
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hinit (ε / K) (div_pos hε hK)
  refine ⟨N, fun n hn m hm t ht ↦ ?_⟩
  rw [dist_eq_norm]
  calc
    ‖z n t - z m t‖ ≤ K * ‖z n a - z m a‖ := hbound _ _ (henergy n m t ht)
    _ < K * (ε / K) :=
      mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hN n hn m hm) hK
    _ = ε := by field_simp [hK.ne']

/-- A family controlled by a coercive difference energy has a strongly
continuous limit whenever its initial states converge. The limit is uniform
on the entire time set, including its endpoints. -/
theorem exists_continuousOn_limit_of_autonomousWaveEnergy_difference_le [CompleteSpace V]
    [CompleteSpace H] {X : Type*} [TopologicalSpace X] (B : V →L[ℝ] V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (z : ℕ → X → V × H) (s : Set X) (a : X) (ha : a ∈ s)
    (x₀ : V × H) (hinit : Tendsto (fun n ↦ z n a) atTop (𝓝 x₀)) (hcont : ∀ n, ContinuousOn (z n) s)
    (henergy : ∀ n m t, t ∈ s → autonomousWaveEnergy B (z n t - z m t) ≤
      autonomousWaveEnergy B (z n a - z m a)) :
    ∃ u : X → V × H, ContinuousOn u s ∧ TendstoUniformlyOn z u atTop s ∧ u a = x₀ := by
  classical
  have hCauchy := uniformCauchySeqOn_of_autonomousWaveEnergy_difference_le
    B hc hcoercive z s a hinit.cauchySeq henergy
  have hpoint (t : s) : CauchySeq fun n ↦ z n t := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hCauchy ε hε
    exact ⟨N, fun n hn m hm ↦ hN n hn m hm t t.property⟩
  choose v hv using fun t : s ↦ cauchySeq_tendsto_of_complete (hpoint t)
  let u : X → V × H := fun t ↦ if ht : t ∈ s then v ⟨t, ht⟩ else 0
  have hu (t : X) (ht : t ∈ s) :
      Tendsto (fun n ↦ z n t) atTop (𝓝 (u t)) := by
    simpa only [u, dite_eq_left ht] using hv ⟨t, ht⟩
  have huniform : TendstoUniformlyOn z u atTop s := hCauchy.tendstoUniformlyOn_of_tendsto hu
  refine ⟨u, huniform.continuousOn (Frequently.of_forall hcont), huniform, ?_⟩
  exact tendsto_nhds_unique (hu a ha) hinit

/-- Conservation of the approximants' energies survives the strong limit.
Together with difference-energy control, this constructs continuous energy
traces and their exact conservation law, rather than merely essential bounds. -/
theorem exists_continuousOn_limit_conserving_autonomousWaveEnergy [CompleteSpace V]
    [CompleteSpace H] {X : Type*} [TopologicalSpace X] (B : V →L[ℝ] V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (z : ℕ → X → V × H) (s : Set X) (a : X) (ha : a ∈ s)
    (x₀ : V × H) (hinit : Tendsto (fun n ↦ z n a) atTop (𝓝 x₀)) (hcont : ∀ n, ContinuousOn (z n) s)
    (henergy : ∀ n t, t ∈ s → autonomousWaveEnergy B (z n t) = autonomousWaveEnergy B (z n a))
    (hdifference : ∀ n m t, t ∈ s → autonomousWaveEnergy B (z n t - z m t) ≤
      autonomousWaveEnergy B (z n a - z m a)) :
    ∃ u : X → V × H, ContinuousOn u s ∧ TendstoUniformlyOn z u atTop s ∧ u a = x₀ ∧ ∀ t ∈ s,
      autonomousWaveEnergy B (u t) = autonomousWaveEnergy B x₀ := by
  obtain ⟨u, hucont, hu, hua⟩ := exists_continuousOn_limit_of_autonomousWaveEnergy_difference_le
      B hc hcoercive z s a ha x₀ hinit hcont hdifference
  refine ⟨u, hucont, hu, hua, fun t ht ↦ ?_⟩
  have hleft := (continuous_autonomousWaveEnergy B).continuousAt.tendsto.comp (hu.tendsto_at ht)
  have hright := (continuous_autonomousWaveEnergy B).continuousAt.tendsto.comp hinit
  exact tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun n ↦ (henergy n t ht).symm))

variable [InnerProductSpace ℝ H]

/-- A classical homogeneous wave has constant energy. The equation is tested
only with its velocity; finite spectral sums satisfy this ambient variational
equation even though their trajectories lie in a finite-dimensional subspace. -/
theorem autonomousWaveEnergy_eq_initial_of_hasDerivAt (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) (J : V →L[ℝ] H) {q v d : ℝ → V} {a b : ℝ}
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (v t) t) (hv : ∀ t ∈ Icc a b, HasDerivAt v (d t) t)
    (heq : ∀ t ∈ Icc a b, inner ℝ (J (d t)) (J (v t)) + B (q t) (v t) = 0) :
    ∀ t ∈ Icc a b, autonomousWaveEnergy B (q t, J (v t)) =
      autonomousWaveEnergy B (q a, J (v a)) := by
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ autonomousWaveEnergy B (q s, J (v s))) 0 t := by
    have hBq := B.hasFDerivAt.comp_hasDerivAt t (hq t ht)
    have hpotential := hBq.clm_apply (hq t ht)
    have hkinetic := (J.hasFDerivAt.comp_hasDerivAt t (hv t ht)).norm_sq
    have hsum := hpotential.add hkinetic
    have hzero : B (v t) (q t) + B (q t) (v t) +
        2 * inner ℝ (J (v t)) (J (d t)) = 0 := by
      rw [hsymm (v t) (q t)]
      have hzero := heq t ht
      rw [real_inner_comm (J (d t)) (J (v t))]
      linarith
    have hsum_zero := hsum.congr_deriv (by
      simpa only [Function.comp_def] using hzero)
    exact hsum_zero.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hnorm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht ↦ (hderiv t ht).hasDerivWithinAt) (fun _ _ ↦ le_refl (‖(0 : ℝ)‖))
  intro t ht
  have hz := hnorm t ht
  simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hz

/-- Two classical homogeneous waves conserve the energy of their difference.
The ambient variational equations allow each wave to have a different spectral truncation. -/
theorem autonomousWaveEnergy_difference_eq_initial_of_hasDerivAt (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) (J : V →L[ℝ] H) {q₁ q₂ v₁ v₂ d₁ d₂ : ℝ → V} {a b : ℝ}
    (hq₁ : ∀ t ∈ Icc a b, HasDerivAt q₁ (v₁ t) t) (hq₂ : ∀ t ∈ Icc a b, HasDerivAt q₂ (v₂ t) t)
    (hv₁ : ∀ t ∈ Icc a b, HasDerivAt v₁ (d₁ t) t) (hv₂ : ∀ t ∈ Icc a b, HasDerivAt v₂ (d₂ t) t)
    (heq₁ : ∀ t ∈ Icc a b, ∀ w, inner ℝ (J (d₁ t)) (J w) + B (q₁ t) w = 0)
    (heq₂ : ∀ t ∈ Icc a b, ∀ w, inner ℝ (J (d₂ t)) (J w) + B (q₂ t) w = 0) :
    ∀ t ∈ Icc a b, autonomousWaveEnergy B ((q₁ t, J (v₁ t)) - (q₂ t, J (v₂ t))) =
      autonomousWaveEnergy B ((q₁ a, J (v₁ a)) - (q₂ a, J (v₂ a))) := by
  have heq (t : ℝ) (ht : t ∈ Icc a b) : inner ℝ (J (d₁ t - d₂ t)) (J (v₁ t - v₂ t)) +
        B (q₁ t - q₂ t) (v₁ t - v₂ t) = 0 := by
    have h₁ := heq₁ t ht (v₁ t - v₂ t)
    have h₂ := heq₂ t ht (v₁ t - v₂ t)
    simp only [map_sub, sub_apply, inner_sub_left, inner_sub_right] at h₁ h₂ ⊢
    linarith
  simpa only [map_sub, Pi.sub_apply, Prod.mk_sub_mk] using
    autonomousWaveEnergy_eq_initial_of_hasDerivAt B hsymm J (fun t ht ↦ (hq₁ t ht).sub (hq₂ t ht))
      (fun t ht ↦ (hv₁ t ht).sub (hv₂ t ht)) heq

/-- Classical ambient wave approximations with convergent initial states
construct a continuous energy trajectory and its conservation law. Both energy
estimates are derived from the differential equations. -/
theorem exists_continuousOn_energy_limit_of_classical_waves [CompleteSpace V] [CompleteSpace H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (J : V →L[ℝ] H) (q v d : ℕ → ℝ → V) {a b : ℝ}
    (hab : a ≤ b) (hq : ∀ n t, t ∈ Icc a b → HasDerivAt (q n) (v n t) t)
    (hv : ∀ n t, t ∈ Icc a b → HasDerivAt (v n) (d n t) t)
    (heq : ∀ n t, t ∈ Icc a b → ∀ w, inner ℝ (J (d n t)) (J w) + B (q n t) w = 0) (x₀ : V × H)
    (hinit : Tendsto (fun n ↦ (q n a, J (v n a))) atTop (𝓝 x₀)) :
    ∃ u : ℝ → V × H, ContinuousOn u (Icc a b) ∧
      TendstoUniformlyOn (fun n t ↦ (q n t, J (v n t))) u atTop (Icc a b) ∧ u a = x₀ ∧
      ∀ t ∈ Icc a b, autonomousWaveEnergy B (u t) = autonomousWaveEnergy B x₀ := by
  apply exists_continuousOn_limit_conserving_autonomousWaveEnergy
    B hc hcoercive (fun n t ↦ (q n t, J (v n t))) (Icc a b) a (left_mem_Icc.mpr hab) x₀ hinit
  · exact fun n t ht ↦ (hq n t ht).continuousAt.continuousWithinAt.prodMk
      ((J.continuous.continuousAt.comp (hv n t ht).continuousAt).continuousWithinAt)
  · exact fun n ↦ autonomousWaveEnergy_eq_initial_of_hasDerivAt B hsymm J
      (hq n) (hv n) (fun t ht ↦ heq n t ht (v n t))
  · exact fun n m t ht ↦ (autonomousWaveEnergy_difference_eq_initial_of_hasDerivAt B hsymm J
      (hq n) (hq m) (hv n) (hv m) (heq n) (heq m) t ht).le

end Hyperbolic.Variational

namespace Hyperbolic.Variational

open MeasureTheory
open scoped Interval

variable {V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Classical homogeneous wave approximations construct a continuous energy
solution with both initial traces, both integrated wave equations, and exact
conservation. `K` is the pivot-to-dual map associated with `J`. -/
theorem exists_energy_solution_of_classical_wave_approximations (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (J : V →L[ℝ] H) (K : H →L[ℝ] V →L[ℝ] ℝ) (hK : ∀ p w, K p w = inner ℝ p (J w))
    (q v d : ℕ → ℝ → V) {a b : ℝ} (hab : a ≤ b)
    (hq : ∀ n t, t ∈ Icc a b → HasDerivAt (q n) (v n t) t)
    (hv : ∀ n t, t ∈ Icc a b → HasDerivAt (v n) (d n t) t)
    (heq : ∀ n t, t ∈ Icc a b → ∀ w, inner ℝ (J (d n t)) (J w) + B (q n t) w = 0) (q₀ : V) (p₀ : H)
    (hinit : Tendsto (fun n ↦ (q n a, J (v n a))) atTop (𝓝 (q₀, p₀))) :
    ∃ u : ℝ → V × H, ContinuousOn u (Icc a b) ∧
      TendstoUniformlyOn (fun n t ↦ (q n t, J (v n t))) u atTop (Icc a b) ∧
      u a = (q₀, p₀) ∧
      (∀ t ∈ Icc a b, autonomousWaveEnergy B (u t) =
        autonomousWaveEnergy B (q₀, p₀)) ∧
      (∀ t ∈ Icc a b, (∫ s in a..t, (u s).2) = J (u t).1 - J q₀) ∧
      (∀ t ∈ Icc a b, (∫ s in a..t, -(B (u s).1)) = K (u t).2 - K p₀) := by
  obtain ⟨u, hucont, hu, hua, henergy⟩ :=
    exists_continuousOn_energy_limit_of_classical_waves B hsymm hc hcoercive
      J q v d hab hq hv heq (q₀, p₀) hinit
  have hcont (n : ℕ) : ContinuousOn (fun t ↦ (q n t, J (v n t))) (Icc a b) :=
    fun t ht ↦ (hq n t ht).continuousAt.continuousWithinAt.prodMk
      ((J.continuous.continuousAt.comp (hv n t ht).continuousAt).continuousWithinAt)
  have hdisplacement := PDE.Analysis.Evolution.integral_eq_sub_of_uniform_limit
    (J.comp (ContinuousLinearMap.fst ℝ V H)) (ContinuousLinearMap.snd ℝ V H)
    hcont hu (fun n t ht ↦ J.hasFDerivAt.comp_hasDerivAt t (hq n t ht))
  have hvelocityDeriv (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ K (J (v n s))) (-(B (q n t))) t := by
    have hacceleration : K (J (d n t)) = -(B (q n t)) := by
      ext w
      rw [hK, neg_apply]
      exact eq_neg_of_add_eq_zero_left (heq n t ht w)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, hacceleration]
      using (K.comp J).hasFDerivAt.comp_hasDerivAt t (hv n t ht)
  have hvelocity := PDE.Analysis.Evolution.integral_eq_sub_of_uniform_limit
    (K.comp (ContinuousLinearMap.snd ℝ V H))
    (-(B.comp (ContinuousLinearMap.fst ℝ V H))) hcont hu hvelocityDeriv
  refine ⟨u, hucont, hu, hua, henergy, ?_, ?_⟩
  · intro t ht
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', hua] using hdisplacement t ht
  · intro t ht
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', neg_apply, hua] using hvelocity t ht

end Hyperbolic.Variational
