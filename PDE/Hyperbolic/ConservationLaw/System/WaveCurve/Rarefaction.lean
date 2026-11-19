/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Flow.Contact
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Rarefactions and contacts along local characteristic flows

A local characteristic flow with strictly increasing speed gives a rarefaction
connection on any positive segment inside its construction interval.

For a linearly degenerate field, differentiating the speed along an
integral curve gives zero. Differentiating `F(R(s,q)) - λ(q) R(s,q)` then
gives zero as well. The mean value theorem proves constant speed and the
Rankine–Hugoniot identity on one common interval for all nearby left states.

In the notation of Evans, §11.2, the flow solves the ODE (6) of §11.2.1, so its trajectory
through `q` is the rarefaction curve `R_k(q)`. By `IsRarefactionConnection.of_local_flow`, when
`λ_k` increases along the trajectory, each point with positive parameter is joined to `q` by an
arc on which `λ_k` increases, so it lies in `R_k^+(q)`; §11.2.2, Theorem 1, builds a
`k`-rarefaction wave from such an arc.
`exists_uniform_contact_of_local_flow` is what the proof of §11.2.3, Theorem 3, gives for a
field that is linearly degenerate (12) near `q₀`: `λ_k` is constant along `R_k(q)`, and each
of its points satisfies the Rankine–Hugoniot condition with `q` and speed `λ_k(q)`, so it lies
in `S_k(q)` with `σ = λ_k(q)`. Evans integrates where we use the mean value theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (6) and (12) and the notation
  `R_k^±(z₀)`; §11.2.2, Theorem 1; §11.2.3, Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- A local characteristic flow with strictly increasing speed produces a
rarefaction connection. The whole closed parameter segment lies inside the
open interval on which the differential equation and regularity hold. -/
theorem IsRarefactionConnection.of_local_flow {m : ℕ} {flux : ℝ^m → ℝ^m}
    (C : CharacteristicField flux) {curve : ℝ → ℝ^m} {q : ℝ^m} {δ s : ℝ}
    (hzero : curve 0 = q) (hreg : ContDiffOn ℝ 1 curve (Ioo (-δ) δ))
    (hflow : ∀ t ∈ Ioo (-δ) δ, HasDerivAt curve (C.rightEigenvector (curve t)) t)
    (hmono : StrictMonoOn (fun t ↦ C.speed (curve t)) (Ioo (-δ) δ)) (hs : 0 < s) (hsδ : s < δ) :
    IsRarefactionConnection C q (curve s) := by
  have hδ : 0 < δ := by linarith
  refine ⟨curve, s, Ioo (-δ) δ, isOpen_Ioo, ?_, hreg, hzero,
    fun t ht ↦ (hflow t ht).hasDerivWithinAt, rfl, ?_⟩
  · rw [uIcc_of_le hs.le]
    exact Icc_subset_Ioo (neg_lt_zero.mpr hδ) hsδ
  · have hmem {θ : ℝ} (hθ : θ ∈ Icc 0 1) : θ * s ∈ Ioo (-δ) δ :=
      ⟨lt_of_lt_of_le (neg_lt_zero.mpr hδ) (mul_nonneg hθ.1 hs.le),
        lt_of_le_of_lt (mul_le_of_le_one_left hs.le hθ.2) hsδ⟩
    exact fun a ha b hb hab ↦ hmono (hmem ha) (hmem hb) (mul_lt_mul_of_pos_right hab hs)

/-- A locally linearly degenerate characteristic flow produces contacts on
a uniform neighborhood. The jump identity is derived by differentiating the
flux along the constructed trajectories. -/
theorem exists_uniform_contact_of_local_flow {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : Differentiable ℝ flux) {eig : ℝ^m → ℝ} {r : ℝ^m → ℝ^m} {R : ℝ × ℝ^m → ℝ^m} {q₀ : ℝ^m}
    (hR : ContinuousAt R (0, q₀)) (hzero : ∀ᶠ q in 𝓝 q₀, R (0, q) = q)
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), HasDerivAt (fun t ↦ R (t, p.2)) (r (R p)) p.1)
    (hfield : ∀ᶠ q in 𝓝 q₀, DifferentiableAt ℝ eig q ∧ fderiv ℝ eig q (r q) = 0 ∧
      fderiv ℝ flux q (r q) = eig q • r q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ, ∀ s ∈ Ioo (-δ) δ,
      eig (R (s, q)) = eig q ∧ RankineHugoniot flux q (R (s, q)) (eig q) := by
  have ht : Tendsto R (𝓝 (0, q₀)) (𝓝 q₀) := by
    simpa only [ContinuousAt, hzero.self_of_nhds] using hR
  have hnear := hflow.and (ht.eventually hfield)
  have hz : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), R (0, p.2) = p.2 := (continuousAt_snd :
      ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hnear.and hz)
  refine ⟨δ, hδ, fun q hq ↦ ?_⟩
  have hmem {s : ℝ} (hs : s ∈ Ioo (-δ) δ) :
      (s, q) ∈ ball ((0 : ℝ), q₀) δ := by
    rw [← ball_prod_same]
    refine ⟨?_, hq⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hR₀ : R (0, q) = q := (hball (hmem h0)).2
  intro s hs
  simpa only [hR₀] using constant_speed_rankineHugoniot_of_integralCurve
    isOpen_Ioo isPreconnected_Ioo (fun t _ ↦ hflux (R (t, q))) (fun _ ht ↦ (hball (hmem ht)).1.1)
    (fun _ ht ↦ (hball (hmem ht)).1.2) hs h0

end PDE.Hyperbolic.ConservationLaw.System
