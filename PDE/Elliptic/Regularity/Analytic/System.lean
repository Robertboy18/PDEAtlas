/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.DerivativeBounds
public import PDE.Analysis.Calculus.AnalyticDerivativeBounds

/-!
# Smooth solutions of elliptic systems with analytic coefficients are analytic

## Motivation

Is a smooth solution `v = (v_l)` of the autonomous diagonal system
`∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ(v) ∂ⱼ v_l - f_{l i}(v)) = 0` on an open set real-analytic when the coefficients
`aᵢⱼ` and the forcing `f_{l i}` are real-analytic functions of the values of `v` and the matrix
`a(v(x))` is elliptic at every point?

## The idea

Yes. This is the analytic step in the regularity theory of minimizers of analytic integrands:
the gradient of a minimizer solves a system of this class. Near a point `x₀` the values of `v`
stay in a ball where the derivatives of all the coefficients are at most `m! C Kᵐ` (Cauchy
estimates for analytic functions), and the frozen matrices stay uniformly elliptic by
continuity. That is the setting `SolutionOnBall`, where the derivatives of `v` are at most
`i! M K₀ⁱ`, so the Taylor series of `v` converges.

The estimate itself is a maximum-principle argument in sup norms. A weighted sum of the squares
of the derivatives of order `j` and `j - 1` has a maximum in the ball. At that point the
elliptic operator with frozen coefficients is nonpositive on it, and the Bernstein inequality
bounds the operator from below by the derivatives of order `j + 1` and `j`. The derivatives of
the equation are controlled by the Leibniz rule and the chain rule with a weight that is closed
under convolution. This gives bounds of the right size as soon as they hold with a constant
twice as large, and that is enough to obtain them.

## Main results

* `exists_solutionOnBall`: near every point of the open set the hypotheses of `SolutionOnBall`
  hold on a small ball.
* `exists_familyNorm_le_of_autonomous_system`: all smooth solutions have derivative bounds
  `|Dⁱv| ≤ i! M K₀ⁱ` near every point, for all `i`.
* `analyticOnNhd_of_autonomous_system`: all smooth solutions are real-analytic on the open set.
  Every dimension, every finite family, coefficients analytic and elliptic along the solution.

## Relations

This is the analytic counterpart of
`PDE.Elliptic.Regularity.Quasilinear.Bootstrap.contDiffOn_infty_of_autonomous_system`, which
makes `C¹` weak solutions smooth when the coefficients are smooth; here the solution is assumed
smooth and the equation is pointwise. `analyticOnNhd_of_autonomous_system` is
`SolutionOnBall.analyticAt` at every point, and it uses
`AnalyticAt.exists_norm_iteratedFDeriv_le_family` for the coefficients. The case of the gradient
of a solution of an Euler–Lagrange equation is
`PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_gradientDensity`.

## What stays open

Systems whose principal part couples the components, and equations with a source term outside
the divergence, are not covered. Regularity up to the boundary is not treated. The library
applies the theorem to gradients and to harmonic families, with zero forcing, and to an
exponential family with a forcing that is linear in the solution
(`PDE.Examples.AnalyticSystem.analyticOnNhd_exponentialFamily`).

## References

* S. Blatt, *On the analyticity of solutions to non-linear elliptic partial differential
  equations*, arXiv:2009.08762v2, 2024, Theorem 1.1 and §3. We follow its plan (weighted
  derivatives of every order and a recursion that absorbs the top order), with the `L²` estimate
  and the Banach algebra `H^m` replaced by the maximum principle and sup norms, and the majorant
  equation replaced by a self-improving bound.
  <https://arxiv.org/abs/2009.08762>
  Its introduction gives the history of the theorem (S. Bernstein in two variables, 1904;
  I. G. Petrowsky, 1939; C. B. Morrey, 1958); we have not used those proofs.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped ContDiff Topology
open SobolevSpace.GraphSpace.BoundaryRegularity (principalEnergy)

namespace PDE.Elliptic.Regularity.Analytic

variable {n : ℕ}

/-- The quadratic forms of two matrices differ by at most the sum of the absolute differences of
their entries times `|ξ|²`. -/
theorem abs_principalEnergy_sub_le (A A' : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    |principalEnergy A ξ - principalEnergy A' ξ| ≤
      (∑ i, ∑ j, |A i j - A' i j|) * ∑ i, ξ i ^ 2 := by
  have hS (i : Fin n) : ξ i ^ 2 ≤ ∑ k, ξ k ^ 2 :=
    Finset.single_le_sum (f := fun k ↦ ξ k ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)
  have hterm (i j : Fin n) :
      |(A i j - A' i j) * ξ i * ξ j| ≤ |A i j - A' i j| * ∑ k, ξ k ^ 2 := by
    rw [mul_assoc, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 := hS i
    have h2 := hS j
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (ξ i + ξ j), sq_nonneg (ξ i - ξ j)]
  have hdiff : principalEnergy A ξ - principalEnergy A' ξ =
      ∑ i, ∑ j, (A i j - A' i j) * ξ i * ξ j := by
    simp only [principalEnergy, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hdiff, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ hterm i j)

variable {I : Type*} [Fintype I] {a : Fin n → Fin n → (I → ℝ) → ℝ}
  {f : I → Fin n → (I → ℝ) → ℝ} {v : ℝ^n → I → ℝ} {Ω : Set (ℝ^n)}

/-- **The local setting exists.** Let `v` be a smooth solution of the autonomous diagonal system
on an open set `Ω`, with coefficients and forcing analytic at the values of `v` and with the
matrix `a(v(x))` elliptic at every `x ∈ Ω`. Then every point of `Ω` is the centre of a ball on
which the hypotheses `SolutionOnBall` hold: Cauchy estimates bound the derivatives of the
coefficients near `v x₀`, and ellipticity persists near `x₀` by continuity. -/
theorem exists_solutionOnBall (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ∀ x ∈ Ω, ∀ i j, AnalyticAt ℝ (a i j) (v x))
    (hf : ∀ x ∈ Ω, ∀ l i, AnalyticAt ℝ (f l i) (v x))
    (hell : ∀ x ∈ Ω, ∃ lam > 0, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, ξ i ^ 2 ≤ principalEnergy (fun i j ↦ a i j (v x)) ξ)
    (heq : ∀ x ∈ Ω, ∀ l, ∑ i, (∂[i] (flux a f v l i)) x = 0) {x₀ : ℝ^n} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : Set (ℝ^n)) (R lam Lam C K : ℝ), U ⊆ Ω ∧ SolutionOnBall a f v U x₀ R lam Lam C K := by
  classical
  -- Cauchy estimates for the finite family of coefficients and forcing terms
  have hg : ∀ s : (Fin n × Fin n) ⊕ (I × Fin n),
      AnalyticAt ℝ (Sum.elim (fun p : Fin n × Fin n ↦ a p.1 p.2)
        (fun p : I × Fin n ↦ f p.1 p.2) s) (v x₀) := by
    rintro (p | p)
    · exact ha x₀ hx₀ p.1 p.2
    · exact hf x₀ hx₀ p.1 p.2
  obtain ⟨r, hr, C, K, hC, hK, hbound⟩ := AnalyticAt.exists_norm_iteratedFDeriv_le_family hg
  obtain ⟨lam₀, hlam₀, hlow₀⟩ := hell x₀ hx₀
  -- the neighbourhood where the values of `v` stay in the ball of the estimates
  have hvc : ContinuousOn v Ω := hv.continuousOn
  have hU₁ : IsOpen (Ω ∩ v ⁻¹' ball (v x₀) r) := hvc.isOpen_inter_preimage hΩ isOpen_ball
  have hx₀U : x₀ ∈ Ω ∩ v ⁻¹' ball (v x₀) r := ⟨hx₀, mem_ball_self hr⟩
  -- near `x₀` the coefficients are close to their values at `x₀`
  have hvx : ContinuousAt v x₀ := hvc.continuousAt (hΩ.mem_nhds hx₀)
  have hcont : ContinuousAt (fun x ↦ ∑ i, ∑ j, |a i j (v x) - a i j (v x₀)|) x₀ :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
      ((((ha x₀ hx₀ i j).continuousAt.comp hvx).sub continuousAt_const).abs :
        ContinuousAt (fun x ↦ |a i j (v x) - a i j (v x₀)|) x₀)
  have hsmall : ∀ᶠ x in 𝓝 x₀, ∑ i, ∑ j, |a i j (v x) - a i j (v x₀)| < lam₀ / 2 := by
    refine hcont.eventually_lt continuousAt_const ?_
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    positivity
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Filter.inter_mem (hU₁.mem_nhds hx₀U) hsmall)
  have hsum0 (x : ℝ^n) : 0 ≤ ∑ i, ∑ j, |a i j (v x)| :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hzero (ξ : Fin n → ℝ) : principalEnergy (fun _ _ ↦ (0 : ℝ)) ξ = 0 := by
    simp [principalEnergy]
  refine ⟨Ω ∩ v ⁻¹' ball (v x₀) r, R, lam₀ / 2, (∑ i, ∑ j, |a i j (v x₀)|) + lam₀ / 2, C, K,
    inter_subset_left, ?_⟩
  exact
    { isOpen := hU₁
      closedBall_subset := fun y hy ↦ (hball hy).1
      contDiffOn := hv.mono inter_subset_left
      coeff_contDiffAt := fun y hy i j ↦ (ha y hy.1 i j).contDiffAt
      forcing_contDiffAt := fun y hy l i ↦ (hf y hy.1 l i).contDiffAt
      equation := fun y hy l ↦ heq y hy.1 l
      radius_pos := hR
      lam_pos := by positivity
      Lam_nonneg := add_nonneg (hsum0 x₀) (by positivity)
      lower := fun x hx ξ ↦ by
        have h1 := hlow₀ ξ
        have h2 := abs_le.mp (abs_principalEnergy_sub_le (fun i j ↦ a i j (v x))
          (fun i j ↦ a i j (v x₀)) ξ)
        have h3 : ∑ i, ∑ j, |a i j (v x) - a i j (v x₀)| < lam₀ / 2 := (hball hx).2
        have hS : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
        have h4 := mul_le_mul_of_nonneg_right h3.le hS
        linarith only [h1, h2.1, h4]
      upper := fun x hx ξ ↦ by
        have h2 := abs_le.mp (abs_principalEnergy_sub_le (fun i j ↦ a i j (v x))
          (fun i j ↦ a i j (v x₀)) ξ)
        have h3 : ∑ i, ∑ j, |a i j (v x) - a i j (v x₀)| < lam₀ / 2 := (hball hx).2
        have hS : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
        have h4 := mul_le_mul_of_nonneg_right h3.le hS
        have h5 := abs_le.mp (abs_principalEnergy_sub_le (fun i j ↦ a i j (v x₀))
          (fun _ _ ↦ (0 : ℝ)) ξ)
        simp only [sub_zero, hzero] at h5
        linarith only [h2.2, h4, h5.2]
      C_nonneg := hC
      K_nonneg := hK.le
      coeff_bound := fun x hx i j m ↦ hbound (Sum.inl (i, j)) m (v x) (hball hx).1.2
      forcing_bound := fun x hx l i m ↦ hbound (Sum.inr (l, i)) m (v x) (hball hx).1.2 }

/-- **Factorial derivative bounds for smooth solutions.** In the setting of
`analyticOnNhd_of_autonomous_system`, every point `x₀ ∈ Ω` has a ball inside `Ω` on which
`|Dⁱv| ≤ i! M K₀ⁱ` in the family norm, for all `i`. -/
theorem exists_familyNorm_le_of_autonomous_system (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ∀ x ∈ Ω, ∀ i j, AnalyticAt ℝ (a i j) (v x))
    (hf : ∀ x ∈ Ω, ∀ l i, AnalyticAt ℝ (f l i) (v x))
    (hell : ∀ x ∈ Ω, ∃ lam > 0, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, ξ i ^ 2 ≤ principalEnergy (fun i j ↦ a i j (v x)) ξ)
    (heq : ∀ x ∈ Ω, ∀ l, ∑ i, (∂[i] (flux a f v l i)) x = 0) {x₀ : ℝ^n} (hx₀ : x₀ ∈ Ω) :
    ∃ r > 0, ∃ M K₀ : ℝ, 0 < M ∧ 0 < K₀ ∧ ball x₀ r ⊆ Ω ∧
      ∀ i, ∀ x ∈ ball x₀ r, familyNorm i v x ≤ i.factorial * M * K₀ ^ i := by
  obtain ⟨U, R, lam, Lam, C, K, hUΩ, hS⟩ := exists_solutionOnBall hΩ hv ha hf hell heq hx₀
  have hR := hS.radius_pos
  obtain ⟨M, K₀, hM, hK₀, hb⟩ := hS.exists_familyNorm_le
  obtain ⟨S, hS0, hSb⟩ := hS.exists_familyNorm_bound 0
  have hsub : ball x₀ (R / 2) ⊆ closedBall x₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  refine ⟨R / 2, by positivity, M + S, K₀, by positivity, hK₀,
    (hsub.trans hS.closedBall_subset).trans hUΩ, fun i x hx ↦ ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using (hSb x (hsub hx)).trans (le_add_of_nonneg_left hM.le)
  · refine (hb i hi x hx).trans ?_
    have h1 : (0 : ℝ) ≤ i.factorial := Nat.cast_nonneg _
    have h2 : 0 ≤ K₀ ^ i := pow_nonneg hK₀.le i
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) h1) h2

/-- **Analytic regularity for the autonomous diagonal system.** Let `Ω ⊆ ℝ^n` be open and let
`v = (v_l)` be a smooth family on `Ω` with
`∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ(v) ∂ⱼ v_l - f_{l i}(v)) = 0` at every point of `Ω`. If the coefficients `aᵢⱼ` and
the forcing `f_{l i}` are real-analytic at the values of `v`, and the matrix `a(v(x))` has
quadratic form at least `λ(x) |ξ|²` with `λ(x) > 0` at every `x ∈ Ω`, then `v` is real-analytic
on `Ω`. All dimensions and all finite families; no symmetry of the matrix and no uniformity of
the ellipticity is assumed. The derivatives of `v` of order `i` are bounded by `i! M K₀ⁱ` near
each point by the maximum principle (`SolutionOnBall.exists_familyNorm_le`), and such bounds
give a convergent Taylor series. -/
theorem analyticOnNhd_of_autonomous_system (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ∀ x ∈ Ω, ∀ i j, AnalyticAt ℝ (a i j) (v x))
    (hf : ∀ x ∈ Ω, ∀ l i, AnalyticAt ℝ (f l i) (v x))
    (hell : ∀ x ∈ Ω, ∃ lam > 0, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, ξ i ^ 2 ≤ principalEnergy (fun i j ↦ a i j (v x)) ξ)
    (heq : ∀ x ∈ Ω, ∀ l, ∑ i, (∂[i] (flux a f v l i)) x = 0) : AnalyticOnNhd ℝ v Ω := by
  intro x₀ hx₀
  obtain ⟨U, R, lam, Lam, C, K, -, hS⟩ := exists_solutionOnBall hΩ hv ha hf hell heq hx₀
  exact hS.analyticAt

end PDE.Elliptic.Regularity.Analytic
