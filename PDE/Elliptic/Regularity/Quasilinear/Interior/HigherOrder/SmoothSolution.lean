/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.ClassicalEquation
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.AutonomousSmooth
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.NonlinearFlux

/-!
# Smooth representatives for smooth uniformly convex densities

For an autonomous homogeneous Euler–Lagrange equation, the De Giorgi–Schauder
argument of `ClassicalSolution` constructs a C² representative from an H¹
weak solution. If the density is smooth, the argument continues: its first
derivatives satisfy an elliptic system with the Hessian as principal matrix.
Adjoining derivatives repeatedly gives smoothness.

This is the smoothness remark following the regularity argument in Evans
§8.3.2. The bounded, uniformly positive Hessian is assumed on the density;
no bounds on all its higher derivatives, regularity of the weak gradient,
or smoothness of the domain boundary are assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Elliptic.Regularity.Quasilinear

open Bootstrap

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}

/-- The nonlinear bootstrap improves a given C² representative to smoothness.
Its differentiated equations are derived from the local weak flux identity. -/
theorem contDiffOn_infty_of_gradientDensity
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) {L : ℝ^n → ℝ} (hL : ContDiff ℝ (⊤ : ℕ∞) L)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpos : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hQ : HasZeroWeakDivergenceOn Ω (fun i x ↦ ∇ L (∇ v x) i)) :
    ContDiffOn ℝ (⊤ : ℕ∞) v Ω := by
  have hL2 : ContDiff ℝ 2 L := hL.of_le (by simp)
  have hA := contDiff_infty_gradient hL
  let g : ℝ^n → Fin n → ℝ := fun x i ↦ ∇ v x i
  let a (i j : Fin n) (p : Fin n → ℝ) :=
    jacobianMatrix (∇ L) (WithLp.toLp 2 p) i j
  have htuple (x : ℝ^n) : WithLp.toLp 2 (g x) = ∇ v x := rfl
  have hg : ContDiffOn ℝ 1 g Ω := contDiffOn_pi.mpr fun i x hx ↦ by
    simpa only [g, gradient_apply_eq_partialDeriv, Nat.cast_one] using
      (contDiffAt_partialDeriv 1 (hv.contDiffAt (hΩ.mem_nhds hx)) i).contDiffWithinAt
  have hab (x : ℝ^n) (_hx : x ∈ Ω) (i j : Fin n) : ‖a i j (g x)‖ ≤ Λ := by
    change ‖jacobianMatrix (∇ L) (∇ v x) i j‖ ≤ Λ
    rw [jacobianMatrix_apply_eq_fderiv (hA.differentiable (by simp) _)]
    have hLip := lipschitzWith_gradient_of_hessian_bound hL2 hbound
    exact (PiLp.norm_apply_le _ i).trans
      (((fderiv ℝ (∇ L) (∇ v x)).le_opNorm _).trans
        (by simpa using norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := ∇ v x)))
  have hae (x : ℝ^n) (_hx : x ∈ Ω) (ξ : Fin n → ℝ) :
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j (g x) * ξ j * ξ i := by
    let z : ℝ^n := WithLp.toLp 2 ξ
    have h := hpos (∇ v x) z
    rw [← inner_fderiv_gradient_at hL2.contDiffAt] at h
    have he :
        ⟪fderiv ℝ (∇ L) (∇ v x) z, z⟫ =
          ∑ i, ∑ j, a i j (g x) * ξ j * ξ i := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← sum_jacobianMatrix_mul (hA.differentiable (by simp) _) z i]
      simp only [RCLike.inner_apply, RCLike.conj_to_real, z, a, htuple, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [he, EuclideanSpace.real_norm_sq_eq z] at h
    simpa only [z, pow_two] using h
  have heq (k : Fin n) : HasZeroWeakDivergenceOn Ω (fun i x ↦
      (∑ j, a i j (g x) * (∂[j] (fun y ↦ g y k)) x) - 0) := by
    change HasZeroWeakDivergenceOn Ω (fun i x ↦
      (∑ j, jacobianMatrix (∇ L) (∇ v x) i j * (∂[j] (fun y ↦ ∇ v y k)) x) - 0)
    simpa only [gradient_apply_eq_partialDeriv, sub_zero] using
      hasZeroWeakDivergenceOn_linearized_gradientDensity hΩ hL2 hv hQ k
  have hgs := contDiffOn_infty_of_autonomous_system hq2 hq hΩ
    (contDiff_infty_hessianEntry hL) (fun _ _ ↦ contDiff_const) hg
    hθ Λ.coe_nonneg hab hae heq
  apply (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mpr
  refine ⟨hv.differentiableOn (by norm_num), ?_⟩
  rw [show fderiv ℝ v = fun x ↦ ∑ i, (∂[i] v) x • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) from
    funext fun x ↦ fderiv_eq_sum_partialDeriv_smul_proj v x]
  refine ContDiffOn.sum fun i _ ↦ ?_
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) (∂[i] v) Ω := by
    simpa only [g, gradient_apply_eq_partialDeriv] using contDiffOn_pi.mp hgs i
  exact hi.smul contDiffOn_const

/-- Raw H¹ weak solutions for a smooth uniformly convex density have smooth
representatives, with the same weak gradient and the pointwise equation.
The auxiliary Sobolev exponent is the one used by the C² construction. -/
theorem exists_smooth_solution_of_gradientDensity_of_exponent
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ (⊤ : ℕ∞) L) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpos : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u : H¹(Ω))
    (hu : ∀ w : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (w : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧
      v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u ∧
      (∇ v : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] ∇ u ∧
      ∀ x ∈ Ω, -(PDE.divergence (fun y ↦ ∇ L (∇ v y)) x) = 0 := by
  obtain ⟨v, hv, hva, hgrad, heq⟩ := exists_classical_solution_of_gradientDensity
    hq2 hq hΩ hb (hL.of_le (by simp)) hbound hθ hpos u hu
  exact ⟨v, contDiffOn_infty_of_gradientDensity hq2 hq hΩ hL hbound hθ hpos hv
    (hasZeroWeakDivergenceOn_gradientDensity hb (hL.of_le (by simp)) hbound u hu hgrad),
    hva, hgrad, heq⟩

/-- Smoothness of the weak solution, with no auxiliary exponent
hypothesis. In dimension above two the Sobolev exponent is `2n/(n-2)`;
in dimensions one and two the local estimate uses exponent four. -/
theorem exists_smooth_solution_of_gradientDensity
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ (⊤ : ℕ∞) L) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpos : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u : H¹(Ω))
    (hu : ∀ w : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (w : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧
      v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u ∧
      (∇ v : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] ∇ u ∧
      ∀ x ∈ Ω, -(PDE.divergence (fun y ↦ ∇ L (∇ v y)) x) = 0 := by
  have hn : 0 < n := Fact.out
  let q : ℝ≥0 := if 2 < n then Inequalities.pStar n 2 else 4
  have hq : (2 : ℝ≥0) < q := by
    dsimp only [q]
    split_ifs with hdim
    · have hd : (2 : ℝ) < n := by exact_mod_cast hdim
      change (2 : ℝ) < (Inequalities.pStar n 2 : ℝ)
      rw [Inequalities.pStar_coe hn (by simpa using hd)]
      norm_num
      apply (lt_div_iff₀ (by linarith : 0 < (n : ℝ) - 2)).mpr
      nlinarith
    · norm_num
  exact exists_smooth_solution_of_gradientDensity_of_exponent
    (q := (q : ℝ≥0∞)) (by exact_mod_cast hq) le_rfl hΩ hb hL hbound hθ hpos u hu

end PDE.Elliptic.Regularity.Quasilinear
