/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Potential.Classical
public import PDE.Spaces.Sobolev.Calculus.Potential.Mollification
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.ClosedGradient
public import PDE.Spaces.Sobolev.Approximation.Mollification.L2Operator

/-!
# Weak scalar potentials on interior balls

Mollification makes a weakly closed `L²` field classically closed on smaller
balls. The classical Poincaré lemma supplies a potential there. Strong `L²`
convergence and the derived closed range of the gradient then give a weak
potential for the original field. No weak derivative of the field itself is
assumed to be represented by a function.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace Metric Filter
open scoped ENNReal Distributions Topology Sobolev

namespace SobolevSpace

open GraphSpace Approximation

variable {n : ℕ} [Fact (0 < n)]

/-- Globally `L²` components whose distributional derivatives commute on a ball
are the weak gradient of a scalar `H¹` function on every smaller ball.
The global integrability is used only to mollify representatives; the equation
is required only on the outer ball. -/
theorem exists_wkpSpaceOn_gradient_eq_on_ball_of_weakly_closed
    (a : ℝ^n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (f : Fin n → Lp ℝ 2 (volume : Measure (ℝ^n)))
    (hweak : ∀ i j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ ball a R →
      (∫ y, f j y * (∂[i] (φ : ℝ^n → ℝ)) y) = ∫ y, f i y * (∂[j] (φ : ℝ^n → ℝ)) y) :
    ∃ u : W^{1,2}(ball a r),
      ∀ᵐ x ∂domainMeasure n (ball a r), ∀ i : Fin n,
        ∇ u x i = f i x := by
  let δ := (R - r) / 4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hrR) (by norm_num)
  let b : ContDiffBump (0 : ℝ^n) :=
    { rIn := 1
      rOut := 2
      rIn_pos := zero_lt_one
      rIn_lt_rOut := one_lt_two }
  let μ : Mollifier n :=
    { ρ := b.normed volume
      smooth := b.contDiff_normed
      compactSupport := b.hasCompactSupport_normed
      nonneg := b.nonneg_normed
      integral_one := b.integral_normed }
  have hμ : tsupport μ.ρ ⊆ closedBall 0 2 := by
    simpa only [μ, b] using (b.tsupport_normed_eq (μ := volume)).subset
  let ε (k : ℕ) : ℝ := δ / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := div_pos hδ (by positivity)
  have hεle (k : ℕ) : ε k ≤ δ :=
    div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_const_nhds (x := δ)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let M (k : ℕ) (x : ℝ^n) : ℝ^n :=
    WithLp.toLp 2 fun i ↦ mollify μ (ε k) (f i) x
  have hM (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (M k) :=
    (PiLp.continuousLinearEquiv 2 ℝ _).symm.contDiff.comp
      (contDiff_pi.mpr fun i ↦
        mollify_contDiff_of_pos μ (hε k) (f i)
          ((Lp.memLp (f i)).locallyIntegrable (by norm_num)))
  have hMclosed (k : ℕ) (x : ℝ^n) (hx : x ∈ ball a (r + δ)) (i j : Fin n) :
      (∂[i] (fun y ↦ M k y j)) x =
        (∂[j] (fun y ↦ M k y i)) x := by
    refine partialDeriv_mollify_eq_of_weakly_closed i j μ (hε k) hμ
      ((Lp.memLp (f j)).locallyIntegrable (by norm_num))
      ((Lp.memLp (f i)).locallyIntegrable (by norm_num)) (hweak i j) x fun y hy ↦ ?_
    have hy' : dist y x ≤ ε k * 2 := hy
    have hx' : dist x a < r + δ := hx
    have hδeq : 4 * δ = R - r := by dsimp only [δ]; ring
    change dist y a < R
    linarith [hεle k, dist_triangle y x a]
  let S : Lp ℝ 2 (volume : Measure (ℝ^n)) →L[ℝ]
      Lp ℝ 2 (domainMeasure n (ball a r)) :=
    Lp.restrictionCLMOfLE Measure.restrict_le_self
  let F (k : ℕ) : Lp (ℝ^n) 2 (domainMeasure n (ball a r)) :=
    Lp.euclideanTuple fun i ↦ S (mollifierL2CLM μ (hε k) (f i))
  let F₀ : Lp (ℝ^n) 2 (domainMeasure n (ball a r)) :=
    Lp.euclideanTuple fun i ↦ S (f i)
  have hF (k : ℕ) : (F k : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (ball a r)] M k := by
    have hrows : ∀ᵐ x ∂domainMeasure n (ball a r), ∀ i : Fin n,
        S (mollifierL2CLM μ (hε k) (f i)) x = mollify μ (ε k) (f i) x :=
      ae_all_iff.mpr fun i ↦ (Lp.restrictionCLMOfLE_apply_ae Measure.restrict_le_self _).trans
        (ae_restrict_of_ae (PDE.Analysis.convolutionL2CLM_ae_eq
          (scaled μ (ε k)) (integrable_scaled μ (hε k)) (f i)))
    filter_upwards [Lp.euclideanTuple_apply_ae
      (fun i ↦ S (mollifierL2CLM μ (hε k) (f i))), hrows] with x hx hy
    exact PiLp.ext fun i ↦ (hx i).trans (hy i)
  have hFrange (k : ℕ) : F k ∈ Set.range
      (fun u : W^{1,2}(ball a r) ↦ ∇ u) := by
    have hcl : closure (ball a r) ⊆ ball a (r + δ) := by
      rw [closure_ball a hr.ne']
      exact closedBall_subset_ball (by linarith)
    obtain ⟨u, hu⟩ := exists_wkpSpaceOn_gradient_eq_of_partialDeriv_comm
      isOpen_ball (convex_ball a (r + δ)) ((hM k).differentiable (by simp)).differentiableOn
      (hMclosed k) isOpen_ball
      (isCompact_closedBall a r |>.of_isClosed_subset isClosed_closure
        (closure_minimal ball_subset_closedBall isClosed_closedBall)) hcl 2
    exact ⟨u, Lp.ext (hu.trans (hF k).symm)⟩
  have hlim : Tendsto F atTop (𝓝 F₀) :=
    Lp.euclideanTuple.continuous.tendsto _ |>.comp
      (tendsto_pi_nhds.mpr fun i ↦
        S.continuous.tendsto _ |>.comp (tendsto_mollifierL2CLM μ ε hε hε0 (f i)))
  obtain ⟨u, hu⟩ :=
    (isClosed_range_wkpGradientCLM_ball (p := 2) a hr).mem_of_tendsto hlim
      (Eventually.of_forall hFrange)
  dsimp only at hu
  refine ⟨u, ?_⟩
  have hrows : ∀ᵐ x ∂domainMeasure n (ball a r), ∀ i : Fin n, S (f i) x = f i x :=
    ae_all_iff.mpr fun i ↦ Lp.restrictionCLMOfLE_apply_ae Measure.restrict_le_self (f i)
  rw [hu]
  filter_upwards [Lp.euclideanTuple_apply_ae (fun i ↦ S (f i)), hrows] with x hx hy
  exact fun i ↦ (hx i).trans (hy i)

/-- The local version needs L² integrability only on the outer ball. Zero
extension is an internal construction used for mollification, and imposes no
boundary condition on the prescribed field. -/
theorem exists_wkpSpaceOn_gradient_eq_on_ball_of_memLp_weakly_closed
    (a : ℝ^n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict (ball a R)))
    (hweak : ∀ i j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ ball a R →
      (∫ y in ball a R, f j y * (∂[i] (φ : ℝ^n → ℝ)) y) =
        ∫ y in ball a R, f i y * (∂[j] (φ : ℝ^n → ℝ)) y) :
    ∃ u : W^{1,2}(ball a r),
      ∀ᵐ x ∂domainMeasure n (ball a r), ∀ i : Fin n,
        ∇ u x i = f i x := by
  have hzero (i : Fin n) : MemLp ((ball a R).indicator (f i)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr (hf i)
  let F (i : Fin n) : Lp ℝ 2 (volume : Measure (ℝ^n)) :=
    (hzero i).toLp ((ball a R).indicator (f i))
  have hpair (i : Fin n) (v : ℝ^n → ℝ) :
      (∫ x, F i x * v x) = ∫ x in ball a R, f i x * v x := by
    rw [← integral_indicator measurableSet_ball]
    exact integral_congr_ae (((hzero i).coeFn_toLp.mul Filter.EventuallyEq.rfl).trans
      (ae_of_all _ fun x ↦ (indicator_mul_left _ _ _).symm))
  obtain ⟨u, hu⟩ := exists_wkpSpaceOn_gradient_eq_on_ball_of_weakly_closed a hr hrR F
    (fun i j φ hφ ↦ by simpa only [hpair] using hweak i j φ hφ)
  have hF : ∀ᵐ x ∂domainMeasure n (ball a r), ∀ i : Fin n, F i x = f i x := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (ae_all_iff.mpr fun i ↦ (hzero i).coeFn_toLp)] with x hx heq
    intro i
    exact (heq i).trans (Set.indicator_of_mem (ball_subset_ball hrR.le hx) _)
  exact ⟨u, by filter_upwards [hu, hF] with x hx hy using fun i ↦ (hx i).trans (hy i)⟩

end SobolevSpace
