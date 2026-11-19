/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Estimates.Scaling
public import PDE.Analysis.Calculus.Affine.MixedDerivative
import Mathlib.Analysis.Calculus.TangentCone.Prod
import CAS.ExactTactic

/-!
# Mixed interior estimates with parabolic weights

The normalized extension is pulled back to physical coordinates. It agrees
with the field on a relative neighborhood, which identifies the derivatives
within the cylinder at the terminal time. The multilinear chain rule
then gives the exact exponent `k+2l+n+2`.
-/

@[expose] public section

open PDE (laplacian spaceTimeMixedFDerivWithin)

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace HeatEquation

/-- All mixed derivatives within the closed half cylinder satisfy the local
L1 estimate, with a constant independent of every geometric and solution
parameter. The hypotheses are continuous C²,¹ jets and the heat equation on
the closed time slab. -/
theorem exists_norm_spaceTimeMixedFDerivWithin_on_Icc_le (n k l : ℕ) :
    ∃ C > 0, ∀ (Ω : Set (ℝ^n)) (u : ℝ^n → ℝ → ℝ)
      (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ)
      (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ)
      (Dt : ℝ^n × ℝ → ℝ) (x : ℝ^n) (t r : ℝ),
      0 < r → IsOpen Ω → closedBall x r ⊆ Ω →
      ContinuousOn u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t) →
      ContinuousOn Dx (Ω ×ˢ Icc (t - r ^ 2) t) →
      ContinuousOn Dxx (Ω ×ˢ Icc (t - r ^ 2) t) →
      ContinuousOn Dt (Ω ×ˢ Icc (t - r ^ 2) t) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        HasFDerivAt (fun y ↦ u y p.2) (Dx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        HasFDerivAt (fun y ↦ Dx (y, p.2)) (Dxx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        HasDerivWithinAt (u p.1) (Dt p) (Icc (t - r ^ 2) t) p.2) →
      (∀ p ∈ Ω ×ˢ Icc (t - r ^ 2) t,
        Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0) →
      ∀ p ∈ closedBall x (r / 2) ×ˢ Icc (t - (r / 2) ^ 2) t,
        ‖spaceTimeMixedFDerivWithin k l u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t) p‖ ≤
          C / r ^ (k + 2 * l + n + 2) *
            ∫ q in closedBall x r ×ˢ Icc (t - r ^ 2) t, ‖u q.1 q.2‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_normalized_extension_norm_iteratedFDeriv_le n (l + k)
  refine ⟨C, hC, fun Ω u Dx Dxx Dt x t r hr hΩ hball
    hu hDx hDxx hDt hspace hhessian htime hheat p hp ↦ ?_⟩
  obtain ⟨v, hv, heq, hjet⟩ :=
    hbound Ω u Dx Dxx Dt x t r hr hΩ hball
      hu hDx hDxx hDt hspace hhessian htime hheat
  let N : ℝ^n × ℝ → ℝ^n × ℝ :=
    fun q ↦ (r⁻¹ • (q.1 - x), (r ^ 2)⁻¹ * (q.2 - t))
  let W : ℝ^n × ℝ → ℝ := v ∘ N
  have hN : ContDiff ℝ ∞ N := by fun_prop
  have hW : ContDiff ℝ ∞ W := hv.comp hN
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hhalf : (r / 2) ^ 2 = r ^ 2 / 4 := by cas
  have hundo (q : ℝ^n × ℝ) :
      x + r • (N q).1 = q.1 ∧ t + r ^ 2 * (N q).2 = q.2 :=
    ⟨by simp [N, smul_smul, hr.ne'], by simp [N, hr.ne']⟩
  have hNx : ‖(N p).1‖ ≤ 1 / 2 := by
    change ‖r⁻¹ • (p.1 - x)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), ← div_eq_inv_mul,
      div_le_iff₀ hr]
    have hx : ‖p.1 - x‖ ≤ r / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hp.1
    linarith
  have hNt : -1 / 4 ≤ (N p).2 := by
    change -1 / 4 ≤ (r ^ 2)⁻¹ * (p.2 - t)
    rw [← div_eq_inv_mul, le_div_iff₀ hr2]
    linarith [hp.2.1]
  have hNtop (q : ℝ^n × ℝ) (hq : q.2 ≤ t) : (N q).2 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hr2.le) (sub_nonpos.mpr hq)
  have hpQ : p ∈ Ω ×ˢ Icc (t - r ^ 2) t := by
    refine ⟨hball ((closedBall_subset_closedBall (half_le_self hr.le)) hp.1), ?_, hp.2.2⟩
    linarith [hp.2.1, hr2.le]
  have hnear : N ⁻¹' (ball (0 : ℝ^n) (5 / 8) ×ˢ Ioi (-3 / 8 : ℝ)) ∈ 𝓝 p := by
    refine ((isOpen_ball.prod isOpen_Ioi).preimage hN.continuous).mem_nhds ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using (show ‖(N p).1‖ < 5 / 8 by linarith)
    · exact show -3 / 8 < (N p).2 by linarith
  have hagree (q : ℝ^n × ℝ) (hq : ‖(N q).1‖ < 5 / 8)
      (hs : -3 / 8 < (N q).2) (ht : q.2 ≤ t) : u.uncurry q = W q := by
    change u q.1 q.2 = v (N q)
    simpa only [(hundo q).1, (hundo q).2, Prod.mk.eta] using
      heq (N q).1 (N q).2 hq hs (hNtop q ht)
  have hgerm : u.uncurry =ᶠ[𝓝[Ω ×ˢ Icc (t - r ^ 2) t] p] W := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with q hq hqQ
    exact hagree q (by simpa only [mem_ball, dist_zero_right] using hq.1) hq.2 hqQ.2.2
  have hjets :
      iteratedFDerivWithin ℝ (l + k) u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t) p =
        iteratedFDeriv ℝ (l + k) W p := by
    rw [hgerm.iteratedFDerivWithin_eq (hagree p (by linarith) (by linarith) hp.2.2)]
    exact iteratedFDerivWithin_eq_iteratedFDeriv
      (hΩ.uniqueDiffOn.prod (uniqueDiffOn_Icc (by linarith)))
      ((hW.of_le (by simp)).contDiffAt) hpQ
  have hmixed :
      spaceTimeMixedFDerivWithin k l u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t) p =
        spaceTimeMixedFDerivWithin k l W univ p := by
    unfold spaceTimeMixedFDerivWithin
    rw [hjets, iteratedFDerivWithin_univ]
  rw [hmixed]
  have hscale :
      ‖spaceTimeMixedFDerivWithin k l W univ p‖ ≤
        (((r ^ 2)⁻¹) ^ l * (r⁻¹) ^ k) * ‖iteratedFDeriv ℝ (l + k) v (N p)‖ := by
    have hs := PDE.norm_spaceTimeMixedFDerivWithin_comp_prod_affine_le
      k l hv x t r⁻¹ (r ^ (2 : ℕ))⁻¹ p
    rwa [abs_of_pos (inv_pos.mpr hr2), abs_of_pos (inv_pos.mpr hr)] at hs
  refine hscale.trans ((mul_le_mul_of_nonneg_left (hjet (N p)) (by positivity)).trans_eq ?_)
  have hfactor :
      (((r ^ 2)⁻¹) ^ l * (r⁻¹) ^ k) = (r ^ (k + 2 * l))⁻¹ := by
    rw [inv_pow, ← pow_mul, inv_pow, ← mul_inv, ← pow_add, add_comm]
  rw [hfactor, show k + 2 * l + n + 2 = (k + 2 * l) + (n + 2) by omega]
  simp only [div_eq_mul_inv, pow_add, mul_inv]
  ac_rfl

end HeatEquation
