/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.TransportConeGronwall
public import PDE.Hyperbolic.HamiltonJacobi.Weak.ResidualConvergence

/-!
# Cone comparison for the mollified Hamilton–Jacobi drift

The smooth cone comparison applies to the mollifications. Its speed and
divergence constants are derived from Lipschitz continuity, spatial semiconcavity,
and the `C²` convex Hamiltonian. The only source term is the transport
residual, whose local integral tends to zero for cutoffs of AE solutions.
This is step 6 of the proof of Theorem 7 in Evans, §3.3.3(b), before the limit: the cone
speed is the bound (47) on `DH` and the energy obeys the Grönwall inequality (48).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, step 6, equations (47)
  and (48).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Metric Set
open scoped Convolution RealInnerProductSpace

variable {n : ℕ} {μ : Measure (ℝ^n × ℝ)} [μ.IsAddHaarMeasure]

/-- Swapping the spacetime coordinates identifies the joint transport derivative
with the time derivative plus the spatial gradient pairing. -/
theorem fderiv_swap_transport {f : ℝ^n × ℝ → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (x b : ℝ^n) :
    fderiv ℝ (fun z : ℝ × ℝ^n ↦ f (z.2, z.1)) (t, x) (1, b) =
      fderiv ℝ f (x, t) (0, 1) + ⟪b, ∇ (fun y ↦ f (y, t)) x⟫ := by
  have hswap : HasFDerivAt (fun z : ℝ × ℝ^n ↦ f (z.2, z.1)) ((fderiv ℝ f (x, t)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ^n)).prod (ContinuousLinearMap.fst ℝ ℝ (ℝ^n)))) (t, x) :=
    (hf (x, t)).hasFDerivAt.comp (t, x) (hasFDerivAt_snd.prodMk hasFDerivAt_fst)
  rw [hswap.fderiv, inner_gradient_right, fderiv_spaceSlice (hf (x, t))]
  change fderiv ℝ f (x, t) (b, 1) = fderiv ℝ f (x, t) (0, 1) + fderiv ℝ f (x, t) (b, 0)
  rw [← map_add]
  simp

omit [μ.IsAddHaarMeasure] in
/-- Positive normalized convolution preserves nonnegativity of a forward
nonnegative density, including when the density is unbounded. -/
theorem mollified_forwardExtension_nonneg {w : ℝ^n × ℝ → ℝ} (hw : ∀ z, 0 ≤ z.2 → 0 ≤ w z)
    (φ : ContDiffBump (0 : ℝ^n × ℝ)) (z : ℝ^n × ℝ) :
    0 ≤ (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w) z :=
  integral_nonneg fun y ↦ mul_nonneg (φ.nonneg_normed y)
    (hw ((z - y).1, max (z - y).2 0) (le_max_right _ _))

/-- Evans's mollified cone comparison with all drift constants derived. The
comparison holds for every forward Lipschitz nonnegative density; for a cutoff
of two AE solutions its displayed source tends to zero on compact time slabs. -/
theorem exists_mollified_cone_comparison [Fact (0 < n)] {H : ℝ^n → ℝ} (hH : ContDiff ℝ 2 H)
    (hconv : ConvexOn ℝ univ H) {u v : ℝ^n × ℝ → ℝ} {Ku Kv : NNReal}
    (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2}) (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) {C : ℝ}
    (hC : 0 ≤ C)
    (hu_semi : ∀ x z t, 0 < t → u (x + z, t) - 2 * u (x, t) + u (x - z, t) ≤
      C * (1 + t⁻¹) * ‖z‖ ^ 2)
    (hv_semi : ∀ x z t, 0 < t → v (x + z, t) - 2 * v (x, t) + v (x - z, t) ≤
      C * (1 + t⁻¹) * ‖z‖ ^ 2) :
    ∃ R C₁ : ℝ, 0 < R ∧ 0 ≤ C₁ ∧
      ∀ (w : ℝ^n × ℝ → ℝ) (Kw : NNReal),
      LipschitzOnWith Kw w {z | 0 ≤ z.2} →
      (∀ z, 0 ≤ z.2 → 0 ≤ w z) →
      ∀ (φ : ContDiffBump (0 : ℝ^n × ℝ)) (c : ℝ^n) (a d T : ℝ),
      2 * φ.rOut < a → d < T → ∀ t ∈ Icc a d,
      PDE.Analysis.ballIntegral n (fun x ↦
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w) (x, t))
          c (R * (T - t)) ≤
        (PDE.Analysis.ballIntegral n (fun x ↦
          (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w) (x, a))
            c (R * (T - a)) +
          ∫ s in a..d, ∫ x in closedBall c (R * (T - a)),
            ‖mollifiedTransportResidual (μ := μ) H φ u v w (x, s)‖) *
          Real.exp (C₁ * (1 + a⁻¹) * (t - a)) := by
  obtain ⟨R₀, hR₀, _, hRb⟩ :=
    exists_norm_drift_le (μ := μ) (hH.of_le (by norm_num)) hu hv
  obtain ⟨C₁, hC₁, hdiv⟩ :=
    exists_trace_fderiv_mollifiedDrift_le (μ := μ) hH hconv hu hv hC hu_semi hv_semi
  refine ⟨R₀ + 1, C₁, by positivity, hC₁, fun w Kw hw hw0 φ c a d T ha hdT ↦ ?_⟩
  let W := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w
  let b := mollifiedDrift (μ := μ) H φ u v
  have hW : ContDiff ℝ 1 W := φ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed
      (lipschitzWith_forwardExtension hw).continuous.locallyIntegrable
  have hb : ContDiff ℝ 1 b := contDiff_mollifiedDrift hH hu hv φ
  have ha0 : 0 < a := (mul_pos two_pos φ.rOut_pos).trans ha
  have htime (s : ℝ) (hs : s ∈ Icc a d) : 2 * φ.rOut < s := ha.trans_le hs.1
  have htime' (s : ℝ) (hs : s ∈ Icc a d) : φ.rOut < s := by
    have := φ.rOut_pos
    have := htime s hs
    linarith
  have hbound := PDE.Analysis.ballIntegral_shrinking_le_mul_exp
    (R := R₀ + 1) (T := T) (L := (R₀ + 1) * (T - a))
    (w := fun s x ↦ W (x, s)) (b := fun z : ℝ × ℝ^n ↦ b (z.2, z.1))
    (hW.comp (contDiff_snd.prodMk contDiff_fst)) (hb.comp (contDiff_snd.prodMk contDiff_fst)) c
    (show 0 ≤ C₁ * (1 + a⁻¹) by positivity)
    (fun s hs ↦ mul_pos (by positivity) (sub_pos.mpr (hs.2.trans_lt hdT)))
    (fun s hs ↦ mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 T) (by positivity))
    (fun s _ x _ ↦ mollified_forwardExtension_nonneg hw0 φ (x, s) (μ := μ))
    (fun s hs x _ ↦ (hRb φ x s (htime' s hs)).trans (by linarith)) (fun s hs x _ ↦ ?_)
  · intro t ht
    have h := hbound t ht
    simpa only [Function.uncurry_def, fderiv_swap_transport (hW.differentiable one_ne_zero),
      mollifiedTransportResidual, W, b] using h
  · have hbs : DifferentiableAt ℝ (fun y ↦ b (y, s)) x :=
      (hb.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero x
    change ∇· (fun y ↦ b (y, s)) x ≤ _
    rw [PDE.Analysis.divergence_eq_trace_fderiv hbs]
    exact (hdiv φ s (htime s hs) x).trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (inv_anti₀ ha0 hs.1)) hC₁)

end HamiltonJacobi.Weak
