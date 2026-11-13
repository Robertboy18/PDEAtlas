/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Weak.ConeLimit

/-!
# Cone comparison for an almost-everywhere transported density

The mollified cone comparison passes to the original Lipschitz density.
The residual tends to zero in local integral, and the energies converge
at both endpoint times. Thus the integrated Grönwall estimate holds for every
nonnegative AE solution of the transport equation. This is the limit `ε → 0` in step 6 of the
proof of Theorem 7 in Evans, §3.3.3(b), which leads to (48).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, step 6, equation (48).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Filter Set
open scoped Convolution Topology RealInnerProductSpace

variable {n : ℕ}

/-- The cone comparison for any nonnegative forward Lipschitz AE transported
density. The speed and exponential constants depend only on the two Lipschitz
semiconcave inputs and the convex `C²` Hamiltonian. -/
theorem exists_ae_transport_cone_comparison [Fact (0 < n)] {H : ℝ^n → ℝ} (hH : ContDiff ℝ 2 H)
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
      (∀ᵐ z ∂(volume : Measure (ℝ^n × ℝ)).restrict {z | 0 < z.2},
        fderiv ℝ w z (0, 1) + ⟪drift H u v z, ∇ (fun x ↦ w (x, z.2)) z.1⟫ = 0) →
      ∀ (c : ℝ^n) (a d T : ℝ), 0 < a → a ≤ d → d < T → ∀ t ∈ Icc a d,
      PDE.Analysis.ballIntegral n (fun x ↦ w (x, t)) c (R * (T - t)) ≤
        PDE.Analysis.ballIntegral n (fun x ↦ w (x, a)) c (R * (T - a)) *
          Real.exp (C₁ * (1 + a⁻¹) * (t - a)) := by
  obtain ⟨R, C₁, hR, hC₁, hcomp⟩ :=
    exists_mollified_cone_comparison (μ := volume) hH hconv hu hv hC hu_semi hv_semi
  refine ⟨R, C₁, hR, hC₁, fun w Kw hw hw0 heq c a d T ha had hdT t ht ↦ ?_⟩
  let φ : ℕ → ContDiffBump (0 : ℝ^n × ℝ) := fun k ↦
    { rIn := 1 / ((k : ℝ) + 1)
      rOut := 2 * (1 / ((k : ℝ) + 1))
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith }
  have hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) := by
    simpa only [φ, mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have hratio : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn := Eventually.of_forall fun _ ↦ le_rfl
  have hsmall : ∀ᶠ k in atTop, 2 * (φ k).rOut < a :=
    (show Tendsto (fun k ↦ 2 * (φ k).rOut) atTop (𝓝 0) by
      simpa only [mul_zero] using hφ.const_mul 2).eventually (Iio_mem_nhds ha)
  have hleft := tendsto_ballIntegral_mollified_forwardExtension hw hφ c
    (R * (T - t)) (ha.le.trans ht.1)
  have hinitial := tendsto_ballIntegral_mollified_forwardExtension hw hφ c (R * (T - a)) ha.le
  have hsource := tendsto_integral_ball_mollifiedTransportResidual hH hu hv hw heq
    hφ hratio c (R * (T - a)) ha had
  have hright := (hinitial.add hsource).mul_const (Real.exp (C₁ * (1 + a⁻¹) * (t - a)))
  have hle := le_of_tendsto_of_tendsto hleft hright
    (hsmall.mono fun k hk ↦ hcomp w Kw hw hw0 (φ k) c a d T hk hdT t ht)
  simpa only [add_zero] using hle

end HamiltonJacobi.Weak
