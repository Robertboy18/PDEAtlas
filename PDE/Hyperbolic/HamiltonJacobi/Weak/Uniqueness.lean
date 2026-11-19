/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Weak.Cutoff
public import PDE.Hyperbolic.HamiltonJacobi.Weak.TransportComparison
import CAS.ExactTactic

/-!
# Uniqueness of semiconcave weak Hamilton–Jacobi solutions

We prove the uniqueness assertion of Evans, §3.3.3(b), Theorem 7, for forward spacetime
Lipschitz functions that solve the equation almost everywhere at positive times. Each solution
has a semiconcavity bound `C * (1 + 1/t)`, condition (c) of Evans's definition of weak solution.
The Hamiltonian is convex and `C²`. Evans also assumes the superlinear growth in (19); we do not
need it, and the solutions and their common initial data may be unbounded.

## Main results

* `eq_of_ae_solution_of_semiconcave_of_initial_eq`: two such solutions with the same initial
  values agree at every nonnegative time.

## How it works

We follow Evans's proof. The cone comparison
(`PDE.Hyperbolic.HamiltonJacobi.Weak.TransportComparison`) comes from smoothing both the drift
and the transported density, applying Reynolds transport and Grönwall, and passing to the limit
(steps 3-6 of the proof). The transported density is a smooth cutoff of the difference that
vanishes where `|u - v| ≤ ε (Lip u + Lip v + 1)`, so it vanishes at the time `ε` (step 7). Its
integral over a ball around `x` at time `t` therefore vanishes, which gives
`|u - v| < 2 ε (Lip u + Lip v + 1)` at `(x, t)`. Letting `ε → 0` proves equality.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), definition of weak solution (38) and Theorem 7
  with its proof.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Metric Filter Set
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

/-- Two forward Lipschitz AE solutions of a convex `C²` Hamilton–Jacobi equation
with Evans's spatial semiconcavity and the same initial values agree everywhere
at nonnegative times. -/
theorem eq_of_ae_solution_of_semiconcave_of_initial_eq [Fact (0 < n)] {H : ℝ^n → ℝ}
    (hH : ContDiff ℝ 2 H) (hconv : ConvexOn ℝ univ H) {u v : ℝ^n × ℝ → ℝ} {Ku Kv : NNReal}
    (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2}) (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2})
    (hu_eq : ∀ᵐ z ∂(volume : Measure (ℝ^n × ℝ)).restrict positiveTimeDomain,
      fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) = 0)
    (hv_eq : ∀ᵐ z ∂(volume : Measure (ℝ^n × ℝ)).restrict positiveTimeDomain,
      fderiv ℝ v z (0, 1) + H (∇ (fun x ↦ v (x, z.2)) z.1) = 0)
    {Cu Cv : ℝ} (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (hu_semi : ∀ x z t, 0 < t → u (x + z, t) - 2 * u (x, t) + u (x - z, t) ≤
      Cu * (1 + t⁻¹) * ‖z‖ ^ 2)
    (hv_semi : ∀ x z t, 0 < t → v (x + z, t) - 2 * v (x, t) + v (x - z, t) ≤
      Cv * (1 + t⁻¹) * ‖z‖ ^ 2)
    (hinit : ∀ x, u (x, 0) = v (x, 0)) :
    ∀ x t, 0 ≤ t → u (x, t) = v (x, t) := by
  have hH' : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  have hu_bound (x z : ℝ^n) (t : ℝ) (ht : 0 < t) : u (x + z, t) - 2 * u (x, t) + u (x - z, t) ≤
        (Cu + Cv) * (1 + t⁻¹) * ‖z‖ ^ 2 :=
    (hu_semi x z t ht).trans (by gcongr; linarith)
  have hv_bound (x z : ℝ^n) (t : ℝ) (ht : 0 < t) : v (x + z, t) - 2 * v (x, t) + v (x - z, t) ≤
        (Cu + Cv) * (1 + t⁻¹) * ‖z‖ ^ 2 :=
    (hv_semi x z t ht).trans (by gcongr; linarith)
  obtain ⟨R, C₁, hR, _, hcomp⟩ :=
    exists_ae_transport_cone_comparison hH hconv hu hv (add_nonneg hCu hCv) hu_bound hv_bound
  intro x t ht
  rcases ht.eq_or_lt with ht | ht
  · simpa only [← ht] using hinit x
  have hbound (ε : ℝ) (hε : 0 < ε) (hεt : ε ≤ t) :
      |u (x, t) - v (x, t)| < 2 * (ε * ((Ku : ℝ) + (Kv : ℝ) + 1)) := by
    have ha : 0 < ε * ((Ku : ℝ) + (Kv : ℝ) + 1) := by positivity
    obtain ⟨χ, Kχ, hχsmooth, hχLip, hχnonneg, hχzero, hχsmall⟩ := exists_smooth_difference_cutoff ha
    let w : ℝ^n × ℝ → ℝ := fun z ↦ χ (u z - v z)
    have hw : LipschitzOnWith (Kχ * (Ku + Kv)) w {z | 0 ≤ z.2} :=
      hχLip.comp_lipschitzOnWith (hu.sub hv)
    have hw0 (z : ℝ^n × ℝ) (_ : 0 ≤ z.2) : 0 ≤ w z := hχnonneg _
    have heq : ∀ᵐ z ∂(volume : Measure (ℝ^n × ℝ)).restrict {z | 0 < z.2}, fderiv ℝ w z (0, 1) +
          ⟪drift H u v z, ∇ (fun y ↦ w (y, z.2)) z.1⟫ = 0 := by
      filter_upwards [ae_transport_comp_sub_eq_zero (μ := volume) hH' hu hv hu_eq hv_eq
        (hχsmooth.differentiable (by simp))] with z hz
      simpa only [w, averagedFDeriv_eq_inner_integral_gradient hH', drift] using hz
    have hinitial : (fun y : ℝ^n ↦ w (y, ε)) = 0 := funext fun y ↦
      hχzero _ ((abs_sub_le_of_initial_eq hu hv hinit y hε.le).trans (by linarith))
    have he : PDE.Analysis.ballIntegral n (fun y ↦ w (y, t)) x R ≤ 0 := by
      have hc := hcomp w _ hw hw0 heq x ε t (t + 1) hε hεt (by linarith) t ⟨hεt, le_rfl⟩
      simpa only [show t + 1 - t = 1 by cas, mul_one, hinitial,
        PDE.Analysis.ballIntegral, Pi.zero_apply, integral_zero, integral_zero', zero_mul] using hc
    have hcont : Continuous (fun y : ℝ^n ↦ w (y, t)) := by
      simpa only [forwardExtension, max_eq_left ht.le, Function.comp_def, id_eq] using
        (lipschitzWith_forwardExtension hw).continuous.comp
          (continuous_id.prodMk (continuous_const (y := t)))
    have hi : IntegrableOn (fun y ↦ w (y, t)) (ball x R) volume :=
      (hcont.continuousOn.integrableOn_compact (isCompact_closedBall x R)).mono_set
        ball_subset_closedBall
    have hezero : (∫ y in ball x R, w (y, t)) = 0 :=
      le_antisymm he (integral_nonneg fun y ↦ hw0 (y, t) ht.le)
    have hae : (fun y ↦ w (y, t)) =ᵐ[volume.restrict (ball x R)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y ↦ hw0 (y, t) ht.le) hi).mp hezero
    have hzero : w (x, t) = 0 := Measure.eqOn_open_of_ae_eq hae isOpen_ball hcont.continuousOn
        continuousOn_const (mem_ball_self hR)
    exact hχsmall _ hzero
  have hseq (k : ℕ) : 0 < t * (1 / ((k : ℝ) + 1)) := by positivity
  have hle (k : ℕ) : t * (1 / ((k : ℝ) + 1)) ≤ t := mul_le_of_le_one_right ht.le
    (div_le_one_of_le₀ (le_add_of_nonneg_left k.cast_nonneg) (by positivity))
  have hlim : Tendsto (fun k : ℕ ↦
      2 * (t * (1 / ((k : ℝ) + 1)) * ((Ku : ℝ) + (Kv : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul t).mul_const _).const_mul 2
  exact sub_eq_zero.mp (abs_nonpos_iff.mp
    (ge_of_tendsto hlim (Eventually.of_forall fun k ↦ (hbound _ (hseq k) (hle k)).le)))

end HamiltonJacobi.Weak
