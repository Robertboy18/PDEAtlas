/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.KernelLaplacian
public import PDE.Analysis.MeasureTheory.SphereSymmetry
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.InteriorRegularity

/-!
# Normalization of the ball Poisson extension

The Poisson kernel of the ball has total mass one: for `0 < r` and `‖x‖ < r`,

`∫_{∂B(0,r)} (r² - ‖x‖²) / (n α(n) r ‖x - y‖ⁿ) dS(y) = 1`.

Equivalently, the Poisson extension of the constant boundary datum `1` is identically `1` on the
open ball. This is the ball analogue of the normalization (34) in step 2 of Evans's proof of
§2.2.4(b), Theorem 14, which Evans states without the calculation.

## Main results

* `poissonBallExtension_one_eq_one_on_ball`: for `0 < r` and every `x ∈ B(0, r)`,
  `poissonBallExtension r (fun _ => 1) x = 1`.

## How it works

We derive the normalization from harmonicity of the Poisson extension
(`laplacian_poissonBallExtension_eq_zero`) in three steps. At the centre the kernel is constant on
the sphere, so the integral reduces to the surface area of `∂B(0, r)` and the value is `1` by the
definition of `unitBallVolume` and the sphere measure. Next, the sphere measure is invariant under
linear isometries, so `u = poissonBallExtension r 1` is invariant under every linear isometry of
`ℝ^n`; reflecting `x` onto `‖x‖ e₀` shows `u` is radial. Finally, a `C²` radial harmonic function
`u(x) = F(‖x‖)` satisfies `(tⁿ⁻¹ F'(t))' = 0` on `(0, r)`, and since `F'(0) = 0` the constant
`tⁿ⁻¹ F'(t)` must vanish, so `F` is constant and equals `F(0) = u(0) = 1`.

## Implementation notes

The invariance step uses the isometry invariance of `Measure.toSphere` from
`PDE.Analysis.MeasureTheory.SphereSymmetry`. The radial ODE is extracted from the coordinate
Laplacian by restricting `u` to the line `t ↦ t • e₀`, where `e₀` is the first standard basis
vector; the hypothesis `Fact (0 < n)` is needed to have such a coordinate at all.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), the normalization (34) in step 2 of the proof of
  Theorem 14, p. 38; §2.2.4(c), Poisson's formula (45) and Poisson's kernel for `B(0, r)`, p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace GreenFunction

open PDE.Analysis
open PotentialTheory
open MeasureTheory
open Set

section PoissonBallNormalization

open scoped BigOperators Pointwise

variable {n : ℕ}

private theorem poissonBallExtension_one_at_zero [Fact (0 < n)] {r : ℝ} (hr : 0 < r) :
    poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ (1 : ℝ)) (0 : ℝ^n) = 1 := by
  classical
  have hdist (ω : Metric.sphere (0 : ℝ^n) 1) : dist (0 : ℝ^n) (0 + r • (ω : ℝ^n)) = r := by
    simpa [dist_comm] using smul_unitSphere_mem_sphere hr.le ω
  have hA : (volume : Measure ℝ^n).toSphere.real univ = n * unitBallVolume n := unitSphereArea_eq n
  have := (unitBallVolume_pos n).ne'
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
  unfold poissonBallExtension sphereIntegral
  simp only [hdist, integral_const, hA, smul_eq_mul, norm_zero, abs_of_pos hr]
  field_simp
  rw [← pow_sub_one_mul (Fact.out : 0 < n).ne' r]
  ring

local notation "Y" => Metric.sphere (0 : ℝ^n) (1 : ℝ)

private theorem poissonBallExtension_one_invariant {r : ℝ}
    (f : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) {x : ℝ^n} :
    poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ (1 : ℝ)) (f x) =
      poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ (1 : ℝ)) x := by
  classical
  unfold poissonBallExtension sphereIntegral
  rw [f.norm_map]
  congr 2
  refine ((MeasureTheory.LinearIsometryEquiv.measurePreserving_toSphere f).integral_comp'
    _).symm.trans ?_
  congr 1 with ω
  simp only [MeasureTheory.sphereLinearIsometryEquiv_coe, zero_add, ← map_smul, f.dist_map]

variable [Fact (0 < n)]

private noncomputable def i0 : Fin n :=
  ⟨0, Fact.out⟩

private noncomputable def e0 : ℝ^n :=
  EuclideanSpace.single (i0 (n := n)) (1 : ℝ)

private theorem norm_e0 : ‖e0 (n := n)‖ = (1 : ℝ) := by
  classical
  simp [e0]

private theorem poissonBallExtension_one_eq_radial {r : ℝ} :
    ∀ x ∈ Metric.ball (0 : ℝ^n) r,
      poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ (1 : ℝ)) x =
        poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ (1 : ℝ))
          (‖x‖ • e0 (n := n)) := by
  classical
  intro x hx
  let y : ℝ^n := ‖x‖ • e0 (n := n)
  have hnorm : ‖x‖ = ‖y‖ := by
    have : ‖y‖ = ‖x‖ := by
      simp [y, norm_smul, norm_e0 (n := n)]
    exact this.symm
  let R : ℝ^n ≃ₗᵢ[ℝ] ℝ^n := (Submodule.span ℝ ({x - y} : Set ℝ^n))ᗮ.reflection
  have hRx : R x = y := by
    simpa [R, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      Submodule.reflection_sub (v := x) (w := y) hnorm
  have hEq :=
    poissonBallExtension_one_invariant (n := n) (r := r) (f := R) (x := x)
  simpa [hRx] using hEq.symm

/-- The Poisson extension of constant boundary data `1` equals `1` throughout the open ball. -/
theorem poissonBallExtension_one_eq_one_on_ball {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ Metric.ball (0 : ℝ^n) r,
      poissonBallExtension (n := n) r (fun _ : ℝ^n ↦ (1 : ℝ)) x = 1 := by
  classical
  let F : ℝ → ℝ := fun t ↦ poissonBallExtension (n := n) r (fun _ ↦ 1) (t • e0 (n := n))
  have hnorm (t : ℝ) : ‖t • e0 (n := n)‖ = |t| := by simp [norm_smul, norm_e0]
  have hF : ContDiffOn ℝ 2 F (Ioo (-r) r) :=
    (contDiffOn_poissonBallExtension hr continuous_const.continuousOn).comp (by fun_prop)
      fun t ht ↦ by simpa [hnorm] using abs_lt.2 ht
  have hF' : ContDiffOn ℝ 1 (deriv F) (Ioo (-r) r) := hF.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsub : Ioo 0 r ⊆ Ioo (-r) r := Ioo_subset_Ioo_left (by linarith)
  have hdiff {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioo (-r) r)) {t : ℝ} (ht : t ∈ Ioo 0 r) :
      DifferentiableAt ℝ φ t :=
    (hφ.contDiffAt (isOpen_Ioo.mem_nhds (hsub ht))).differentiableAt one_ne_zero
  have hconst (φ : ℝ → ℝ) (hφ : ContDiffOn ℝ 1 φ (Ioo (-r) r))
      (h0 : ∀ t ∈ Ioo 0 r, deriv φ t = 0) (t : ℝ) (ht : t ∈ Ioo 0 r) : φ t = φ 0 := by
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope φ ht.1
      (hφ.continuousOn.mono (Icc_subset_Ioo (by linarith) ht.2))
      fun s hs ↦ (hdiff hφ ⟨hs.1, hs.2.trans ht.2⟩).differentiableWithinAt
    rw [h0 c ⟨hc.1, hc.2.trans ht.2⟩, eq_comm, div_eq_zero_iff, sub_eq_zero, sub_zero] at hcd
    exact hcd.resolve_right ht.1.ne'
  have hODE (t : ℝ) (ht : t ∈ Ioo 0 r) :
      deriv (deriv F) t + ((n : ℝ) - 1) / t * deriv F t = 0 := by
    have hn : ‖t • e0 (n := n)‖ = t := by rw [hnorm, abs_of_pos ht.1]
    have hx : t • e0 (n := n) ∈ Metric.ball (0 : ℝ^n) r := by simpa [hn] using ht.2
    have hEq : poissonBallExtension r (fun _ ↦ 1) =ᶠ[nhds (t • e0 (n := n))] F ∘ norm := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
      exact poissonBallExtension_one_eq_radial z hz
    have := EuclideanLaplacian.laplacian_radial F _ (by rw [← norm_ne_zero_iff, hn]; exact ht.1.ne')
      (by rw [hn]; exact hF.contDiffAt (isOpen_Ioo.mem_nhds (hsub ht)))
    rwa [← EuclideanLaplacian.laplacian_congr_nhds hEq,
      laplacian_poissonBallExtension_eq_zero hr continuous_const.continuousOn hx, hn,
      eq_comm] at this
  have hDeriv0 : deriv F 0 = 0 := by
    have hEven : (fun t ↦ F (-t)) =ᶠ[nhds 0] F := Filter.Eventually.of_forall fun t ↦ by
      simpa [F, neg_smul] using
        poissonBallExtension_one_invariant (LinearIsometryEquiv.neg ℝ) (x := t • e0 (n := n))
    have := hEven.deriv_eq
    rw [deriv_comp_neg, neg_zero] at this
    linarith
  have hH (t : ℝ) (ht : t ∈ Ioo 0 r) : deriv (fun t ↦ t ^ (n - 1) * deriv F t) t = 0 := by
    rw [((hasDerivAt_pow (n - 1) t).fun_mul (hdiff hF' ht).hasDerivAt).deriv,
      show deriv (deriv F) t = -(((n : ℝ) - 1) / t * deriv F t) by linarith [hODE t ht]]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Fact.out : 0 < n)
    rcases m with _ | k
    · simp
    · have := ht.1.ne'
      simp only [zero_add, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [pow_succ]
      field_simp
      ring
  have hFzero (t : ℝ) (ht : t ∈ Ioo 0 r) : deriv F t = 0 := by
    have hHt : t ^ (n - 1) * deriv F t = 0 := by
      simpa [hDeriv0] using hconst _ ((contDiff_id.pow _).contDiffOn.mul hF') hH t ht
    exact (mul_eq_zero.1 hHt).resolve_left (pow_ne_zero _ ht.1.ne')
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact poissonBallExtension_one_at_zero hr
  calc _ = F ‖x‖ := poissonBallExtension_one_eq_radial x hx
    _ = F 0 := hconst F (hF.of_le (by norm_num)) hFzero ‖x‖ ⟨norm_pos_iff.2 hx0, by simpa using hx⟩
    _ = 1 := by simpa [F] using poissonBallExtension_one_at_zero hr

end PoissonBallNormalization

end GreenFunction
