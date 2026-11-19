/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.RadialBarrier
public import PDE.Common.Euclidean
import CAS.ExactTactic

/-!
# Hopf's boundary point lemma

A strict boundary maximum of a classical elliptic subsolution has strictly positive derivative along
the outward unit normal of an interior tangent ball. The coefficients satisfy uniform ellipticity
and boundedness on the outer half of the ball; no coefficient continuity or regularity of the rest
of the boundary is used. These are parts (i) and (ii) of Hopf's Lemma in Evans's §6.4.2:
`hopf_inward_deriv_neg` and `hopf_normal_fderiv_pos` give part (ii), with `c ≥ 0` and a nonnegative
maximum, and `hopf_inward_deriv_neg_of_nonneg_mul` also covers part (i), where `c = 0` and the
maximum may have either sign.

The statements are local to `closedBall z R`, with `R > 0` and `‖x₀ - z‖ = R`. To apply them to a
domain with an interior tangent ball at `x₀`, restrict the function and coefficient hypotheses to
this ball. The outward unit normal here is `R⁻¹ • (x₀ - z)`; identifying it with a normal of an
ambient boundary is a separate geometric step.

The sign convention is `Lu = -∑ D²u[σₖ,σₖ] + Du[b] + cu`, with `Lu ≤ 0`, `c ≥ 0`, and a nonnegative
boundary maximum. The annular formulation `hopf_inward_deriv_neg_of_nonneg_mul` instead assumes
`c(x)u(x₀) ≥ 0` only on the outer annulus, allowing a maximum of either sign when the potential
vanishes there. It also needs the subsolution inequality only on that annulus: subtracting the
maximum and setting all coefficients to zero elsewhere reduces to the ball-local result.

## Main results

* `exists_radialBarrier_le_gap`: a positive multiple of the radial barrier lies below the gap under
  the boundary maximum on the outer annulus.
* `hopf_inward_deriv_neg`: the one-sided derivative along the inward radius is negative.
* `hopf_normal_fderiv_pos`: the Fréchet derivative along the outward unit normal is positive.
* `hopf_inward_deriv_neg_of_nonneg_mul`: the annular formulation.

## How it works

We follow Evans's proof. He takes the barrier `v = e^{-λ|x|²} - e^{-λr²}`, with `Lv ≤ 0` on the
annulus `B°(0, r) - B(0, r/2)` for large `λ`, (15), chooses `ε` with `u(x⁰) ≥ u + εv` on the inner
sphere, (16), and applies his Theorem 2 to `u + εv - u(x⁰)`. Our `radialBarrier` is a strict
subsolution on the annulus (`exists_radialBarrier_strict_subsolution`), so
`exists_radialBarrier_le_gap` needs only the strict bound `strict_subsolution_le_of_boundary_le`
with `M = 0`. The derivative conclusion uses only existence of the one-sided derivative along the
inward radius: the gap vanishes at `x₀` and dominates `εv`, whose derivative along the inward radius
is positive. A second formulation gives positivity of the outward unit-normal Fréchet derivative
when the function is differentiable at `x₀`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, Hopf's Lemma, (14), and its proof, (15)-(17),
  pp. 347-349.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open Filter Metric PDE.Analysis Set
open scoped InnerProductSpace Topology

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The gap below a nonnegative strict upper bound inside a ball dominates a positive
multiple of a radial barrier on its outer annulus. The barrier and its comparison are
constructed from the coefficient bounds and the strict maximum gap on the inner half-ball. -/
theorem exists_radialBarrier_le_gap
    (σ : ℝ^n → ι → ℝ^n) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (z : ℝ^n)
    {R κ A B C M : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (helliptic : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      ∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤ ∑ k, ⟪v, σ x k⟫_ℝ ^ 2)
    (htrace : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ∑ k, ‖σ x k‖ ^ 2 ≤ A)
    (hdrift : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ‖b x‖ ≤ B)
    (hpotential : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} (hucont : ContinuousOn u (closedBall z R))
    (hureg : ∀ x ∈ ball z R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball z R, factoredOperator σ b c u x ≤ 0)
    (hstrict : ∀ x ∈ ball z R, u x < M) :
    ∃ α ε : ℝ, 0 < α ∧ 0 < ε ∧
      ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
        ε * radialBarrier z R α x ≤ M - u x := by
  obtain ⟨α, hα, hbarrier⟩ :=
    exists_radialBarrier_strict_subsolution σ b c z hR hκ hA hB hC
      helliptic htrace hdrift hpotential
  have hhalf : R / 2 < R := by linarith
  obtain ⟨p, hp, hpmax⟩ := (isCompact_closedBall z (R / 2)).exists_isMaxOn
    ⟨z, mem_closedBall_self (by positivity)⟩ (hucont.mono (closedBall_subset_closedBall hhalf.le))
  let ε : ℝ := M - u p
  have hε : 0 < ε := sub_pos.mpr (hstrict p (mem_ball.mpr ((mem_closedBall.mp hp).trans_lt hhalf)))
  have hule (x : ℝ^n) (hx : x ∈ closedBall z R) : u x ≤ M := by
    rw [← closure_ball z hR.ne'] at hucont hx
    exact le_on_closure (fun y hy ↦ (hstrict y hy).le) hucont continuousOn_const hx
  let Ω : Set (ℝ^n) := {x | R / 2 < ‖x - z‖ ∧ ‖x - z‖ < R}
  have hnormcont : Continuous (fun x : ℝ^n ↦ ‖x - z‖) := by fun_prop
  have hΩopen : IsOpen Ω :=
    (isOpen_lt continuous_const hnormcont).inter (isOpen_lt hnormcont continuous_const)
  have hclosure : closure Ω ⊆ {x | R / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ R} :=
    closure_minimal (fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩)
      ((isClosed_le continuous_const hnormcont).inter (isClosed_le hnormcont continuous_const))
  have hclball : closure Ω ⊆ closedBall z R := fun x hx ↦
    mem_closedBall.mpr (by simpa only [dist_eq_norm] using (hclosure hx).2)
  have hΩcompact : IsCompact (closure Ω) :=
    (isCompact_closedBall z R).of_isClosed_subset isClosed_closure hclball
  let w : ℝ^n → ℝ := fun x ↦ (u x - M) + ε * radialBarrier z R α x
  have hqreg := contDiff_radialBarrier z R α
  have hwcont : ContinuousOn w (closure Ω) :=
    ((hucont.mono hclball).sub continuousOn_const).add
      (hqreg.continuous.const_mul ε).continuousOn
  have huregΩ (x : ℝ^n) (hx : x ∈ Ω) : ContDiffAt ℝ 2 u x :=
    hureg x (mem_ball.mpr (by simpa only [dist_eq_norm] using hx.2))
  have hwreg (x : ℝ^n) (hx : x ∈ Ω) : ContDiffAt ℝ 2 w x :=
    ((huregΩ x hx).sub contDiffAt_const).add (hqreg.contDiffAt.const_smul ε)
  have hwsub (x : ℝ^n) (hx : x ∈ Ω) : factoredOperator σ b c w x < 0 := by
    have huM : ContDiffAt ℝ 2 (fun y ↦ u y - M) x :=
      (huregΩ x hx).sub contDiffAt_const
    have hqε : ContDiffAt ℝ 2 (fun y ↦ ε * radialBarrier z R α y) x :=
      hqreg.contDiffAt.const_smul ε
    rw [show w = (fun y ↦ (u y - M) + ε * radialBarrier z R α y) from rfl,
      factoredOperator_add σ b c huM hqε, factoredOperator_sub_const,
      factoredOperator_const_mul σ b c (hqreg.differentiable (by norm_num) x)]
    have hux := hsub x (mem_ball.mpr (by simpa only [dist_eq_norm] using hx.2))
    have hcM := mul_nonneg (hpotential x hx.1 hx.2).1 hM
    exact add_neg_of_nonpos_of_neg (by linarith)
      (mul_neg_of_pos_of_neg hε (hbarrier x hx.1 hx.2))
  have hwboundary (x : ℝ^n) (hx : x ∈ frontier Ω) : w x ≤ 0 := by
    have hxcl := hclosure (frontier_subset_closure hx)
    have hxnot : x ∉ Ω := (hΩopen.frontier_eq ▸ hx).2
    by_cases hxinner : ‖x - z‖ = R / 2
    · have hxsmall : x ∈ closedBall z (R / 2) := by
        simp only [mem_closedBall, dist_eq_norm, hxinner, le_refl]
      have hux : u x ≤ u p := hpmax hxsmall
      have hq := mul_le_mul_of_nonneg_left (radialBarrier_le_one z R hα.le x) hε.le
      dsimp [w, ε]
      dsimp [ε] at hq
      linarith
    · have hxouter : ‖x - z‖ = R := by
        by_contra hne
        exact hxnot ⟨lt_of_le_of_ne hxcl.1 (Ne.symm hxinner),
          lt_of_le_of_ne hxcl.2 hne⟩
      have hux := hule x (hclball (frontier_subset_closure hx))
      dsimp [w]
      rw [radialBarrier_eq_zero hxouter, mul_zero, add_zero]
      exact sub_nonpos.mpr hux
  have hwle := strict_subsolution_le_of_boundary_le hΩopen hΩcompact σ b c (M := 0)
    (fun x hx ↦ (hpotential x hx.1 hx.2).1) (fun _ _ ↦ by simp)
    hwcont hwreg hwsub hwboundary
  refine ⟨α, ε, hα, hε, fun x hxinner hxouter ↦ ?_⟩
  have := hwle x (subset_closure ⟨hxinner, hxouter⟩)
  simp only [w] at this
  linarith

/-- Hopf's boundary point lemma using only the one-sided derivative along the inward
radius. A nonnegative strict maximum at the tangent point forces this derivative to
be negative. The inward radius is parametrized by `x₀ + s • (z - x₀)`, with `s ↓ 0`.
No differentiability of `u` outside the ball is required. -/
theorem hopf_inward_deriv_neg
    (σ : ℝ^n → ι → ℝ^n) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (z : ℝ^n)
    {R κ A B C : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      ∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤ ∑ k, ⟪v, σ x k⟫_ℝ ^ 2)
    (htrace : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ∑ k, ‖σ x k‖ ^ 2 ≤ A)
    (hdrift : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ‖b x‖ ≤ B)
    (hpotential : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} {x₀ : ℝ^n} (hx₀ : ‖x₀ - z‖ = R) (hmaxnonneg : 0 ≤ u x₀)
    (hucont : ContinuousOn u (closedBall z R))
    (hureg : ∀ x ∈ ball z R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball z R, factoredOperator σ b c u x ≤ 0)
    (hstrict : ∀ x ∈ ball z R, u x < u x₀)
    {d : ℝ} (hderiv : HasDerivWithinAt
      (fun s : ℝ ↦ u (x₀ + s • (z - x₀))) d (Ioi 0) 0) :
    d < 0 := by
  obtain ⟨α, ε, hα, hε, hgap⟩ :=
    exists_radialBarrier_le_gap σ b c z hR hκ hA hB hC hmaxnonneg
      helliptic htrace hdrift hpotential hucont hureg hsub hstrict
  let γ : ℝ → ℝ^n := fun s ↦ x₀ + s • (z - x₀)
  have hnorm (s : ℝ) : ‖γ s - z‖ = |1 - s| * R := by
    have hline : γ s - z = (1 - s) • (x₀ - z) := by
      dsimp [γ]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [hline, norm_smul, Real.norm_eq_abs, hx₀]
  have hγannulus (s : ℝ) (hs : 0 < s) (hs' : s < 1 / 2) :
      R / 2 < ‖γ s - z‖ ∧ ‖γ s - z‖ < R := by
    rw [hnorm, abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
    constructor <;> nlinarith [mul_pos hR hs, mul_pos hR (sub_pos.mpr hs')]
  have hqfun : (fun s ↦ radialBarrier z R α (γ s)) =
      fun s : ℝ ↦ Real.exp (-α * ((1 - s) * R) ^ 2) - Real.exp (-α * R ^ 2) := by
    funext s
    simp only [radialBarrier, hnorm, mul_pow, sq_abs]
  let D : ℝ := 2 * α * R ^ 2 * Real.exp (-α * R ^ 2)
  have hD : 0 < D := by dsimp [D]; positivity
  have hqderiv : HasDerivAt (fun s ↦ radialBarrier z R α (γ s)) D 0 := by
    rw [hqfun]
    dsimp [D]
    cas
  let w : ℝ → ℝ := fun s ↦ (u (γ s) - u x₀) + ε * radialBarrier z R α (γ s)
  have hwzero : w 0 = 0 := by simp [w, γ, radialBarrier_eq_zero hx₀]
  have hwderiv : HasDerivWithinAt w (d + ε * D) (Ioi 0) 0 :=
    (hderiv.sub_const (u x₀)).add (hqderiv.hasDerivWithinAt.const_mul ε)
  have hwlim : Tendsto (slope w 0) (𝓝[>] 0) (𝓝 (d + ε * D)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hwderiv
  have hsign : d + ε * D ≤ 0 := by
    apply le_of_tendsto hwlim
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
      with s hs hs'
    have hbound := hgap (γ s) (hγannulus s hs hs').1 (hγannulus s hs hs').2
    simp only [slope_def_field, hwzero, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by simp only [w]; linarith) hs.le
  linarith [mul_pos hε hD]

/-- At a nonnegative strict boundary maximum, the Fréchet derivative along the ball's
outward unit normal `R⁻¹ • (x₀ - z)` is positive. Its normalization follows from
`‖x₀ - z‖ = R` and `R > 0`. Only differentiability at the tangent point is required
at the boundary. -/
theorem hopf_normal_fderiv_pos
    (σ : ℝ^n → ι → ℝ^n) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (z : ℝ^n)
    {R κ A B C : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      ∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤ ∑ k, ⟪v, σ x k⟫_ℝ ^ 2)
    (htrace : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ∑ k, ‖σ x k‖ ^ 2 ≤ A)
    (hdrift : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ‖b x‖ ≤ B)
    (hpotential : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} {x₀ : ℝ^n} (hx₀ : ‖x₀ - z‖ = R) (hmaxnonneg : 0 ≤ u x₀)
    (hucont : ContinuousOn u (closedBall z R))
    (hureg : ∀ x ∈ ball z R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball z R, factoredOperator σ b c u x ≤ 0)
    (hstrict : ∀ x ∈ ball z R, u x < u x₀)
    (hubdry : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (R⁻¹ • (x₀ - z)) := by
  have hline : HasDerivAt (fun s : ℝ ↦ x₀ + s • (z - x₀)) (z - x₀) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (z - x₀)).const_add x₀
  have hdu : HasDerivAt (fun s : ℝ ↦ u (x₀ + s • (z - x₀)))
      (fderiv ℝ u x₀ (z - x₀)) 0 := by
    have hu' : HasFDerivAt u (fderiv ℝ u x₀) (x₀ + (0 : ℝ) • (z - x₀)) := by
      simpa using hubdry.hasFDerivAt
    exact hu'.comp_hasDerivAt 0 hline
  have hneg := hopf_inward_deriv_neg σ b c z hR hκ hA hB hC
    helliptic htrace hdrift hpotential hx₀ hmaxnonneg hucont hureg hsub hstrict
    hdu.hasDerivWithinAt
  rw [show z - x₀ = -(x₀ - z) by abel, map_neg] at hneg
  rw [map_smul, smul_eq_mul]
  exact mul_pos (inv_pos.mpr hR) (neg_lt_zero.mp hneg)

/-- Hopf's inward derivative conclusion with a compatible maximum of either sign.
All coefficient hypotheses and the subsolution inequality are needed only on the outer
annulus. Setting the coefficients to zero elsewhere reduces this statement to the
ball-local factored theorem. -/
theorem hopf_inward_deriv_neg_of_nonneg_mul
    (σ : ℝ^n → ι → ℝ^n) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (z : ℝ^n)
    {R κ A B C : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      ∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤ ∑ k, ⟪v, σ x k⟫_ℝ ^ 2)
    (htrace : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ∑ k, ‖σ x k‖ ^ 2 ≤ A)
    (hdrift : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ‖b x‖ ≤ B)
    (hpotential : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} {x₀ : ℝ^n} (hx₀ : ‖x₀ - z‖ = R)
    (hcM : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x * u x₀)
    (hucont : ContinuousOn u (closedBall z R))
    (hureg : ∀ x ∈ ball z R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      factoredOperator σ b c u x ≤ 0)
    (hstrict : ∀ x ∈ ball z R, u x < u x₀)
    {d : ℝ} (hderiv : HasDerivWithinAt
      (fun s : ℝ ↦ u (x₀ + s • (z - x₀))) d (Ioi 0) 0) :
    d < 0 := by
  classical
  let S : Set (ℝ^n) := {x | R / 2 < ‖x - z‖ ∧ ‖x - z‖ < R}
  let σ' : ℝ^n → ι → ℝ^n := fun x k ↦ if x ∈ S then σ x k else 0
  let b' : ℝ^n → ℝ^n := fun x ↦ if x ∈ S then b x else 0
  let c' : ℝ^n → ℝ := fun x ↦ if x ∈ S then c x else 0
  have hsub' : ∀ x ∈ ball z R,
      factoredOperator σ' b' c' (fun y ↦ u y - u x₀) x ≤ 0 := by
    intro x _
    rw [factoredOperator_sub_const]
    by_cases hx : x ∈ S
    · have hbound : factoredOperator σ b c u x - c x * u x₀ ≤ 0 :=
        sub_nonpos.mpr ((hsub x hx.1 hx.2).trans (hcM x hx.1 hx.2))
      simpa only [factoredOperator, σ', b', c', ite_eq_left hx] using hbound
    · simp [factoredOperator, σ', b', c', hx, secondDirectionalDerivative]
  refine hopf_inward_deriv_neg (u := fun y ↦ u y - u x₀)
    σ' b' c' z hR hκ hA hB hC ?_ ?_ ?_ ?_ hx₀ (by simp)
    (hucont.sub continuousOn_const) (fun x hx ↦ (hureg x hx).sub contDiffAt_const)
    hsub' ?_ (hderiv.sub_const (u x₀))
  · exact fun x h₁ h₂ v ↦ by
      simpa only [σ', ite_eq_left (show x ∈ S from ⟨h₁, h₂⟩)] using helliptic x h₁ h₂ v
  · exact fun x h₁ h₂ ↦ by
      simpa only [σ', ite_eq_left (show x ∈ S from ⟨h₁, h₂⟩)] using htrace x h₁ h₂
  · exact fun x h₁ h₂ ↦ by
      simpa only [b', ite_eq_left (show x ∈ S from ⟨h₁, h₂⟩)] using hdrift x h₁ h₂
  · exact fun x h₁ h₂ ↦ by
      simpa only [c', ite_eq_left (show x ∈ S from ⟨h₁, h₂⟩)] using hpotential x h₁ h₂
  · exact fun x hx ↦ by simpa only [sub_self] using sub_neg.mpr (hstrict x hx)

end EllipticMaximum
