/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.LocalMinimizer.Basic
public import Mathlib.Topology.MetricSpace.Holder
import PDE.Analysis.Calculus.Gradient.HessianNorm
import PDE.Elliptic.Regularity.Interior.Schauder.Reconstruction.HigherOrder
import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.HolderCoefficients
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative

/-!
# Hölder continuous gradients of local minimizers

## Motivation

How regular is a local minimizer of `∫ F(∇u)` when `F` is only `C²`, with
`θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²` and `θ > 0`?

## The idea

Schauder estimates do not apply at this stage: the coefficients `D²F(∇u)` of
the linearized equation are functions of a gradient that is not yet known to be
continuous. On a small ball the minimizer is a weak solution of `div(∇F(∇u)) = 0`.
Difference quotients give second weak derivatives there, and each first derivative `∂ᵢu`
is a weak solution of the linear equation `div(D²F(∇u) ∇(∂ᵢu)) = 0`. Its coefficients are
measurable, bounded by `Λ` and elliptic with constant `θ`, and nothing more is known about
them. De Giorgi's theorem needs nothing more. It gives a Hölder continuous representative
of `∂ᵢu` on a smaller ball, with an exponent `γ` that depends on the dimension, `θ` and `Λ`
only. A function whose weak gradient is continuous has a `C¹` representative, and the
representatives on balls glue over `Ω`. In the other direction, the classical gradient of
any `C¹` representative is the weak gradient, so it agrees with the Hölder representative
on each small ball.

## Main results

* `exists_holder_gradient_of_isLocalMinimizerOn` (all dimensions `n`, all open `Ω ⊆ ℝⁿ`,
  all `C²` densities with the two bounds, all local minimizers in `W^{1,2}_loc(Ω)`): there
  is `γ` in `(0, 1)`, chosen before `Ω`, `F` and `u`, such that `u` has a representative in
  `C¹(Ω)` whose gradient is Hölder continuous with exponent `γ` on a ball around each point.
* `exists_contDiffOn_one_of_isLocalMinimizerOn` (same scope): the `C¹` representative.
* `exists_holder_exponent_gradient_of_isLocalMinimizerOn` (same scope, all `C¹`
  representatives): the gradient of every `C¹` representative is Hölder continuous with
  exponent `γ` near each point.

The Hölder condition is `HolderOnWith C γ (fun y ↦ ∇ v y) (ball x r)`: one bound for the
whole gradient, as a map into `ℝⁿ` with its Euclidean distance. This is Mathlib's
`HolderOnWith`, which the regularity theorems of the library use. The constant `C` and the
radius `r` depend on the point `x`.

## Relations

* `exists_holder_exponent_weakGradient_of_gradientDensity` is the input. It treats an `H¹`
  weak solution on a bounded open set in positive dimension, and its exponent is chosen
  before the domain. `exists_auxiliary_exponent` supplies its auxiliary Sobolev exponent.
* `GraphSpace.exists_contDiffOn_representative_of_wkpCoordinate_ae_eq` builds the `C¹`
  representative, `wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn` identifies classical and
  weak derivatives, and `exists_holder_euclideanTuple` combines the coordinates.
* `exists_holder_gradient_of_isLocalMinimizerOn` is the second and the third result
  together.
* `exists_holder_exponent_gradient_of_isLocalMinimizerOn` applies to the `C²` and `C^∞`
  representatives of `PDE.CalculusOfVariations.LocalMinimizer.Smooth`. There it says less
  than is known, since the gradient of a `C²` function is locally Lipschitz.

## What stays open

A Hölder bound on each compact subset of `Ω` follows from the bounds on balls and the
continuity of the gradient, and is not stated. The constant is not estimated in terms of
`u`, and `γ` is not explicit.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.3: the second derivative estimates of §8.3.1 and
  the use of the De Giorgi–Nash theorem for the linearized equation in §8.3.2.
  <https://doi.org/10.1090/gsm/019>
* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino, P. I., III. Ser. 3 (1957), 25–43, and J. Nash,
  *Continuity of solutions of parabolic and elliptic equations*, Amer. J. Math. 80 (1958),
  931–954: Hölder continuity for linear equations with bounded measurable coefficients. Cited
  for the attribution of the theorem, as in Evans §8.3.2. The two papers were not consulted
  for the proofs here.
  <https://doi.org/10.2307/2372841>
* S. Armstrong and J. Kempe, *Formalization of De Giorgi–Nash–Moser Theory in Lean*,
  arXiv:2604.05984, 2026: another Lean formalization of interior Hölder regularity for linear
  divergence-form equations with bounded measurable coefficients. It is not used here.
  <https://arxiv.org/abs/2604.05984>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.CalculusOfVariations

open PDE.Elliptic.Regularity.Quasilinear

variable {n : ℕ}

/-- De Giorgi's theorem for the nonlinear equation on a ball, with the exponent chosen
first. A weak solution on `ball x r` has Hölder continuous representatives of its weak
derivatives on `ball x (r / 128)`. This is
`exists_holder_exponent_weakGradient_of_gradientDensity` on the pair of balls of radii `r`
and `r / 2`. -/
private theorem exists_holder_wkpCoordinate_ball [Fact (0 < n)] {Λ : ℝ≥0} {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧ ∀ F : ℝ^n → ℝ, ContDiff ℝ 2 F →
      (∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ) →
      (∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ) →
      ∀ (x : ℝ^n) (r : ℝ), 0 < r → ∀ U : H¹(ball x r),
        (∀ w : H¹₀(ball x r),
          (∫ y, ⟪∇ F (∇ U y), ∇ (w : H¹(ball x r)) y⟫ ∂domainMeasure n (ball x r)) = 0) →
        ∀ i : Fin n, ∃ (g : ℝ^n → ℝ) (K : ℝ≥0), Continuous g ∧
          HolderOnWith K γ g (ball x (r / 128)) ∧
          g =ᵐ[volume.restrict (ball x (r / 128))]
            wkpCoordinateCLM (singleDerivIndex n i) U := by
  obtain ⟨q, hq2, hq⟩ := exists_auxiliary_exponent (n := n)
  obtain ⟨γ, hγ0, hγ1, hreg⟩ :=
    exists_holder_exponent_weakGradient_of_gradientDensity (n := n) (Λ := Λ) hq2 hq hθ
  refine ⟨γ, hγ0, hγ1, fun F hF hbound hell x r hr U hU i ↦ ?_⟩
  have hc : IsCompact (closure (ball x (r / 2))) :=
    (isCompact_closedBall x (r / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hcl : closure (ball x (r / 2)) ⊆ ball x r :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  have h := hreg (ball x r) (ball x (r / 2)) isOpen_ball isBounded_ball isOpen_ball hc hcl
    F hF hbound hell U hU x (r / 2) (by positivity) Subset.rfl i
  rwa [show r / 2 / 64 = r / 128 by ring] at h

variable {Ω : Set (ℝ^n)} {F : ℝ^n → ℝ} {u : ℝ^n → ℝ} {θ Λ : ℝ}

/-- **`C¹` regularity of local minimizers for `C²` densities.** Let `Ω ⊆ ℝⁿ` be open, in
any dimension, and let `F` be `C²` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and
`ξ`, where `θ > 0`. Every local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)` has a
representative that is `C¹` on `Ω`.

On a ball, De Giorgi's theorem gives continuous representatives of the weak derivatives,
and a function with continuous weak gradient has a `C¹` representative. The local
representatives glue by `IsLocalMinimizerOn.exists_contDiffOn_ae_eq`. -/
theorem exists_contDiffOn_one_of_isLocalMinimizerOn (hΩ : IsOpen Ω) (hF : ContDiff ℝ 2 F)
    (hθ : 0 < θ) (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn F Ω u) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ 1 v Ω ∧ v =ᵐ[volume.restrict Ω] u := by
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
  · -- `ℝ^0` is a point, so `u` is constant.
    exact ⟨u, (contDiffOn_const (c := u 0)).congr fun x _ ↦ congrArg u (Subsingleton.elim x 0),
      .rfl⟩
  have : Fact (0 < n) := ⟨i₀.pos⟩
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF.contDiffAt hθ.le (hell p) (hbound p)
  obtain ⟨γ, -, -, hball⟩ := exists_holder_wkpCoordinate_ball (n := n) (Λ := Λ.toNNReal) hθ
  refine hmin.exists_contDiffOn_ae_eq hΩ (hF.differentiable (by norm_num))
    (lipschitzWith_gradient_of_hessian_bound hF hnorm) hu fun x r hr U hU ↦ ?_
  -- De Giorgi: continuous representatives of the weak derivatives near `x`.
  choose g K hg _ hga using hball F hF hnorm hell x r hr U hU
  let G : ℝ^n → ℝ^n := fun y ↦ WithLp.toLp 2 (fun i ↦ g i y)
  have hG : Continuous G := by fun_prop
  -- A function with continuous weak gradient has a `C¹` representative.
  obtain ⟨w, -, hwd, hwa, -⟩ :=
    exists_contDiffOn_representative_of_wkpCoordinate_ae_eq 0 U hG
      (by positivity : 0 < r / 128) (ball_subset_ball (by linarith))
      (contDiffOn_zero.mpr hG.continuousOn) hga
  exact ⟨ball x (r / 128 / 4), isOpen_ball, mem_ball_self (by positivity),
    ball_subset_ball (by linarith), w, by simpa only [Nat.cast_zero, zero_add] using hwd, hwa⟩

/-- **The gradient of every `C¹` representative is Hölder continuous.** In every dimension
`n` and for all `θ > 0` and `Λ` there is an exponent `γ` in `(0, 1)` with the following
property. Let `Ω ⊆ ℝⁿ` be open, let `F` be `C²` with
`θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, and let `u` be a local minimizer of
`∫ F(∇u)`. If `v` is `C¹` on `Ω` and equals `u` almost everywhere on `Ω`, then every point of
`Ω` is the centre of a ball on which `∇v` is Hölder continuous with exponent `γ`.

The exponent depends on `n`, `θ` and `Λ` only, and `u` is in `W^{1,2}_loc(Ω)` because `v`
is. The partial derivatives of `v` are weak derivatives of `u`, so on a small ball they are
the Hölder representatives given by De Giorgi's theorem. -/
theorem exists_holder_exponent_gradient_of_isLocalMinimizerOn (n : ℕ) {θ Λ : ℝ}
    (hθ : 0 < θ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧ ∀ (Ω : Set (ℝ^n)), IsOpen Ω → ∀ F : ℝ^n → ℝ,
      ContDiff ℝ 2 F →
      (∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ) →
      (∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2) →
      ∀ u : ℝ^n → ℝ, IsLocalMinimizerOn F Ω u →
      ∀ v : ℝ^n → ℝ, ContDiffOn ℝ 1 v Ω → v =ᵐ[volume.restrict Ω] u →
        ∀ x ∈ Ω, ∃ r > 0, ∃ C : ℝ≥0, HolderOnWith C γ (fun y ↦ ∇ v y) (ball x r) := by
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
  · -- `ℝ^0` is a point, and every map is Hölder continuous on a point.
    exact ⟨1 / 2, half_pos one_pos, NNReal.half_lt_self one_ne_zero,
      fun Ω _ F _ _ _ u _ v _ _ x _ ↦
        ⟨1, one_pos, 0, Set.subsingleton_of_subsingleton.holderOnWith _ _ _⟩⟩
  have : Fact (0 < n) := ⟨i₀.pos⟩
  obtain ⟨γ, hγ0, hγ1, hball⟩ :=
    exists_holder_wkpCoordinate_ball (n := n) (Λ := Λ.toNNReal) hθ
  refine ⟨γ, hγ0, hγ1, fun Ω hΩ F hF hell hbound u hmin v hv hvu x hx ↦ ?_⟩
  have hu : IsLocallyWkpOn 1 2 Ω u := (isLocallyWkpOn_of_contDiffOn hΩ hv 2).congr_ae hvu
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF.contDiffAt hθ.le (hell p) (hbound p)
  obtain ⟨r, hr, hrΩ, U, hU, hweak⟩ := hmin.exists_ball_weakSolution hΩ
    (hF.differentiable (by norm_num)) (lipschitzWith_gradient_of_hessian_bound hF hnorm) hu hx
  choose g K hg hgh hga using hball F hF hnorm hell x r hr U hweak
  have hsub : ball x (r / 128) ⊆ ball x r := ball_subset_ball (by linarith)
  have hUv : baseRepresentative U =ᵐ[domainMeasure n (ball x r)] v :=
    hU.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hrΩ hvu))
  -- Each partial derivative of `v` is the Hölder representative of a weak derivative.
  have hpartial (i : Fin n) : HolderOnWith (K i) γ (∂[i] v) (ball x (r / 128)) := by
    have hda := wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn isOpen_ball U (hv.mono hrΩ)
      hUv i
    have heq : EqOn (g i) (∂[i] v) (ball x (r / 128)) :=
      Measure.eqOn_open_of_ae_eq (μ := volume)
        ((hga i).trans (ae_mono (domainMeasure_le hsub) hda)) isOpen_ball (hg i).continuousOn
        (fun y hy ↦ (contDiffAt_partialDeriv 0
          (hv.contDiffAt (hΩ.mem_nhds (hrΩ (hsub hy)))) i).continuousAt.continuousWithinAt)
    intro y hy z hz
    rw [← heq hy, ← heq hz]
    exact hgh i y hy z hz
  obtain ⟨M, hM⟩ := exists_holder_euclideanTuple hpartial
  have hgrad : (fun y ↦ ∇ v y) = fun y ↦ (WithLp.toLp 2 (fun i ↦ (∂[i] v) y) : ℝ^n) :=
    funext fun y ↦ PiLp.ext fun i ↦ gradient_apply_eq_partialDeriv v y i
  exact ⟨r / 128, by positivity, M, hgrad ▸ hM⟩

/-- **Hölder continuous gradient of local minimizers (De Giorgi–Nash regularity).** In
every dimension `n` and for all `θ > 0` and `Λ` there is an exponent `γ` in `(0, 1)` with
the following property. Let `Ω ⊆ ℝⁿ` be open, let `F` be `C²` with
`θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, and let `u` in `W^{1,2}_loc(Ω)` be a
local minimizer of `∫ F(∇u)`. Then `u` has a representative `v` that is `C¹` on `Ω`, and
every point of `Ω` is the centre of a ball on which `∇v` is Hölder continuous with
exponent `γ`.

This is the first step of the regularity theory of minimizers (De Giorgi, Nash): a `C²`
density gives `C^{1,γ}` locally. The Hölder condition is stated for the gradient as a
map into `ℝⁿ`. The statement is `exists_contDiffOn_one_of_isLocalMinimizerOn` together with
`exists_holder_exponent_gradient_of_isLocalMinimizerOn`. -/
theorem exists_holder_gradient_of_isLocalMinimizerOn (n : ℕ) {θ Λ : ℝ} (hθ : 0 < θ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧ ∀ (Ω : Set (ℝ^n)), IsOpen Ω → ∀ F : ℝ^n → ℝ,
      ContDiff ℝ 2 F →
      (∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ) →
      (∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2) →
      ∀ u : ℝ^n → ℝ, IsLocallyWkpOn 1 2 Ω u → IsLocalMinimizerOn F Ω u →
        ∃ v : ℝ^n → ℝ, ContDiffOn ℝ 1 v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
          ∀ x ∈ Ω, ∃ r > 0, ∃ C : ℝ≥0, HolderOnWith C γ (fun y ↦ ∇ v y) (ball x r) := by
  obtain ⟨γ, hγ0, hγ1, hγ⟩ :=
    exists_holder_exponent_gradient_of_isLocalMinimizerOn n (Λ := Λ) hθ
  refine ⟨γ, hγ0, hγ1, fun Ω hΩ F hF hell hbound u hu hmin ↦ ?_⟩
  obtain ⟨v, hv, hvu⟩ :=
    exists_contDiffOn_one_of_isLocalMinimizerOn hΩ hF hθ hell hbound hu hmin
  exact ⟨v, hv, hvu, hγ Ω hΩ F hF hell hbound u hmin v hv hvu⟩

end PDE.CalculusOfVariations
