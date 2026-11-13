/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderStream
public import PDE.Fluid.Euler.Axisymmetric.CylinderKernel
public import PDE.FDeriv.Laplacian.Meridian
public import PDE.Elliptic.Classical.Poisson.FundamentalSolution
public import PDE.CoordinateSystems.Axisymmetric.Isometry
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# The stream function is bounded by the Newtonian potential of the vorticity

Let `φ` solve `-(∂_rr + r⁻¹ ∂_r + ∂_zz) φ + r⁻² φ = ω` in the meridian rectangle
`0 < r < 1`, `a < z < b`, be continuous on the closed rectangle and vanish on its boundary (the
axis, the wall and the two horizontal sides). Then

```text
|φ(r, z)| ≤ ∫ Φ((r, 0, z) - y) |ω(r(y), z(y))| 1_K(y) dy,
```

where `Φ = 1/(4π|·|)` is the Newtonian kernel of `ℝ^3` and `K` the solid cylinder over the
rectangle (`abs_le_integral_fundamentalSolution_mul_meridianLift`). Only continuity of `ω` on the
closed rectangle is used.

## Main results

* `convolution_axisRotation`: the convolution of two axisymmetric functions is axisymmetric.
* `streamOperator_comp_meridianEmbedding`: the stream operator of the meridian slice of an
  axisymmetric field.
* `abs_le_integral_fundamentalSolution_mul_meridianLift`: the comparison bound.

## How it works

We compare `φ` with the meridian slice `M̂` of the Newtonian potential `M = Φ ⋆ g` of a smooth,
nonnegative, axisymmetric function `g` with `|ω| ≤ g + ε` (`abs_le_newtonianPotential_add`). Since
`M` is rotation invariant (`convolution_axisRotation`) and `-ΔM = g`, the meridian Laplacian
(`PDE.CoordinateSystems.laplacian_comp_meridianEmbedding`) gives
`streamOperator M̂ = g + M̂ / r² ≥ g` (`streamOperator_comp_meridianEmbedding`). With the barrier
`(1 - r²)/4` (`wallBarrier`), whose stream operator is at least one, `M̂ ∓ φ + ε (1 - r²)/4` is a
supersolution, nonnegative on the boundary because `M ≥ 0`, hence nonnegative by the minimum
principle `nonneg_of_streamOperator_nonneg_of_isCompact`; this gives `|φ| ≤ M̂ + ε/4`. For `g` we
take radial mollifications of `|ω| ψₙ` (`exists_contDiff_axisymmetric_approx`) with `ε = 1/(n + 1)`,
for cutoffs `ψₙ` decreasing to `1_K` (`radialCutoff`, `axialCutoff`), and dominated convergence
passes to the limit.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, Lemma 6.1, p. 95.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (laplacian partialDeriv)

namespace Euler.Cylinder

open EuclideanSpace MeasureTheory PotentialTheory Filter
open PDE.CoordinateSystems PDE.Common
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-! ### Axisymmetric convolutions -/

/-- The rotation about the axis commutes with differences. -/
theorem axisRotation_sub (θ : ℝ) (x y : ℝ^3) :
    axisRotation θ x - axisRotation θ y = axisRotation θ (x - y) := by
  rw [← axialRotation_apply, ← axialRotation_apply, ← axialRotation_apply, map_sub]

/-- **Axisymmetric convolutions.** The convolution of two functions invariant under the
rotations about the axis is invariant under these rotations. -/
theorem convolution_axisRotation {k f : ℝ^3 → ℝ} (hk : IsInvariantUnderAxisRotation k)
    (hf : IsInvariantUnderAxisRotation f) (θ : ℝ) (x : ℝ^3) :
    convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume (axisRotation θ x) =
      convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  rw [convolution_mul, convolution_mul]
  have hmp := measurePreserving_axialRotation θ
  rw [← hmp.integral_comp (axialRotation θ).toHomeomorph.measurableEmbedding]
  congr 1
  funext t
  change k (axialRotation θ t) * f (axisRotation θ x - axialRotation θ t) = k t * f (x - t)
  rw [axialRotation_apply, hk, axisRotation_sub, hf]

/-! ### A radial mollifier -/

/-- The radial bump `y ↦ smoothTransition (1 - ‖y‖² / δ²)`, positive exactly on the ball of
radius `δ`. -/
def radialBump (δ : ℝ) (y : ℝ^3) : ℝ :=
  Real.smoothTransition (1 - ‖y‖ ^ 2 / δ ^ 2)

/-- The radial bump is smooth. -/
theorem contDiff_radialBump (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (radialBump δ) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

/-- The radial bump is nonnegative. -/
theorem radialBump_nonneg (δ : ℝ) (y : ℝ^3) : 0 ≤ radialBump δ y := by
  unfold radialBump
  exact Real.smoothTransition.nonneg _

/-- The radial bump is at most one. -/
theorem radialBump_le_one (δ : ℝ) (y : ℝ^3) : radialBump δ y ≤ 1 := by
  unfold radialBump
  exact Real.smoothTransition.le_one _

/-- The support of the radial bump is the ball of radius `δ`. -/
theorem support_radialBump {δ : ℝ} (hδ : 0 < δ) :
    Function.support (radialBump δ) = Metric.ball 0 δ := by
  ext y
  rw [Function.mem_support, radialBump, Ne, Real.smoothTransition.zero_iff_nonpos, not_le,
    mem_ball_zero_iff, sub_pos, div_lt_one (by positivity)]
  constructor
  · intro h
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le h
  · intro h
    exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero

/-- The radial bump has compact support. -/
theorem hasCompactSupport_radialBump {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (radialBump δ) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^3) δ)
  rw [support_radialBump hδ]
  exact Metric.ball_subset_closedBall

/-- The radial bump has positive integral. -/
theorem integral_radialBump_pos {δ : ℝ} (hδ : 0 < δ) : 0 < ∫ y, radialBump δ y := by
  have hint : Integrable (radialBump δ) :=
    (contDiff_radialBump δ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_radialBump hδ)
  rw [integral_pos_iff_support_of_nonneg (radialBump_nonneg δ) hint, support_radialBump hδ]
  exact Metric.measure_ball_pos _ _ hδ

/-- The radial mollifier of radius `δ`: the radial bump normalized to integral one. -/
def radialMollifier (δ : ℝ) (y : ℝ^3) : ℝ :=
  radialBump δ y / ∫ t, radialBump δ t

/-- The radial mollifier is smooth. -/
theorem contDiff_radialMollifier (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (radialMollifier δ) :=
  (contDiff_radialBump δ).div_const _

/-- The radial mollifier is nonnegative. -/
theorem radialMollifier_nonneg {δ : ℝ} (hδ : 0 < δ) (y : ℝ^3) : 0 ≤ radialMollifier δ y :=
  div_nonneg (radialBump_nonneg δ y) (integral_radialBump_pos hδ).le

/-- The support of the radial mollifier is the ball of radius `δ`. -/
theorem support_radialMollifier {δ : ℝ} (hδ : 0 < δ) :
    Function.support (radialMollifier δ) = Metric.ball 0 δ := by
  unfold radialMollifier
  rw [Function.support_div, support_radialBump hδ]
  have : Function.support (fun _ : ℝ^3 ↦ ∫ t, radialBump δ t) = Set.univ :=
    Function.support_const (integral_radialBump_pos hδ).ne'
  rw [this, Set.inter_univ]

/-- The radial mollifier has compact support. -/
theorem hasCompactSupport_radialMollifier {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (radialMollifier δ) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^3) δ)
  rw [support_radialMollifier hδ]
  exact Metric.ball_subset_closedBall

/-- The radial mollifier has integral one. -/
theorem integral_radialMollifier {δ : ℝ} (hδ : 0 < δ) : ∫ y, radialMollifier δ y = 1 := by
  unfold radialMollifier
  rw [integral_div, div_self (integral_radialBump_pos hδ).ne']

/-- The radial mollifier is invariant under the rotations about the axis. -/
theorem isInvariantUnderAxisRotation_radialMollifier (δ : ℝ) :
    IsInvariantUnderAxisRotation (radialMollifier δ) := by
  intro θ y
  simp only [radialMollifier, radialBump]
  rw [← axialRotation_apply, LinearIsometryEquiv.norm_map]

/-- The Newtonian kernel of `ℝ^3` is invariant under the rotations about the axis. -/
theorem isInvariantUnderAxisRotation_fundamentalSolution :
    IsInvariantUnderAxisRotation (fundamentalSolution 3) := by
  intro θ y
  rw [← axialRotation_apply]
  exact fundamentalSolution_eq_of_norm_eq (LinearIsometryEquiv.norm_map _ _)

/-- The Newtonian kernel of `ℝ^3` is nonnegative. -/
theorem fundamentalSolution_three_nonneg (y : ℝ^3) : 0 ≤ fundamentalSolution 3 y := by
  rw [fundamentalSolution_three_eq]
  positivity

/-! ### Meridian rectangles and the barrier -/

/-- The closed meridian rectangle `0 ≤ r ≤ 1`, `a ≤ z ≤ b`. -/
def closedMeridianRectangle (a b : ℝ) : Set (ℝ^2) :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ a ≤ p 1 ∧ p 1 ≤ b}

/-- The open meridian rectangle `0 < r < 1`, `a < z < b`. -/
def meridianRectangle (a b : ℝ) : Set (ℝ^2) :=
  {p | 0 < p 0 ∧ p 0 < 1 ∧ a < p 1 ∧ p 1 < b}

/-- The open meridian rectangle is open. -/
theorem isOpen_meridianRectangle (a b : ℝ) : IsOpen (meridianRectangle a b) := by
  have h0 : Continuous (fun x : ℝ^2 ↦ x 0) := by fun_prop
  have h1 : Continuous (fun x : ℝ^2 ↦ x 1) := by fun_prop
  exact (isOpen_lt continuous_const h0).inter ((isOpen_lt h0 continuous_const).inter
    ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))

/-- The open meridian rectangle lies in the closed one. -/
theorem meridianRectangle_subset (a b : ℝ) :
    meridianRectangle a b ⊆ closedMeridianRectangle a b :=
  fun _ hp ↦ ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩

/-- The closed meridian rectangle is compact. -/
theorem isCompact_closedMeridianRectangle (a b : ℝ) :
    IsCompact (closedMeridianRectangle a b) := by
  have h0 : Continuous (fun x : ℝ^2 ↦ x 0) := by fun_prop
  have h1 : Continuous (fun x : ℝ^2 ↦ x 1) := by fun_prop
  have hcl : IsClosed (closedMeridianRectangle a b) :=
    (isClosed_le continuous_const h0).inter ((isClosed_le h0 continuous_const).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const)))
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ^2)).2 ⟨1 + |a| + |b|, fun x hx ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.sqrt_le_left (by positivity)]
  have h0' : x 0 ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2.1]
  have h1' : x 1 ^ 2 ≤ (|a| + |b|) ^ 2 := by
    have : |x 1| ≤ |a| + |b| := by
      rw [abs_le]
      constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [hx.2.2.1, hx.2.2.2]
    calc x 1 ^ 2 = |x 1| ^ 2 := (sq_abs _).symm
      _ ≤ (|a| + |b|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- The barrier `(1 - r²)/4`, whose stream operator is at least one in the strip. -/
def wallBarrier (p : ℝ^2) : ℝ :=
  (1 - p 0 ^ 2) / 4

/-- The radial derivative of a function of the radius alone. -/
theorem partialDeriv_zero_comp_radius {g : ℝ → ℝ} {q : ℝ^2} (hg : DifferentiableAt ℝ g (q 0)) :
    (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ g (y 0))) q = deriv g (q 0) := by
  have hp : HasFDerivAt (fun y : ℝ^2 ↦ y 0) (proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ) q :=
    (proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  have h : HasFDerivAt (fun y : ℝ^2 ↦ g (y 0)) (deriv g (q 0) • (proj (0 : Fin 2))) q :=
    hg.hasDerivAt.comp_hasFDerivAt q hp
  rw [partialDeriv, h.fderiv]
  simp

/-- The axial derivative of a function of the radius alone vanishes. -/
theorem partialDeriv_one_comp_radius {g : ℝ → ℝ} {q : ℝ^2} (hg : DifferentiableAt ℝ g (q 0)) :
    (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ g (y 0))) q = 0 := by
  have hp : HasFDerivAt (fun y : ℝ^2 ↦ y 0) (proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ) q :=
    (proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  have h : HasFDerivAt (fun y : ℝ^2 ↦ g (y 0)) (deriv g (q 0) • (proj (0 : Fin 2))) q :=
    hg.hasDerivAt.comp_hasFDerivAt q hp
  rw [partialDeriv, h.fderiv]
  simp

/-- The radial derivative of the barrier. -/
theorem partialDeriv_zero_wallBarrier :
    (∂[(0 : Fin 2)] wallBarrier) = fun q ↦ -(q 0 / 2) := by
  funext q
  have hg : HasDerivAt (fun t : ℝ ↦ (1 - t ^ 2) / 4) (-(q 0 / 2)) (q 0) := by
    have := ((hasDerivAt_pow 2 (q 0)).const_sub 1).div_const 4
    convert this using 1
    ring
  rw [show wallBarrier = fun y : ℝ^2 ↦ (fun t : ℝ ↦ (1 - t ^ 2) / 4) (y 0) from rfl,
    partialDeriv_zero_comp_radius hg.differentiableAt, hg.deriv]

/-- The stream operator of the barrier. -/
theorem streamOperator_wallBarrier {p : ℝ^2} (hp : p 0 ≠ 0) :
    streamOperator wallBarrier p = 1 + (1 - p 0 ^ 2) / (4 * p 0 ^ 2) := by
  have hd0 : DifferentiableAt ℝ (fun t : ℝ ↦ -(t / 2)) (p 0) := by fun_prop
  have hdd0 : (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] wallBarrier)) p = -(1 / 2) := by
    rw [partialDeriv_zero_wallBarrier,
      show (fun q : ℝ^2 ↦ -(q 0 / 2)) = fun y : ℝ^2 ↦ (fun t : ℝ ↦ -(t / 2)) (y 0) from rfl,
      partialDeriv_zero_comp_radius hd0]
    have : HasDerivAt (fun t : ℝ ↦ -(t / 2)) (-(1 / 2)) (p 0) :=
      ((hasDerivAt_id (p 0)).div_const 2).neg
    exact this.deriv
  have hd1 : ∀ q : ℝ^2, (∂[(1 : Fin 2)] wallBarrier) q = 0 := by
    intro q
    have hg : DifferentiableAt ℝ (fun t : ℝ ↦ (1 - t ^ 2) / 4) (q 0) := by fun_prop
    rw [show wallBarrier = fun y : ℝ^2 ↦ (fun t : ℝ ↦ (1 - t ^ 2) / 4) (y 0) from rfl,
      partialDeriv_one_comp_radius hg]
  have hdd1 : (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] wallBarrier)) p = 0 := by
    rw [show (∂[(1 : Fin 2)] wallBarrier) = fun _ ↦ (0 : ℝ) from funext hd1]
    exact PDE.partialDeriv_const _
  rw [streamOperator, laplacian, Fin.sum_univ_two, hdd0, hdd1, partialDeriv_zero_wallBarrier]
  simp only [wallBarrier]
  field_simp
  ring

/-- The stream operator of the barrier is at least one in the strip. -/
theorem one_le_streamOperator_wallBarrier {p : ℝ^2} (hp0 : 0 < p 0) (hp1 : p 0 ≤ 1) :
    1 ≤ streamOperator wallBarrier p := by
  rw [streamOperator_wallBarrier hp0.ne']
  have : 0 ≤ (1 - p 0 ^ 2) / (4 * p 0 ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  linarith

/-- The barrier is smooth. -/
theorem contDiff_wallBarrier : ContDiff ℝ (⊤ : ℕ∞) wallBarrier :=
  (contDiff_const.sub (((proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff).pow 2)).div_const 4

/-- The stream operator commutes with multiplication by constants. -/
theorem streamOperator_const_mul (c : ℝ) (f : ℝ^2 → ℝ) (x : ℝ^2) :
    streamOperator (fun y ↦ c * f y) x = c * streamOperator f x := by
  have hlap : laplacian (fun y ↦ c * f y) x = c * laplacian f x := PDE.laplacian_const_smul c f x
  have hd : (∂[(0 : Fin 2)] (fun y ↦ c * f y)) x = c * (∂[(0 : Fin 2)] f) x := by
    simpa [smul_eq_mul] using PDE.partialDeriv_const_smul (i := (0 : Fin 2)) (f := f) (x := x) c
  rw [streamOperator, streamOperator, hlap, hd]
  ring

/-- The stream operator of the meridian slice of an axisymmetric field. -/
theorem streamOperator_comp_meridianEmbedding {F : ℝ^3 → ℝ} (hF : IsInvariantUnderAxisRotation F)
    {p : ℝ^2} (hp : p 0 ≠ 0) (hreg : ContDiffAt ℝ 2 F (meridianEmbedding p)) :
    streamOperator (F ∘ meridianEmbedding) p =
      -laplacian F (meridianEmbedding p) + F (meridianEmbedding p) / p 0 ^ 2 := by
  rw [streamOperator, laplacian_comp_meridianEmbedding hF hp hreg]
  simp only [Function.comp_apply]
  ring

/-! ### Comparison with the Newtonian potential of a smooth majorant -/

/-- The Newtonian potential `∫ Φ(t) g(x - t) dt` of a function on `ℝ^3`. -/
def newtonianPotential (g : ℝ^3 → ℝ) (x : ℝ^3) : ℝ :=
  ∫ t, fundamentalSolution 3 t * g (x - t)

/-- **Comparison with a smooth majorant.** If `g` is a smooth, compactly supported, nonnegative,
axisymmetric function with `|ω| ≤ g + ε` on the open rectangle, then
`|φ| ≤ M + ε/4` on the closed rectangle for the meridian slice `M` of the Newtonian potential
of `g`. -/
theorem abs_le_newtonianPotential_add {a b ε : ℝ} {ω φ : ℝ^2 → ℝ}
    (hφc : ContinuousOn φ (closedMeridianRectangle a b))
    (hφreg : ∀ ⦃p : ℝ^2⦄, p ∈ meridianRectangle a b → ContDiffAt ℝ 2 φ p)
    (heq : ∀ ⦃p : ℝ^2⦄, p ∈ meridianRectangle a b → streamOperator φ p = ω p)
    (hbd : ∀ ⦃p : ℝ^2⦄, p ∈ closedMeridianRectangle a b → p ∉ meridianRectangle a b →
      φ p = 0)
    {g : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hg0 : ∀ y, 0 ≤ g y)
    (hgi : IsInvariantUnderAxisRotation g) (hε : 0 ≤ ε)
    (hmaj : ∀ ⦃p : ℝ^2⦄, p ∈ meridianRectangle a b → |ω p| ≤ g (meridianEmbedding p) + ε)
    {p : ℝ^2} (hp : p ∈ closedMeridianRectangle a b) :
    |φ p| ≤ newtonianPotential g (meridianEmbedding p) + ε / 4 := by
  let G : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^3)) ℝ 2 :=
    { toFun := g
      contDiff' := hg
      hasCompactSupport' := hgc
      tsupport_subset' := Set.subset_univ _ }
  set M : ℝ^3 → ℝ := PoissonEquation.fundamentalSolutionConvolution 3 G
  have hMdef : ∀ x, M x = newtonianPotential g x := by
    intro x
    simp only [M, PoissonEquation.fundamentalSolutionConvolution, convolution_mul,
      newtonianPotential]
    rfl
  have hM2 : ContDiff ℝ 2 M := PoissonEquation.contDiff_two_fundamentalSolutionConvolution 3 G
  have hMlap : ∀ x, -laplacian M x = g x :=
    PoissonEquation.negative_laplacian_fundamentalSolutionConvolution (by norm_num) G
  have hMinv : IsInvariantUnderAxisRotation M :=
    convolution_axisRotation isInvariantUnderAxisRotation_fundamentalSolution hgi
  have hM0 (x : ℝ^3) : 0 ≤ M x := by
    rw [hMdef]
    exact integral_nonneg fun t ↦ mul_nonneg (fundamentalSolution_three_nonneg t) (hg0 _)
  set Mh : ℝ^2 → ℝ := M ∘ meridianEmbedding
  have hMh2 : ContDiff ℝ 2 Mh := hM2.comp meridianEmbedding.contDiff
  have hMhop : ∀ ⦃q : ℝ^2⦄, q ∈ meridianRectangle a b →
      g (meridianEmbedding q) ≤ streamOperator Mh q := by
    intro q hq
    rw [streamOperator_comp_meridianEmbedding hMinv hq.1.ne' hM2.contDiffAt, hMlap]
    have : 0 ≤ M (meridianEmbedding q) / q 0 ^ 2 := div_nonneg (hM0 _) (sq_nonneg _)
    linarith
  have hb2 : ContDiff ℝ 2 wallBarrier := contDiff_wallBarrier.of_le (by norm_num)
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      s * φ p ≤ Mh p + ε * wallBarrier p := by
    intro s hs
    set v : ℝ^2 → ℝ := fun q ↦ Mh q - s * φ q + ε * wallBarrier q
    have hv := nonneg_of_streamOperator_nonneg_of_isCompact (isOpen_meridianRectangle a b)
      (isCompact_closedMeridianRectangle a b) (meridianRectangle_subset a b)
      (fun q hq ↦ hq.1) (v := v)
      (by
        refine ((hMh2.continuous.continuousOn.sub (continuousOn_const.mul hφc)).add
          (continuousOn_const.mul hb2.continuous.continuousOn)))
      (fun q hq ↦ ((hMh2.contDiffAt.sub (contDiffAt_const.mul (hφreg hq))).add
          (contDiffAt_const.mul hb2.contDiffAt)))
      (fun q hq ↦ by
        have h1 : ContDiffAt ℝ 2 (fun y ↦ Mh y - s * φ y) q :=
          hMh2.contDiffAt.sub (contDiffAt_const.mul (hφreg hq))
        rw [streamOperator_add h1 (contDiffAt_const.mul hb2.contDiffAt),
          streamOperator_sub hMh2.contDiffAt (contDiffAt_const.mul (hφreg hq)),
          streamOperator_const_mul, streamOperator_const_mul,
          heq hq]
        have hop := hMhop hq
        have hbar := one_le_streamOperator_wallBarrier hq.1 hq.2.1.le
        have hm := hmaj hq
        have hsω : s * ω q ≤ |ω q| := by rcases hs with rfl | rfl <;> simp [le_abs_self, neg_le_abs]
        nlinarith)
      (fun q hq hqU ↦ by
        simp only [v, hbd hq hqU, mul_zero, sub_zero]
        have : 0 ≤ wallBarrier q := by
          unfold wallBarrier
          nlinarith [hq.1, hq.2.1]
        exact add_nonneg (hM0 _) (mul_nonneg hε this))
    linarith [hv hp]
  have hb4 : ε * wallBarrier p ≤ ε / 4 := by
    unfold wallBarrier
    have : (1 - p 0 ^ 2) / 4 ≤ 1 / 4 := by nlinarith [sq_nonneg (p 0)]
    nlinarith
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  rw [← hMdef]
  rw [abs_le]
  constructor <;> simp only [Mh, Function.comp_apply] at h1 h2 <;> linarith

/-! ### Smooth axisymmetric approximation -/

/-- **Smooth axisymmetric approximation.** A continuous, compactly supported, nonnegative,
axisymmetric function vanishing outside the ball of radius `R` is uniformly approximated, within
any `ε > 0`, by smooth, compactly supported, nonnegative, axisymmetric functions vanishing
outside the ball of radius `R + 1` (radial mollification). -/
theorem exists_contDiff_axisymmetric_approx {F : ℝ^3 → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hF0 : ∀ y, 0 ≤ F y) (hFi : IsInvariantUnderAxisRotation F)
    {R : ℝ} (hR : ∀ y, F y ≠ 0 → ‖y‖ ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ (∀ y, 0 ≤ g y) ∧
      IsInvariantUnderAxisRotation g ∧ (∀ y, |g y - F y| ≤ ε) ∧
      (∀ y, g y ≠ 0 → ‖y‖ ≤ R + 1) := by
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuous_iff.1
    (hFc.uniformContinuous_of_continuous hF) ε hε
  set ρ : ℝ := min (δ / 2) 1
  have hρ : 0 < ρ := lt_min (by linarith) one_pos
  have hρδ : ρ < δ := (min_le_left _ _).trans_lt (by linarith)
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  refine ⟨convolution (radialMollifier ρ) F (ContinuousLinearMap.mul ℝ ℝ) volume,
    (hasCompactSupport_radialMollifier hρ).contDiff_convolution_left
      (ContinuousLinearMap.mul ℝ ℝ) (contDiff_radialMollifier ρ) hF.locallyIntegrable,
    (hasCompactSupport_radialMollifier hρ).convolution _ hFc, ?_,
    convolution_axisRotation (isInvariantUnderAxisRotation_radialMollifier ρ) hFi, ?_, ?_⟩
  · intro y
    rw [convolution_mul]
    exact integral_nonneg fun t ↦ mul_nonneg (radialMollifier_nonneg hρ t) (hF0 _)
  · intro y
    have h := dist_convolution_le (μ := volume) (z₀ := F y) hε.le
      (support_radialMollifier hρ).subset (radialMollifier_nonneg hρ)
      (integral_radialMollifier hρ) hF.aestronglyMeasurable
      (fun x hx ↦ (hU (lt_trans (Metric.mem_ball.1 hx) hρδ)).le)
    rw [Real.dist_eq, convolution_lsmul] at h
    rw [convolution_mul]
    simpa [smul_eq_mul] using h
  · intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) (Function.mem_support.2 hy)
    rw [support_radialMollifier hρ, mem_ball_zero_iff] at hu
    have := hR v hv
    calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith

/-! ### Cutoffs decreasing to the solid cylinder -/

/-- A continuous radial cutoff, `1` for `t ≤ 1` and `0` for `t ≥ 1 + 1/(n+1)`. -/
def radialCutoff (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (1 - (n + 1) * (t - 1)))

/-- A continuous axial cutoff, `1` on `[a, b]` and `0` at distance at least `1/(n+1)`. -/
def axialCutoff (a b : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  max 0 (min 1 (1 - (n + 1) * max (a - z) (z - b)))

/-- The radial cutoff is continuous. -/
theorem continuous_radialCutoff (n : ℕ) : Continuous (radialCutoff n) := by
  unfold radialCutoff
  fun_prop

/-- The axial cutoff is continuous. -/
theorem continuous_axialCutoff (a b : ℝ) (n : ℕ) : Continuous (axialCutoff a b n) := by
  unfold axialCutoff
  fun_prop

/-- The radial cutoff is nonnegative. -/
theorem radialCutoff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ radialCutoff n t := le_max_left _ _

/-- The axial cutoff is nonnegative. -/
theorem axialCutoff_nonneg (a b : ℝ) (n : ℕ) (z : ℝ) : 0 ≤ axialCutoff a b n z :=
  le_max_left _ _

/-- The radial cutoff is at most one. -/
theorem radialCutoff_le_one (n : ℕ) (t : ℝ) : radialCutoff n t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The axial cutoff is at most one. -/
theorem axialCutoff_le_one (a b : ℝ) (n : ℕ) (z : ℝ) : axialCutoff a b n z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The radial cutoff is one for `t ≤ 1`. -/
theorem radialCutoff_of_le {n : ℕ} {t : ℝ} (ht : t ≤ 1) : radialCutoff n t = 1 := by
  have : 1 ≤ 1 - (n + 1) * (t - 1) := by
    have : (n + 1 : ℝ) * (t - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  simp [radialCutoff, min_eq_left this]

/-- The axial cutoff is one on `[a, b]`. -/
theorem axialCutoff_of_mem {a b : ℝ} {n : ℕ} {z : ℝ} (ha : a ≤ z) (hb : z ≤ b) :
    axialCutoff a b n z = 1 := by
  have : 1 ≤ 1 - (n + 1) * max (a - z) (z - b) := by
    have : (n + 1 : ℝ) * max (a - z) (z - b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (max_le (by linarith) (by linarith))
    linarith
  simp [axialCutoff, min_eq_left this]

/-- The radial cutoff vanishes for `t ≥ 2`. -/
theorem lt_of_radialCutoff_ne_zero {n : ℕ} {t : ℝ} (h : radialCutoff n t ≠ 0) : t < 2 := by
  by_contra ht
  rw [not_lt] at ht
  apply h
  have : 1 - (n + 1) * (t - 1) ≤ 0 := by
    have : (1 : ℝ) ≤ (n + 1) * (t - 1) := by
      have h1 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      nlinarith
    linarith
  simp [radialCutoff, min_eq_right ((this).trans zero_le_one), this]

/-- The axial cutoff vanishes outside `(a - 1, b + 1)`. -/
theorem mem_of_axialCutoff_ne_zero {a b : ℝ} {n : ℕ} {z : ℝ} (h : axialCutoff a b n z ≠ 0) :
    a - 1 < z ∧ z < b + 1 := by
  have key : max (a - z) (z - b) < 1 := by
    by_contra hz
    rw [not_lt] at hz
    apply h
    have : 1 - (n + 1) * max (a - z) (z - b) ≤ 0 := by
      have h1 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      nlinarith
    simp [axialCutoff, min_eq_right (this.trans zero_le_one), this]
  constructor
  · linarith [le_max_left (a - z) (z - b)]
  · linarith [le_max_right (a - z) (z - b)]

/-- The radial cutoffs decrease to the indicator of `t ≤ 1`. -/
theorem tendsto_radialCutoff (t : ℝ) :
    Tendsto (fun n : ℕ ↦ radialCutoff n t) atTop (𝓝 (if t ≤ 1 then 1 else 0)) := by
  split_ifs with ht
  · exact tendsto_const_nhds.congr fun n ↦ (radialCutoff_of_le ht).symm
  · rw [not_le] at ht
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (t - 1))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpos : 0 < t - 1 := by linarith
    have : 1 ≤ (n + 1) * (t - 1) := by
      have h1 : 1 / (t - 1) < n + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [div_lt_iff₀ hpos] at h1
      linarith
    simp [radialCutoff, min_eq_right ((show 1 - (n + 1) * (t - 1) ≤ 0 by linarith).trans
      zero_le_one), show 1 - (n + 1) * (t - 1) ≤ 0 by linarith]

/-- The axial cutoffs decrease to the indicator of `[a, b]`. -/
theorem tendsto_axialCutoff (a b z : ℝ) :
    Tendsto (fun n : ℕ ↦ axialCutoff a b n z) atTop
      (𝓝 (if a ≤ z ∧ z ≤ b then 1 else 0)) := by
  split_ifs with hz
  · exact tendsto_const_nhds.congr fun n ↦ (axialCutoff_of_mem hz.1 hz.2).symm
  · have hpos : 0 < max (a - z) (z - b) := by
      rw [not_and_or, not_le, not_le] at hz
      rcases hz with hz | hz
      · exact lt_max_of_lt_left (by linarith)
      · exact lt_max_of_lt_right (by linarith)
    set m := max (a - z) (z - b)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / m)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have : 1 ≤ (n + 1) * m := by
      have h1 : 1 / m < n + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [div_lt_iff₀ hpos] at h1
      linarith
    simp [axialCutoff, m, min_eq_right ((show 1 - (n + 1) * m ≤ 0 by linarith).trans
      zero_le_one), show 1 - (n + 1) * m ≤ 0 by linarith]

/-! ### The comparison bound -/

/-- The meridian coordinates of the meridian embedding of a point with `r ≥ 0`. -/
theorem meridianCoordinates_meridianEmbedding {q : ℝ^2} (hq : 0 ≤ q 0) :
    meridianCoordinates (meridianEmbedding q) = q := by
  rw [meridianEmbedding_apply, meridianCoordinates_meridianPoint _ _ hq]
  ext i
  fin_cases i <;> simp

/-- The norm on `ℝ^3` is at most the cylindrical radius plus the absolute axial coordinate. -/
theorem norm_le_cylindricalRadius_add (y : ℝ^3) : ‖y‖ ≤ cylindricalRadius y + |y 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.sqrt_le_left (by
    exact add_nonneg (cylindricalRadius_nonneg y) (abs_nonneg _))]
  have h := cylindricalRadius_sq y
  simp only [cylindricalRadiusSq] at h
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [cylindricalRadius_nonneg y, abs_nonneg (y 2), sq_abs (y 2)]

/-- **The stream function is bounded by the Newtonian potential of the vorticity.** Let `φ` be
continuous on the closed meridian rectangle `0 ≤ r ≤ 1`, `a ≤ z ≤ b`, `C²` in the open rectangle,
solve `-(∂_rr + r⁻¹ ∂_r + ∂_zz) φ + r⁻² φ = ω` there and vanish on the boundary of the
rectangle, with `ω` continuous on the closed rectangle. Then at every point of the closed
rectangle `|φ(r, z)|` is at most the Newtonian potential at `(r, 0, z)` of `|ω|` on the solid
cylinder over the rectangle. -/
theorem abs_le_integral_fundamentalSolution_mul_meridianLift {a b : ℝ} {ω φ : ℝ^2 → ℝ}
    (hφc : ContinuousOn φ (closedMeridianRectangle a b))
    (hφreg : ∀ ⦃p : ℝ^2⦄, p ∈ meridianRectangle a b → ContDiffAt ℝ 2 φ p)
    (heq : ∀ ⦃p : ℝ^2⦄, p ∈ meridianRectangle a b → streamOperator φ p = ω p)
    (hbd : ∀ ⦃p : ℝ^2⦄, p ∈ closedMeridianRectangle a b → p ∉ meridianRectangle a b →
      φ p = 0)
    (hω : ContinuousOn ω (closedMeridianRectangle a b)) {p : ℝ^2}
    (hp : p ∈ closedMeridianRectangle a b) :
    |φ p| ≤ ∫ y, fundamentalSolution 3 (PDE.CoordinateSystems.meridianPoint (p 0) (p 1) - y) *
      meridianLift ((closedMeridianRectangle a b).indicator fun q ↦ |ω q|) y := by
  have hab : a ≤ b := hp.2.2.1.trans hp.2.2.2
  -- A continuous extension of `ω` from the closed rectangle.
  set c : ℝ^2 → ℝ^2 := fun q ↦ WithLp.toLp 2 ![max 0 (min 1 (q 0)), max a (min b (q 1))]
  have hc_cont : Continuous c := by
    simp only [c]
    fun_prop
  have hc_mem (q : ℝ^2) : c q ∈ closedMeridianRectangle a b :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _), le_max_left _ _,
      max_le hab (min_le_left _ _)⟩
  have hc_id : ∀ q ∈ closedMeridianRectangle a b, c q = q := by
    intro q hq
    ext i
    fin_cases i
    · simp [c, min_eq_right hq.2.1, max_eq_right hq.1]
    · simp [c, min_eq_right hq.2.2.2, max_eq_right hq.2.2.1]
  set ωb : ℝ^2 → ℝ := ω ∘ c
  have hωb : Continuous ωb := hω.comp_continuous hc_cont hc_mem
  set h : ℝ^3 → ℝ := meridianLift fun q ↦ |ωb q|
  have hh : Continuous h := (continuous_abs.comp hωb).comp continuous_meridianCoordinates
  have hhi : IsInvariantUnderAxisRotation h := isInvariantUnderAxisRotation_meridianLift _
  -- Cutoffs and the functions to mollify.
  set ψ : ℕ → ℝ^3 → ℝ := fun n y ↦ radialCutoff n (cylindricalRadius y) * axialCutoff a b n (y 2)
  set F : ℕ → ℝ^3 → ℝ := fun n y ↦ h y * ψ n y
  set R0 : ℝ := 3 + |a| + |b|
  have hψi : ∀ n, IsInvariantUnderAxisRotation (ψ n) := by
    intro n θ y
    simp only [ψ, cylindricalRadius_axisRotation, axisRotation_apply_two]
  have hFi : ∀ n, IsInvariantUnderAxisRotation (F n) := by
    intro n θ y
    simp only [F, hhi θ y, hψi n θ y]
  have hcylR : Continuous cylindricalRadius := by
    unfold cylindricalRadius cylindricalRadiusSq
    fun_prop
  have hFc : ∀ n, Continuous (F n) := fun n ↦
    hh.mul (((continuous_radialCutoff n).comp hcylR).mul
      ((continuous_axialCutoff a b n).comp (by fun_prop)))
  have hF0 : ∀ n y, 0 ≤ F n y := fun n y ↦
    mul_nonneg (abs_nonneg _) (mul_nonneg (radialCutoff_nonneg _ _) (axialCutoff_nonneg _ _ _ _))
  have hFR : ∀ n y, F n y ≠ 0 → ‖y‖ ≤ R0 := by
    intro n y hy
    have hψ : ψ n y ≠ 0 := right_ne_zero_of_mul hy
    have h1 := lt_of_radialCutoff_ne_zero (left_ne_zero_of_mul hψ)
    have h2 := mem_of_axialCutoff_ne_zero (right_ne_zero_of_mul hψ)
    have h3 : |y 2| ≤ |a| + |b| + 1 := by
      rw [abs_le]
      constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [h2.1, h2.2]
    linarith [norm_le_cylindricalRadius_add y]
  have hFcs (n : ℕ) : HasCompactSupport (F n) :=
    .of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^3) R0) fun y hy ↦
      mem_closedBall_zero_iff.2 (hFR n y hy)
  -- A bound for `h` on the region where the approximants live.
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : ℝ^3) (R0 + 1)).exists_bound_of_continuousOn
    hh.continuousOn
  set B : ℝ := max B₀ 0
  have hFB (n : ℕ) (y : ℝ^3) : F n y ≤ B := by
    by_cases hy : F n y = 0
    · exact hy ▸ le_max_right _ _
    refine (mul_le_of_le_one_right (abs_nonneg _) ((mul_le_of_le_one_left
      (axialCutoff_nonneg _ _ _ _) (radialCutoff_le_one _ _)).trans
        (axialCutoff_le_one _ _ _ _))).trans
      ((le_abs_self _).trans ((hB₀ y ?_).trans (le_max_left _ _)))
    exact mem_closedBall_zero_iff.2 (by linarith [hFR n y hy])
  -- The smooth approximants.
  have happrox : ∀ n : ℕ, ∃ g : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ y, 0 ≤ g y) ∧ IsInvariantUnderAxisRotation g ∧ (∀ y, |g y - F n y| ≤ 1 / (n + 1)) ∧
      (∀ y, g y ≠ 0 → ‖y‖ ≤ R0 + 1) := fun n ↦
    exists_contDiff_axisymmetric_approx (hFc n) (hFcs n) (hF0 n) (hFi n) (hFR n)
      (by positivity)
  choose g hg_smooth hg_cs hg0 hgi hg_approx hg_supp using happrox
  set x : ℝ^3 := meridianEmbedding p
  -- The comparison for each approximant.
  have hcmp : ∀ n : ℕ, |φ p| ≤ newtonianPotential (g n) x + 1 / (n + 1) / 4 := by
    intro n
    refine abs_le_newtonianPotential_add hφc hφreg heq hbd ((hg_smooth n).of_le (by norm_num))
      (hg_cs n) (hg0 n) (hgi n) (by positivity) (fun q hq ↦ ?_) hp
    have hq0 : 0 ≤ q 0 := hq.1.le
    have hqR : q ∈ closedMeridianRectangle a b := meridianRectangle_subset a b hq
    have hFq : F n (meridianEmbedding q) = |ω q| := by
      have hcyl : cylindricalRadius (meridianEmbedding q) = q 0 := by
        rw [meridianEmbedding_apply, cylindricalRadius_meridianPoint _ _ hq0]
      have h2 : (meridianEmbedding q) 2 = q 1 := by
        rw [meridianEmbedding_apply]
        simp [PDE.CoordinateSystems.meridianPoint]
      simp only [F, ψ, h, meridianLift, hcyl, h2, radialCutoff_of_le hqR.2.1,
        axialCutoff_of_mem hqR.2.2.1 hqR.2.2.2, mul_one,
        meridianCoordinates_meridianEmbedding hq0, ωb, Function.comp_apply, hc_id q hqR]
    have := hg_approx n (meridianEmbedding q)
    rw [hFq, abs_le] at this
    linarith [this.1]
  -- The limit of the approximants.
  set L : ℝ^3 → ℝ := meridianLift ((closedMeridianRectangle a b).indicator fun q ↦ |ω q|)
  have hlimF : ∀ y, Tendsto (fun n : ℕ ↦ F n y) atTop (𝓝 (L y)) := by
    intro y
    have hψlim : Tendsto (fun n : ℕ ↦ ψ n y) atTop
        (𝓝 ((if cylindricalRadius y ≤ 1 then 1 else 0) *
          (if a ≤ y 2 ∧ y 2 ≤ b then 1 else 0))) :=
      (tendsto_radialCutoff _).mul (tendsto_axialCutoff a b _)
    have hval : h y * ((if cylindricalRadius y ≤ 1 then 1 else 0) *
        (if a ≤ y 2 ∧ y 2 ≤ b then 1 else 0)) = L y := by
      simp only [h, L, meridianLift, Set.indicator, closedMeridianRectangle, Set.mem_ofPred_eq,
        meridianCoordinates_apply_zero, meridianCoordinates_apply_one, axialCoordinate,
        cylindricalRadius_nonneg y, true_and]
      by_cases h1 : cylindricalRadius y ≤ 1 <;> by_cases h2 : a ≤ y 2 ∧ y 2 ≤ b
      · have hmem : meridianCoordinates y ∈ closedMeridianRectangle a b :=
          ⟨by simp [cylindricalRadius_nonneg], by simpa using h1, by simpa [axialCoordinate]
            using h2.1, by simpa [axialCoordinate] using h2.2⟩
        simp only [h1, h2, and_self, ite_true, mul_one, ωb, Function.comp_apply, hc_id _ hmem]
      all_goals simp [h1, h2]
    rw [← hval]
    exact tendsto_const_nhds.mul hψlim
  have hlimg (y : ℝ^3) : Tendsto (fun n : ℕ ↦ g n y) atTop (𝓝 (L y)) := by
    simpa using ((tendsto_zero_iff_abs_tendsto_zero _).2 (squeeze_zero (fun n ↦ abs_nonneg _)
      (fun n ↦ hg_approx n y) tendsto_one_div_add_atTop_nhds_zero_nat)).add (hlimF y)
  have hlim : Tendsto (fun n : ℕ ↦ newtonianPotential (g n) x) atTop
      (𝓝 (∫ t, fundamentalSolution 3 t * L (x - t))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun t ↦ (B + 1) * (Metric.closedBall x (R0 + 1)).indicator (fundamentalSolution 3) t)
      (fun n ↦ ?_) ?_ (fun n ↦ Eventually.of_forall fun t ↦ ?_)
      (Eventually.of_forall fun t ↦ (tendsto_const_nhds.mul (hlimg (x - t))))
    · exact (measurable_fundamentalSolution_three.aestronglyMeasurable).mul
        ((hg_smooth n).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · refine Integrable.const_mul ?_ _
      have : Fact (0 < 3) := ⟨by norm_num⟩
      exact ((locallyIntegrable_fundamentalSolution 3).integrableOn_isCompact
        (isCompact_closedBall x (R0 + 1))).integrable_indicator
          Metric.isClosed_closedBall.measurableSet
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fundamentalSolution_three_nonneg t)
        (hg0 n _))]
      by_cases ht : t ∈ Metric.closedBall x (R0 + 1)
      · rw [Set.indicator_of_mem ht, mul_comm (B + 1)]
        have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by simp) (by positivity)
        have h2 := (abs_le.1 (hg_approx n (x - t))).2
        exact mul_le_mul_of_nonneg_left (by linarith [hFB n (x - t)])
          (fundamentalSolution_three_nonneg t)
      · have : g n (x - t) = 0 := by_contra fun hne ↦ ht <| by
          rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
          exact hg_supp n (x - t) hne
        rw [Set.indicator_of_notMem ht, this, mul_zero, mul_zero]
  have hfinal : |φ p| ≤ ∫ t, fundamentalSolution 3 t * L (x - t) := ge_of_tendsto'
    (by simpa using hlim.add (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 4)) hcmp
  rw [show (∫ t, fundamentalSolution 3 t * L (x - t)) = ∫ y, fundamentalSolution 3 (x - y) * L y by
    simpa using integral_sub_left_eq_self (fun y ↦ fundamentalSolution 3 (x - y) * L y) volume x]
    at hfinal
  simpa [x, meridianEmbedding_apply] using hfinal

/-- The closed meridian rectangle is measurable. -/
theorem measurableSet_closedMeridianRectangle (a b : ℝ) :
    MeasurableSet (closedMeridianRectangle a b) :=
  (isCompact_closedMeridianRectangle a b).isClosed.measurableSet

/-- **The logarithmic bound for the stream function** (the estimate of Chen and Hou, Part I,
Lemma 6.1, on a meridian rectangle). Under the hypotheses of
`abs_le_integral_fundamentalSolution_mul_meridianLift`, if moreover `ω` vanishes on the
rectangle where `r < 1/2`, then at every point of the closed rectangle with `r ≥ 1/4`,

```text
|φ(r, z)| ≤ 2 ∫_{rectangle} |ω(r₁, z₁)| (1 + |log((r - r₁)² + (z - z₁)²)|) r₁ dr₁ dz₁.
```
-/
theorem abs_le_two_mul_integral_logKernel {a b : ℝ} {ω φ : ℝ^2 → ℝ}
    (hφc : ContinuousOn φ (closedMeridianRectangle a b))
    (hφreg : ∀ ⦃p : ℝ^2⦄, p ∈ meridianRectangle a b → ContDiffAt ℝ 2 φ p)
    (heq : ∀ ⦃p : ℝ^2⦄, p ∈ meridianRectangle a b → streamOperator φ p = ω p)
    (hbd : ∀ ⦃p : ℝ^2⦄, p ∈ closedMeridianRectangle a b → p ∉ meridianRectangle a b →
      φ p = 0)
    (hω : ContinuousOn ω (closedMeridianRectangle a b))
    (hsupp : ∀ ⦃q : ℝ^2⦄, q ∈ closedMeridianRectangle a b → ω q ≠ 0 → 1 / 2 ≤ q 0)
    {p : ℝ^2} (hp : p ∈ closedMeridianRectangle a b) (hp0 : 1 / 4 ≤ p 0) :
    |φ p| ≤ 2 * ∫ q in closedMeridianRectangle a b,
      |ω q| * (1 + |Real.log ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2)|) * q 0 := by
  classical
  set K := closedMeridianRectangle a b
  set H : ℝ^2 → ℝ := K.indicator fun q ↦ |ω q|
  have hHmeas : Measurable H := by
    have : H = K.piecewise (fun q ↦ |ω q|) 0 := by
      funext q
      simp [H, Set.indicator, Set.piecewise]
    rw [this]
    exact ContinuousOn.measurable_piecewise (continuous_abs.comp_continuousOn hω)
      continuousOn_const (measurableSet_closedMeridianRectangle a b)
  obtain ⟨M, hM⟩ := (isCompact_closedMeridianRectangle a b).exists_bound_of_continuousOn hω
  have hHM : ∀ q, H q ≤ M := by
    intro q
    by_cases hq : q ∈ K
    · simp only [H, Set.indicator_of_mem hq]
      simpa [Real.norm_eq_abs] using hM q hq
    · simp only [H, Set.indicator_of_notMem hq]
      exact (norm_nonneg _).trans (hM p hp)
  have hH0 : ∀ q, 0 ≤ H q := fun q ↦ Set.indicator_nonneg (fun _ _ ↦ abs_nonneg _) q
  have hHsupp : ∀ q, H q ≠ 0 → 1 / 2 ≤ q 0 ∧ q 0 ≤ 1 ∧ a ≤ q 1 ∧ q 1 ≤ b := by
    intro q hq
    have hqK : q ∈ K := by
      by_contra h
      exact hq (Set.indicator_of_notMem h _)
    have hωq : ω q ≠ 0 := by
      intro h0
      apply hq
      simp [H, Set.indicator_of_mem hqK, h0]
    exact ⟨hsupp hqK hωq, hqK.2.1, hqK.2.2.1, hqK.2.2.2⟩
  have h1 := abs_le_integral_fundamentalSolution_mul_meridianLift hφc hφreg heq hbd hω hp
  have h2 := integral_fundamentalSolution_mul_meridianLift_le (r := p 0) (z := p 1) H hHmeas
    hH0 hHM hHsupp hp0
  refine h1.trans (h2.trans (le_of_eq ?_))
  congr 1
  refine setIntegral_congr_fun (measurableSet_closedMeridianRectangle a b) fun q hq ↦ ?_
  have hqK : q ∈ K := hq
  simp only [H, Set.indicator_of_mem hqK]

end

end Euler.Cylinder
