/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Representations.Similarity.Calculus
public import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.Classical
public import PDE.Solution.Singularity.FiniteTime.Norm.SpatialSupremum
import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.Similarity.Calculus
import PDE.Solution.Singularity.FiniteTime.Norm.Similarity

/-!
# Type I profiles for the nonlinear heat equation

We derive the classical Type I reduction for

`uₜ = Δu + uᵖ`.

Profiles are ordinary functions because the reduced equation is pointwise and uses a classical
Laplacian. A weak or Sobolev profile would need the dilation pullback and the reduced equation
defined on equivalence classes.

The derivation has five steps:

1. `typeIAnsatz` specializes the equation-independent backward similarity transformation;
2. `typeIProfileResidual` is the reduced elliptic residual;
3. `type_i_ansatz_nonnegative_iff` transfers nonnegativity in both directions;
4. `equation_residual_type_i_ansatz` factors the full parabolic residual by a positive time scale;
5. the zero-residual equivalences and
   `HasZeroTypeIProfileResidual.is_pointwise_classical_solution_on_pre_singular` connect the
   reduced equation to `IsNonnegativePointwiseClassicalSolutionOn`.

Regularity and nonnegativity are hypotheses of the individual theorems. The algebraic
substitution needs only `p ≠ 1`; building a classical solution and proving norm divergence
need `p > 1`.

The backward self-similar variables are classical; see Giga and Kohn. The results are exact
substitution identities for a given profile.

## References

* Y. Giga and R. V. Kohn, "Asymptotically self-similar blow-up of semilinear heat equations",
  *Comm. Pure Appl. Math.* 38 (1985), 297-319.
  <https://doi.org/10.1002/cpa.3160380304>
-/

open scoped Gradient

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.NonlinearHeat

open PDE.Representations.Similarity

variable {n : ℕ} (p : ℝ)

/-- The Type I ansatz
`(T - t)^(-1/(p-1)) f ((T-t)^(-1/2) • (x-x₀))`.

The intended domain is `p > 1` and `t < T`; with Lean's real powers and inversion the function
is also defined outside it. -/
noncomputable def typeIAnsatz
    (profile : ℝ^n → ℝ) (T : ℝ) (x₀ : ℝ^n) (x : ℝ^n) (t : ℝ) : ℝ :=
  backwardSelfSimilarAnsatz profile (1 / (p - 1)) (1 / 2) T x₀ x t

/-- The elliptic residual obtained from the Type I scaling.

The profile equation is

`Δf + fᵖ - (p-1)⁻¹ f - (1/2) y · ∇f = 0`.

Writing it through `scalingGenerator` keeps the balance-law derivation visible and reuses the
dilation term from the similarity calculus. -/
noncomputable def typeIProfileResidual
    (profile : ℝ^n → ℝ) (y : ℝ^n) : ℝ :=
  laplacian profile y + profile y ^ p -
    scalingGenerator (1 / (p - 1)) (1 / 2) profile y

/-- Expanded coordinate form of the Type I profile residual. -/
theorem type_i_profile_residual_eq (profile : ℝ^n → ℝ) (y : ℝ^n) :
    typeIProfileResidual p profile y =
      laplacian profile y -
          (1 / 2) * (∑ i, y i * (∇ profile y) i) -
          (1 / (p - 1)) * profile y +
          profile y ^ p := by
  simp only [typeIProfileResidual, scalingGenerator, gradient_apply_eq_partialDeriv]
  ring

/-- The Type I residual vanishes pointwise.

This predicate does not assert that `profile` is differentiable. Theorems interpreting it as a
classical elliptic equation supply `C²` regularity separately. -/
def HasZeroTypeIProfileResidual (profile : ℝ^n → ℝ) : Prop :=
  ∀ y, typeIProfileResidual p profile y = 0

/-- A zero Type I residual has the corresponding expanded coordinate identity. -/
theorem HasZeroTypeIProfileResidual.equation
    {profile : ℝ^n → ℝ} (hequation : HasZeroTypeIProfileResidual (n := n) p profile)
    (y : ℝ^n) :
    laplacian profile y -
          (1 / 2) * (∑ i, y i * (∇ profile y) i) -
          (1 / (p - 1)) * profile y +
          profile y ^ p =
      0 := by
  rw [← type_i_profile_residual_eq]
  exact hequation y

/-- At every pre-singular time, the Type I ansatz is nonnegative at all spatial points exactly
when its profile is nonnegative.

The reverse implication evaluates the ansatz at the inverse-dilated point corresponding to an
arbitrary profile coordinate. The amplitude can then be cancelled because every backward power
scale is strictly positive before `T`. -/
theorem type_i_ansatz_nonnegative_iff
    (profile : ℝ^n → ℝ) (T : ℝ) (x₀ : ℝ^n) (t : ℝ) (ht : t < T) :
    (∀ x, 0 ≤ typeIAnsatz p profile T x₀ x t) ↔
      ∀ y, 0 ≤ profile y := by
  constructor
  · intro hansatz y
    let amplitude := backwardPowerScale (1 / (p - 1)) T t
    let spatialScale := backwardPowerScale (1 / 2) T t
    have hamplitude : 0 < amplitude :=
      backward_power_scale_pos ht
    have hspatial : spatialScale ≠ 0 :=
      (backward_power_scale_pos ht).ne'
    let x := x₀ + spatialScale⁻¹ • y
    have hvalue :
        typeIAnsatz p profile T x₀ x t =
          amplitude * profile y := by
      change
        scaledProfileAnsatz profile
            (backwardPowerScale (1 / (p - 1)) T)
            (backwardPowerScale (1 / 2) T) x₀ x t =
          _
      simpa only [x, amplitude, spatialScale, smul_eq_mul] using
        scaled_profile_ansatz_at_inverse_dilation
          profile
          (backwardPowerScale (1 / (p - 1)) T)
          (backwardPowerScale (1 / 2) T)
          x₀ y t hspatial
    have hproduct : 0 ≤ amplitude * profile y := by
      rw [← hvalue]
      exact hansatz x
    exact nonneg_of_mul_nonneg_right hproduct hamplitude
  · intro hprofile x
    simpa only [typeIAnsatz, backwardSelfSimilarAnsatz, scaledProfileAnsatz, smul_eq_mul] using
      mul_nonneg (backward_power_scale_pos ht).le (hprofile _)

/-- The full parabolic residual factors by the Type I time scale.

The two assumptions do different jobs: `p ≠ 1` proves the reaction balance
`p / (p - 1) = 1 + 1 / (p - 1)`, while nonnegativity at the similarity coordinate justifies
separating the real power of the amplitude-profile product. -/
theorem equation_residual_type_i_ansatz
    (profile : ℝ^n → ℝ) (T : ℝ) (x₀ x : ℝ^n) (t : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hnonneg :
      0 ≤ profile
        (centeredDilation (backwardPowerScale (1 / 2) T t) x₀ x))
    (hp : p ≠ 1) (ht : t < T) :
    equationResidual p (typeIAnsatz p profile T x₀) x t =
      backwardPowerScale (1 / (p - 1) + 1) T t *
        typeIProfileResidual p profile
          (centeredDilation (backwardPowerScale (1 / 2) T t) x₀ x) := by
  change
    equationResidual p
        (backwardSelfSimilarAnsatz profile
          (1 / (p - 1)) (1 / 2) T x₀) x t =
      _
  simpa only [typeIProfileResidual] using
    equation_residual_backward_self_similar_ansatz
      (n := n) p profile (1 / (p - 1)) (1 / 2) T x₀ x t
      hprofile hnonneg ht (by norm_num) (by
        field_simp [sub_ne_zero.mpr hp]
        ring)

/-- At a pre-singular time, the Type I ansatz has zero parabolic residual exactly when the
profile residual vanishes at the corresponding similarity coordinate.

The time-dependent factor in `equation_residual_type_i_ansatz` is strictly positive on `t < T`,
so multiplication by it neither creates nor removes zeros. -/
theorem equation_residual_type_i_ansatz_eq_zero_iff
    (profile : ℝ^n → ℝ) (T : ℝ) (x₀ x : ℝ^n) (t : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hnonneg :
      0 ≤ profile
        (centeredDilation (backwardPowerScale (1 / 2) T t) x₀ x))
    (hp : p ≠ 1) (ht : t < T) :
    equationResidual p (typeIAnsatz p profile T x₀) x t = 0 ↔
      typeIProfileResidual p profile
        (centeredDilation (backwardPowerScale (1 / 2) T t) x₀ x) = 0 := by
  rw [equation_residual_type_i_ansatz p profile T x₀ x t hprofile hnonneg hp ht]
  exact mul_eq_zero_iff_left (backward_power_scale_pos ht).ne'

/-- At any fixed pre-singular time, a nonnegative `C²` function is a Type I profile exactly when
its Type I ansatz has zero parabolic residual at every spatial point.

For the reverse implication, inverse dilation realizes every profile coordinate as a similarity
coordinate because the pre-singular spatial scale is nonzero. -/
theorem has_zero_type_i_profile_residual_iff_equation_residual_type_i_ansatz_eq_zero
    (profile : ℝ^n → ℝ) (T : ℝ) (x₀ : ℝ^n) (t : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hnonneg : ∀ y, 0 ≤ profile y)
    (hp : p ≠ 1) (ht : t < T) :
    HasZeroTypeIProfileResidual (n := n) p profile ↔
      ∀ x, equationResidual p (typeIAnsatz p profile T x₀) x t = 0 := by
  constructor
  · intro hequation x
    exact
      (equation_residual_type_i_ansatz_eq_zero_iff
        p profile T x₀ x t hprofile (hnonneg _) hp ht).2
        (hequation _)
  · intro hansatz y
    let scale := backwardPowerScale (1 / 2) T t
    have hscale : scale ≠ 0 :=
      (backward_power_scale_pos ht).ne'
    let x := x₀ + scale⁻¹ • y
    have hresidual :
        typeIProfileResidual p profile
            (centeredDilation scale x₀ x) =
          0 :=
      (equation_residual_type_i_ansatz_eq_zero_iff
        p profile T x₀ x t hprofile (hnonneg _) hp ht).1
        (hansatz x)
    simpa only [x, centered_dilation_center_add_inv_smul hscale] using hresidual

/-- A nonnegative `C²` Type I profile gives a pointwise classical solution on `t < T`.

The resulting field has joint spacetime `C¹` regularity and globally `C²` spatial slices. This
theorem completes the substitution step but does not assert norm divergence or joint
`C^{2,1}` regularity. -/
theorem HasZeroTypeIProfileResidual.is_pointwise_classical_solution_on_pre_singular
    {profile : ℝ^n → ℝ}
    (hequation : HasZeroTypeIProfileResidual (n := n) p profile)
    (hprofile : ContDiff ℝ 2 profile)
    (hnonneg : ∀ y, 0 ≤ profile y)
    (hp : 1 < p) (T : ℝ) (x₀ : ℝ^n) :
    IsNonnegativePointwiseClassicalSolutionOn
      (n := n) p (Set.Iio T) (typeIAnsatz p profile T x₀) where
  exponent_superlinear := hp
  time_domain_open := isOpen_Iio
  spacetime_contDiffOn := by
    simpa only [typeIAnsatz, backwardSelfSimilarAnsatz] using
      contDiffOn_prod_scaled_profile_ansatz
        profile
        (backwardPowerScale (1 / (p - 1)) T)
        (backwardPowerScale (1 / 2) T)
        x₀ (Set.Iio T)
        (hprofile.of_le (by norm_num))
        (contDiffOn_backward_power_scale (1 / (p - 1)) T)
        (contDiffOn_backward_power_scale (1 / 2) T)
  spatial_slice_contDiff := by
    intro t _ht
    simpa only [typeIAnsatz, backwardSelfSimilarAnsatz] using
      contDiff_scaled_profile_ansatz_slice
        profile
        (backwardPowerScale (1 / (p - 1)) T)
        (backwardPowerScale (1 / 2) T)
        x₀ t hprofile
  nonnegative := by
    intro x t ht
    exact mul_nonneg (backward_power_scale_pos ht).le (hnonneg _)
  equation := by
    intro x t ht
    apply
      (equation_residual_eq_zero_iff p
        (typeIAnsatz p profile T x₀) x t).1
    exact
      (equation_residual_type_i_ansatz_eq_zero_iff
        p profile T x₀ x t hprofile (hnonneg _) hp.ne' ht).2
        (hequation _)

/-- Nonnegativity of a classical Type I solution forces nonnegativity of its profile.

No equation or regularity hypothesis is needed: one pre-singular time slice, inverse dilation,
and positivity of the similarity amplitude suffice. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.profile_nonnegative_of_type_i_ansatz
    {profile : ℝ^n → ℝ} {T : ℝ} {x₀ : ℝ^n}
    (hsolution :
      IsNonnegativePointwiseClassicalSolutionOn
        (n := n) p (Set.Iio T) (typeIAnsatz p profile T x₀)) :
    ∀ y, 0 ≤ profile y := by
  have ht : T - 1 < T := by
    linarith
  exact
    (type_i_ansatz_nonnegative_iff p profile T x₀ (T - 1) ht).1 fun x ↦
      hsolution.nonnegative x (T - 1) ht

/-- A nonnegative pointwise classical solution represented by the Type I ansatz satisfies the
reduced Type I profile equation.

The solution law supplies a zero parabolic residual at `T - 1`; the preceding theorem recovers
the profile sign needed to reverse the exact residual factorization. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.has_zero_type_i_profile_residual_of_type_i_ansatz
    {profile : ℝ^n → ℝ} {T : ℝ} {x₀ : ℝ^n}
    (hsolution :
      IsNonnegativePointwiseClassicalSolutionOn
        (n := n) p (Set.Iio T) (typeIAnsatz p profile T x₀))
    (hprofile : ContDiff ℝ 2 profile) :
    HasZeroTypeIProfileResidual (n := n) p profile := by
  have ht : T - 1 < T := by
    linarith
  have hnonneg :=
    IsNonnegativePointwiseClassicalSolutionOn.profile_nonnegative_of_type_i_ansatz
      (p := p) hsolution
  exact
    (has_zero_type_i_profile_residual_iff_equation_residual_type_i_ansatz_eq_zero
      p profile T x₀ (T - 1) hprofile hnonneg
        hsolution.exponent_superlinear.ne' ht).2 fun x ↦
      IsNonnegativePointwiseClassicalSolutionOn.equation_residual_eq_zero
        (p := p) hsolution x (T - 1) ht

/-- Under the stated regularity and sign assumptions, a function is a Type I profile exactly
when its ansatz is a nonnegative pointwise classical solution on the full pre-singular time
interval.

The forward implication uses the supplied profile sign. The reverse implication recovers that
sign from the solution itself, then inspects its equation at the fixed time `T - 1`. -/
theorem
    has_zero_type_i_profile_residual_iff_is_nonnegative_pointwise_classical_solution_on_pre_singular
    (profile : ℝ^n → ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hnonneg : ∀ y, 0 ≤ profile y)
    (hp : 1 < p) (T : ℝ) (x₀ : ℝ^n) :
    HasZeroTypeIProfileResidual (n := n) p profile ↔
      IsNonnegativePointwiseClassicalSolutionOn
        (n := n) p (Set.Iio T) (typeIAnsatz p profile T x₀) := by
  constructor
  · intro hequation
    exact
      HasZeroTypeIProfileResidual.is_pointwise_classical_solution_on_pre_singular
        (p := p) hequation hprofile hnonneg hp T x₀
  · intro hsolution
    exact
      IsNonnegativePointwiseClassicalSolutionOn.has_zero_type_i_profile_residual_of_type_i_ansatz
        (p := p) hsolution hprofile

/-- If a bounded profile has one nonzero value, its Type I ansatz blows up in spatial supremum norm
at `T`.

The profile need not solve the reduced equation; only the similarity scaling is used. If it also
satisfies the reduced equation and the hypotheses of
`HasZeroTypeIProfileResidual.is_pointwise_classical_solution_on_pre_singular`, the two results
together give a pointwise classical solution that blows up. -/
theorem type_i_ansatz_blows_up_at
    (profile : ℝ^n → ℝ) (hp : 1 < p) (T : ℝ) (x₀ : ℝ^n)
    (y : ℝ^n) (hy : profile y ≠ 0)
    (hbounded : Bornology.IsBounded (Set.range profile)) :
    SpatialSupNormBlowsUpAt (typeIAnsatz p profile T x₀) T := by
  change
    SpatialSupNormBlowsUpAt
      (backwardSelfSimilarAnsatz profile (1 / (p - 1)) (1 / 2) T x₀) T
  exact
    backward_self_similar_ansatz_blows_up_at
      profile (1 / (p - 1)) (1 / 2) T x₀
        (one_div_pos.mpr (sub_pos.mpr hp)) y hy hbounded

end PDE.Solution.Singularity.FiniteTime.NonlinearHeat
