/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.MeasureTheory.Function.L2Space
import PDE.CalculusOfVariations.DirectMethod
import PDE.CalculusOfVariations.WeakLowerSemicontinuity

/-!
# A convex integral functional on `L²`

The direct method has a simple integral model: for prescribed data
`f ∈ L²(μ; E)`, consider the quadratic fidelity energy

`J_f(u) = ∫ x, ‖u(x) - f(x)‖² ∂μ`.

The density is integrable, and the energy is `2`-strongly convex and
norm-continuous, hence lower semicontinuous for the weak `L²` topology. Its
coercivity lets the direct method produce a unique minimizer. The integral
identity with the squared `L²` distance identifies that minimizer with `f`
and shows that convergence of the energy to zero is equivalent to strong
`L²` convergence to `f`.

Here the identity with a squared norm supplies both lower semicontinuity and
coercivity. Gradient-dependent energies require estimates that account for
spatial derivatives; `SobolevIntegral.lean` treats a jointly convex first-order
Sobolev functional with strong lower semicontinuity and coercivity as hypotheses.
For the direct method for integral functionals of the gradient, see Evans, §8.2.1 and §8.2.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.1 and §8.2.2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set
open MeasureTheory

open scoped ENNReal InnerProductSpace MeasureTheory Topology

namespace PDE.CalculusOfVariations

noncomputable section

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic integral fidelity energy on real Hilbert-valued `L²`. -/
def quadraticIntegralEnergy (f u : α →₂[μ] E) : ℝ :=
  ∫ x, ‖(u - f) x‖ ^ 2 ∂μ

/-- The pointwise quadratic density defining `quadraticIntegralEnergy` is
integrable for every pair of `L²` functions. -/
theorem integrable_quadraticIntegralEnergy_density (f u : α →₂[μ] E) :
    Integrable (fun x ↦ ‖(u - f) x‖ ^ 2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (u - f) (u - f))

omit [InnerProductSpace ℝ E] in
/-- The canonical-representative definition agrees with the usual pointwise
formula `∫ ‖u(x) - f(x)‖²`. -/
theorem quadraticIntegralEnergy_eq_integral_norm_sub (f u : α →₂[μ] E) :
    quadraticIntegralEnergy f u = ∫ x, ‖u x - f x‖ ^ 2 ∂μ := by
  unfold quadraticIntegralEnergy
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u f] with x hx
  simpa only [Pi.sub_apply] using congrArg (fun z : E ↦ ‖z‖ ^ 2) hx

/-- The quadratic integral is exactly the squared `L²` distance to the data. -/
theorem quadraticIntegralEnergy_eq_norm_sq (f u : α →₂[μ] E) :
    quadraticIntegralEnergy f u = ‖u - f‖ ^ 2 := by
  unfold quadraticIntegralEnergy
  simpa only [real_inner_self_eq_norm_sq] using
    (MeasureTheory.L2.inner_def (𝕜 := ℝ) (u - f) (u - f)).symm

/-- The quadratic integral energy vanishes exactly at its prescribed datum. -/
@[simp]
theorem quadraticIntegralEnergy_eq_zero_iff (f u : α →₂[μ] E) :
    quadraticIntegralEnergy f u = 0 ↔ u = f := by
  rw [quadraticIntegralEnergy_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero,
    sub_eq_zero]

/-- The quadratic integral energy is continuous in the strong `L²` topology. -/
theorem continuous_quadraticIntegralEnergy (f : α →₂[μ] E) :
    Continuous (quadraticIntegralEnergy f) := by
  rw [show quadraticIntegralEnergy f = fun u ↦ ‖u - f‖ ^ 2 by
    funext u
    exact quadraticIntegralEnergy_eq_norm_sq f u]
  fun_prop

/-- The quadratic integral energy is `2`-strongly convex on `L²`, in
Mathlib's normalization of strong convexity. -/
theorem strongConvexOn_quadraticIntegralEnergy (f : α →₂[μ] E) :
    StrongConvexOn Set.univ 2 (quadraticIntegralEnergy f) := by
  rw [strongConvexOn_iff_convex]
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b _ _ hab
  simp only [quadraticIntegralEnergy_eq_norm_sq, smul_eq_mul]
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real,
    inner_add_left, inner_smul_left, inner_smul_left]
  norm_num
  nlinarith [sq_nonneg ‖f‖]

/-- The quadratic integral energy is convex on `L²`. -/
theorem convexOn_quadraticIntegralEnergy (f : α →₂[μ] E) :
    ConvexOn ℝ Set.univ (quadraticIntegralEnergy f) := by
  exact
    ((strongConvexOn_quadraticIntegralEnergy f).strictConvexOn
      (by norm_num)).convexOn

/-- The quadratic integral energy is lower semicontinuous for the weak `L²`
topology. -/
theorem lowerSemicontinuous_weakSpace_quadraticIntegralEnergy
    (f : α →₂[μ] E) :
    LowerSemicontinuous
      (fun w : WeakSpace ℝ (α →₂[μ] E) ↦
        quadraticIntegralEnergy f
          ((toWeakSpace ℝ (α →₂[μ] E)).symm w)) := by
  exact lowerSemicontinuous_weakSpace_of_convex
    (quadraticIntegralEnergy f)
    (convexOn_quadraticIntegralEnergy f)
    (continuous_quadraticIntegralEnergy f).lowerSemicontinuous

/-- The quadratic integral energy tends to infinity when the `L²` norm tends
to infinity. -/
theorem quadraticIntegralEnergy_coercive (f : α →₂[μ] E) :
    Tendsto (quadraticIntegralEnergy f)
      (Bornology.cobounded (α →₂[μ] E)) atTop := by
  have hdist :
      Tendsto (fun u : α →₂[μ] E ↦ ‖u - f‖)
        (Bornology.cobounded (α →₂[μ] E)) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_sub_const_cobounded f)
  have hsquare :
      Tendsto (fun u : α →₂[μ] E ↦ ‖u - f‖ ^ 2)
        (Bornology.cobounded (α →₂[μ] E)) atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp hdist
  rw [show quadraticIntegralEnergy f = fun u ↦ ‖u - f‖ ^ 2 by
    funext u
    exact quadraticIntegralEnergy_eq_norm_sq f u]
  exact hsquare

/-- Along any filter, convergence of the quadratic energy to its minimum
value zero is equivalent to strong `L²` convergence to the data. -/
theorem tendsto_quadraticIntegralEnergy_nhds_zero_iff
    {ι : Type*} {l : Filter ι} (f : α →₂[μ] E)
    (u : ι → α →₂[μ] E) :
    Tendsto (fun i ↦ quadraticIntegralEnergy f (u i)) l (𝓝 0) ↔
      Tendsto u l (𝓝 f) := by
  constructor
  · intro henergy
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp henergy
    change Tendsto
      (fun i ↦ √(quadraticIntegralEnergy f (u i))) l
      (𝓝 (√0)) at hsqrt
    simpa only [quadraticIntegralEnergy_eq_norm_sq,
      Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  · intro hu
    have henergy :=
      (continuous_quadraticIntegralEnergy f).continuousAt.tendsto.comp hu
    change Tendsto (fun i ↦ quadraticIntegralEnergy f (u i)) l
      (𝓝 (quadraticIntegralEnergy f f)) at henergy
    simpa only [quadraticIntegralEnergy_eq_norm_sq, sub_self, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using henergy

/-- The direct method produces a unique global minimizer of the quadratic
integral energy, and the integral identity identifies it with the data `f`. -/
theorem existsUnique_global_minimizer_quadraticIntegralEnergy
    [CompleteSpace E] (f : α →₂[μ] E) :
    ∃! u, ∀ v, quadraticIntegralEnergy f u ≤ quadraticIntegralEnergy f v := by
  exact
    existsUnique_global_minimizer_of_weak_lowerSemicontinuous_of_coercive_of_strictConvex
      (quadraticIntegralEnergy f)
      (lowerSemicontinuous_weakSpace_quadraticIntegralEnergy f)
      (quadraticIntegralEnergy_coercive f)
      ((strongConvexOn_quadraticIntegralEnergy f).strictConvexOn
        (by norm_num))

end

end PDE.CalculusOfVariations
