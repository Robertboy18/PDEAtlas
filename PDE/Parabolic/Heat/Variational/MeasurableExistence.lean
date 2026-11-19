/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.AEBounds
public import PDE.Parabolic.Heat.Variational.MeasurableCoefficients
public import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial

/-!
# Weak parabolic solutions for raw bounded measurable coefficients

The raw joint L∞ coefficients determine measurable evaluations of the form.
Joint ellipticity gives its almost-everywhere Gårding bound. The spectral
Dirichlet trial spaces and the measurable Galerkin theorem then yield the weak
solution for arbitrary L² forcing and L² initial data, with its weak
derivative and continuous L² trace.

This is Evans's §7.1.2, Theorems 3 and 4, under his assumptions (4)-(7), with the
continuous `L²` representative of his §5.9.2, Theorem 3, and the energy estimate on every
initial subinterval. The principal matrix is not assumed symmetric; Evans assumes
`aⁱʲ = aʲⁱ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3 (More calculus), pp. 303-304; §7.1.1, (4),
  p. 372, (5)-(7) and the symmetry assumption, p. 373, and the definition of weak solution, p. 374;
  §7.1.2, Theorem 3 (Existence of weak solution), (32), pp. 378-379, and Theorem 4 (Uniqueness of
  weak solutions), p. 379.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace HeatEquation.Variational.BoundedMeasurableCoefficients

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The canonical pivot load has dual norm at most its spatial L² norm. -/
theorem norm_pivotLoad_le (hΩopen : IsOpen Ω) (f : DerivLp n 2 Ω) :
    ‖(h10L2GelfandTriple hΩopen).pivotToDual f‖ ≤ ‖f‖ := by
  have hinclusion : ‖(h10L2GelfandTriple hΩopen).inclusion‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
      simpa only [one_mul, h10L2GelfandTriple_inclusion_apply] using baseCoordCLM_norm_le v
  exact ((h10L2GelfandTriple hΩopen).norm_pivotToDual_le f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hinclusion (norm_nonneg f))

/-- Raw jointly bounded measurable coefficients give a weak solution with its weak time
derivative, continuous initial trace, and prefix Gårding energy bound. The statement is
existence, as `Nonempty` of the solution structure; uniqueness is `unique_of_ae_equation`.
No operator-norm measurability hypothesis occurs. -/
theorem nonempty_gardingWeakSolutionOn
    (C : BoundedMeasurableCoefficients n Ω (volume.restrict (Ioc a b)))
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hab : a < b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ᵐ z ∂(volume.restrict (Ioc a b)).prod (domainMeasure n Ω),
      ∀ ξ : Fin n → ℝ,
        alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, C.principal i j z * ξ j * ξ i)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) (uInit : DerivLp n 2 Ω) :
    Nonempty (GardingWeakSolutionOn (h10L2GelfandTriple hΩopen) C.form
      (fun t ↦ (h10L2GelfandTriple hΩopen).pivotToDual (f t)) uInit a b
      (alpha / 2) (coerciveShift (n := n) alpha C.bound C.bound)) := by
  let T := h10L2GelfandTriple hΩopen
  let S := h10L2SpectralTrialSystem hΩopen hΩbounded
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f
  have hell : (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ T.pivotToDual (f t) :=
    T.pivotToDual.coeFn_compLpL f
  have hgamma : 0 ≤ coerciveShift (n := n) alpha C.bound C.bound := by
    unfold coerciveShift gardingMass
    positivity
  obtain ⟨U⟩ :=
    @GardingWeakSolutionOn.nonempty_of_ae_garding
      (H¹₀(Ω)) (DerivLp n 2 Ω)
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      T S.space S.finiteDimensional 1 S.projection S.denseEnergy
      C.form a b (alpha / 2) (coerciveShift (n := n) alpha C.bound C.bound)
      ell hab (half_pos halpha) hgamma C.aestronglyMeasurable_form_apply C.formBound
      (Eventually.of_forall C.norm_form_le) (C.ae_garding hΩopen halpha hElliptic) uInit
  exact ⟨U.congrForcing hell⟩

end HeatEquation.Variational.BoundedMeasurableCoefficients
