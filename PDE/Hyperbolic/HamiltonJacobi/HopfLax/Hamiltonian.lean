/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Viscosity
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Starting from a prescribed convex Hamiltonian

Superlinearity bounds the dual supremum. Boundedness of the Hamiltonian on
compact balls then gives superlinear growth of that dual. Mathlib supplies
continuous affine minorants of a convex function, with values arbitrarily
close to it at a prescribed point. Riesz representation turns each minorant
into a velocity in the dual supremum, proving that the double dual is the
original Hamiltonian, including at corners.

For a real-valued convex superlinear Hamiltonian in finite dimension,
continuity follows from convexity. Thus the Hopf–Lax construction needs no
differentiability assumption on the Hamiltonian. It gives the
viscosity initial solution for bounded uniformly continuous data.

Double duality is part (ii) of Theorem 3 in Evans, §3.3.2(a), with the roles of `L` and `H`
exchanged; Evans proves it with a supporting hyperplane. The existence theorem is Theorem 3 of
§10.3.4, which Evans proves for a bounded Lipschitz datum.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(a), Theorem 3(ii); §10.3.4, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

set_option linter.missingDocs true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Testing the dual supremum on a fixed-radius ball gives an arbitrarily
large norm lower bound. Continuity of the original Hamiltonian supplies the
uniform bound on that compact ball. -/
theorem superlinear_hamiltonian {H : E → ℝ} (hH : Superlinear H) (hcont : Continuous H) :
    Superlinear (hamiltonian H) := by
  intro A
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) |A|).bddAbove_image hcont.continuousOn
  refine ⟨B, fun q ↦ ?_⟩
  by_cases hq : q = 0
  · subst q
    have hB0 : H 0 ≤ B := hB ⟨0, by simp, rfl⟩
    have hsupport := le_hamiltonian hH (0 : E) 0
    simp only [inner_zero_left, norm_zero, mul_zero] at *
    linarith
  · have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
    let p : E := (A / ‖q‖) • q
    have hpnorm : ‖p‖ = |A| := by
      dsimp only [p]
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hn]
      exact div_mul_cancel₀ _ (ne_of_gt hn)
    have hpB : H p ≤ B :=
      hB ⟨p, by
        simp only [Metric.mem_closedBall, dist_zero_right, hpnorm, le_refl], rfl⟩
    have hpq : inner ℝ q p = A * ‖q‖ := by
      dsimp only [p]
      rw [real_inner_smul_self_right]
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hn)]
    have hsupport := le_hamiltonian hH q p
    rw [hpq] at hsupport
    linarith

/-- Double duality for a real-valued convex superlinear Hamiltonian in
finite dimension. Mathlib's affine minorants approach `H p` from below;
Riesz representation and Fenchel's inequality give the two bounds. -/
theorem biconjugate_eq {H : E → ℝ} (hH : Superlinear H) (hconv : ConvexOn ℝ Set.univ H) {p : E} :
    hamiltonian (hamiltonian H) p = H p := by
  have hcont : Continuous H := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hdual := superlinear_hamiltonian hH hcont
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨r, rfl⟩
    have hf := le_hamiltonian hH r p
    rw [real_inner_comm p r] at hf
    linarith
  · refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
    obtain ⟨ℓ, c, hle, heq⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ)
      (Set.mem_univ p) ha isClosed_univ
      (lowerSemicontinuousOn_univ_iff.mpr hcont.lowerSemicontinuous) hconv
    have hminorant (r : E) : ℓ r + c ≤ H r := hle ⟨r, Set.mem_univ r⟩
    have heq_real : ℓ p + c = a := heq
    let q : E := (InnerProductSpace.toDual ℝ E).symm ℓ
    have hinner (r : E) : inner ℝ q r = ℓ r := InnerProductSpace.toDual_symm_apply
    have hdual_le : hamiltonian H q ≤ -c := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨r, rfl⟩
      change inner ℝ q r - H r ≤ -c
      rw [hinner]
      linarith [hminorant r]
    have hf := le_hamiltonian hdual p q
    rw [real_inner_comm q p, hinner] at hf
    linarith only [heq_real, hdual_le, hf]

/-- Hopf–Lax existence for a prescribed convex superlinear Hamiltonian in
any finite dimension, with bounded uniformly continuous data. The Hamiltonian
may be nonsmooth; its dual growth and double duality are derived. -/
theorem isViscosityInitialSolution_of_convex
    {H g : E → ℝ} (hH : Superlinear H) (hconv : ConvexOn ℝ Set.univ H)
    (hg : UniformContinuous g) (hgb : Bornology.IsBounded (Set.range g)) :
    IsViscosityInitialSolution (fun p _ ↦ H p) g
      (fun z : E × ℝ ↦ value (hamiltonian H) g z.2 z.1) := by
  have hcont : Continuous H := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hdual := superlinear_hamiltonian hH hcont
  have hsol := isViscosityInitialSolution hdual (convexOn_hamiltonian hH) hg hgb
  have heq : hamiltonian (hamiltonian H) = H := by
    funext p
    exact biconjugate_eq hH hconv (p := p)
  rwa [heq] at hsol

end HamiltonJacobi.HopfLax

end
