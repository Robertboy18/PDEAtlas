/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.AlmostEverywhere
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Growth
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Semiconcavity.Hamiltonian
public import PDE.Hyperbolic.HamiltonJacobi.Weak.InitialValue

/-!
# The Hopf–Lax formula as the unique semiconcave weak solution

The Hopf–Lax value for a convex superlinear Hamiltonian is globally Lipschitz
on the forward half-space and solves the equation almost everywhere. Either
semiconcavity of the datum or uniform convexity of the Hamiltonian supplies
Evans's additional spatial bound `C * (1 + 1/t)`.

The final theorem assembles existence and uniqueness under the original
hypotheses of Evans, §3.3.3(b), Theorem 8.
It uses the growth condition (19), a quotient at infinity, and the uniform convexity
condition (35) on the Hessian, and derives the constants that the weak theory needs.
The Lipschitz datum may be unbounded. Equality holds everywhere at nonnegative
times.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), definition of weak solution (38) and
  Theorem 8.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

open MeasureTheory Set Filter Bornology

variable {n : ℕ}

private theorem isWeakInitialSolution_value_of_second_difference {H g : ℝ^n → ℝ}
    (hH : Superlinear H) (hconv : ConvexOn ℝ univ H) {K : NNReal} (hg : LipschitzWith K g) {C : ℝ}
    (hC : 0 < C)
    (hsemi : ∀ x z t, 0 < t → value (hamiltonian H) g t (x + z) - 2 * value (hamiltonian H) g t x +
      value (hamiltonian H) g t (x - z) ≤ C * (1 + t⁻¹) * ‖z‖ ^ 2) :
    Weak.IsInitialSolution H g (fun z ↦ value (hamiltonian H) g z.2 z.1) := by
  have hL := superlinear_hamiltonian hH (continuousOn_univ.mp (hconv.continuousOn isOpen_univ))
  obtain ⟨D, hD, hLD, hbound⟩ := exists_trace_constant hL K
  exact {
    lipschitz := ⟨K + ⟨D, hD⟩, lipschitzOnWith_forward (continuous_hamiltonian hH)
      hL (convexOn_hamiltonian hH) hg hD hLD hbound⟩
    initial := value_zero (hamiltonian H) g
    equation := ae_residual_eq_zero_of_convex hg hH hconv
    semiconcave := ⟨C, hC, hsemi⟩ }

/-- A globally Lipschitz semiconcave datum gives a semiconcave weak Hopf–Lax
solution. An arbitrary initial semiconcavity constant is enlarged to a positive
constant of Evans's time-dependent form. -/
theorem isWeakInitialSolution_value_of_initial_semiconcavity {H g : ℝ^n → ℝ} (hH : Superlinear H)
    (hconv : ConvexOn ℝ univ H) {K : NNReal} (hg : LipschitzWith K g) {C : ℝ}
    (hsemi : ∀ x z, g (x + z) - 2 * g x + g (x - z) ≤ C * ‖z‖ ^ 2) :
    Weak.IsInitialSolution H g (fun z ↦ value (hamiltonian H) g z.2 z.1) := by
  have hC : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine isWeakInitialSolution_value_of_second_difference hH hconv hg hC fun x z t ht ↦ ?_
  have hL := superlinear_hamiltonian hH (continuousOn_univ.mp (hconv.continuousOn isOpen_univ))
  have hbound := second_difference_value_le_of_initial_semiconcavity
    (continuous_hamiltonian hH) hL hg hsemi ht.le x z
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    C ≤ max C 1 := le_max_left _ _
    _ ≤ max C 1 * (1 + t⁻¹) := by
      have htinv : (1 : ℝ) ≤ 1 + t⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr ht.le)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htinv hC.le

/-- A uniformly convex Hamiltonian makes the Hopf–Lax value a semiconcave weak
solution for every globally Lipschitz datum. Superlinearity is derived from
strong convexity, and the weak semiconcavity constant is `θ⁻¹`. -/
theorem isWeakInitialSolution_value_of_strongConvex {H g : ℝ^n → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hconv : StrongConvexOn (univ : Set (ℝ^n)) θ H) {K : NNReal} (hg : LipschitzWith K g) :
    Weak.IsInitialSolution H g (fun z ↦ value (hamiltonian H) g z.2 z.1) := by
  apply isWeakInitialSolution_value_of_second_difference
    (superlinear_of_strongConvex hθ hconv) (hconv.strictConvexOn hθ).convexOn hg (inv_pos.mpr hθ)
  intro x z t ht
  apply (second_difference_value_dual_le_of_strongConvex hθ hconv hg ht x z).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [one_div, mul_inv]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (inv_nonneg.mpr hθ.le)

/-- Evans's differential uniform convexity assumption yields a weak Hopf–Lax
solution. The proof derives strong convexity and superlinearity from the Hessian lower bound. -/
theorem isWeakInitialSolution_value_of_hessian_lower_bound {H g : ℝ^n → ℝ} (hH : ContDiff ℝ 2 H)
    {θ : ℝ} (hθ : 0 < θ) (hbound : ∀ p v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ H) p v v) {K : NNReal}
    (hg : LipschitzWith K g) :
    Weak.IsInitialSolution H g (fun z ↦ value (hamiltonian H) g z.2 z.1) := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  exact isWeakInitialSolution_value_of_strongConvex hθ
    (PDE.Analysis.strongConvexOn_univ_of_hessian_lower_bound
      (hH.differentiable (by norm_num)) hdf.differentiable_one hbound) hg

/-- The Hopf–Lax formula is the unique Evans weak solution when the datum is
semiconcave or the Hamiltonian is uniformly convex. The datum is only globally
Lipschitz and may be unbounded; uniqueness is pointwise on the closed forward
half-space. This is Evans's Theorem 8 in §3.3.3(b). -/
theorem value_is_unique_weakInitialSolution [Fact (0 < n)] {H g : ℝ^n → ℝ} (hH : ContDiff ℝ 2 H)
    (hconv : ConvexOn ℝ univ H) (hgrowth : Tendsto (fun p ↦ H p / ‖p‖) (cobounded (ℝ^n)) atTop)
    {K : NNReal} (hg : LipschitzWith K g)
    (hregularity : (∃ C : ℝ, ∀ x z, g (x + z) - 2 * g x + g (x - z) ≤ C * ‖z‖ ^ 2) ∨
      (∃ θ : ℝ, 0 < θ ∧ ∀ p v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ H) p v v)) :
    Weak.IsInitialSolution H g (fun z ↦ value (hamiltonian H) g z.2 z.1) ∧
      ∀ u : ℝ^n × ℝ → ℝ, Weak.IsInitialSolution H g u →
        EqOn u (fun z ↦ value (hamiltonian H) g z.2 z.1) {z | 0 ≤ z.2} := by
  have hsol : Weak.IsInitialSolution H g (fun z ↦ value (hamiltonian H) g z.2 z.1) := by
    rcases hregularity with ⟨C, hsemi⟩ | ⟨θ, hθ, hbound⟩
    · exact isWeakInitialSolution_value_of_initial_semiconcavity
        ((superlinear_iff_tendsto_div_norm hH.continuous).2 hgrowth) hconv hg hsemi
    · exact isWeakInitialSolution_value_of_hessian_lower_bound hH hθ hbound hg
  exact ⟨hsol, fun u hu ↦ hu.eqOn hH hconv hsol⟩

end HamiltonJacobi.HopfLax
