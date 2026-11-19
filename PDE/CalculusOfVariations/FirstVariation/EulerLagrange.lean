/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FirstVariation.BoundaryFlux
public import PDE.CalculusOfVariations.NullLagrangian.Basic
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.ZeroBoundary

/-!
# First variation and the classical Euler–Lagrange expression

For a variation with zero boundary values, the density differential integrates
to the pairing with `-div D_P L + D_z L`. Flux regularity and integrability follow
from finite closure data. Integration by parts uses the zero-trace Sobolev
space, so the variation need not have compact support in the domain.

For `v ∈ C_c^∞(U; ℝ^m)` this is the integration by parts in Evans, §8.1.4(a), that turns `i'(0)`
into the pairing with the left side of the Euler–Lagrange system (16).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(a), (15)-(16), p. 460.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

open Analysis SobolevSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u v : ℝ^n → ℝ^m}

/-- The integrated first variation is the Euler–Lagrange pairing for every
classical variation that vanishes on the boundary. -/
theorem integral_lagrangian_firstVariation_eq
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hzero : ∀ x ∈ frontier Ω, v x = 0) :
    (∫ x in Ω, fderiv ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix u x, (u x, x)) (jacobianMatrix v x, (v x, 0))) =
      ∫ x in Ω, ∑ k, classicalEulerLagrange L u x k * v x k := by
  let A (k : Fin m) (i : Fin n) (x : ℝ^n) :=
    fderiv ℝ (fun P ↦ L P (u x) x) (jacobianMatrix u x) (Matrix.single k i 1)
  let B (k : Fin m) (x : ℝ^n) :=
    fderiv ℝ (fun z ↦ L (jacobianMatrix u x) z x) (u x) (EuclideanSpace.single k 1)
  let V (k : Fin m) (x : ℝ^n) := v x k
  have hA (k : Fin m) (i : Fin n) : ContDiffUpToBoundary 1 (A k i) Ω :=
    contDiffUpToBoundary_lagrangian_matrix_deriv hopen hbounded hL hu k i
  have hB (k : Fin m) : ContDiffUpToBoundary 1 (B k) Ω :=
    contDiffUpToBoundary_lagrangian_value_deriv hopen hbounded hL hu k
  have hvc (k : Fin m) : ContDiff ℝ 1 (V k) :=
    ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.comp hv).of_le (by norm_num)
  have hV (k : Fin m) : ContDiffUpToBoundary 1 (V k) Ω :=
    ContDiffUpToBoundary.of_contDiff (hvc k) hbounded
  have hAV (k : Fin m) (i : Fin n) :
      IntegrableOn (fun x ↦ A k i x * (∂[i] (V k)) x) Ω :=
    (((hA k i).of_le (Nat.zero_le 1)).mul
      ((hV k).partialDeriv_of_succ hopen i) hopen hbounded).integrableOn hopen hbounded
  have hDA (k : Fin m) (i : Fin n) :
      IntegrableOn (fun x ↦ (∂[i] (A k i)) x * V k x) Ω :=
    (((hA k i).partialDeriv_of_succ hopen i).mul
      ((hV k).of_le (Nat.zero_le 1)) hopen hbounded).integrableOn hopen hbounded
  have hBV (k : Fin m) : IntegrableOn (fun x ↦ B k x * V k x) Ω :=
    ((hB k).mul (hV k) hopen hbounded).integrableOn hopen hbounded
  have hSAV (k : Fin m) :
      IntegrableOn (fun x ↦ ∑ i, A k i x * (∂[i] (V k)) x) Ω :=
    integrable_finsetSum _ fun i _ ↦ hAV k i
  have hSDA (k : Fin m) :
      IntegrableOn (fun x ↦ ∑ i, (∂[i] (A k i)) x * V k x) Ω :=
    integrable_finsetSum _ fun i _ ↦ hDA k i
  have hfirst :
      (∫ x in Ω, fderiv ℝ
        (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
        (jacobianMatrix u x, (u x, x)) (jacobianMatrix v x, (v x, 0))) =
      (∫ x in Ω, ∑ k, ∑ i, A k i x * (∂[i] (V k)) x) +
        ∫ x in Ω, ∑ k, B k x * V k x := by
    rw [← integral_add (integrable_finsetSum _ fun k _ ↦ hSAV k)
      (integrable_finsetSum _ fun k _ ↦ hBV k)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    rw [fderiv_lagrangian_apply_matrix_value
      (hL.hasFDerivAt (hopen.preimage (continuous_snd.comp continuous_snd))
        (show (jacobianMatrix u x, (u x, x)) ∈ {a | a.2.2 ∈ Ω} from hx)).differentiableAt]
    simp only [A, B, V, jacobianMatrix, jacobianColumn, Matrix.of_apply, mul_comm]
  have hibp :
      (∫ x in Ω, ∑ k, ∑ i, A k i x * (∂[i] (V k)) x) =
        -(∫ x in Ω, ∑ k, ∑ i, (∂[i] (A k i)) x * V k x) := by
    rw [integral_finsetSum _ fun k _ ↦ hSAV k,
      integral_finsetSum _ fun k _ ↦ hSDA k, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum _ fun i _ ↦ hAV k i,
      integral_finsetSum _ fun i _ ↦ hDA k i, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have : Fact (0 < n) := ⟨Fin.pos i⟩
    exact integral_mul_partialDeriv_eq_neg_of_eq_zero_on_frontier hopen hbounded hgraph
      (hA k i) (hV k) (hvc k).continuous.continuousOn
      (fun x hx ↦ congrArg (fun z : ℝ^m ↦ z k) (hzero x hx)) i
  rw [hfirst, hibp]
  have hn : IntegrableOn
      (fun x ↦ -(∑ k, ∑ i, (∂[i] (A k i)) x * V k x)) Ω :=
    (integrable_finsetSum Finset.univ fun k _ ↦ hSDA k).neg
  have hb : IntegrableOn (fun x ↦ ∑ k, B k x * V k x) Ω :=
    integrable_finsetSum Finset.univ fun k _ ↦ hBV k
  rw [← integral_neg, ← integral_add hn hb]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [classicalEulerLagrange, A, B, V, add_mul, neg_mul,
      Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- The action derivative along a zero-boundary variation is the
Euler–Lagrange pairing, with the sign `-div D_P L + D_z L`. -/
theorem hasDerivAt_lagrangianAction_eulerLagrange
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hzero : ∀ x ∈ frontier Ω, v x = 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + s • v x))
      (∫ x in Ω, ∑ k, classicalEulerLagrange L (fun y ↦ u y + t • v y) x k * v x k)
      t := by
  apply (hasDerivAt_lagrangianAction hopen hbounded hL hu hv t).congr_deriv
  have ht : ContDiff ℝ 2 (fun x ↦ u x + t • v x) :=
    hu.add ((contDiff_const (c := t)).smul hv)
  rw [← integral_lagrangian_firstVariation_eq hopen hbounded hgraph hL ht hv hzero]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    dsimp only
    have hvs : DifferentiableAt ℝ (fun y ↦ t • v y) x :=
      ((contDiff_const (c := t)).smul hv).differentiable (by norm_num) x
    rw [jacobianMatrix_add (hu.differentiable (by norm_num) x)
      hvs,
      jacobianMatrix_const_smul]

end PDE.CalculusOfVariations
