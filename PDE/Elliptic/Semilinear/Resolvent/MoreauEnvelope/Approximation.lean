/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Resolvent.MoreauEnvelope.Basic
import PDE.Analysis.Convex.Differentiable.Supporting

/-!
# Approximation by Moreau envelopes

We give the quantitative approximation properties of the Moreau
envelope of a differentiable convex functional. The envelope lies below the
original functional, with errors controlled by either the Yosida approximation
or the original gradient. It is antitone in the positive regularization
parameter and converges pointwise to the functional as that parameter tends to
zero.

## Main results

* `convexGradientMoreauEnvelope_add_yosida_error_le_self`,
  `self_le_convexGradientMoreauEnvelope_add_gradient_error`: the two-sided
  bounds `M_lambda Phi + (lambda/2) ‖A_lambda‖² ≤ Phi ≤ M_lambda Phi +
  (lambda/2) ‖grad Phi‖²`, where `A_lambda` is the Yosida approximation.
* `convexGradientMoreauEnvelope_antitone_parameter`: `M_lambda Phi` is
  antitone in `lambda > 0`.
* `tendsto_convexGradientMoreauEnvelope`: `M_lambda Phi x → Phi x` as
  `lambda → 0⁺`.

## References

* J.-J. Moreau, "Proximité et dualité dans un espace hilbertien", *Bull. Soc. Math. France* 93
  (1965), 273-299, 7.a, p. 284.
  <https://doi.org/10.24033/bsmf.1625>
* H. Brezis, *Opérateurs maximaux monotones et semi-groupes de contractions dans les espaces
  de Hilbert*, North-Holland Mathematics Studies, North-Holland, 1973.
  <https://doi.org/10.1016/S0304-0208(08)X7125-7>
-/

@[expose] public section

noncomputable section

open Filter Set

open scoped Topology Gradient

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The envelope error controls the squared Yosida approximation:

`M_lambda Phi x + (lambda / 2) * ‖A_lambda x‖² ≤ Phi x`.
-/
theorem convexGradientMoreauEnvelope_add_yosida_error_le_self
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x +
        (lambda / 2) *
          ‖convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x‖ ^ 2 ≤
      Phi x := by
  let J :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le
  let A :=
    convexGradientYosidaApproximation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  have hsub : x - J x = lambda • A x := by
    have hdecomp :=
      convexGradientResolvent_add_smul_yosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x
    change J x + lambda • A x = x at hdecomp
    calc
      x - J x = (J x + lambda • A x) - J x :=
        congrArg (fun u ↦ u - J x) hdecomp.symm
      _ = lambda • A x := by abel
  have htoDual :
      InnerProductSpace.toDual ℝ H (A x) = DPhi (J x) := by
    simpa only [A, J] using
      toDual_convexGradientYosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x
  have hsupport :
      DPhi (J x) (x - J x) ≤ Phi x - Phi (J x) :=
    PDE.Analysis.fderiv_apply_sub_le_sub_of_convex
      hPhiConvex (hPhiDiff (J x)) x
      (Set.mem_univ _) (Set.mem_univ _)
  rw [hsub, ← htoDual] at hsupport
  simp only [map_smul, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply,
    real_inner_self_eq_norm_sq] at hsupport
  rw [convexGradientMoreauEnvelope_eq_add_yosida_norm_sq
    Phi hPhiConvex DPhi hPhiDiff lambda hlambda x]
  change
    Phi (J x) + (lambda / 2) * ‖A x‖ ^ 2 +
        (lambda / 2) * ‖A x‖ ^ 2 ≤
      Phi x
  linarith

/-- The Moreau envelope approximates `Phi` from below with the standard
first-order error bound. -/
theorem self_le_convexGradientMoreauEnvelope_add_gradient_error
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    Phi x ≤
      convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x +
        (lambda / 2) * ‖∇ Phi x‖ ^ 2 := by
  let J :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le
  let A :=
    convexGradientYosidaApproximation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  have hsub : x - J x = lambda • A x := by
    have hdecomp :=
      convexGradientResolvent_add_smul_yosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x
    change J x + lambda • A x = x at hdecomp
    calc
      x - J x = (J x + lambda • A x) - J x :=
        congrArg (fun u ↦ u - J x) hdecomp.symm
      _ = lambda • A x := by abel
  have hsupport :
      Phi x - Phi (J x) ≤ DPhi x (x - J x) := by
    have h :=
      PDE.Analysis.fderiv_apply_sub_le_sub_of_convex
        hPhiConvex (hPhiDiff x) (J x)
        (Set.mem_univ _) (Set.mem_univ _)
    have hneg : J x - x = -(x - J x) := by abel
    rw [hneg, map_neg] at h
    linarith
  rw [hsub, map_smul, smul_eq_mul, ← (hPhiDiff x).fderiv,
    ← toDual_gradient, InnerProductSpace.toDual_apply_apply] at hsupport
  have hyoung :
      2 * inner ℝ (∇ Phi x) (A x) ≤
        ‖∇ Phi x‖ ^ 2 + ‖A x‖ ^ 2 := by
    have hsq : 0 ≤ ‖∇ Phi x - A x‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at hsq
    linarith
  have hscaledYoung :=
    mul_le_mul_of_nonneg_left hyoung hlambda.le
  rw [convexGradientMoreauEnvelope_eq_add_yosida_norm_sq
    Phi hPhiConvex DPhi hPhiDiff lambda hlambda x]
  change
    Phi x ≤
      Phi (J x) + (lambda / 2) * ‖A x‖ ^ 2 +
        (lambda / 2) * ‖∇ Phi x‖ ^ 2
  nlinarith

/-- Increasing the positive regularization parameter decreases the Moreau
envelope. -/
theorem convexGradientMoreauEnvelope_antitone_parameter
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (mu : ℝ) (hmu : 0 < mu)
    (lambda : ℝ) (hlambda : 0 < lambda) (hmulambda : mu ≤ lambda)
    (x : H) :
    convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x ≤
      convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff mu hmu x := by
  let u :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff mu hmu.le x
  have hminimal :
      convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x ≤
        proximalEnergy Phi lambda x u := by
    exact convexGradientMoreauEnvelope_le
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x u
  have hpenalty :
      ‖x - u‖ ^ 2 / (2 * lambda) ≤ ‖x - u‖ ^ 2 / (2 * mu) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlambda)
      (mul_pos (by norm_num) hmu)).2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmulambda (by norm_num))
      (sq_nonneg ‖x - u‖)
  calc
    convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x ≤
        proximalEnergy Phi lambda x u :=
      hminimal
    _ ≤ proximalEnergy Phi mu x u := by
      simp only [proximalEnergy]
      linarith
    _ =
        convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff mu hmu x := rfl

/-- The Moreau envelope converges pointwise to `Phi` as the positive
regularization parameter tends to zero. -/
theorem tendsto_convexGradientMoreauEnvelope
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    {ι : Type*} {l : Filter ι}
    (lambda : ι → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (hlambda_zero : Tendsto lambda l (𝓝 0)) (x : H) :
    Tendsto
      (fun i ↦
        convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff (lambda i) (hlambda i) x)
      l (𝓝 (Phi x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
    (g := fun i ↦ (lambda i / 2) * ‖∇ Phi x‖ ^ 2)
  · exact fun _ ↦ norm_nonneg _
  · intro i
    have hnonpos :
        convexGradientMoreauEnvelope
              Phi hPhiConvex DPhi hPhiDiff (lambda i) (hlambda i) x -
            Phi x ≤
          0 :=
      sub_nonpos.mpr <|
        convexGradientMoreauEnvelope_le_self
          Phi hPhiConvex DPhi hPhiDiff (lambda i) (hlambda i) x
    rw [Real.norm_eq_abs, abs_of_nonpos hnonpos]
    linarith only [
      self_le_convexGradientMoreauEnvelope_add_gradient_error
        Phi hPhiConvex DPhi hPhiDiff (lambda i) (hlambda i) x]
  · simpa only [div_eq_mul_inv, mul_assoc, zero_mul] using
      (hlambda_zero.mul_const (2⁻¹ * ‖∇ Phi x‖ ^ 2))

end PDE.Elliptic.Semilinear
