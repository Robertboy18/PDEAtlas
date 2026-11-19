/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Resolvent.YosidaApproximation
import Mathlib.Tactic.Positivity.Finset

/-!
# Proximal energies and Moreau envelopes

Let `Phi` be a differentiable convex functional on a real Hilbert space. For
`lambda > 0` and `x`, the resolvent of `grad Phi` is the unique minimizer of

`u ↦ Phi u + ‖x - u‖² / (2 * lambda)`.

The main result is the strong three-point inequality

`E(J x) + ‖u - J x‖² / (2 * lambda) ≤ E(u)`,

where `E` is the proximal energy and `J` is the resolvent. Both this
inequality and uniqueness of the minimizer are the real-valued case of
`PDE.Analysis.Convex.resolvent_three_point_le` and
`PDE.Analysis.Convex.existsUnique_minimizer_proximalEnergy`. The inequality also
gives the basic envelope representation in terms of the Yosida approximation.

Approximation as the parameter tends to zero is developed in
`MoreauEnvelope.Approximation`; differentiability and the Lipschitz gradient
are developed in `MoreauEnvelope.Differentiability`. No additional operator or
optimization structure is introduced.

## Main results

* `proximalEnergy`, `convexGradientResolvent_three_point_le`: the proximal
  energy and the strong three-point inequality.
* `existsUnique_minimizer_proximalEnergy`: the resolvent is the unique
  minimizer of the proximal energy.
* `convexGradientMoreauEnvelope`, `convexGradientMoreauEnvelope_le_self`,
  `convexGradientMoreauEnvelope_eq_add_yosida_norm_sq`: the Moreau envelope,
  its bound by `Phi`, and the representation
  `M_lambda Phi x = Phi (J x) + (lambda/2) ‖A_lambda x‖²`.

## References

* J.-J. Moreau, "Proximité et dualité dans un espace hilbertien", *Bull. Soc. Math. France* 93
  (1965), 273-299, 3.a (p. 278) and 7.a (p. 284).
  <https://doi.org/10.24033/bsmf.1625>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, the definitions of the nonlinear resolvent and of the
  Yosida approximation (7), p. 563.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set

open scoped Topology

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The functional minimized by the proximal map at parameter `lambda` and
base point `x`. -/
def proximalEnergy (Phi : H → ℝ) (lambda : ℝ) (x u : H) : ℝ :=
  Phi u + ‖x - u‖ ^ 2 / (2 * lambda)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The signed extended proximal energy of the coerced potential is the real one. -/
theorem extendedProximalEnergy_coe (Phi : H → ℝ) (lambda : ℝ) (w u : H) :
    PDE.Analysis.Convex.proximalEnergy (fun x ↦ (Phi x : EReal)) lambda w u =
      (proximalEnergy Phi lambda w u : EReal) := by
  simp only [PDE.Analysis.Convex.proximalEnergy, PDE.Analysis.Convex.quadraticPenalty,
    proximalEnergy, EReal.coe_add, norm_sub_rev u w]

/-- The convex-gradient resolvent satisfies the strong three-point
inequality for the proximal energy. -/
theorem convexGradientResolvent_three_point_le
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x u : H) :
    proximalEnergy Phi lambda x
          (convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x) +
        ‖u -
            convexGradientResolvent
              Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x‖ ^ 2 /
          (2 * lambda) ≤
      proximalEnergy Phi lambda x u := by
  have h := PDE.Analysis.Convex.resolvent_three_point_le
      (PDE.Analysis.Convex.isProper_coeReal Phi)
      (PDE.Analysis.Convex.convex_realEpigraph_coeReal hPhiConvex)
      (lowerSemicontinuous_coe_of_hasFDerivAt Phi DPhi hPhiDiff) hlambda x u
  rw [subdifferentialResolvent_eq_convexGradientResolvent Phi hPhiConvex DPhi hPhiDiff hlambda,
    extendedProximalEnergy_coe, extendedProximalEnergy_coe,
    PDE.Analysis.Convex.quadraticPenalty, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  exact h

/-- The convex-gradient resolvent minimizes the proximal energy. -/
theorem convexGradientResolvent_minimizes_proximalEnergy
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    ∀ u,
      proximalEnergy Phi lambda x
          (convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x) ≤
        proximalEnergy Phi lambda x u := by
  intro u
  have hthreePoint :=
    convexGradientResolvent_three_point_le
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x u
  exact
    (le_add_of_nonneg_right
      (div_nonneg (sq_nonneg _)
        (mul_nonneg (by norm_num) hlambda.le))).trans hthreePoint

/-- The proximal energy of a differentiable convex functional has a unique
global minimizer, namely its convex-gradient resolvent. -/
theorem existsUnique_minimizer_proximalEnergy
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    ∃! u, ∀ v,
      proximalEnergy Phi lambda x u ≤ proximalEnergy Phi lambda x v := by
  simpa only [extendedProximalEnergy_coe, EReal.coe_le_coe_iff] using
    PDE.Analysis.Convex.existsUnique_minimizer_proximalEnergy
      (PDE.Analysis.Convex.isProper_coeReal Phi)
      (PDE.Analysis.Convex.convex_realEpigraph_coeReal hPhiConvex)
      (lowerSemicontinuous_coe_of_hasFDerivAt Phi DPhi hPhiDiff) hlambda x

/-- The Moreau envelope of `Phi`, represented by its convex-gradient
resolvent. -/
noncomputable def convexGradientMoreauEnvelope
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) : ℝ :=
  proximalEnergy Phi lambda x
    (convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x)

/-- The Moreau envelope is bounded above by every value of the proximal
energy. -/
theorem convexGradientMoreauEnvelope_le
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x u : H) :
    convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x ≤
      proximalEnergy Phi lambda x u := by
  simpa only [convexGradientMoreauEnvelope] using
    convexGradientResolvent_minimizes_proximalEnergy
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x u

/-- The Moreau envelope lies below the original functional. -/
theorem convexGradientMoreauEnvelope_le_self
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x ≤
      Phi x := by
  simpa [proximalEnergy] using
    convexGradientMoreauEnvelope_le
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x x

/-- The Moreau envelope is the value of `Phi` at the resolvent plus the
quadratic Yosida energy. -/
theorem convexGradientMoreauEnvelope_eq_add_yosida_norm_sq
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x =
      Phi
          (convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x) +
        (lambda / 2) *
          ‖convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x‖ ^ 2 := by
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
  change
    Phi (J x) + ‖x - J x‖ ^ 2 / (2 * lambda) =
      Phi (J x) + (lambda / 2) * ‖A x‖ ^ 2
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  field_simp [hlambda.ne']

end PDE.Elliptic.Semilinear
