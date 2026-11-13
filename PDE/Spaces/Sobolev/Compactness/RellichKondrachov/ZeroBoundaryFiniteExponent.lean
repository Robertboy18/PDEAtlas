/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.FiniteExponentCompactness
public import PDE.Spaces.Sobolev.Compactness.Rellich.FiniteExponentTranslation

/-!
# Compact inclusion for zero-boundary Sobolev spaces on bounded sets

At every finite exponent `p ≥ 1`, the base-coordinate inclusion from the
supported smooth-core closure `W^{1,p}_0(Ω)` to `Lp(Ω)` is compact when `Ω` is
bounded and measurable. On open sets this is the usual zero-boundary Sobolev
space. Neither a boundary atlas nor a lower bound on the dimension is needed.

Zero extension constructs the global weak derivatives and preserves their
norms. The image of the Sobolev unit ball has bounded support and a uniform
translation estimate, so the finite-exponent compactness criterion applies.
Restriction to `Ω` recovers the original inclusion.

For bounded open `Ω` and finite `p` this is the compact embedding `W^{1,p}_0(U) ⊂⊂ L^p(U)` noted,
for bounded open `U` without the assumption that `∂U` is C¹, in the Remark after Evans §5.7,
Theorem 1. Evans gives no separate proof. Instead of the mollifier argument of his Theorem 1 we use
zero extension and the translation criterion `totallyBounded_Lp_of_bounded_support_translation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Remark after the proof of Theorem 1, p. 289.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.RellichKondrachov

open MeasureTheory Set ZeroTrace
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If `Ω` is bounded and measurable and `1 ≤ p < ∞`, the base coordinate restricted to
`W^{1,p}_0(Ω)` is a compact operator into `L^p(Ω)`. No boundary regularity is assumed; the proof
uses zero extension and translation bounds. -/
theorem wkp0BaseCoordinate_isCompactOperator_of_bounded
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (hp : p ≠ ∞) :
    IsCompactOperator
      ((wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)).comp
        (Submodule.subtypeL (wkp0SubmoduleOn (n := n) (k := 1) (p := p)
          (Ω := Ω)).toSubmodule)) := by
  let F : W₀^{1,p}(Ω) →L[ℝ] DerivLp n p Set.univ :=
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Set.univ)).comp
      (zeroExtendWkp0 hΩ)
  let S := F '' Metric.closedBall (0 : W₀^{1,p}(Ω)) 1
  obtain ⟨R, hR⟩ := hbounded.subset_ball (0 : ℝ^n)
  have htot : TotallyBounded S := by
    apply totallyBounded_Lp_of_bounded_support_translation hp
      S (Metric.isBounded_closedBall.image F) R n (Nat.cast_nonneg n)
    · rintro f ⟨u, _, rfl⟩
      have hsupp := zeroExtendWkp0_coordinate_ae_eq_zero hΩ u (baseIndex n 1)
      filter_upwards [hsupp] with x hx hxBall
      exact hx (fun hxΩ ↦ hxBall (hR hxΩ))
    · rintro f ⟨u, hu, rfl⟩ h
      have hunorm : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
      calc
        ‖Rellich.translateLp p h (F u) - F u‖ ≤ (n : ℝ) * ‖h‖ * ‖u‖ :=
          Rellich.norm_translateLp_zeroExtendWkp0_base_sub_le hΩ hp h u
        _ ≤ (n : ℝ) * ‖h‖ * 1 :=
          mul_le_mul_of_nonneg_left hunorm (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        _ = ‖h‖ * (n : ℝ) := by ring
  have hcompact : IsCompactOperator F := by
    apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image F).mpr
    refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 (by norm_num), ?_⟩
    exact htot.closure.isCompact_of_isClosed isClosed_closure
  let T : DerivLp n p Set.univ →L[ℝ] DerivLp n p Ω :=
    restrictDerivLp (subset_univ Ω)
  have hrestricted : T.comp F =
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)).comp
        (Submodule.subtypeL (wkp0SubmoduleOn (n := n) (k := 1) (p := p)
          (Ω := Ω)).toSubmodule) := by
    apply ContinuousLinearMap.ext
    intro u
    change restrictDerivLp (subset_univ Ω)
        (wkpCoordinateCLM (baseIndex n 1) (zeroExtendWkp0 hΩ u)) =
      wkpCoordinateCLM (baseIndex n 1) (u : W^{1,p}(Ω))
    exact restrict_zeroExtendWkp0_coordinate hΩ u (baseIndex n 1)
  rw [← hrestricted]
  exact hcompact.clm_comp T

end SobolevSpace.GraphSpace.RellichKondrachov
