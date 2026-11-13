/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeightedLp
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.WeakDilation
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Interior weak derivatives of weighted reflection

Finite sums of the normal-dilation weak chain rule give every weak derivative of
the weighted lower branch. No regularity beyond the source weak derivative and
the two `L^p` coordinates is needed. The boundary moment identities are not needed
for this interior calculation; their role is in gluing to the upper branch.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory
open scoped ENNReal

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Mixed weak derivatives of the lower branch increase its normal weight by the
normal multiplicity of the derivative word. -/
theorem hasWeakDerivativeOn_weightedPullbackLp (r : ℕ)
    (u du : DerivLp n p ℝ^n₊) (α : List (Fin n))
    (hweak : HasWeakDerivativeOn ℝ^n₊ α (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn ℝ^n₋ α (weightedPullbackLp n k p r u : ℝ^n → ℝ)
      (weightedPullbackLp n k p (r + α.count (PDE.Common.lastIndex (n := n))) du :
        ℝ^n → ℝ) := by
  let i := PDE.Common.lastIndex (n := n)
  have hterm (j : Fin (k + 1)) :
      HasWeakDerivativeOn ℝ^n₋ α
        (fun x ↦ (reflectionCoeff k j * reflectionNode k j ^ r) *
          u (normalDilation i (reflectionNode k j) x))
        (fun x ↦ (reflectionCoeff k j * reflectionNode k j ^ (r + α.count i)) *
          du (normalDilation i (reflectionNode k j) x)) := by
    let a := reflectionNode k j
    have hd := hasWeakDerivativeOn_dilationPullbackLp n p a (reflectionNode_neg k j)
      u du α hweak
    have hg :
        ((a ^ α.count i • dilationPullbackLp n p a (reflectionNode_neg k j) du :
          DerivLp n p ℝ^n₋) : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₋]
        fun x ↦ a ^ α.count i * du (normalDilation i a x) := by
      filter_upwards [Lp.coeFn_smul (a ^ α.count i)
          (dilationPullbackLp n p a (reflectionNode_neg k j) du),
        dilationPullbackLp_apply_ae n p a (reflectionNode_neg k j) du] with x hx hy
      simp only [hx, Pi.smul_apply, smul_eq_mul, hy, i]
    have hlit := hd.congr_ae
      (dilationPullbackLp_apply_ae n p a (reflectionNode_neg k j) u) hg
    simpa only [Pi.smul_def, smul_eq_mul, pow_add, mul_assoc, a, i] using
      hasWeakDerivativeOn_smul (reflectionCoeff k j * reflectionNode k j ^ r) hlit
  have hsum := hasWeakDerivativeOn_finsetSum Finset.univ _ _ α (fun j _ ↦ hterm j)
  have hlit : HasWeakDerivativeOn ℝ^n₋ α (reflectedJet i k r u)
      (reflectedJet i k (r + α.count i) du) := by
    exact hsum
  exact hlit.congr_ae (weightedPullbackLp_apply_ae n k p r u).symm
    (weightedPullbackLp_apply_ae n k p (r + α.count i) du).symm

end SobolevSpace.GraphSpace.HigherOrderReflection
