/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.IntegralIdentities
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.BoundaryCutoff

/-!
# Normal derivative of the half-space reflection extension

Let `u ∈ W^{1,p}(ℝ^n₊)` with weak normal derivative `∂ₙu = du`, and let `ū` be the even reflection
of `u` across `{xₙ = 0}`. The tangential weak derivatives of `ū` are the even reflections of those
of `u` (proved in `Reflection.FirstOrder.TangentialDerivative`); we prove the remaining identity,
that the weak normal derivative of `ū` on all of `ℝ^n` is the odd reflection of `du`. Together these
give the reflection lemma behind the half-space extension theorem (Brezis,
*Functional Analysis, Sobolev Spaces and PDE*, Chapter 9). Evans, PDE, §5.4, proves the extension
theorem with a different reflection, applied to `C¹` functions and followed by a density argument.

The difficulty is that the odd symmetrisation `ψ = oddPartTestFunction φ` of a test function `φ` on
`ℝ^n` is not compactly supported inside the open half-space, so the weak-derivative identity for `u`
on `ℝ^n₊` cannot be applied to `ψ` directly. We test against `ηδ ψ`, where `ηδ = cutoffAway δ` is a
smooth cutoff vanishing for `xₙ ≤ δ` and equal to one for `xₙ ≥ 2δ`. The product rule produces an
interior term and a boundary-strip term `∫ u · (∂ₙηδ) ψ`. Since `ψ` is odd in `xₙ`, hence
`|ψ(x)| ≤ M xₙ`, while `|∂ₙηδ| ≤ C/δ` on the strip `δ ≤ xₙ ≤ 2δ`, the strip integrand is bounded by
`2CM|u|` on a set whose measure tends to zero, and the strip term vanishes as `δ → 0` by dominated
convergence.

The cutoff error estimate applies to every smooth test that vanishes on the boundary,
including the moment-cancelled tests used by higher-order weighted reflection.

## Main results

* `hasWeakDerivativeOn_univ_evenExtend_of_upper_last`: if `du` is the weak `∂ₙ`-derivative of `u`
  on `ℝ^n₊`, then `oddExtendLp du` is the weak `∂ₙ`-derivative of `evenExtendLp u` on `ℝ^n`.

The `NormalDerivative.CutoffBounds` helpers bound `∂ₙ(cutoffAway δ)` by `C/δ` and locate its support
in the strip `δ < xₙ < 2δ`; the integral identities relating whole-space integrals of even and odd
extensions to half-space integrals come from `Reflection.FirstOrder.IntegralIdentities`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for the reflection lemma for `W^{1,p}` on a half-space.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, whose proof extends `C¹`
  functions across a flat boundary by the higher-order reflection (3), p. 269, in place of the even
  reflection, and then argues by density.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Set MeasureTheory Function
open scoped ENNReal Topology

section

namespace Extension

namespace GraphSpace

open SobolevSpace.GraphSpace


namespace HalfSpace

open _root_.SobolevSpace.HalfSpace

variable (n : ℕ)
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]


section Proofs

open scoped RealInnerProductSpace
open Filter


local notation "μ" => (domainMeasure n (Set.univ : Set (ℝ^n)))
local notation "μ₊" => (domainMeasure n ℝ^n₊)
local notation "μ₋" => (domainMeasure n ℝ^n₋)

section PositiveDimension

variable [Fact (0 < n)]

/-- The normal weak derivative of the even reflection across the boundary of the
upper half-space is the odd reflection of the original normal weak derivative.
The sign change is obtained from the reflected test-function identity. -/
theorem hasWeakDerivativeOn_univ_evenExtend_of_upper_last (u du : DerivLp n p ℝ^n₊)
    (hweak :
      HasWeakDerivativeOn (n := n) ℝ^n₊ [PDE.Common.lastIndex (n := n)]
        (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [PDE.Common.lastIndex (n := n)]
      ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) u :
          DerivLp n p Set.univ) : ℝ^n → ℝ)
      ((_root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := p) du :
          DerivLp n p Set.univ) : ℝ^n → ℝ) := by
  refine ⟨memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out,
    memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out, ?_⟩
  intro φ _
  let i : Fin n := PDE.Common.lastIndex (n := n)
  generalize hφi :
    (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) = φi
  -- Reduce both integrals on `univ` to `ℝ^n₊` integrals via even/odd identities.
  have hEvenLHS := integral_evenExtendLp_mul_testFunction (n := n) (p := p) u φi
  have hOddRHS := integral_oddExtendLp_mul_testFunction (n := n) (p := p) du φ
  -- Work on `ℝ^n₊` with the odd symmetrization `ψ`.
  let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := oddPartTestFunction (n := n) φ
  have hψder :
      iteratedPartialDeriv (n := n) [i] (⇑ψ) =
        (⇑(evenPartTestFunction (n := n) φi)) := by
    funext x
    -- `∂_last(oddPartTestFunction φ) = evenPartTestFunction(∂_last φ)`
    change (∂[PDE.Common.lastIndex (n := n)]
        (⇑(oddPartTestFunction (n := n) φ))) x =
      (evenPartTestFunction (n := n) φi) x
    rw [← hφi]
    rw [← lineDerivCLM_oddPartTestFunction_last (n := n) φ x]
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [((oddPartTestFunction (n := n) φ).contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  -- The general boundary-test identity applies to the odd test, which vanishes on the plane.
  have hUpper :
      (∫ x, (u : ℝ^n → ℝ) x * (⇑(evenPartTestFunction (n := n) φi)) x ∂ μ₊) =
        (-1 : ℝ) * (∫ x, (du : ℝ^n → ℝ) x * ψ x ∂ μ₊) := by
    have h :=
      SobolevSpace.GraphSpace.HigherOrderReflection.integral_mul_partialDeriv_eq_neg_of_boundary
        n p i u du hweak ψ (fun _ x hx ↦ oddPartTestFunction_zero_on_boundary (n := n) φ hx)
    simpa only [← hψder, iteratedPartialDeriv, neg_one_mul, TestFunction.toFun_eq_coe] using h
  -- Reflection identities convert the upper-half-space relation into the whole-space one.
  have hsign : (-1 : ℝ) ^ (List.length [i]) = (-1 : ℝ) := by simp
  calc
    (∫ x,
        ((_root_.SobolevSpace.HalfSpace.evenExtendLp
          (n := n) (p := p) u : DerivLp n p Set.univ) x) *
            iteratedPartialDeriv (n := n) [i] (⇑φ) x ∂ μ)
        =
      ∫ x,
        ((_root_.SobolevSpace.HalfSpace.evenExtendLp
          (n := n) (p := p) u : DerivLp n p Set.univ) x) *
          (⇑φi) x ∂ μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [← hφi]
            change
              ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) u :
                  DerivLp n p Set.univ) x) * (∂[i] (⇑φ)) x =
                ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) u :
                  DerivLp n p Set.univ) x) *
                  (_root_.TestFunction.lineDerivCLM ℝ
                    (EuclideanSpace.single i (1 : ℝ)) φ :
                      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x
            rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
            rw [(φ.contDiff.differentiable
              (by simp)).differentiableAt.lineDeriv_eq_fderiv]
            rfl
    _ =
      ∫ x, (u : ℝ^n → ℝ) x * (⇑(evenPartTestFunction (n := n) φi)) x ∂ μ₊ := by
        simpa using hEvenLHS
    _ =
      (-1 : ℝ) ^ (List.length [i]) *
        (∫ x, (du : ℝ^n → ℝ) x * (⇑ψ) x ∂ μ₊) := by
        simpa [hsign, mul_assoc] using hUpper
    _ =
      (-1 : ℝ) ^ (List.length [i]) *
        (∫ x,
          ((_root_.SobolevSpace.HalfSpace.oddExtendLp
            (n := n) (p := p) du : DerivLp n p Set.univ) x) *
            (⇑φ) x ∂ μ) := by
        -- Odd reflection identifies the final upper-half-space integral with its whole-space form.
        simpa using congrArg (fun I ↦ (-1 : ℝ) ^ (List.length [i]) * I) hOddRHS.symm

end PositiveDimension

end Proofs

end HalfSpace

end GraphSpace

end Extension

end

end SobolevSpace
