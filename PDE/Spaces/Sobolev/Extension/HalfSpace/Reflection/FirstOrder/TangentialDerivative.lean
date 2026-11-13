/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TestFunctions
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.IntegralIdentities
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.BoundaryCutoff

/-!
# Tangential weak derivatives of half-space reflections

For `u ∈ W^{1,p}(ℝ^n₊)` and a tangential direction `i ≠ n`, the even reflection `ū` of `u` has
weak derivative `∂ᵢū = (∂ᵢu)‾` on all of `ℝ^n`, and the odd reflection `ũ` has `∂ᵢũ = (∂ᵢu)~`.
Reflection commutes with tangential differentiation, so no sign appears; the whole difficulty
is that the symmetrised test function `φ ± φ ∘ reflect` is not supported inside the open
half-space, and the weak-derivative identity for `u` only applies to tests in `C_c^∞(ℝ^n₊)`.
This is the tangential half of the reflection lemma behind the half-space extension theorem
(Brezis, *Functional Analysis, Sobolev Spaces and PDE*, Chapter 9); the
normal direction, where a sign does appear, is treated in `HalfSpace.FirstOrder.NormalDerivative`.

The boundary-test identity from `HigherOrder.BoundaryCutoff` removes this support restriction.
Its proof tests against `η_{δₘ} ψ`, where `η_δ = cutoffAway δ` vanishes for `xₙ ≤ δ` and `ψ`
is the even or odd part of the test function. Because `i` is tangential, `∂ᵢη_δ = 0`, so no
boundary-strip term arises and the identity at scale `δₘ` is exact. Letting `m → ∞`, dominated
convergence (`tendsto_integral_mul_cutoff`) removes the cutoff.

## Main results

* `hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last`: tangential weak derivatives of the
  even reflection are the even reflections of the tangential weak derivatives.
* `hasWeakDerivativeOn_univ_oddExtend_of_upper_ne_last`: the same for the odd reflection.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
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

/-!
### Weak derivatives for the reflection extensions (`k = 1`)

This is the core step of the reflection lemma: even extension preserves tangential weak
derivatives, and the normal derivative is reflected with an odd symmetry.
-/

/-- The common argument of the even and the odd reflection. Let `E` extend `Lᵖ` classes from
the upper half-space to `ℝ^n` and let `P` act on test functions, with `∫ (E w) φ = ∫_{ℝ^n₊} w (P φ)`
(`hint`) and `P` commuting with the tangential derivative `∂ᵢ`, `i ≠ n` (`hline`). Then `E` maps a
tangential weak derivative on the half-space to a weak derivative on `ℝ^n`. A boundary-cutoff
limit removes the need for a trace assumption. -/
private theorem hasWeakDerivativeOn_univ_extend_of_upper_ne_last
    (E : DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p Set.univ)
    (P : 𝓓((⊤ : Opens (ℝ^n)), ℝ) → 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (hi : i ≠ PDE.Common.lastIndex (n := n))
    (hline : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n),
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) (P φ) :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
      (P (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ))) x)
    (hint : ∀ (w : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      (∫ x, ((E w : DerivLp n p Set.univ) x) * φ.toFun x ∂μ) =
        ∫ x, (w : ℝ^n → ℝ) x * (P φ).toFun x ∂μ₊)
    (u du : DerivLp n p ℝ^n₊)
    (hweak : HasWeakDerivativeOn (n := n) ℝ^n₊ [i] (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
      ((E u : DerivLp n p Set.univ) : ℝ^n → ℝ) ((E du : DerivLp n p Set.univ) : ℝ^n → ℝ) := by
  refine ⟨memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out,
    memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp _) Fact.out, ?_⟩
  intro φ _
  -- Reduce both integrals on `univ` to `ℝ^n₊` integrals via the extension identity `hint`.
  let φi : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ
  -- Tangential tests need no boundary vanishing condition.
  have hUpper :
      (∫ x, (u : ℝ^n → ℝ) x * (⇑(P φi)) x ∂ μ₊)
        =
      (-1 : ℝ) *
        (∫ x, (du : ℝ^n → ℝ) x * (⇑(P φ)) x ∂ μ₊) := by
    let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := P φ
    -- Identify `∂_i ψ` as the part `P` of `∂_i φ`.
    have hpsi :
        (fun x ↦ (∂[i] (⇑ψ)) x) =
          fun x ↦ (⇑(P φi)) x := by
      funext x
      change (∂[i] (⇑(P φ))) x =
        (P
          (_root_.TestFunction.lineDerivCLM ℝ
            (EuclideanSpace.single i (1 : ℝ)) φ :
              𝓓((⊤ : Opens (ℝ^n)), ℝ))) x
      calc
        (∂[i] (⇑(P φ))) x =
            (_root_.TestFunction.lineDerivCLM ℝ
              (EuclideanSpace.single i (1 : ℝ)) (P φ) :
                𝓓((⊤ : Opens (ℝ^n)), ℝ)) x := by
          rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
          rw [((P φ).contDiff.differentiable
            (by simp)).differentiableAt.lineDeriv_eq_fderiv]
          rfl
        _ = _ := hline φ x
    simpa only [TestFunction.toFun_eq_coe, hpsi, neg_one_mul] using
      HigherOrderReflection.integral_mul_partialDeriv_eq_neg_of_boundary
        (n := n) (p := p) i u du hweak ψ (fun h ↦ (hi h).elim)
  -- The extension converts the upper-half-space identity into the whole-space identity.
  have hEvenLHS := hint u φi
  have hEvenRHS := hint du φ
  have hsign : (-1 : ℝ) ^ (List.length [i]) = (-1 : ℝ) := by simp
  calc
    (∫ x,
      ((E u : DerivLp n p Set.univ) x) *
        iteratedPartialDeriv (n := n) [i] (⇑φ) x ∂ μ)
        =
      ∫ x,
        ((E u : DerivLp n p Set.univ) x) * (⇑φi) x ∂ μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            change
              ((E u : DerivLp n p Set.univ) x) * (∂[i] (⇑φ)) x =
                ((E u : DerivLp n p Set.univ) x) *
                  (_root_.TestFunction.lineDerivCLM ℝ
                    (EuclideanSpace.single i (1 : ℝ)) φ :
                      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x
            rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
            rw [(φ.contDiff.differentiable
              (by simp)).differentiableAt.lineDeriv_eq_fderiv]
            rfl
    _ =
      ∫ x, (u : ℝ^n → ℝ) x * (⇑(P φi)) x ∂ μ₊ := by
        simpa using hEvenLHS
    _ =
      (-1 : ℝ) ^ (List.length [i]) *
        (∫ x, (du : ℝ^n → ℝ) x * (⇑(P φ)) x ∂ μ₊) := by
        simpa [hsign, mul_assoc] using hUpper
    _ =
      (-1 : ℝ) ^ (List.length [i]) *
        (∫ x,
          ((E du : DerivLp n p Set.univ) x) * (⇑φ) x ∂ μ) := by
        -- The extension identifies the final upper-half-space integral with its whole-space form.
        simpa using congrArg (fun I ↦ (-1 : ℝ) ^ (List.length [i]) * I) hEvenRHS.symm

/-- The even reflection of a `W^{1,p}` function across the boundary of the upper
half-space has the even reflection of its weak derivative in every tangential
direction. A boundary-cutoff limit removes the need for a trace assumption. -/
theorem hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last (i : Fin n)
    (hi : i ≠ PDE.Common.lastIndex (n := n)) (u du : DerivLp n p ℝ^n₊)
    (hweak : HasWeakDerivativeOn (n := n) ℝ^n₊ [i] (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
      ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) u :
          DerivLp n p Set.univ) : ℝ^n → ℝ)
      ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) du :
          DerivLp n p Set.univ) : ℝ^n → ℝ) :=
  hasWeakDerivativeOn_univ_extend_of_upper_ne_last (n := n) (p := p)
    (_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p)) (evenPartTestFunction (n := n))
    i hi (lineDerivCLM_evenPartTestFunction_of_ne_last (n := n) (i := i) hi)
    (integral_evenExtendLp_mul_testFunction (n := n) (p := p)) u du hweak

/-- The odd reflection of a `W^{1,p}` function across the boundary of the upper half-space has
the odd reflection of its weak derivative in every tangential direction `i ≠ n`. This is the
odd-parity companion of `hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last`; it is needed
for higher-order reflection, where an odd first derivative is differentiated again. -/
theorem hasWeakDerivativeOn_univ_oddExtend_of_upper_ne_last (i : Fin n)
    (hi : i ≠ PDE.Common.lastIndex (n := n)) (u du : DerivLp n p ℝ^n₊)
    (hweak : HasWeakDerivativeOn (n := n) ℝ^n₊ [i] (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
      ((_root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := p) u :
          DerivLp n p Set.univ) : ℝ^n → ℝ)
      ((_root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := p) du :
          DerivLp n p Set.univ) : ℝ^n → ℝ) :=
  hasWeakDerivativeOn_univ_extend_of_upper_ne_last (n := n) (p := p)
    (_root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := p)) (oddPartTestFunction (n := n))
    i hi (lineDerivCLM_oddPartTestFunction_of_ne_last (n := n) (i := i) hi)
    (integral_oddExtendLp_mul_testFunction (n := n) (p := p)) u du hweak

end PositiveDimension

end Proofs

end HalfSpace

end GraphSpace

end Extension

end

end SobolevSpace
