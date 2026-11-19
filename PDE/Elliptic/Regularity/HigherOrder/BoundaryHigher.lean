/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Elliptic.Regularity.Boundary.H2.TangentialDifferenceQuotient
import PDE.Elliptic.Regularity.Global.PrincipalHigher
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# Arbitrary-order tangential boundary induction

`exists_principal_higherOrder_tangential_of_previous_upper` is the tangential part of our
higher-order boundary regularity induction on the upper half-space.

An `H^{r+2}` Dirichlet solution need not belong to `H^{r+2}_0`: its normal derivatives generally
have nonzero trace. The flat-boundary difference-quotient argument does, however, show that each
tangential first derivative belongs to `H¹₀` (`tangentialDerivativeWord_mem_H10_upper`). Restricting
the higher Sobolev bundle to order two makes that result available at every order.

The principal differentiated-equation theorem then gives an `H^r` forcing for the tangential
derivative. Applying only the preceding-order regularity theorem promotes this derivative to
`H^{r+2}`. No `H^{r+3}` conclusion for the original solution, and no normal-flux regularity, is
assumed.

In step 3 of the proof of §6.3.2, Theorem 5, Evans differentiates `m + 1` times in tangential
directions and applies the `H²` estimate of Theorem 4 to `D^α u`; we differentiate once and apply
the theorem of the preceding order.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 3 of the proof of Theorem 5, (85)-(90),
  pp. 341-342.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n r : ℕ} [Fact (0 < n)]

/--
Every tangential first derivative of an `H^{r+2}` upper-half-space field
whose base field has zero trace also has zero trace.

Only the order-two restriction of the field is used.  Thus this is the
ordinary Dirichlet condition `H^{r+2} ∩ H¹₀`, not the stronger requirement
that the field lie in `H^{r+2}_0`.
-/
theorem tangentialDerivativeWord_mem_H10_upper
    (U : W^{r + 2,2}(HalfSpace.upper n))
    (htrace0 :
      lowerOrderCLM
          (n := n) (p := 2) (Ω := HalfSpace.upper n) (by omega) U ∈
        (h10SubmoduleOn
          (n := n) (Ω := HalfSpace.upper n)).toSubmodule)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) :
    derivativeWordCLM
        (n := n) (m := r + 2) (r := 1) (p := 2)
        (Ω := HalfSpace.upper n) [k] (by simp) U ∈
      (h10SubmoduleOn
        (n := n) (Ω := HalfSpace.upper n)).toSubmodule := by
  let upper := HalfSpace.upper n
  let U2 : W^{2,2}(upper) :=
    lowerOrderCLM
      (n := n) (k := 2) (m := r + 2) (p := 2) (Ω := upper)
      (by omega) U
  have hU2Base :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := upper)
          (by norm_num) U2 =
        lowerOrderCLM
          (n := n) (k := 1) (m := r + 2) (p := 2) (Ω := upper)
          (by omega) U := by
    simpa [U2] using
      lowerOrderCLM_trans_apply
        (n := n) (r := 1) (k := 2) (m := r + 2) (p := 2)
        (Ω := upper) (by omega) (by omega) U
  have hU2Tangential :
      derivativeWordCLM
          (n := n) (m := 2) (r := 1) (p := 2) (Ω := upper)
          [k] (by simp) U2 =
        derivativeWordCLM
          (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := upper)
          [k] (by simp) U := by
    simpa [U2] using
      derivativeWordCLM_lowerOrderCLM_apply
        (n := n) (m := r + 2) (s := 2) (r := 1) (p := 2)
        (Ω := upper) (by omega) [k] (by simp) U
  have htraceU2 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := upper)
          (by norm_num) U2 ∈
        (h10SubmoduleOn (n := n) (Ω := upper)).toSubmodule := by
    rw [hU2Base]
    exact htrace0
  have htraceTangential :=
    tangentialDerivative_mem_H10 U2 htraceU2 k
      (by simpa [upper] using hk)
  rw [hU2Tangential] at htraceTangential
  exact htraceTangential

/--
Tangential successor step for the upper-half-space boundary induction.

Assume only the preceding principal boundary theorem: every admissible weak
solution with `H^r` forcing has an `H^{r+2}` representative.  Then a
tangential first derivative of the current `H^{r+2}` solution has an
`H^{r+2}` representative.  This theorem does not assemble an
`H^{r+3}` representative for the original solution; the missing normal
derivative is left to normal-flux recovery.
-/
theorem exists_principal_higherOrder_tangential_of_previous_upper
    (A : Fin n → Fin n →
      W^{r + 2,∞}(HalfSpace.upper n))
    (F : W^{r + 1,2}(HalfSpace.upper n))
    (U : W^{r + 2,2}(HalfSpace.upper n))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (htrace0 :
      lowerOrderCLM
          (n := n) (p := 2) (Ω := HalfSpace.upper n) (by omega) U ∈
        (h10SubmoduleOn
          (n := n) (Ω := HalfSpace.upper n)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (r + 2) ∞ (HalfSpace.upper n))
          (baseIndex n (r + 2)) :
            DerivLp n ∞ (HalfSpace.upper n)))
      ((F : WkpAmbientOn n (r + 1) 2 (HalfSpace.upper n))
        (baseIndex n (r + 1)) : DerivLp n 2 (HalfSpace.upper n))
      ⟨lowerOrderCLM
          (n := n) (p := 2) (Ω := HalfSpace.upper n) (by omega) U,
        htrace0⟩)
    (hprevious :
      ∀ (G : W^{r,2}(HalfSpace.upper n))
        (v : H¹₀(HalfSpace.upper n)),
        IsWeakDivergenceSolution
          (n := n) (Ω := HalfSpace.upper n)
          (fun i j ↦
            ((lowerOrderCLM
                (n := n) (k := r + 1) (m := r + 2) (p := ∞)
                (Ω := HalfSpace.upper n) (by simp) (A i j) :
                  WkpAmbientOn n (r + 1) ∞ (HalfSpace.upper n))
              (baseIndex n (r + 1)) :
                DerivLp n ∞ (HalfSpace.upper n)))
          ((G : WkpAmbientOn n r 2 (HalfSpace.upper n))
            (baseIndex n r) : DerivLp n 2 (HalfSpace.upper n))
          v →
        ∃ V : W^{r + 2,2}(HalfSpace.upper n),
          ⇑((V : WkpAmbientOn n (r + 2) 2 (HalfSpace.upper n))
              (baseIndex n (r + 2)) :
                DerivLp n 2 (HalfSpace.upper n))
            =ᵐ[domainMeasure n (HalfSpace.upper n)]
              ⇑(((v : H¹(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
                  (baseIndex n 1) :
                    DerivLp n 2 (HalfSpace.upper n))) :
    ∃ V : W^{r + 2,2}(HalfSpace.upper n),
      ⇑((V : WkpAmbientOn n (r + 2) 2 (HalfSpace.upper n))
          (baseIndex n (r + 2)) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑((derivativeWordCLM
              (n := n) (m := r + 2) (r := r + 1) (p := 2)
              (Ω := HalfSpace.upper n) [k] (by
                simp only [List.length_singleton]
                omega) U :
                W^{r + 1,2}(HalfSpace.upper n)) :
              WkpAmbientOn n (r + 1) 2 (HalfSpace.upper n))
            (baseIndex n (r + 1)) := by
  let htracek :=
    tangentialDerivativeWord_mem_H10_upper U htrace0 k hk
  let uk : H¹₀(HalfSpace.upper n) :=
    ⟨derivativeWordCLM
        (n := n) (m := r + 2) (r := 1) (p := 2)
        (Ω := HalfSpace.upper n) [k] (by simp) U,
      htracek⟩
  obtain ⟨G, hG⟩ :=
    exists_coordinateDerivative_higherOrder_weakEquation_solution
      (HalfSpace.isOpen_upper (n := n)) A F U k htrace0 htracek hu
  have hGuk : IsWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((lowerOrderCLM
            (n := n) (k := r + 1) (m := r + 2) (p := ∞)
            (Ω := HalfSpace.upper n) (by simp) (A i j) :
              WkpAmbientOn n (r + 1) ∞ (HalfSpace.upper n))
          (baseIndex n (r + 1)) :
            DerivLp n ∞ (HalfSpace.upper n)))
      ((G : WkpAmbientOn n r 2 (HalfSpace.upper n))
        (baseIndex n r) : DerivLp n 2 (HalfSpace.upper n))
      uk := by
    simpa [uk, htracek] using hG
  obtain ⟨V, hV⟩ := hprevious G uk hGuk
  refine ⟨V, ?_⟩
  simpa [uk] using hV

end SobolevSpace.GraphSpace.BoundaryRegularity
