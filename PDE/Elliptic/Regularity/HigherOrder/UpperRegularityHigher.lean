/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.FlattenedH2
import PDE.Elliptic.Regularity.HigherOrder.HalfSpaceHigher
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Elliptic.Regularity.Boundary.H3.HalfSpaceEstimate
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace

/-!
# Arbitrary-order regularity on the upper half-space

Forcing in `W^{k,2}` and coefficients in `W^{k+1,∞}` give a `W^{k+2,2}` representative of a
zero-trace weak solution on the upper half-space (`exists_principal_higherOrder_on_upper`), when the
normal coefficient is a compact perturbation of a constant (`NormalCoefficientCompactPerturbation`).
This closes the induction of the higher-order boundary successor.

## How it works

Evans proves §6.3.2, Theorem 5 by induction on `m` on a half-ball: step 3 applies the `H²` estimate
to the tangential derivatives `D^α u` with `|α| = m + 1`, and step 4 recovers the remaining normal
derivatives by a second induction on their number. Our induction raises the order by one at each
step. The first two orders are the flattened `H²` and `H³` theorems, `exists_flattened_h2` and
`exists_flattened_h3_on_upper`. At every higher order, the induction hypothesis supplies the
representative required by `exists_principal_higherOrder_succ_upper_of_previous_compactPerturbation`
and also discharges that theorem's preceding-order hypothesis for all differentiated equations.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity) and steps 1-4
  of its proof, (78)-(94), pp. 340-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/--
Global data for the normal principal coefficient on the upper half-space.

`exists_principal_higherOrder_on_upper` uses a `Cᵏ` representative that is
constant outside a compact set. The `base_ae` field identifies this representative
with the normal entry of the Sobolev coefficient matrix.
-/
structure NormalCoefficientCompactPerturbation
    (k : ℕ)
    (A : Fin n → Fin n →
      W^{k + 1,∞}(HalfSpace.upper n)) where
  /-- A globally defined representative of the normal principal coefficient. -/
  representative : ℝ^n → ℝ
  /-- The constant value outside the compact perturbation. -/
  constant : ℝ
  /-- The representative has the `k` classical derivatives used by the boundary induction. -/
  contDiff : ContDiff ℝ k representative
  /-- The representative differs from its constant value only on a compact set. -/
  compactSupport_sub_constant :
    HasCompactSupport (fun x ↦ representative x - constant)
  /-- On the upper half-space, the representative agrees almost everywhere with the
  normal-normal Sobolev coefficient. -/
  base_ae :
    ((((A (PDE.Common.lastIndex (n := n)) (PDE.Common.lastIndex (n := n)) :
        WkpAmbientOn n (k + 1) ∞ (HalfSpace.upper n))
      (baseIndex n (k + 1)) :
        DerivLp n ∞ (HalfSpace.upper n)) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n (HalfSpace.upper n)] representative

/--
Forget excess Sobolev regularity in a compact-perturbation model of the
normal coefficient.
-/
noncomputable def NormalCoefficientCompactPerturbation.lowerOrder
    {q k : ℕ}
    {A : Fin n → Fin n →
      W^{k + 1,∞}(HalfSpace.upper n)}
    (data : NormalCoefficientCompactPerturbation k A)
    (hqk : q ≤ k) :
    NormalCoefficientCompactPerturbation q
      (fun i j ↦
        lowerOrderCLM
          (n := n) (k := q + 1) (m := k + 1) (p := ∞)
          (Ω := HalfSpace.upper n) (by omega) (A i j)) where
  representative := data.representative
  constant := data.constant
  contDiff := data.contDiff.of_le (by exact_mod_cast hqk)
  compactSupport_sub_constant := data.compactSupport_sub_constant
  base_ae := by
    simpa using data.base_ae

/-- A Sobolev representative of a zero-trace weak solution carries the weak equation to its own
first-order part. -/
private theorem isWeakDivergenceSolution_lowerOrder_of_base_ae {m : ℕ} (hm : 1 ≤ m)
    {a : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n)} {f : DerivLp n 2 (HalfSpace.upper n)}
    {u : H¹₀(HalfSpace.upper n)} (U : W^{m,2}(HalfSpace.upper n))
    (hU : baseRepresentative U =ᵐ[domainMeasure n (HalfSpace.upper n)]
      fun x ↦ ⇑(((u : H¹(HalfSpace.upper n)) : WkpAmbientOn n 1 2 (HalfSpace.upper n))
        (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n)) x)
    (hu : IsWeakDivergenceSolution (n := n) (Ω := HalfSpace.upper n) a f u) :
    ∃ h : lowerOrderCLM (n := n) (k := 1) (m := m) (p := 2) (Ω := HalfSpace.upper n) hm U ∈
        (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule,
      IsWeakDivergenceSolution (n := n) (Ω := HalfSpace.upper n) a f ⟨_, h⟩ := by
  have hU1 : lowerOrderCLM (n := n) (k := 1) (m := m) (p := 2) (Ω := HalfSpace.upper n) hm U =
      (u : H¹(HalfSpace.upper n)) := by
    apply WkpSpaceOn.ext_of_base_ae (HalfSpace.isOpen_upper (n := n))
    simpa [baseRepresentative] using hU
  exact ⟨hU1 ▸ u.property, by convert hu; exact Subtype.ext hU1⟩

/--
Qualitative principal regularity on the upper half-space, by induction on the order.

The compact-perturbation hypothesis on the normal coefficient is the global
condition needed to divide by that coefficient on the unbounded half-space
from the first successor step onward.
The representative and ellipticity hypotheses are retained explicitly
because they are the inputs to the flattened `H2` and `H3` base cases.
-/
theorem exists_principal_higherOrder_on_upper
    (k : ℕ)
    (A : Fin n → Fin n →
      W^{k + 1,∞}(HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n (k + 1) ∞ (HalfSpace.upper n))
          (baseIndex n (k + 1)) :
            DerivLp n ∞ (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ (HalfSpace.upper n))
          (baseIndex n (k + 1)) :
            DerivLp n ∞ (HalfSpace.upper n)))
      alpha)
    (hnormal : 2 ≤ k → NormalCoefficientCompactPerturbation k A)
    (F : W^{k,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ (HalfSpace.upper n))
          (baseIndex n (k + 1)) :
            DerivLp n ∞ (HalfSpace.upper n)))
      ((F : WkpAmbientOn n k 2 (HalfSpace.upper n))
        (baseIndex n k) : DerivLp n 2 (HalfSpace.upper n))
      u) :
    ∃ W : W^{k + 2,2}(HalfSpace.upper n),
      baseRepresentative W =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun x ↦
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n)) x) := by
  classical
  induction k using Nat.strong_induction_on generalizing u with
  | h k ih =>
      rcases k with _ | k
      · simpa [baseRepresentative] using exists_flattened_h2 _ a C haLip haRep hA hA.1 _ u
          ((isWeakSolution_iff_isWeakDivergenceSolution (HalfSpace.isOpen_upper (n := n))
            _ _ u).2 hu)
      rcases k with _ | r
      · let A1 (i j : Fin n) : W^{1,∞}(HalfSpace.upper n) := lowerOrderCLM (n := n) (k := 1)
          (m := 2) (p := ∞) (Ω := HalfSpace.upper n) (by norm_num) (A i j)
        obtain ⟨U2, hU2⟩ := exists_flattened_h2 _ a C haLip
          (fun i j ↦ by simpa [A1] using haRep i j) (by simpa [A1] using hA) hA.1 _ u
          ((isWeakSolution_iff_isWeakDivergenceSolution (HalfSpace.isOpen_upper (n := n))
            (fun i j ↦ ((A1 i j : WkpAmbientOn n 1 ∞ (HalfSpace.upper n)) (baseIndex n 1) :
              DerivLp n ∞ (HalfSpace.upper n))) _ u).2 (by simpa [A1] using hu))
        obtain ⟨htrace, hu2⟩ :=
          isWeakDivergenceSolution_lowerOrder_of_base_ae (by omega) U2 hU2 hu
        obtain ⟨W, hW⟩ := exists_flattened_h3_on_upper A a C haLip (by simpa using haRep)
          (by simpa using hA) hA.1 F U2 htrace (by simpa using hu2)
        exact ⟨W, hW.trans hU2⟩
      let q := r + 1
      let Aprev (i j : Fin n) : W^{q + 1,∞}(HalfSpace.upper n) := lowerOrderCLM (n := n)
        (k := q + 1) (m := q + 2) (p := ∞) (Ω := HalfSpace.upper n) (by simp) (A i j)
      let normalData := hnormal (by omega)
      have ihq := ih q (by simp [q]) Aprev (by simpa [Aprev, q] using haRep)
        (by simpa [Aprev, q] using hA)
        fun _ ↦ by simpa [Aprev, q] using normalData.lowerOrder (q := q) (by omega)
      obtain ⟨U, hU⟩ := ihq (lowerOrderCLM (n := n) (k := q) (m := q + 1) (p := 2)
        (Ω := HalfSpace.upper n) (by simp) F) u (by simpa [Aprev, q] using hu)
      obtain ⟨htrace, huU⟩ := isWeakDivergenceSolution_lowerOrder_of_base_ae (by omega) U hU hu
      have hpositive : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
          alpha ≤ normalData.representative x := by
        filter_upwards [aeUniformlyElliptic_diagonal_lower_bound _ hA
          (PDE.Common.lastIndex (n := n)), normalData.base_ae] with x hx hrep
        exact hx.trans_eq hrep
      obtain ⟨W, hW⟩ := exists_principal_higherOrder_succ_upper_of_previous_compactPerturbation
        (by simp) A F U htrace (by simpa [q] using huU) (fun G v hv ↦ ihq G v hv)
        normalData.representative (normalData.contDiff.of_le (by simp)) normalData.constant
        normalData.compactSupport_sub_constant hA.1 hpositive normalData.base_ae
      exact ⟨W, hW.trans hU⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
