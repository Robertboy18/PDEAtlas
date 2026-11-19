/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions

/-!
# Representative-Level Sobolev Spaces

The representative-level membership condition underlying `W^{k,p}(Ω)`:
a concrete function lies in `L^p(Ω)` and has an `L^p` weak derivative for every derivative word
of order at most `k`. Permutation invariance identifies words encoding the same multi-index.
For `1 ≤ p ≤ ∞` and open `Ω`, this is the definition of Evans §5.2.2 before functions that agree
almost everywhere are identified.

The quotient-level normed space is constructed separately in
`PDE.Spaces.Sobolev.GraphSpace.Model.Definitions` from Mathlib's `MeasureTheory.Lp`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, the definition of `W^{k,p}(U)` and Remark (ii),
  p. 258.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped NNReal

variable {n : ℕ} {p : ℝ≥0∞}

/-- `f` has a weak derivative of order `α` represented by a function in `L^p(Ω)`.

This isolates the derivative clause in the definition of `W^{k,p}(Ω)` in Evans §5.2.2.
Membership of `f` itself in `L^p(Ω)` is imposed by `SobolevSpaceOn`. -/
def HasWeakDerivativeInLpOn (Ω : Set (ℝ^n)) (α : List (Fin n)) (p : ℝ≥0∞)
    (f : ℝ^n → ℝ) : Prop :=
  ∃ g : ℝ^n → ℝ,
    MeasureTheory.MemLp g p (domainMeasure n Ω) ∧
    HasWeakDerivativeOn (n := n) Ω α f g

/-- Having an `L^p` weak derivative depends only on the almost-everywhere
class of the base representative on the domain. -/
theorem hasWeakDerivativeInLpOn_congr_ae
    {Ω : Set (ℝ^n)} {α : List (Fin n)} {f g : ℝ^n → ℝ}
    (hfg : f =ᵐ[domainMeasure n Ω] g) :
    HasWeakDerivativeInLpOn (n := n) Ω α p f ↔
      HasWeakDerivativeInLpOn (n := n) Ω α p g := by
  constructor
  · rintro ⟨d, hdLp, hfd⟩
    exact ⟨d, hdLp,
      (hasWeakDerivativeOn_congr_ae (n := n) hfg (MeasureTheory.ae_eq_refl d)).mp hfd⟩
  · rintro ⟨d, hdLp, hgd⟩
    exact ⟨d, hdLp,
      (hasWeakDerivativeOn_congr_ae (n := n) hfg.symm (MeasureTheory.ae_eq_refl d)).mp hgd⟩

/-- A representative-level package of `Lᵖ` functions and weak-derivative witnesses on `Ω`.

This stores a concrete representative `toFun` and existential weak-derivative data. It does not
identify functions modulo almost-everywhere equality; use `SobolevSpace.GraphSpace.WkpSpaceOn`
for the `Lp`-quotient normed-space packaging.

For `1 ≤ p ≤ ∞` and open `Ω`, this is the representative-level condition defining
`W^{k,p}(Ω)` in Evans §5.2.2. The order-zero witness is then redundant, but retaining it makes local
integrability explicit when this structure is used at other exponents and prevents nonintegrable
functions from entering through the totalized Bochner integral. On a nonopen set the structure
uses the generalized test-function relation documented by `HasWeakDerivativeOn`, so the usual
uniqueness theorem need not apply. -/
structure SobolevSpaceOn (n k : ℕ) (p : ℝ≥0∞) (Ω : Set (ℝ^n)) where
  /-- Representative function. -/
  toFun : ℝ^n → ℝ
  /-- `u ∈ L^p(Ω)` -/
  memLp : MeasureTheory.MemLp toFun p (domainMeasure n Ω)
  /-- For each derivative word `α` with `|α| ≤ k`, `D^α u ∈ L^p(Ω)` in the weak sense. -/
  weak_derivs_inLp : ∀ α : List (Fin n), α.length ≤ k → HasWeakDerivativeInLpOn (n := n) Ω α p toFun

/-- Two representative-level packages are equal as soon as their stored functions are equal:
the membership and weak-derivative fields are proofs of propositions and carry no data. -/
@[ext]
theorem SobolevSpaceOn.ext {k : ℕ} {Ω : Set (ℝ^n)} {u v : SobolevSpaceOn n k p Ω}
    (h : u.toFun = v.toFun) : u = v := by
  cases u with
  | mk uFun uLp uWeak =>
    cases v with
    | mk vFun vLp vWeak =>
      cases h
      have hLp : uLp = vLp := Subsingleton.elim _ _
      have hWeak : uWeak = vWeak := Subsingleton.elim _ _
      simp

/-- A package can be applied to a point; this evaluates the stored representative. -/
instance {k : ℕ} {Ω : Set (ℝ^n)} : CoeFun (SobolevSpaceOn n k p Ω) (fun _ ↦ ℝ^n → ℝ) where
  coe u := u.toFun

/-- Every packaged Sobolev representative is locally integrable on its domain,
independently of the exponent. This follows from its order-zero weak-derivative
witness, not from an implicit assumption that `p ≥ 1`. -/
theorem SobolevSpaceOn.locallyIntegrableOn {k : ℕ} {Ω : Set (ℝ^n)}
    (u : SobolevSpaceOn n k p Ω) :
    MeasureTheory.LocallyIntegrableOn u.toFun Ω MeasureTheory.volume := by
  obtain ⟨d, _hdLp, hud⟩ := u.weak_derivs_inLp [] (Nat.zero_le k)
  exact hud.locallyIntegrable_f

/-- Replace the stored representative by an almost-everywhere equal function.

The resulting structure is different from `u`, since `SobolevSpaceOn` stores
concrete representatives; only the membership proofs are transported. -/
def SobolevSpaceOn.ofAEEq {k : ℕ} {Ω : Set (ℝ^n)}
    (u : SobolevSpaceOn n k p Ω) (f : ℝ^n → ℝ)
    (hfu : f =ᵐ[domainMeasure n Ω] u.toFun) : SobolevSpaceOn n k p Ω where
  toFun := f
  memLp := (MeasureTheory.memLp_congr_ae hfu).mpr u.memLp
  weak_derivs_inLp := by
    intro α hα
    exact (hasWeakDerivativeInLpOn_congr_ae (n := n) (p := p) hfu).mpr
      (u.weak_derivs_inLp α hα)

/-- The representative stored by `ofAEEq` is the supplied function `f`. -/
@[simp] theorem SobolevSpaceOn.ofAEEq_toFun {k : ℕ} {Ω : Set (ℝ^n)}
    (u : SobolevSpaceOn n k p Ω) (f : ℝ^n → ℝ)
    (hfu : f =ᵐ[domainMeasure n Ω] u.toFun) :
    (u.ofAEEq f hfu).toFun = f :=
  rfl

/-- The global representative-level Sobolev package, obtained by taking `Ω = univ`. -/
abbrev GlobalSobolevSpace (n k : ℕ) (p : ℝ≥0∞) : Type :=
  SobolevSpaceOn n k p Set.univ

end SobolevSpace

end
