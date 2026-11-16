/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# Trace-compatible data for higher-order reflection

Higher-order reflection across the flat boundary is bounded on the ambient
derivative bundle.  The zero-trace hypotheses under which it lands in a
global Sobolev space are stated here as closed subspaces of upper-half-space
`H^m`.

For even reflection, the source slices with odd normal multiplicity must
belong to `H¹₀`.  For odd reflection, the source slices with even normal
multiplicity must belong to `H¹₀`.

The module also has the lemma that both reflections use to pass from their one-step weak
derivative recurrences to all derivative words of length at most `m`,
`hasWeakDerivativeOn_of_word_step`.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace HigherOrderReflection

open Set
open scoped ENNReal

variable (n m : ℕ) [Fact (0 < n)]

/--
The closed subspace of upper-half-space `H^m` data compatible with even
reflection.  Every derivative slice below top order having odd normal
multiplicity belongs to `H¹₀`.
-/
noncomputable def evenReflectionSubmodule :
    ClosedSubmodule ℝ (W^{m,2}(ℝ^n₊)) :=
  ⨅ (α : List (Fin n)) (hα : α.length < m)
      (_hodd : ¬ Even (α.count (PDE.Common.lastIndex (n := n)))),
    (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).comap
        (derivativeSlice (n := n) (Ω := ℝ^n₊) α hα)

/-- The even-reflection compatibility submodule is closed in upper-half-space
`H^m`. -/
instance instIsClosed_evenReflectionSubmodule_toSubmodule :
    IsClosed ((evenReflectionSubmodule n m).toSubmodule :
      Set (W^{m,2}(ℝ^n₊))) :=
  (evenReflectionSubmodule n m).isClosed

/-- The type of upper-half-space `H^m` data compatible with even reflection. -/
abbrev EvenReflectionSpace :=
  (evenReflectionSubmodule n m).toSubmodule

/-- Membership in the even-reflection subspace is exactly the expected family
of odd-normal zero-trace conditions. -/
@[simp] theorem mem_evenReflectionSubmodule_iff
    (U : W^{m,2}(ℝ^n₊)) :
    U ∈ evenReflectionSubmodule n m ↔
      ∀ (α : List (Fin n)) (hα : α.length < m),
        ¬ Even (α.count (PDE.Common.lastIndex (n := n))) →
          derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
            (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule := by
  simp [evenReflectionSubmodule]

/--
The closed subspace of upper-half-space `H^m` data compatible with odd
reflection.  Every derivative slice below top order having even normal
multiplicity belongs to `H¹₀`.
-/
noncomputable def oddReflectionSubmodule :
    ClosedSubmodule ℝ (W^{m,2}(ℝ^n₊)) :=
  ⨅ (α : List (Fin n)) (hα : α.length < m)
      (_heven : Even (α.count (PDE.Common.lastIndex (n := n)))),
    (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).comap
        (derivativeSlice (n := n) (Ω := ℝ^n₊) α hα)

/-- The odd-reflection compatibility submodule is closed in upper-half-space
`H^m`. -/
instance instIsClosed_oddReflectionSubmodule_toSubmodule :
    IsClosed ((oddReflectionSubmodule n m).toSubmodule :
      Set (W^{m,2}(ℝ^n₊))) :=
  (oddReflectionSubmodule n m).isClosed

/-- The type of upper-half-space `H^m` data compatible with odd reflection. -/
abbrev OddReflectionSpace :=
  (oddReflectionSubmodule n m).toSubmodule

/-- Membership in the odd-reflection subspace is exactly the expected family
of even-normal zero-trace conditions. -/
@[simp] theorem mem_oddReflectionSubmodule_iff
    (U : W^{m,2}(ℝ^n₊)) :
    U ∈ oddReflectionSubmodule n m ↔
      ∀ (α : List (Fin n)) (hα : α.length < m),
        Even (α.count (PDE.Common.lastIndex (n := n))) →
          derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
            (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule := by
  simp [oddReflectionSubmodule]

/-! ## Weak derivatives from one-step recurrences -/

omit [Fact (0 < n)] in
/-- Iterated weak derivatives from one-step recurrences, for a family indexed by the derivative
words of length at most `m`. If `D []` is locally integrable on `Ω` and, for every word `β` of
length less than `m` and every `i`, `D (β ++ [i])` is the weak `i`-th derivative of `D β` on
`Ω`, then `D α` is the weak `α`-derivative of `D []` on `Ω` for every word `α` of length at most
`m`. This is `hasWeakDerivativeOn_of_append_single_chain_order` for a family that is defined
only on the words of length at most `m`; both reflections use it. -/
theorem hasWeakDerivativeOn_of_word_step {Ω : Set (ℝ^n)}
    (D : (α : List (Fin n)) → α.length ≤ m → ℝ^n → ℝ)
    (hD0 : MeasureTheory.LocallyIntegrableOn (D [] (Nat.zero_le m)) Ω MeasureTheory.volume)
    (hstep : ∀ (β : List (Fin n)) (hβ : β.length < m) (i : Fin n),
      HasWeakDerivativeOn (n := n) Ω [i] (D β (Nat.le_of_lt hβ))
        (D (β ++ [i]) (by simpa [List.length_append] using hβ)))
    (α : List (Fin n)) (hα : α.length ≤ m) :
    HasWeakDerivativeOn (n := n) Ω α (D [] (Nat.zero_le m)) (D α hα) := by
  let D' : List (Fin n) → ℝ^n → ℝ := fun β ↦ if hβ : β.length ≤ m then D β hβ else 0
  have hD0' : MeasureTheory.LocallyIntegrableOn (D' []) Ω MeasureTheory.volume := by
    simpa [D'] using hD0
  have hstep' : ∀ (β : List (Fin n)) (i : Fin n), β.length < m →
      HasWeakDerivativeOn (n := n) Ω [i] (D' β) (D' (β ++ [i])) := by
    intro β i hβ
    have hβLe : β.length ≤ m := Nat.le_of_lt hβ
    have hβiLe : (β ++ [i]).length ≤ m := by
      simpa [List.length_append] using hβ
    simpa [D', hβ, hβLe, hβiLe] using hstep β hβ i
  simpa [D', hα] using hasWeakDerivativeOn_of_append_single_chain_order
    (n := n) (Ω := Ω) m D' hD0' hstep' α hα

end HigherOrderReflection
end GraphSpace
end SobolevSpace
