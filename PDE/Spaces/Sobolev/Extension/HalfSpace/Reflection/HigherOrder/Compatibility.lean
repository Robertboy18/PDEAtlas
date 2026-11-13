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

end HigherOrderReflection
end GraphSpace
end SobolevSpace
