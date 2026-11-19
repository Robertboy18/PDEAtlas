/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData

/-!
# Canonical continuous values of classical closure data

Uniform continuity determines values on the closure, independently of the total
function's arbitrary values outside the open domain. Completion and Tietze give
an ambient continuous representative. Its choice is unique on the closure and
preserves all available interior derivatives.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open Set

variable {n k : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- A derivative word consumes its length in classical closure regularity. -/
theorem iteratedPartialDeriv_of_le (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (α : List (Fin n)) {r : ℕ} (hr : r + α.length ≤ k) :
    ContDiffUpToBoundary r (iteratedPartialDeriv α f) Ω := by
  induction α generalizing r with
  | nil => exact hf.of_le (by simpa using hr)
  | cons i α ih =>
    exact (ih (r := r + 1) (by simpa [Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hr)).partialDeriv_of_succ hopen i

/-- An ambient continuous extension of the interior values. Only its values on
the closure are canonical, and it need not be smooth. -/
def continuousRepresentative (hf : ContDiffUpToBoundary k f Ω) : ℝ^n → ℝ :=
  hf.exists_continuous_eqOn.choose

/-- The chosen representative is continuous. -/
theorem continuous_continuousRepresentative (hf : ContDiffUpToBoundary k f Ω) :
    Continuous hf.continuousRepresentative :=
  hf.exists_continuous_eqOn.choose_spec.1

/-- The chosen representative has the original values in the domain. -/
theorem continuousRepresentative_eqOn (hf : ContDiffUpToBoundary k f Ω) :
    EqOn hf.continuousRepresentative f Ω :=
  hf.exists_continuous_eqOn.choose_spec.2

/-- A prescribed continuous closure representative agrees with the canonical
one everywhere on the closure. -/
theorem continuousRepresentative_eqOn_closure (hf : ContDiffUpToBoundary k f Ω)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (closure Ω)) (hgf : EqOn g f Ω) :
    EqOn hf.continuousRepresentative g (closure Ω) :=
  (hf.continuousRepresentative_eqOn.trans hgf.symm).of_subset_closure
    hf.continuous_continuousRepresentative.continuousOn hg subset_closure Subset.rfl

/-- Passing to canonical values preserves the available classical regularity. -/
theorem regular_continuousRepresentative (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) :
    ContDiffUpToBoundary k hf.continuousRepresentative Ω :=
  hf.congr hopen hf.continuousRepresentative_eqOn

/-- Changing the finite regularity order does not change canonical closure values. -/
theorem continuousRepresentative_eqOn_of_orders (hf : ContDiffUpToBoundary k f Ω)
    {r : ℕ} (hg : ContDiffUpToBoundary r f Ω) :
    EqOn hf.continuousRepresentative hg.continuousRepresentative (closure Ω) :=
  hf.continuousRepresentative_eqOn_closure
    hg.continuous_continuousRepresentative.continuousOn hg.continuousRepresentative_eqOn

end SobolevSpace.ContDiffUpToBoundary
