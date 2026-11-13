/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.ConstantCoefficient
public import PDE.DistributionTheory.Distribution.Support.CompactCarrier

/-!
# Support under constant-coefficient differential operators

Finite linear combinations of iterated directional derivatives preserve every
vanishing region. Consequently, they cannot enlarge distributional support
and preserve compact carriers.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped BigOperators Distributions SchwartzMap

namespace Distribution

section Ordinary

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Iterated directional derivatives preserve the existence of a compact carrier. -/
theorem HasCompactCarrier.iteratedLineDerivOp
    {T : 𝓓'((⊤ : Opens E), F)}
    (hT : HasCompactCarrier T)
    {n : ℕ}
    (m : Fin n → E) :
    HasCompactCarrier (LineDeriv.iteratedLineDerivOp m T) := by
  rcases hT with ⟨K, hK, hTK⟩
  exact ⟨K, hK, hTK.iteratedLineDerivOp m⟩

/-- A finite constant-coefficient differential operator preserves every
vanishing region of an ordinary distribution. -/
theorem IsVanishingOn.constantCoeffLineDerivCLM
    {T : 𝓓'((⊤ : Opens E), F)} {s : Set E}
    (hT : IsVanishingOn T s)
    {N : ℕ}
    (a : Fin N → ℝ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E) :
    IsVanishingOn
      (PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), F)) a order m T)
      s := by
  intro φ hφ
  rw [PDE.Analysis.constantCoeffLineDerivCLM_apply]
  simp only [sum_apply, smul_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [(Distribution.IsVanishingOn.iteratedLineDerivOp hT (m i)) φ hφ, smul_zero]

/-- A finite constant-coefficient differential operator cannot enlarge
ordinary distributional support. -/
theorem dsupport_constantCoeffLineDerivCLM_subset
    (T : 𝓓'((⊤ : Opens E), F))
    {N : ℕ}
    (a : Fin N → ℝ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E) :
    dsupport
        (PDE.Analysis.constantCoeffLineDerivCLM
          (X := 𝓓'((⊤ : Opens E), F)) a order m T) ⊆
      dsupport T :=
  dsupport_subset_dsupport fun _s _hs hT ↦ hT.constantCoeffLineDerivCLM a order m

/-- A finite constant-coefficient differential operator preserves the
existence of a compact carrier. -/
theorem HasCompactCarrier.constantCoeffLineDerivCLM
    {T : 𝓓'((⊤ : Opens E), F)}
    (hT : HasCompactCarrier T)
    {N : ℕ}
    (a : Fin N → ℝ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E) :
    HasCompactCarrier
      (PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), F)) a order m T) := by
  rcases hT with ⟨K, hK, hvan⟩
  exact ⟨K, hK, hvan.constantCoeffLineDerivCLM a order m⟩

end Ordinary

namespace TemperedDistribution

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A finite constant-coefficient differential operator preserves every
vanishing region of a tempered distribution. -/
theorem IsVanishingOn.constantCoeffLineDerivCLM
    {T : 𝓢'(E, F)} {s : Set E}
    (hT : IsVanishingOn T s)
    {N : ℕ}
    (a : Fin N → ℂ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E) :
    IsVanishingOn
      (PDE.Analysis.constantCoeffLineDerivCLM (X := 𝓢'(E, F)) a order m T)
      s := by
  intro φ hφ
  rw [PDE.Analysis.constantCoeffLineDerivCLM_apply]
  simp only [sum_apply, smul_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [(Distribution.TemperedDistribution.IsVanishingOn.iteratedLineDerivOp
    hT (m i)) φ hφ, smul_zero]

/-- A finite constant-coefficient differential operator cannot enlarge
tempered distributional support. -/
theorem dsupport_constantCoeffLineDerivCLM_subset
    (T : 𝓢'(E, F))
    {N : ℕ}
    (a : Fin N → ℂ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E) :
    dsupport (PDE.Analysis.constantCoeffLineDerivCLM (X := 𝓢'(E, F)) a order m T) ⊆
      dsupport T :=
  dsupport_subset_dsupport fun _s _hs hT ↦
    Distribution.TemperedDistribution.IsVanishingOn.constantCoeffLineDerivCLM
      hT a order m

end TemperedDistribution

end Distribution
