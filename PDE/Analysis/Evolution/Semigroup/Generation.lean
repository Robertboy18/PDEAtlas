/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generation.Identification
import PDE.Analysis.Evolution.Semigroup.LaplaceTransform
import PDE.Analysis.Evolution.Semigroup.Yosida

/-!
# The Hille–Yosida theorem for contraction semigroups

For a closed, densely defined linear operator on a real Banach space, the positive
resolvent range and norm conditions characterize contraction-semigroup generation.
This is the Hille–Yosida theorem, Evans §7.4.2, Theorem 4.

The inverse estimate is stated on the original domain as
`‖x‖ ≤ λ⁻¹ ‖λx - Ax‖`, together with surjectivity of `λI - A`. It gives injectivity
and constructs the bounded inverse with norm at most `λ⁻¹`, so it is Evans's condition (17).
Closedness is retained in the characterization; it also follows from the generation
construction under density and these resolvent conditions.

## How it works

We follow Evans's proof. For necessity, the Laplace transform of the semigroup inverts
`λ - A` with norm at most `λ⁻¹` (Evans §7.4.1, Theorem 3(ii);
`StronglyContinuousSemigroup.hasContractionResolvent_generatorPMap`), and closedness and
density are Theorem 2 (`StronglyContinuousSemigroup.isClosed_generatorPMap`,
`StronglyContinuousSemigroup.dense_generatorPMap_domain_of_complete`). For sufficiency we form
the bounded Yosida approximations `A_λ = λ(λR_λ - I)`
(`HasContractionResolvent.yosidaApproximation`), exponentiate them to contraction semigroups,
prove that their orbits converge uniformly on bounded time intervals, and show that the limit
`HasContractionResolvent.semigroup` has generator exactly `A`
(`HasContractionResolvent.generatorPMap_semigroup`). These are steps 2-6 of Evans's proof.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.2, Theorem 4 (Hille–Yosida theorem) and its proof,
  (17)-(22), pp. 439-441. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace HasContractionResolvent

/-- The positive resolvent conditions and density generate a contraction semigroup. -/
theorem exists_contractionSemigroup {A : E →ₗ.[ℝ] E} (hA : HasContractionResolvent A)
    (hdense : Dense (A.domain : Set E)) :
    ∃ T : StronglyContinuousSemigroup E, T.IsContraction ∧ T.generatorPMap = A :=
  ⟨hA.semigroup hdense, hA.semigroup_isContraction hdense, hA.generatorPMap_semigroup hdense⟩

end HasContractionResolvent

namespace StronglyContinuousSemigroup

/-- The Laplace inverse realizes the resolvent hypotheses for every contraction generator. -/
theorem hasContractionResolvent_generatorPMap (T : StronglyContinuousSemigroup E)
    (hT : T.IsContraction) : HasContractionResolvent T.generatorPMap where
  surjective := fun _ hlambda x ↦ T.exists_generator_shift_eq hT hlambda x
  bound := by
    intro lambda hlambda x
    calc
      ‖(x : E)‖ =
          ‖T.laplaceTransform hT hlambda (lambda • (x : E) - T.generatorPMap x)‖ := by
        rw [T.laplaceTransform_generator_identity hT hlambda x]
      _ ≤ ‖T.laplaceTransform hT hlambda‖ *
          ‖lambda • (x : E) - T.generatorPMap x‖ :=
        (T.laplaceTransform hT hlambda).le_opNorm _
      _ ≤ lambda⁻¹ * ‖lambda • (x : E) - T.generatorPMap x‖ :=
        mul_le_mul_of_nonneg_right (T.norm_laplaceTransform_le hT hlambda) (norm_nonneg _)

end StronglyContinuousSemigroup

/-- The Hille–Yosida theorem (Evans §7.4.2, Theorem 4), with closedness and density of the
domain moved into the condition; every generator has both properties (Evans §7.4.1, Theorem 2).

The generated semigroup is unique: `StronglyContinuousSemigroup.eq_of_generatorPMap_eq`
in `PDE.Analysis.Evolution.Semigroup.Uniqueness` identifies any two strongly continuous
semigroups with this generator. -/
theorem hille_yosida (A : E →ₗ.[ℝ] E) :
    (A.IsClosed ∧ Dense (A.domain : Set E) ∧ HasContractionResolvent A) ↔
      ∃ T : StronglyContinuousSemigroup E, T.IsContraction ∧ T.generatorPMap = A := by
  constructor
  · rintro ⟨_, hdense, hA⟩
    exact hA.exists_contractionSemigroup hdense
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T.isClosed_generatorPMap, T.dense_generatorPMap_domain_of_complete,
      T.hasContractionResolvent_generatorPMap hT⟩

end PDE.Analysis.Evolution
