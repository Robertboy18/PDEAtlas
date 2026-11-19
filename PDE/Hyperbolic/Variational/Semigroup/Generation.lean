/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.Semigroup.Operator
public import PDE.Analysis.Evolution.Semigroup.Generation.Dissipative
public import PDE.Analysis.Evolution.Semigroup.Generation.Identification
public import PDE.Analysis.Variational.LaxMilgram

/-!
# Contraction generation for the autonomous wave operator

The partial wave operator `waveOperator` generates a contraction semigroup on the wave energy
space, and the generator of that semigroup, domain included, is `waveOperator` itself. This is
Theorem 6 of Evans, §7.4.3, for an abstract coercive symmetric form `B` on a Gelfand triple.

## Main results

* `surjective_waveOperator_shift`: every real shift `λ - A` maps the domain onto the energy space.
* `hasContractionResolvent_waveOperator`: the Hille–Yosida resolvent bounds for `λ > 0`.
* `waveContractionSemigroup_isContraction`, `generatorPMap_waveContractionSemigroup`: the
  semigroup contracts the energy norm and its whole generator is the partial wave operator.

## How it works

Lax–Milgram solves the displacement equation with the added mass `λ²`, as in equation (40) of
Evans's proof, and the velocity is then `λu-f`. For the resolvent bound we do not repeat Evans's
generalized Cauchy–Schwarz step: the energy pairing makes the operator skew
(`inner_waveOperator_self`), and `hasContractionResolvent_of_inner_nonpos` turns this and the
range condition into the bound. Evans takes the density of the domain as clear; we derive it from
the same two facts by orthogonal separation
(`HasContractionResolvent.dense_domain_of_inner_nonpos`). Hille–Yosida then constructs the
semigroup and identifies its whole generator with the partial wave operator.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.3, Theorem 6 and its proof, equations (38)-(40);
  §7.4.2, Theorem 4 (Hille–Yosida); §6.2.1, Theorem 1 (Lax–Milgram).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution PDE.Analysis.Variational

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : GelfandTriple (V := V) (H := H))
  (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
  (hsymm : ∀ u v, B u v = B v u)

local notation "W" => WaveEnergySpace (H := H) B hB hsymm
local notation "C" => WaveEnergySpace.coordinates (H := H) B hB hsymm
local notation "A" => waveOperator T B hB hsymm

include hB in
/-- Adding the wave resolvent mass preserves coercivity, even at zero. -/
theorem isCoercive_waveShift (lambda : ℝ) :
    IsCoercive (B + lambda ^ 2 • T.energyToDual) := by
  obtain ⟨c, hc, hbound⟩ := hB
  refine ⟨c, hc, fun u ↦ ?_⟩
  exact (hbound u).trans (le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg lambda) real_inner_self_nonneg))

variable [CompleteSpace V]

/-- Every real shift of the coercive wave operator is onto the energy space. -/
theorem surjective_waveOperator_shift (lambda : ℝ) :
    Function.Surjective (lambda • (A).domain.subtype - (A).toFun) := by
  intro f
  let ell := T.pivotToDual ((C f).2 + lambda • T.inclusion (C f).1)
  let u := solveCLM (B + lambda ^ 2 • T.energyToDual) (isCoercive_waveShift T B hB lambda) ell
  let w := lambda • u - (C f).1
  let x : W := (C).symm (u, T.inclusion w)
  let y : W := (C).symm (w, lambda • T.inclusion w - (C f).2)
  have hBu : B u = -T.pivotToDual (lambda • T.inclusion w - (C f).2) := by
    ext v
    have hu := solveCLM.isWeakSolution (B + lambda ^ 2 • T.energyToDual)
      (isCoercive_waveShift T B hB lambda) ell v
    change B u v + lambda ^ 2 * inner ℝ (T.inclusion u) (T.inclusion v) =
      inner ℝ ((C f).2 + lambda • T.inclusion (C f).1) (T.inclusion v) at hu
    change B u v = -inner ℝ (lambda • T.inclusion w - (C f).2) (T.inclusion v)
    simp only [w, map_sub, map_smul, inner_sub_left, real_inner_smul_left]
    simp only [inner_add_left, real_inner_smul_left] at hu
    nlinarith [hu]
  have hgraph : (x, y) ∈ (A).graph := by
    apply (mem_waveOperator_graph_iff T B hB hsymm x y).mpr
    simpa only [x, y, ContinuousLinearEquiv.apply_symm_apply, true_and] using hBu
  obtain ⟨z, hz, hAz⟩ := (LinearPMap.mem_graph_iff _).mp hgraph
  refine ⟨z, ?_⟩
  change lambda • (z : W) - (A) z = f
  rw [hz, hAz]
  apply (C).injective
  simp only [map_sub, map_smul, x, y, ContinuousLinearEquiv.apply_symm_apply]
  ext
  · change lambda • u - w = (C f).1
    exact sub_sub_cancel _ _
  · exact sub_sub_cancel _ _

/-- The wave energy identity gives all positive contraction resolvent bounds. -/
theorem hasContractionResolvent_waveOperator : HasContractionResolvent (A) :=
  hasContractionResolvent_of_inner_nonpos (fun x ↦ (inner_waveOperator_self T B hB hsymm x).le)
    (fun lambda _ ↦ surjective_waveOperator_shift T B hB hsymm lambda)

variable [CompleteSpace H]

/-- The wave domain is dense in the energy norm. -/
theorem dense_waveOperator_domain : Dense ((A).domain : Set W) :=
  (hasContractionResolvent_waveOperator T B hB hsymm).dense_domain_of_inner_nonpos
    (fun x ↦ (inner_waveOperator_self T B hB hsymm x).le)

/-- The strongly continuous semigroup constructed from the full wave operator. -/
def waveContractionSemigroup : StronglyContinuousSemigroup W :=
  (hasContractionResolvent_waveOperator T B hB hsymm).semigroup
    (dense_waveOperator_domain T B hB hsymm)

/-- The constructed wave semigroup contracts the full energy norm. -/
theorem waveContractionSemigroup_isContraction :
    (waveContractionSemigroup T B hB hsymm).IsContraction :=
  (hasContractionResolvent_waveOperator T B hB hsymm).semigroup_isContraction
    (dense_waveOperator_domain T B hB hsymm)

/-- The whole generator, including its domain, is the partial wave operator. -/
theorem generatorPMap_waveContractionSemigroup :
    (waveContractionSemigroup T B hB hsymm).generatorPMap = (A) :=
  (hasContractionResolvent_waveOperator T B hB hsymm).generatorPMap_semigroup
    (dense_waveOperator_domain T B hB hsymm)

end Hyperbolic.Variational
