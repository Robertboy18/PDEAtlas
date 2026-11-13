/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.Basic
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Lower semicontinuity of extended convex energies

Convex norm-closed sublevels are also weakly closed. Applying this fact to real sublevels
preserves the signed extended energy, including its infinite values. The sequential formulation
agrees with norm lower semicontinuity, but the weak result uses topology directly and needs no
separability hypothesis.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Convex

variable {E : Type*}

section TopologicalSpace

variable [TopologicalSpace E]

/-- Norm or topological lower semicontinuity makes the real-height epigraph closed. -/
theorem isClosed_realEpigraph {I : E → EReal} (hI : LowerSemicontinuous I) :
    IsClosed (realEpigraph I) := by
  have hmap : Continuous (fun p : E × ℝ ↦ (p.1, (p.2 : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  exact hI.isClosed_epigraph.preimage hmap

/-- A continuous finite perturbation preserves lower semicontinuity of an extended energy. -/
theorem lowerSemicontinuous_add_real {I : E → EReal} (hI : LowerSemicontinuous I)
    {q : E → ℝ} (hq : Continuous q) :
    LowerSemicontinuous (fun x ↦ I x + (q x : EReal)) := by
  refine hI.add' (continuous_coe_real_ereal.comp hq).lowerSemicontinuous fun x ↦ ?_
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))

/-- In a sequential space the usual sequential liminf condition is lower semicontinuity. -/
theorem lowerSemicontinuous_iff_seq_liminf [SequentialSpace E] {I : E → EReal} :
    LowerSemicontinuous I ↔
      ∀ (u : ℕ → E) (x : E), Tendsto u atTop (𝓝 x) →
        I x ≤ liminf (fun k ↦ I (u k)) atTop := by
  constructor
  · intro hI u x hu
    refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    exact le_liminf_of_le (by isBoundedDefault)
      ((hu.eventually (hI x r hr)).mono fun _ h ↦ h.le)
  · intro hI
    refine lowerSemicontinuous_iff_isClosed_preimage.2 fun r ↦ ?_
    apply IsSeqClosed.isClosed
    intro u x hu hx
    exact (hI u x hx).trans
      (liminf_le_of_frequently_le' (Eventually.of_forall hu).frequently)

end TopologicalSpace

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex norm-lower-semicontinuous proper energy is weakly lower semicontinuous.

Only exclusion of `-∞` is needed here. Properness is needed later to select a finite sublevel
for minimization. -/
theorem lowerSemicontinuous_weak {I : E → EReal} (hbot : ∀ x, I x ≠ ⊥)
    (hconvex : Convex ℝ (realEpigraph I)) (hI : LowerSemicontinuous I) :
    LowerSemicontinuous (fun x : WeakSpace ℝ E ↦ I ((toWeakSpace ℝ E).symm x)) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun r ↦ ?_
  induction r with
  | bot =>
      have hset : (fun x : WeakSpace ℝ E ↦ I ((toWeakSpace ℝ E).symm x)) ⁻¹'
          Iic ⊥ = ∅ := by
        ext x
        simp [hbot]
      rw [hset]
      exact isClosed_empty
  | top => simp
  | coe r =>
      have hclosed : IsClosed {x | I x ≤ (r : EReal)} :=
        hI.isClosed_preimage (r : EReal)
      have heq := (convex_sublevel hconvex r).toWeakSpace_closure ℝ
      rw [hclosed.closure_eq] at heq
      have hweak : IsClosed ((toWeakSpace ℝ E) '' {x | I x ≤ (r : EReal)}) := by
        rw [heq]
        exact isClosed_closure
      convert hweak using 1
      ext x
      constructor
      · intro hx
        exact ⟨(toWeakSpace ℝ E).symm x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy

end NormedSpace

end PDE.Analysis.Convex
