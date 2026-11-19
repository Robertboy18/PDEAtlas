/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import PDE.Parabolic.Heat.Duhamel.Representation
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.Regularity

/-!
# Joint differentiability of the classical Duhamel solution

The spatial derivative and the moving-boundary time derivative are continuous at positive time. The
shared regularity theorem therefore gives joint differentiability, including when time and space
vary together. Evans states this continuity at the end of step 1 of his proof of §2.3.1(c),
Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(c), Theorem 2 (Solution of nonhomogeneous problem),
  step 1 of its proof, p. 50.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open Set PDE.Common

variable {n : ℕ}

/-- The Duhamel solution of a globally `C²`, compactly supported source is jointly differentiable
in time and space at every positive time. -/
theorem differentiableAt_nonhomogeneousSolution_timeSpace_classical
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (p : ℝ × ℝ^n) (hp : 0 < p.1) :
    DifferentiableAt ℝ
      (fun q : ℝ × ℝ^n ↦
        nonhomogeneousSolution (n := n) f q.2 q.1)
      p := by
  have h := (nonhomogeneousSolution_regularity_classical f hf2 hfc).2.1
  have hm : (p.2, p.1) ∈ (univ ×ˢ Ioi 0 : Set (ℝ^n × ℝ)) := ⟨mem_univ _, hp⟩
  have hd : DifferentiableAt ℝ
      (fun q : ℝ^n × ℝ ↦ nonhomogeneousSolution f q.1 q.2) (p.2, p.1) :=
    (h.contDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds hm)).differentiableAt one_ne_zero
  exact hd.comp (f := fun q : ℝ × ℝ^n ↦ (q.2, q.1)) p (by fun_prop)

end HeatEquation
