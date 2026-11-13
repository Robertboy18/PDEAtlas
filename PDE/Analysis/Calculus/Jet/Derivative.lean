/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Derivatives of evaluated jets

Differentiating an evaluated jet appends directions to the ordinary iterated
Fréchet derivative. The identity identifies mixed derivatives without choosing
a second notion of higher derivative.
-/

@[expose] public section

open scoped ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem iteratedFDeriv_apply_cast {m n : ℕ} (h : m = n)
    (f : E → F) (x : E) (v : Fin n → E) :
    iteratedFDeriv 𝕜 m f x (v ∘ Fin.cast h) = iteratedFDeriv 𝕜 n f x v := by
  subst n
  rfl

namespace PDE

/-- Derivatives of a fixed evaluation of a jet are evaluations of higher jets. -/
theorem iteratedFDeriv_eval_iteratedFDeriv
    {f : E → F} (hf : ContDiff 𝕜 ∞ f)
    (k r : ℕ) (x : E) (v : Fin k → E) (w : Fin r → E) :
    iteratedFDeriv 𝕜 r (fun y ↦ iteratedFDeriv 𝕜 k f y v) x w =
      iteratedFDeriv 𝕜 (r + k) f x (Fin.append w v) := by
  have hval : ContDiff 𝕜 ∞ (fun y ↦ iteratedFDeriv 𝕜 k f y v) :=
    (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin k ↦ E) F v).contDiff.comp
      (hf.iteratedFDeriv_right (by simp))
  induction r generalizing x with
  | zero =>
      have hw : w = Fin.elim0 := Subsingleton.elim _ _
      simpa only [iteratedFDeriv_zero_apply, hw, Fin.elim0_append] using
        (iteratedFDeriv_apply_cast (Nat.zero_add k) f x v).symm
  | succ r ih =>
      have hleft : Differentiable 𝕜
          (iteratedFDeriv 𝕜 r (fun y ↦ iteratedFDeriv 𝕜 k f y v)) :=
        (hval.iteratedFDeriv_right
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl (1 + r))).differentiable
          one_ne_zero
      have hright : Differentiable 𝕜 (iteratedFDeriv 𝕜 (r + k) f) :=
        (hf.iteratedFDeriv_right
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl (1 + (r + k)))).differentiable
          one_ne_zero
      have heq :
          (fun y ↦ iteratedFDeriv 𝕜 r (fun z ↦ iteratedFDeriv 𝕜 k f z v)
            y (Fin.tail w)) =
          (fun y ↦ iteratedFDeriv 𝕜 (r + k) f y (Fin.append (Fin.tail w) v)) :=
        funext fun y ↦ ih y (Fin.tail w)
      calc
        _ = fderiv 𝕜
            (fun y ↦ iteratedFDeriv 𝕜 r (fun z ↦ iteratedFDeriv 𝕜 k f z v)
              y (Fin.tail w)) x (w 0) :=
          (hleft x).iteratedFDeriv_succ_apply_left'
        _ = fderiv 𝕜
            (fun y ↦ iteratedFDeriv 𝕜 (r + k) f y (Fin.append (Fin.tail w) v))
              x (w 0) := by rw [heq]
        _ = iteratedFDeriv 𝕜 (r + k + 1) f x
            (Fin.cons (w 0) (Fin.append (Fin.tail w) v)) :=
          ((hright x).iteratedFDeriv_succ_apply_left'
            (m := Fin.cons (w 0) (Fin.append (Fin.tail w) v))).symm
        _ = _ := by
          conv_rhs => rw [← Fin.cons_self_tail w, Fin.append_cons]
          exact (iteratedFDeriv_apply_cast (Nat.add_right_comm r 1 k) f x
            (Fin.cons (w 0) (Fin.append (Fin.tail w) v))).symm

end PDE
