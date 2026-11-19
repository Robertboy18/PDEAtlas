/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Basic

/-!
# Transport of a covector Riemann invariant

If the differential of a scalar invariant is parallel to a left eigencovector
of `B`, its composition with a classical solution of `u_t + B(u)u_x = 0`
satisfies scalar transport with that eigenvalue. This is a pointwise chain-rule statement.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.Quasilinear

variable {m : ℕ}

/-- Covector parallelism and the original system imply scalar transport.
The multiplier in the parallelism condition may vanish. -/
theorem riemannInvariant_transport {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m} {u : ℝ^2 → ℝ^m} {w : ℝ^m → ℝ} {p : ℝ^2}
    {speed : ℝ} {left : ℝ^m →L[ℝ] ℝ} (hu : DifferentiableAt ℝ u p) (hw : DifferentiableAt ℝ w (u p))
    (hpde : residual B u p = 0) (hleft : ∀ v, left (B (u p) v) = speed * left v)
    (hparallel : ∃ a : ℝ, fderiv ℝ w (u p) = a • left) :
    (∂[0] (w ∘ u)) p + speed * (∂[1] (w ∘ u)) p = 0 := by
  obtain ⟨a, ha⟩ := hparallel
  have hcovector (v : ℝ^m) :
      fderiv ℝ w (u p) (B (u p) v) = speed * fderiv ℝ w (u p) v := by
    simp only [ha, smul_apply, smul_eq_mul, hleft, mul_left_comm a speed]
  have hderiv (i : Fin 2) :
      (∂[i] (w ∘ u)) p = fderiv ℝ w (u p) ((∂[i] u) p) := by
    unfold partialDeriv
    rw [fderiv_comp p hw hu]
    rfl
  rw [hderiv, hderiv, ← hcovector, ← map_add]
  change fderiv ℝ w (u p) (residual B u p) = 0
  rw [hpde, map_zero]

end PDE.Hyperbolic.Quasilinear
