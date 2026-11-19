/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Laplacian.Regularity

/-!
# Coordinate differentiation commutes with the Laplacian

Three derivatives suffice to commute a coordinate derivative with the
coordinate Laplacian. The pointwise theorem needs only a C³ germ and
applies to maps into any real normed space. We use the finite-sum rule
and symmetry of the second derivative, including its equality on a
neighborhood before differentiating it once more.
-/

@[expose] public noncomputable section

open Filter PDE
open scoped Topology

namespace PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ^n → E} {x : ℝ^n}

/-- A coordinate derivative commutes with the Laplacian at a C³ point. -/
theorem partialDeriv_laplacian_at (i : Fin n) (hf : ContDiffAt ℝ 3 f x) :
    (∂[i] (laplacian f)) x = laplacian (∂[i] f) x := by
  change (∂[i] (fun y ↦ ∑ j : Fin n, (∂[j] (∂[j] f)) y)) x =
    ∑ j : Fin n, (∂[j] (∂[j] (∂[i] f))) x
  rw [partialDeriv_sum Finset.univ (fun j _ ↦
    ((hf.partialDeriv j (k := 2) (by norm_num)).partialDeriv j
      (k := 1) (by norm_num)).differentiableAt_one)]
  apply Finset.sum_congr rfl
  intro j _
  rw [partialDeriv_partialDeriv_comm_at i j (hf.partialDeriv j (k := 2) (by norm_num))]
  have hnear : (∂[i] (∂[j] f)) =ᶠ[𝓝 x] (∂[j] (∂[i] f)) := by
    filter_upwards [(hf.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).eventually
      (by norm_num)] with y hy
    exact partialDeriv_partialDeriv_comm_at i j hy
  exact congrArg (fun L : ℝ^n →L[ℝ] E ↦ L (EuclideanSpace.single j (1 : ℝ)))
    hnear.fderiv_eq

/-- Function-valued commutation for a C³ map. -/
theorem partialDeriv_laplacian (i : Fin n) (hf : ContDiff ℝ 3 f) :
    (∂[i] (laplacian f)) = laplacian (∂[i] f) := by
  funext x
  exact partialDeriv_laplacian_at i hf.contDiffAt

/-- Commutation holds throughout an open set of C³ regularity. -/
theorem partialDeriv_laplacian_eqOn (i : Fin n) {s : Set (ℝ^n)}
    (hf : ContDiffOn ℝ 3 f s) (hs : IsOpen s) :
    Set.EqOn (∂[i] (laplacian f)) (laplacian (∂[i] f)) s :=
  fun _ hx ↦ partialDeriv_laplacian_at i ((hf _ hx).contDiffAt (hs.mem_nhds hx))

end PDE
