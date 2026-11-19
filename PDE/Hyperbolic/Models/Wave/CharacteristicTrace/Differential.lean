/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.Surface
public import PDE.FDeriv.SpaceTime.Gradient.Basic
public import PDE.FDeriv.Operators
public import PDE.Hyperbolic.Models.Wave.Operator
import PDE.Analysis.InnerProductSpace.Calculus.Normalization

/-!
# Differential identities on characteristic graphs

The backward-cone current combines the spatial gradient and radial velocity.
Its divergence cancels the mixed second derivatives and expresses the wave
operator with the geometric coefficient `(n-1)/r`.
-/

@[expose] public noncomputable section

open PDE PDE.Common PDE.Analysis Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace Gradient

namespace WaveEquation

variable {n : ℕ}

/-- Pullback of a differentiable scalar to a backward cone. -/
theorem partialDeriv_comp_backwardConeGraph {u : ℝ^(n + 1) → ℝ} (c : ℝ^n) (T : ℝ) {x : ℝ^n}
    (hx : x ≠ c) (hu : DifferentiableAt ℝ u (backwardConeGraph c T x)) (i : Fin n) :
    ∂[i] (u ∘ backwardConeGraph c T) x = ∂[i.succ] u (backwardConeGraph c T x) -
      NormedSpace.normalize (x - c) i * ∂[0] u (backwardConeGraph c T x) := by
  have hd := hu.hasFDerivAt.comp x (hasFDerivAt_backwardConeGraph c T hx)
  rw [partialDeriv, hd.fderiv, ContinuousLinearMap.comp_apply,
    coneGraphDifferential_apply, fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [Fin.sum_univ_succ, timeSpaceCons_zero, timeSpaceCons_succ,
    EuclideanSpace.inner_single_right]
  simp [mul_comm, sub_eq_add_neg, add_comm]

private theorem partialDeriv_normalize_coord (c : ℝ^n) {x : ℝ^n} (hx : x ≠ c) (i : Fin n) :
    ∂[i] (fun y : ℝ^n ↦ NormedSpace.normalize (y - c) i) x =
      ‖x - c‖⁻¹ - (‖x - c‖⁻¹) ^ 3 * (x - c) i ^ 2 := by
  have hd := (NormedSpace.hasFDerivAt_normalize (sub_ne_zero.mpr hx)).comp x
    ((hasFDerivAt_id x).sub_const c)
  have hi := (EuclideanSpace.proj i).hasFDerivAt.comp x hd
  have he := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hi.fderiv
  simpa [partialDeriv, EuclideanSpace.proj, Function.comp_def,
    ContinuousLinearMap.comp_apply, EuclideanSpace.inner_single_right, pow_two, mul_assoc] using he

/-- The radial unit vector has divergence `(n-1)/r` off the center. -/
private theorem sum_partialDeriv_normalize_coord (c : ℝ^n) {x : ℝ^n} (hx : x ≠ c) :
    (∑ i : Fin n, ∂[i] (fun y : ℝ^n ↦ NormedSpace.normalize (y - c) i) x) =
      ((n : ℝ) - 1) / ‖x - c‖ := by
  simp_rw [partialDeriv_normalize_coord c hx]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  field_simp

/-- The characteristic current is the spatial gradient plus the outgoing radial
velocity. Its divergence has no mixed second derivatives. -/
def characteristicCurrent (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (T : ℝ)
    (x : ℝ^n) : ℝ^n :=
  spatialGradient u (backwardConeGraph c T x) +
    ∂[0] u (backwardConeGraph c T x) • NormedSpace.normalize (x - c)

/-- Coordinate form of the characteristic current. -/
@[simp]
theorem characteristicCurrent_apply (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (T : ℝ) (x : ℝ^n) (i : Fin n) :
    characteristicCurrent u c T x i = ∂[i.succ] u (backwardConeGraph c T x) +
      ∂[0] u (backwardConeGraph c T x) * NormedSpace.normalize (x - c) i := by
  simp [characteristicCurrent]

private theorem contDiffAt_coneGraph (c : ℝ^n) (T : ℝ) {x : ℝ^n}
    (hx : x ≠ c) : ContDiffAt ℝ 1 (backwardConeGraph c T) x :=
  (contDiffOn_backwardConeGraph c T).contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)

private theorem contDiffAt_normalize_coord (c : ℝ^n) {x : ℝ^n} (hx : x ≠ c) (i : Fin n) :
    ContDiffAt ℝ 1 (fun y : ℝ^n ↦ NormedSpace.normalize (y - c) i) x :=
  (EuclideanSpace.proj i).contDiff.contDiffAt.comp x
    ((NormedSpace.contDiffAt_normalize (sub_ne_zero.mpr hx)).comp x
      (contDiffAt_id.sub contDiffAt_const))

/-- A C² wave germ gives a C¹ characteristic-current component away from the tip. -/
theorem contDiffAt_characteristicCurrent_coord {u : ℝ^(n + 1) → ℝ} (c : ℝ^n) (T : ℝ) {x : ℝ^n}
    (hx : x ≠ c) (hu : ContDiffAt ℝ 2 u (backwardConeGraph c T x)) (i : Fin n) :
    ContDiffAt ℝ 1 (fun y ↦ characteristicCurrent u c T y i) x := by
  simp only [characteristicCurrent_apply]
  exact ((hu.partialDeriv i.succ (by norm_num)).comp x (contDiffAt_coneGraph c T hx)).add
    (((hu.partialDeriv 0 (by norm_num)).comp x (contDiffAt_coneGraph c T hx)).mul
      (contDiffAt_normalize_coord c hx i))

/-- Divergence of the characteristic current: the unit radial vector cancels the
second time derivative, while mixed derivatives cancel by Clairaut's theorem. -/
theorem divergence_characteristicCurrent {u : ℝ^(n + 1) → ℝ} (c : ℝ^n) (T : ℝ) {x : ℝ^n}
    (hx : x ≠ c) (hu : ContDiffAt ℝ 2 u (backwardConeGraph c T x)) :
    ∇· (characteristicCurrent u c T) x = -waveOperator u (backwardConeGraph c T x) +
      (((n : ℝ) - 1) / ‖x - c‖) * ∂[0] u (backwardConeGraph c T x) := by
  let g := backwardConeGraph c T
  let v := NormedSpace.normalize (x - c)
  have hg := (hasFDerivAt_backwardConeGraph c T hx).differentiableAt
  have hp (i : Fin (n + 1)) : DifferentiableAt ℝ (∂[i] u) (g x) :=
    (hu.partialDeriv i (k := 1) (by norm_num)).differentiableAt_one
  have hd (i : Fin n) : ∂[i] (fun y ↦ characteristicCurrent u c T y i) x =
        ∂[i.succ] (∂[i.succ] u) (g x) - v i ^ 2 * ∂[0] (∂[0] u) (g x) + ∂[0] u (g x) *
            ∂[i] (fun y : ℝ^n ↦ NormedSpace.normalize (y - c) i) x := by
    simp only [characteristicCurrent_apply]
    rw [partialDeriv_add (f := fun y ↦ ∂[i.succ] u (backwardConeGraph c T y))
      (g := fun y ↦ ∂[0] u (backwardConeGraph c T y) *
        NormedSpace.normalize (y - c) i) ((hp i.succ).comp x hg)
      (((hp 0).comp x hg).mul (contDiffAt_normalize_coord c hx i).differentiableAt_one),
      partialDeriv_mul (f := fun y ↦ ∂[0] u (backwardConeGraph c T y))
        ((hp 0).comp x hg) (contDiffAt_normalize_coord c hx i).differentiableAt_one]
    have hpull (j : Fin (n + 1)) : ∂[i] (fun y ↦ ∂[j] u (backwardConeGraph c T y)) x =
          ∂[i.succ] (∂[j] u) (backwardConeGraph c T x) -
            NormedSpace.normalize (x - c) i * ∂[0] (∂[j] u) (backwardConeGraph c T x) := by
      simpa only [Function.comp_def] using partialDeriv_comp_backwardConeGraph c T hx (hp j) i
    rw [hpull i.succ, hpull 0, partialDeriv_partialDeriv_comm_at 0 i.succ hu]
    dsimp only [g, v]
    ring
  have hv : (∑ i : Fin n, v i ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, NormedSpace.norm_normalize (sub_ne_zero.mpr hx), one_pow]
  simp only [PDE.divergence, hd, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hv, sum_partialDeriv_normalize_coord c hx]
  simp only [waveOperator, one_mul]
  ring

/-- The current is the gradient of the cone trace plus twice the radial velocity. -/
theorem characteristicCurrent_eq_gradient {u : ℝ^(n + 1) → ℝ} (c : ℝ^n) (T : ℝ) {x : ℝ^n}
    (hx : x ≠ c) (hu : DifferentiableAt ℝ u (backwardConeGraph c T x)) :
    characteristicCurrent u c T x = ∇ (u ∘ backwardConeGraph c T) x +
      (2 * ∂[0] u (backwardConeGraph c T x)) • NormedSpace.normalize (x - c) := by
  ext i
  simp only [characteristicCurrent_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, gradient_apply_eq_partialDeriv]
  rw [partialDeriv_comp_backwardConeGraph c T hx hu i]
  ring

end WaveEquation
