/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Hyperbolic.HigherRegularity.Data.SobolevTimeJet
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic

/-!
# Weak time derivatives for higher-order wave regularity

We lift the displacement identity from a weak wave in the pivot
space to the corresponding weak time-derivative identity in a higher Sobolev
space.  The proof passes through Bochner integral identities and injectivity
of the Sobolev base-coordinate map.

A weak wave on the Dirichlet Gelfand triple `H¹₀ ⊂ L² ⊂ (H¹₀)*` carries the
relation `u_t = v` only in the weak sense of Evans, §5.9.2 (spaces
involving time): integrated against scalar test functions in time, tested
against elements of `H¹₀`, with values compared in `L²`.  Evans's
higher-regularity argument needs the same relation with values in `H^m`.  If
`U ∈ L²_t H^{m+1}` and `dU ∈ L²_t H^m` project onto `u` and `v` in `L²`, the
`H^m`-valued Bochner integrals `∫ τ dU` and `∫ τ' U` are determined by their
`L²` projections, because the base-coordinate map `H^m → L²` is injective on
an open domain, and the `H^m`-valued weak identity follows.

## Main results

* `higherWeakTimeDerivative_of_weakWave`: the relation
  `HasGelfandWeakTimeDerivativeOn` between `lowerOrderTimeLp U` and `dU`,
  derived from the weak wave and the base-coordinate identification of `U`
  with `u`.  This is the derivative hypothesis of `SobolevTimeJet.succ`, so
  successive jet entries never need a separately postulated derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2 (the weak derivative of a function of time with values
  in a Banach space), and §7.2.3, proof of Theorem 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic

namespace HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

private theorem integrable_timeLp_smul
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {μ : Measure ℝ}
    (φ : Lp ℝ 2 μ) (y : Lp Y 2 μ) : Integrable (fun t ↦ φ t • y t) μ :=
  memLp_one_iff_integrable.mp ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Y →L[ℝ] Y).memLp_of_bilin
    (p := 2) (q := 2) 1 (Lp.memLp φ) (Lp.memLp y))

private theorem inner_integral_timeLp_smul
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    {μ : Measure ℝ} (φ : Lp ℝ 2 μ) (y : Lp Y 2 μ) (z : Y) :
    inner ℝ (∫ t, φ t • y t ∂μ) z = ∫ t, inner ℝ (y t) z * φ t ∂μ := by
  rw [real_inner_comm, ← innerSL_apply_apply,
    ← (innerSL ℝ z).integral_comp_comm (integrable_timeLp_smul φ y)]
  simp [innerSL_apply_apply, real_inner_comm, mul_comm]

private theorem weakWave_displacement_integral {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {a b : ℝ} {T : PDE.Analysis.Evolution.GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
    {acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))} {q0 : V} {p0 : H}
    (hWave : Hyperbolic.Variational.IsGelfandWeakWaveSolution T B ell u velocity acceleration q0 p0)
    (τ : PDE.Analysis.Evolution.TimeTest a b) (hτa : τ.toFun a = 0) :
    (∫ t, τ.toLp t • velocity t ∂(volume.restrict (Set.Ioc a b))) =
      -(∫ t, τ.derivToLp t • T.inclusion (u t) ∂(volume.restrict (Set.Ioc a b))) := by
  let μ := volume.restrict (Set.Ioc a b)
  let uPivot : Lp H 2 μ := T.inclusion.compLpL 2 μ u
  have hu : (fun t ↦ uPivot t) =ᵐ[μ] fun t ↦ T.inclusion (u t) := T.inclusion.coeFn_compLpL u
  let dInt : H := ∫ t, τ.toLp t • velocity t ∂μ
  let xInt : H := ∫ t, τ.derivToLp t • uPivot t ∂μ
  have hInt : dInt = -xInt := ext_inner_right ℝ fun z ↦ congrFun (T.denseRange.equalizer
    (innerSL ℝ dInt).continuous (innerSL ℝ (-xInt)).continuous (funext fun w ↦ by
      change inner ℝ dInt (T.inclusion w) = inner ℝ (-xInt) (T.inclusion w)
      have hdisp := hWave.displacementIdentity.equation w τ
      rw [inner_integral_timeLp_smul τ.toLp velocity (T.inclusion w), inner_neg_left,
        inner_integral_timeLp_smul τ.derivToLp uPivot (T.inclusion w),
        integral_congr_ae (hu.mono fun t ht ↦ by
          simp only [ht] : (fun t ↦ inner ℝ (uPivot t) (T.inclusion w) * τ.derivToLp t) =ᵐ[μ]
            fun t ↦ inner ℝ (T.inclusion (u t)) (T.inclusion w) * τ.derivToLp t)]
      simp only [μ, zero_apply, zero_mul, integral_zero, add_zero,
        PDE.Analysis.Evolution.GelfandTriple.pivotToDual_apply, hτa, mul_zero] at hdisp ⊢
      exact hdisp.symm)) z
  exact hInt.trans (congrArg Neg.neg (integral_congr_ae (hu.mono fun t ht ↦ by simp only [ht])))

/--
Lift the displacement derivative from the weak-wave pivot space to a higher
Sobolev space.

The weak-wave identity first gives `u_t = dU` as an `L²(Omega)`-valued
distribution.  If `U` and `dU` already take values in `H^{m+1}` and `H^m`,
respectively, injectivity of the Sobolev base-coordinate map on the open
domain reflects that identity into `H^m`.  This includes the order-zero
case and shows that the derivative needed by `SobolevTimeJet.succ` is a
consequence of the weak equation and the spatial lift, not an extra
hypothesis.
-/
theorem higherWeakTimeDerivative_of_weakWave (hOmegaOpen : IsOpen Omega)
    (B : ℝ → H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (ell : Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
    (U : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (dU : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (u : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (acceleration : Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
    (q0 : H¹₀(Omega)) (p0 : DerivLp n 2 Omega)
    (hWave : Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) B ell u (baseCoordinateTimeLp dU)
      acceleration q0 p0)
    (hUbase : (fun t ↦ wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := 2) (Ω := Omega)
      ((U : ℝ → W^{(m + 1),2}(Omega)) t)) =ᵐ[(volume.restrict (Set.Ioc t0 t1))] fun t ↦
      wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
      (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t))) :
    PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
      (PDE.Analysis.Evolution.GelfandTriple.identity (W^{m,2}(Omega)))
      (lowerOrderTimeLp U) (PDE.Analysis.Evolution.rieszToDualLp dU) := by
  let μ := volume.restrict (Set.Ioc t0 t1)
  let J : W^{m,2}(Omega) →L[ℝ] DerivLp n 2 Omega :=
    wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega)
  let x : Lp (W^{m,2}(Omega)) 2 μ := lowerOrderTimeLp U
  have hJ : Function.Injective J := fun a b hab ↦ WkpSpaceOn.ext_of_base_ae hOmegaOpen a b (by
    rw [show (a : WkpAmbientOn n m 2 Omega) (baseIndex n m) =
      (b : WkpAmbientOn n m 2 Omega) (baseIndex n m) by
        simpa only [J, wkpBaseCoordinateCLM_apply] using hab])
  have hJx : (fun t ↦ J (x t)) =ᵐ[μ] fun t ↦
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).inclusion
        ((u : ℝ → H¹₀(Omega)) t) := by
    filter_upwards [lowerOrderTimeLp_apply_ae U, hUbase] with t hx hbase
    rw [show x t = lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (U t) by
      simpa only [x, μ] using hx]
    exact hbase
  intro v τ hτa
  let dIntX : W^{m,2}(Omega) := ∫ t, τ.toLp t • dU t ∂μ
  let xIntX : W^{m,2}(Omega) := ∫ t, τ.derivToLp t • x t ∂μ
  have hIntX : dIntX = -xIntX := hJ (by
    rw [map_neg, ← J.integral_comp_comm (integrable_timeLp_smul τ.toLp dU),
      ← J.integral_comp_comm (integrable_timeLp_smul τ.derivToLp x)]
    refine (integral_congr_ae ?_).trans ((weakWave_displacement_integral hWave τ hτa).trans
      (congrArg Neg.neg (integral_congr_ae ?_)))
    · filter_upwards [baseCoordinateTimeLp_apply_ae dU] with t ht
      rw [map_smul, ← ht]
    · filter_upwards [hJx] with t ht
      rw [map_smul, ← ht])
  calc (∫ t, PDE.Analysis.Evolution.rieszToDualLp dU t v * τ.toLp t ∂μ) =
        ∫ t, inner ℝ (dU t) v * τ.toLp t ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [PDE.Analysis.Evolution.rieszToDualLp_apply_ae dU] with t ht
          rw [ht]
          rfl
    _ = -(∫ t, inner ℝ (x t) v * τ.derivToLp t ∂μ) := by
      rw [← inner_integral_timeLp_smul, ← inner_integral_timeLp_smul, ← inner_neg_left]
      exact congrArg (inner ℝ · v) hIntX

end HigherRegularity

end Hyperbolic
