/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# A continuous periodic function is determined by its Fourier coefficients

A continuous periodic function whose Fourier coefficients all vanish is zero. We prove this for
complex functions on a circle of any length, and for functions with values in a complex Banach
space, written on one period `[0, p]`. The point spectral mapping theorem for semigroups
(`IsComplexLinear.exists_mem_graph_smul_of_apply_eq_smul`) applies the second form to the
periodic orbit of an eigenvector of `T(t)`. Convergence of the Fourier series is not needed.

## Main results

* `eq_zero_of_fourierCoeff_eq_zero`: a continuous complex function on `ℝ/Tℤ` with vanishing
  Fourier coefficients is zero.
* `eq_zero_of_intervalIntegral_exp_smul_eq_zero`: let `u` be continuous on `[0, p]` with values
  in a complex Banach space and `u(0) = u(p)`; if `∫₀ᵖ e^{2πins/p} u(s) ds = 0` for every integer
  `n`, then `u = 0` on `[0, p]`.

## How it works

For a complex function the coefficients are the coordinates in Mathlib's Hilbert basis
`fourierBasis` of `L²` of the circle (`fourierBasis_repr`), so the function is zero in `L²`, and
a continuous function that vanishes in `L²` is zero. A function with values in a Banach space is
tested with continuous linear functionals, which pass through the integrals. Because
`u(0) = u(p)`, each `φ ∘ u` lifts to a continuous function on the circle (`AddCircle.liftIco`),
whose coefficients are the vanishing integrals (`fourierCoeff_liftIco_eq`). A vector on which
every functional vanishes is zero.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory

namespace PDE.Analysis

/-- **A continuous function on the circle with vanishing Fourier coefficients is zero.** Its
class in `L²` has zero coordinates in the Fourier basis, and a continuous function is determined
by its class. -/
theorem eq_zero_of_fourierCoeff_eq_zero {T : ℝ} [hT : Fact (0 < T)] {f : C(AddCircle T, ℂ)}
    (h : ∀ n : ℤ, fourierCoeff f n = 0) : f = 0 := by
  have h2 : ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f = 0 := by
    refine fourierBasis.repr.injective (lp.ext (funext fun n ↦ ?_))
    rw [fourierBasis_repr, fourierCoeff_toLp, h n, map_zero]
    rfl
  exact ContinuousMap.toLp_injective AddCircle.haarAddCircle (h2.trans (map_zero _).symm)

/-- **Uniqueness of Fourier coefficients on an interval, for values in a Banach space.** Let `u`
be continuous on `[0, p]` with values in a complex Banach space and `u(0) = u(p)`. If
`∫₀ᵖ e^{2πins/p} u(s) ds = 0` for every integer `n`, then `u = 0` on `[0, p]`. Each continuous
functional `φ` turns `u` into a continuous function on the circle with vanishing coefficients,
so `φ (u s) = 0` for every `φ`. -/
theorem eq_zero_of_intervalIntegral_exp_smul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {p : ℝ} (hp : 0 < p) {u : ℝ → E}
    (hu : ContinuousOn u (Icc 0 p)) (h0 : u 0 = u p)
    (h : ∀ n : ℤ, ∫ s in (0 : ℝ)..p, Complex.exp (2 * π * Complex.I * n * s / p) • u s = 0)
    {s : ℝ} (hs : s ∈ Icc 0 p) : u s = 0 := by
  have : Fact (0 < p) := ⟨hp⟩
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ ↦ ?_
  have hint : ∀ m : ℤ, IntervalIntegrable
      (fun s : ℝ ↦ Complex.exp (2 * π * Complex.I * m * s / p) • u s) volume 0 p := fun m ↦ by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hp.le]
    exact (Continuous.continuousOn (by fun_prop)).smul hu
  have hc : Continuous (AddCircle.liftIco p 0 fun s ↦ φ (u s)) :=
    AddCircle.liftIco_zero_continuous (congrArg φ h0) (φ.continuous.comp_continuousOn hu)
  have hz : (⟨_, hc⟩ : C(AddCircle p, ℂ)) = 0 := eq_zero_of_fourierCoeff_eq_zero fun n ↦ by
    have h1 := φ.intervalIntegral_comp_comm (hint (-n))
    rw [h (-n), map_zero] at h1
    simp only [map_smul, smul_eq_mul] at h1
    change fourierCoeff (AddCircle.liftIco p 0 fun s ↦ φ (u s)) n = 0
    rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
    simp only [fourier_coe_apply, zero_add, sub_zero, smul_eq_mul]
    rw [h1, smul_zero]
  have hval : ∀ r ∈ Ico (0 : ℝ) p, φ (u r) = 0 := fun r hr ↦ by
    have h1 : AddCircle.liftIco p 0 (fun s ↦ φ (u s)) ((r : ℝ) : AddCircle p) = 0 :=
      DFunLike.congr_fun hz _
    rwa [AddCircle.liftIco_coe_apply (by rwa [zero_add])] at h1
  rcases eq_or_lt_of_le hs.2 with hsp | hlt
  · rw [hsp, ← h0]
    exact hval 0 ⟨le_rfl, hp⟩
  · exact hval s ⟨hs.1, hlt⟩

end PDE.Analysis
