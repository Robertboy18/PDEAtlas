/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.RealSpectrum.Classical.Complex
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.Real
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.LinearMap
public import PDE.Analysis.Matrix.Complexification.Euclidean
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Notation

/-!
# Real classical solutions from fractional Sobolev data

For real constant matrices with real spectrum at every real frequency, the
strict real-order threshold `s > n/2 + m` gives one jointly `C¹` real
solution. Its initial value is the canonical representative of each
real Sobolev component. Neither eigenvectors nor Fourier moments are inputs.

The construction works on all signed times, so restriction to nonnegative
times includes a derivative and the PDE on the initial face. Uniqueness is
in `Classical.WellPosed`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SobolevSpace.Fractional
open scoped Sobolev BesselPotentialSpace SchwartzMap Matrix.Norms.L2Operator

namespace PDE.Hyperbolic.FirstOrder

variable {n m : ℕ} {s : ℝ}

/-- The system threshold implies the scalar `C¹` threshold whenever a component
index exists. This also avoids a positive-dimension assumption for empty systems. -/
theorem realSpectrum_component_threshold (hs : (n : ℝ) < 2 * (s - m)) (i : Fin m) :
    (n : ℝ) < 2 * (s - 1) := by
  have hi := i.isLt
  have hm' : 1 ≤ m := by omega
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm'
  linarith

/-- The natural pointwise initial datum assembled from the real
fractional Sobolev components. The empty system gives the unique empty vector. -/
def realSpectrumInitialData (hs : (n : ℝ) < 2 * (s - m))
    (f : Fin m → H^{s}(ℝ^n; ℝ)) (x : ℝ^n) : ℝ^m :=
  WithLp.toLp 2 fun i ↦ (f i).c1Representative (realSpectrum_component_threshold hs i) x

/-- Each coordinate is the canonical representative of the original scalar datum.
The particular proof of the embedding threshold is immaterial. -/
theorem realSpectrumInitialData_apply (hs : (n : ℝ) < 2 * (s - m))
    (hs1 : (n : ℝ) < 2 * (s - 1)) (f : Fin m → H^{s}(ℝ^n; ℝ))
    (x : ℝ^n) (i : Fin m) :
    realSpectrumInitialData hs f x i = (f i).c1Representative hs1 x := rfl

/-- A continuous literal initial function representing the physical Sobolev
data equals the canonical initial function everywhere. The physical `L²`
class, rather than a particular coercion of that class, is the hypothesis. -/
theorem realSpectrumInitialData_eq_of_ae_eq
    (hs : (n : ℝ) < 2 * (s - m)) (f : Fin m → H^{s}(ℝ^n; ℝ))
    {v : ℝ^n → ℝ^m} (hv : Continuous v)
    (h : ∀ i, (fun x ↦ v x i) =ᵐ[volume]
      (HsSpaceReal.toL2FunCLM n
        (by
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith only [hs, hn, hm])
        (f i) : ℝ^n → ℝ)) :
    realSpectrumInitialData hs f = v := by
  funext x
  ext i
  have heq := (f i).eq_c1Representative_of_ae_eq (realSpectrum_component_threshold hs i) _
    ((EuclideanSpace.proj i).continuous.comp hv) (h i)
  exact (congrFun heq x).symm

/-- Real fractional Sobolev data produce one real joint `C¹` solution of
the full constant-coefficient system, with pointwise canonical initial data.
The matrices need only have real spectrum in each real symbol; they need not
be symmetric or diagonalizable. Both zero dimensions are included. -/
theorem exists_jointC1_realSpectrumSolution (B : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ ξ : ℝ^n, ∀ z ∈ spectrum ℂ (∑ j, ξ j • (B j).map Complex.ofReal), z.im = 0)
    (hs : (n : ℝ) < 2 * (s - m)) (f : Fin m → H^{s}(ℝ^n; ℝ)) :
    ∃ U : ℝ × ℝ^n → ℝ^m, ContDiff ℝ 1 U ∧ (∀ p : ℝ × ℝ^n, fderiv ℝ U p (1, 0) + ∑ j,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (B j) (fderiv ℝ U p (0, EuclideanSpace.single j 1)) = 0) ∧
      ∀ x : ℝ^n, U (0, x) = realSpectrumInitialData hs f x := by
  let A (j : Fin n) := (B j).map Complex.ofReal
  let F : H^{s}(ℝ^n, EuclideanSpace ℂ (Fin m)) :=
    BesselPotentialSpace.euclideanTuple fun i ↦ (f i).1
  obtain ⟨g, _, hV, heq, hinit⟩ :=
    exists_jointC1_realSpectrumEvolution_of_memSobolev A hB hs F.memSobolev_toDistr
  let V (p : ℝ × ℝ^n) := realSpectrumFourierEvolution A g p.1 p.2
  let R := EuclideanSpace.realPartCLM (Fin m)
  let U : ℝ × ℝ^n → ℝ^m := R ∘ V
  have hU : ContDiff ℝ 1 U := R.contDiff.comp hV
  refine ⟨U, hU, ?_, ?_⟩
  · intro p
    have hder : HasFDerivAt U (R.comp (fderiv ℝ V p)) p :=
      R.hasFDerivAt.comp p ((hV.differentiable (by norm_num)) p).hasFDerivAt
    rw [hder.fderiv]
    have h := congrArg R (heq p)
    rw [map_zero, Analysis.Fourier.symbolContraction_apply] at h
    change R (fderiv ℝ V p (1, 0) + ∑ j, Matrix.toEuclideanCLM (𝕜 := ℂ) ((B j).map Complex.ofReal)
        (fderiv ℝ V p (0, EuclideanSpace.single j 1))) = 0 at h
    rw [map_add, map_sum] at h
    dsimp only [R] at h
    simp only [EuclideanSpace.realPartCLM_toEuclideanCLM] at h
    exact h
  · intro x
    ext i
    have hs1 := realSpectrum_component_threshold hs i
    have hs' : (Module.finrank ℝ (ℝ^n) : ℝ) < 2 * (s - 1) := by simpa using hs1
    have hc : Continuous (realSpectrumFourierEvolution A g 0) := by
      have hpre : Continuous (fun y : ℝ^n ↦ ((0 : ℝ), y)) := continuous_const.prodMk continuous_id
      have hcont := hV.continuous.comp hpre
      exact hcont
    have hzero := BesselPotentialSpace.eq_c1Representative_of_integral_smul hs' F hc hinit
    change (realSpectrumFourierEvolution A g 0 x i).re = realSpectrumInitialData hs f x i
    rw [hzero, realSpectrumInitialData_apply hs hs1]
    change (BesselPotentialSpace.c1Representative hs'
      (BesselPotentialSpace.euclideanTuple fun j ↦ (f j).1) x i).re = _
    rw [BesselPotentialSpace.c1Representative_euclideanTuple_apply]
    rfl

/-- The endpoint with any continuous literal realization of the initial
Sobolev datum. The conclusion constructs the same joint classical solution. -/
theorem exists_jointC1_realSpectrumSolution_of_ae_eq
    (B : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • (B j).map Complex.ofReal), z.im = 0)
    (hs : (n : ℝ) < 2 * (s - m)) (f : Fin m → H^{s}(ℝ^n; ℝ))
    {v : ℝ^n → ℝ^m} (hv : Continuous v)
    (h : ∀ i, (fun x ↦ v x i) =ᵐ[volume]
      (HsSpaceReal.toL2FunCLM n
        (by
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith only [hs, hn, hm])
        (f i) : ℝ^n → ℝ)) :
    ∃ U : ℝ × ℝ^n → ℝ^m,
      ContDiff ℝ 1 U ∧
      (∀ p : ℝ × ℝ^n,
        fderiv ℝ U p (1, 0) + ∑ j,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
            (fderiv ℝ U p (0, EuclideanSpace.single j 1)) = 0) ∧
      ∀ x : ℝ^n, U (0, x) = v x := by
  obtain ⟨U, hU, heq, hinit⟩ := exists_jointC1_realSpectrumSolution B hB hs f
  refine ⟨U, hU, heq, fun x ↦ ?_⟩
  rw [hinit, realSpectrumInitialData_eq_of_ae_eq hs f hv h]

end PDE.Hyperbolic.FirstOrder
