/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.Determinant.Norm
public import PDE.Analysis.MeasureTheory.Lp.PowerSuperposition

/-!
# Determinants of matrix-valued Lebesgue functions

Taking an `n × n` determinant divides the Lebesgue exponent by `n`.
The alternating multilinear norm estimate gives both membership and a uniform
bound. The power-growth superposition theorem then gives strong continuity for
finite exponents. The measure space is arbitrary.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ENNReal Topology Matrix.Norms.Elementwise
open PDE.Analysis.Matrix

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} {p : ℝ≥0∞}

/-- A matrix-valued `Lᵖ` function has determinant in `L^(p/n)`.
The conclusion also makes sense in dimension zero, where the determinant is one. -/
theorem MemLp.matrix_det {f : α → Matrix (Fin n) (Fin n) ℝ} (hf : MemLp f p μ) :
    MemLp (fun x ↦ (f x).det) (p / n) μ := by
  have hpower : MemLp (fun x ↦ ‖f x‖ ^ n) (p / n) μ := by
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using hf.norm_rpow_div n
  exact (hpower.const_mul (detNormBound n)).mono'
    (continuous_id.matrix_det.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ norm_det_le n (f x))

namespace Lp

/-- The determinant superposition on matrix-valued `Lᵖ`. -/
def matrixDet (f : Lp (Matrix (Fin n) (Fin n) ℝ) p μ) :
    Lp ℝ (p / ENNReal.ofReal (n : ℝ)) μ :=
  (show MemLp (fun x ↦ (f x).det) (p / ENNReal.ofReal (n : ℝ)) μ by
    simpa using (Lp.memLp f).matrix_det).toLp _

/-- The bundled determinant agrees almost everywhere with the determinant of the
matrix representative. -/
theorem coeFn_matrixDet (f : Lp (Matrix (Fin n) (Fin n) ℝ) p μ) :
    matrixDet f =ᵐ[μ] fun x ↦ (f x).det :=
  MemLp.coeFn_toLp _

/-- Strong matrix convergence implies strong determinant convergence at the divided
exponent. This is not a weak-continuity assertion. -/
theorem continuous_matrixDet [Fact (1 ≤ p)] [Fact (1 ≤ p / ENNReal.ofReal (n : ℝ))]
    (hn : 0 < n) (hp : p ≠ ∞) :
    Continuous (matrixDet (μ := μ) (n := n) (p := p)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmem (u : Lp (Matrix (Fin n) (Fin n) ℝ) p μ) :
      MemLp (fun x ↦ (u x).det) (p / ENNReal.ofReal (n : ℝ)) μ := by
    simpa using (Lp.memLp u).matrix_det
  have hc := continuous_superposition_of_rpow_growth hp hnR hmem
    (Eventually.of_forall fun _ ↦ continuous_id.matrix_det)
    (a := fun _ ↦ (0 : ℝ)) (C := detNormBound n) (MemLp.zero) (by
      filter_upwards [] with x P
      simpa only [zero_add, Real.rpow_natCast] using norm_det_le n P)
  exact hc

/-- The determinant's `L^(p/n)` norm is controlled by the `n`th power of the
matrix `Lᵖ` norm, with a constant fixed before the matrix function. -/
theorem norm_matrixDet_le [Fact (1 ≤ p)] [Fact (1 ≤ p / ENNReal.ofReal (n : ℝ))]
    (hn : 0 < n) (f : Lp (Matrix (Fin n) (Fin n) ℝ) p μ) :
    ‖matrixDet f‖ ≤ detNormBound n * ‖f‖ ^ n := by
  let N : Lp ℝ p μ := lipschitzWith_one_norm.compLp (_root_.norm_zero) f
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let B := detNormBound n • normRpow hnR.le N
  have hbound : ‖matrixDet f‖ ≤ ‖B‖ := by
    apply norm_le_norm_of_ae_le
    filter_upwards [coeFn_matrixDet f, coeFn_smul (detNormBound n) (normRpow hnR.le N),
      coeFn_normRpow hnR.le N,
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) f] with x hd hb hp hn'
    rw [hd, hb, Pi.smul_apply, smul_eq_mul, hp]
    change ‖(f x).det‖ ≤ ‖detNormBound n * ‖N x‖ ^ (n : ℝ)‖
    rw [show N x = ‖f x‖ from hn', norm_norm, Real.rpow_natCast,
      Real.norm_of_nonneg (mul_nonneg (detNormBound_nonneg n) (pow_nonneg (norm_nonneg _) _))]
    exact norm_det_le n (f x)
  have hN : ‖N‖ ≤ ‖f‖ := by
    apply norm_le_norm_of_ae_le
    filter_upwards [lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) f] with x hx
    change ‖N x‖ ≤ ‖f x‖
    rw [show N x = ‖f x‖ from hx, norm_norm]
  calc
    ‖matrixDet f‖ ≤ ‖B‖ := hbound
    _ = detNormBound n * ‖N‖ ^ n := by
      rw [norm_smul, Real.norm_of_nonneg (detNormBound_nonneg n), norm_normRpow hnR,
        Real.rpow_natCast]
    _ ≤ detNormBound n * ‖f‖ ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg N) hN n)
        (detNormBound_nonneg n)

/-- A bounded family of matrix `Lᵖ` functions has bounded determinants in `L^(p/n)`. -/
theorem isBounded_matrixDet_range [Fact (1 ≤ p)]
    [Fact (1 ≤ p / ENNReal.ofReal (n : ℝ))]
    (hn : 0 < n) {ι : Type*} (f : ι → Lp (Matrix (Fin n) (Fin n) ℝ) p μ)
    (hf : Bornology.IsBounded (range f)) :
    Bornology.IsBounded (range fun i ↦ matrixDet (f i)) := by
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨detNormBound n * C ^ n, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (norm_matrixDet_le hn (f i)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg (f i)) (hC _ ⟨i, rfl⟩) n)
      (detNormBound_nonneg n))

end Lp
end MeasureTheory
