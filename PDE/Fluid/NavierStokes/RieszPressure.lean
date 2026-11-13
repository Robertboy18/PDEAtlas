/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.DoubleRiesz
public import PDE.Analysis.MeasureTheory.ContinuousRepresentative.Canonical
public import PDE.Analysis.MeasureTheory.Lp.EuclideanFields
public import PDE.FDeriv.PartialDeriv.Smooth
public import PDE.FDeriv.Laplacian.Congruence
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.WholeSpaceClass

/-!
# The Riesz pressure

For a velocity field `u` on `ℝⁿ` whose products `uᵢuⱼ` are square integrable, for example
`u ∈ L⁴`, the pressure of incompressible flow is `P = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)`, with `RᵢRⱼ` the
double Riesz transform. It is the `L²` solution of `-ΔP = Σᵢⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)`:
`∫ P Δχ = -Σᵢⱼ ∫ uᵢuⱼ ∂ᵢ∂ⱼχ` for every smooth compactly supported `χ`
(`integral_rieszPressure_mul_laplacian`). The function `rieszPressure u` is the continuous
member of this `L²` class when the class has one, so a smooth pressure is a genuine function
and not only a class.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

namespace NavierStokes

open MeasureTheory PDE.Analysis.Fourier

variable {n : ℕ}

/-- The complex `L²` class of the product `uᵢ uⱼ`, and zero if the product is not square
integrable. -/
noncomputable def velocityProductL2 (u : ℝ^n → ℝ^n) (i j : Fin n) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) := by
  classical
  exact if h : MemLp (fun x ↦ u x i * u x j) 2 volume then
    h.ofReal.toLp (fun x ↦ ((u x i * u x j : ℝ) : ℂ)) else 0

/-- For square-integrable `uᵢuⱼ` the class `velocityProductL2 u i j` is the complexified
product. -/
theorem coeFn_velocityProductL2 {u : ℝ^n → ℝ^n} {i j : Fin n}
    (h : MemLp (fun x ↦ u x i * u x j) 2 volume) :
    (velocityProductL2 u i j : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ ((u x i * u x j : ℝ) : ℂ) := by
  classical
  unfold velocityProductL2
  simp only [h, dite_true]
  exact MemLp.coeFn_toLp _

/-- The Riesz pressure `Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` as a complex `L²` class. -/
noncomputable def rieszPressureL2 (u : ℝ^n → ℝ^n) : Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  ∑ i, ∑ j, doubleRiesz i j (velocityProductL2 u i j)

/-- The Riesz pressure `P = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` of a velocity field: the continuous member of
the real part of the class `rieszPressureL2 u` if the class has one, and a chosen
representative otherwise. -/
noncomputable def rieszPressure (u : ℝ^n → ℝ^n) : ℝ^n → ℝ :=
  continuousRepresentative volume (fun x ↦ (rieszPressureL2 u x).re)

/-- The Riesz pressure is a member of the real part of the class `rieszPressureL2 u`. -/
theorem rieszPressure_ae_eq (u : ℝ^n → ℝ^n) :
    rieszPressure u =ᵐ[volume] fun x ↦ (rieszPressureL2 u x).re :=
  continuousRepresentative_ae_eq _ _

/-- The product classes depend only on the almost-everywhere class of the velocity. -/
theorem velocityProductL2_congr_ae {u v : ℝ^n → ℝ^n} (h : u =ᵐ[volume] v) (i j : Fin n) :
    velocityProductL2 u i j = velocityProductL2 v i j := by
  classical
  have hp : (fun x ↦ u x i * u x j) =ᵐ[volume] fun x ↦ v x i * v x j := by
    filter_upwards [h] with x hx
    rw [hx]
  unfold velocityProductL2
  by_cases hu : MemLp (fun x ↦ u x i * u x j) 2 volume
  · have hv : MemLp (fun x ↦ v x i * v x j) 2 volume := hu.ae_eq hp
    rw [dite_eq_left hu, dite_eq_left hv]
    apply MemLp.toLp_congr
    filter_upwards [hp] with x hx
    exact congrArg (fun r : ℝ ↦ (r : ℂ)) hx
  · have hv : ¬ MemLp (fun x ↦ v x i * v x j) 2 volume := fun hv ↦ hu (hv.ae_eq hp.symm)
    rw [dite_eq_right hu, dite_eq_right hv]

/-- The Riesz pressure depends only on the almost-everywhere class of the velocity. -/
theorem rieszPressure_congr_ae {u v : ℝ^n → ℝ^n} (h : u =ᵐ[volume] v) :
    rieszPressure u = rieszPressure v := by
  unfold rieszPressure rieszPressureL2
  simp only [velocityProductL2_congr_ae h]

/-- The Riesz pressure is square integrable, with no hypothesis on the velocity: products
`uᵢuⱼ` that are not square integrable enter as the zero class. -/
theorem memLp_two_rieszPressure (u : ℝ^n → ℝ^n) : MemLp (rieszPressure u) 2 volume := by
  have h : MemLp (fun x ↦ (rieszPressureL2 u x).re) 2 volume := by
    simpa using (Lp.memLp (rieszPressureL2 u)).re
  exact h.ae_eq (rieszPressure_ae_eq u).symm

/-- Weak form of `-ΔP = Σᵢⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)` for the Riesz pressure. -/
theorem integral_rieszPressure_mul_laplacian {u : ℝ^n → ℝ^n}
    (hu : ∀ i j, MemLp (fun x ↦ u x i * u x j) 2 volume) {χ : ℝ^n → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∫ x, rieszPressure u x * PDE.laplacian χ x =
      -∑ i, ∑ j, ∫ x, u x i * u x j * iteratedPartialDeriv [i, j] χ x := by
  set f := velocityProductL2 u
  have hΔ : MemLp (fun x ↦ PDE.laplacian χ x) 2 volume :=
    (PDE.contDiff_laplacian_coord hχ).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.coordinate_laplacian hc)
  have hint (i j : Fin n) : Integrable
      (fun x ↦ (doubleRiesz i j (f i j) x).re * PDE.laplacian χ x) volume := by
    have h : MemLp (fun x ↦ (doubleRiesz i j (f i j) x).re) 2 volume := by
      simpa using (Lp.memLp (doubleRiesz i j (f i j))).re
    exact h.integrable_mul hΔ
  have hterm (i j : Fin n) : ∫ x, (doubleRiesz i j (f i j) x).re * PDE.laplacian χ x =
      -∫ x, u x i * u x j * iteratedPartialDeriv [i, j] χ x := by
    rw [integral_re_doubleRiesz_mul_laplacian i j _ hχ hc]
    congr 1
    apply integral_congr_ae
    filter_upwards [coeFn_velocityProductL2 (hu i j)] with x hx
    rw [hx, Complex.ofReal_re]
  have hsum : (fun x ↦ rieszPressure u x * PDE.laplacian χ x) =ᵐ[volume]
      fun x ↦ ∑ i, ∑ j, (doubleRiesz i j (f i j) x).re * PDE.laplacian χ x := by
    filter_upwards [rieszPressure_ae_eq u,
      Lp.coeFn_finsetSum Finset.univ (fun i ↦ ∑ j, doubleRiesz i j (f i j)),
      ae_all_iff.2 fun i ↦ Lp.coeFn_finsetSum Finset.univ (fun j ↦ doubleRiesz i j (f i j))]
      with x h1 h2 h3
    rw [h1, rieszPressureL2, h2, Finset.sum_apply, Complex.re_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h3 i, Finset.sum_apply, Complex.re_sum, Finset.sum_mul]
  rw [integral_congr_ae hsum, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _
    fun j _ ↦ hint i j, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint i j, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ hterm i j

/-! ## Sobolev regularity of the Riesz pressure -/

open SobolevSpace.Fractional SobolevSpace.GraphSpace FourierTransform TemperedDistribution
  BesselPotentialSpace
open scoped SchwartzMap BesselPotentialSpace Sobolev

/-- The products `uᵢuⱼ` are real `L²` classes. -/
theorem isRealL2_velocityProductL2 (u : ℝ^n → ℝ^n) (i j : Fin n) :
    IsRealL2 (velocityProductL2 u i j) := by
  by_cases h : MemLp (fun x ↦ u x i * u x j) 2 volume
  · filter_upwards [coeFn_velocityProductL2 h] with x hx
    rw [hx, Complex.ofReal_im]
  · unfold velocityProductL2
    simp only [h, dite_false]
    exact isRealL2_zero

/-- The Riesz pressure class is real. -/
theorem isRealL2_rieszPressureL2 (u : ℝ^n → ℝ^n) : IsRealL2 (rieszPressureL2 u) :=
  Finset.sum_induction _ IsRealL2 (fun _ _ ha hb ↦ ha.add hb) isRealL2_zero fun i _ ↦
    Finset.sum_induction _ IsRealL2 (fun _ _ ha hb ↦ ha.add hb) isRealL2_zero fun j _ ↦
      isRealL2_doubleRiesz i j (isRealL2_velocityProductL2 u i j)

/-- If every product `uᵢuⱼ` lies in `W^{k,2}(ℝⁿ)`, so does the Riesz pressure class. -/
theorem exists_wkpSpace_rieszPressureL2 {u : ℝ^n → ℝ^n} {k : ℕ}
    (F : Fin n → Fin n → W^{k,2}(ℝ^n)) (hF : ∀ i j, baseL2 (F i j) = velocityProductL2 u i j) :
    ∃ V : W^{k,2}(ℝ^n), baseL2 V = rieszPressureL2 u := by
  have hw : Measurable (besselSymbol n k) := by
    unfold besselSymbol
    fun_prop
  have hterm (i j : Fin n) : MemLp (fun ξ ↦ besselSymbol n k ξ *
      (𝓕 (doubleRiesz i j (velocityProductL2 u i j)) : Lp ℂ 2 volume) ξ) 2 volume := by
    refine memLp_weight_mul_fourier_doubleRiesz i j hw ?_
    rw [← hF i j]
    exact (memSobolev_iff_memLp_besselWeight (k : ℝ) _).mp (memSobolev_baseL2 (F i j))
  have hsum : MemLp (fun ξ ↦ ∑ i, ∑ j, besselSymbol n k ξ *
      (𝓕 (doubleRiesz i j (velocityProductL2 u i j)) : Lp ℂ 2 volume) ξ) 2 volume :=
    memLp_finsetSum _ fun i _ ↦ memLp_finsetSum _ fun j _ ↦ hterm i j
  have hF2 : (𝓕 (rieszPressureL2 u) : Lp ℂ 2 (volume : Measure (ℝ^n))) =
      ∑ i, ∑ j, 𝓕 (doubleRiesz i j (velocityProductL2 u i j)) :=
    (map_sum (Lp.fourierTransformₗᵢ (ℝ^n) ℂ)
      (fun i ↦ ∑ j, doubleRiesz i j (velocityProductL2 u i j)) Finset.univ).trans
      (Finset.sum_congr rfl fun i _ ↦ map_sum (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) _ Finset.univ)
  have hmem : MemLp (fun ξ ↦ besselSymbol n k ξ *
      (𝓕 (rieszPressureL2 u) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume := by
    refine hsum.ae_eq ?_
    rw [hF2]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ ∑ j,
        (𝓕 (doubleRiesz i j (velocityProductL2 u i j)) : Lp ℂ 2 (volume : Measure (ℝ^n)))),
      ae_all_iff.2 fun i ↦ Lp.coeFn_finsetSum Finset.univ (fun j ↦
        (𝓕 (doubleRiesz i j (velocityProductL2 u i j)) : Lp ℂ 2 (volume : Measure (ℝ^n))))]
      with ξ h1 h2
    rw [h1, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h2 i, Finset.sum_apply, Finset.mul_sum]
  obtain ⟨V, hV, -⟩ :=
    exists_wkpSpace_of_isRealL2_of_memLp_besselWeight _ (isRealL2_rieszPressureL2 u) hmem
  exact ⟨V, hV⟩

end NavierStokes
