/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.Expansion
public import PDE.CoordinateSystems.Spherical.Axisymmetric
import PDE.CoordinateSystems.Spherical.Matrix
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Axisymmetric vector spherical harmonics

An axisymmetric vector field `u` on the unit sphere is determined by its meridian profile
`v θ = u (point 1 θ 0)`, the values along the half great circle of azimuth zero. The results
here are stated for profiles `v` in `L²((0, π), sin θ dθ; ℝ³)`.

With `S_l (θ) = P_l (cos θ)` and `S_l' (θ) = -sin θ P_l' (cos θ)`, the axisymmetric vector
spherical harmonics are `Y_l = S_l e_r`, `X_l = S_l' e_θ` and `Z_l = S_l' e_φ`, where
`e_r, e_θ, e_φ` is the spherical frame at azimuth zero. They are mutually orthogonal, with
squared norms `2 / (2l + 1)` for `Y_l` and `2 l (l + 1) / (2l + 1)` for `X_l` and `Z_l`, and
`X_0 = Z_0 = 0`. A profile orthogonal to all of them has frame components orthogonal to every
`P_l (cos θ)` and every `sin θ · P_l' (cos θ)`, so it vanishes by the completeness of the two
scalar families. Hence every profile is the `L²` sum of its expansion
`∑_l (u_l^Y Y_l + u_l^X X_l + u_l^Z Z_l)`, with Parseval's identity, and the coefficients of
any convergent expansion are the `u_l^Y`, `u_l^X`, `u_l^Z`. The partial sums over the degrees
`l < N` converge in `L²` with `‖v - Q_N‖² ≤ 4 ‖v‖²` (`tendsto_integral_norm_sub_partialSum`),
the bound that dominated convergence over the radii of a ball needs.

Rotation through `φ` about the symmetry axis carries each mode at polar angle `θ` on the
meridian of azimuth zero to the same multiple of the frame vector at azimuth `φ`. This identity
holds point by point, as does `u (point r θ φ) = axisRotation φ (u (point r θ 0))` for an
equivariant field `u`.

Under the equatorial reflection `σ (x, y, z) = (x, y, -z)` the meridian point of angle `θ` goes
to that of angle `π - θ`, and `Y_l (π - θ) = (-1)ˡ σ Y_l (θ)`, `X_l (π - θ) = (-1)ˡ σ X_l (θ)`,
`Z_l (π - θ) = (-1)ˡ⁺¹ σ Z_l (θ)`. A field with `v (π - θ) = ε σ (v θ)` therefore expands only in
the modes of parity `ε`: for an even field the modes `Y_l, X_l` with `l` even and `Z_l` with `l`
odd, and the other way around for an odd field.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open CAS.Analysis.SpecialFunctions
open MeasureTheory Polynomial Set PDE.Analysis.Spectral PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace

/-- The zonal harmonic `S_l (θ) = P_l (cos θ)`. -/
def zonalHarmonic (l : ℕ) (θ : ℝ) : ℝ :=
  (legendre l).eval (Real.cos θ)

/-- The polar derivative `S_l' (θ) = -sin θ · P_l' (cos θ)` of the zonal harmonic. -/
def zonalHarmonicDeriv (l : ℕ) (θ : ℝ) : ℝ :=
  -(Real.sin θ * (derivative (legendre l)).eval (Real.cos θ))

/-- The zonal harmonic has derivative `S_l'`. -/
theorem hasDerivAt_zonalHarmonic (l : ℕ) (θ : ℝ) :
    HasDerivAt (zonalHarmonic l) (zonalHarmonicDeriv l θ) θ := by
  have h : HasDerivAt (fun t ↦ (legendre l).eval (Real.cos t))
      ((derivative (legendre l)).eval (Real.cos θ) * -Real.sin θ) θ :=
    ((legendre l).hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
  refine h.congr_deriv ?_
  unfold zonalHarmonicDeriv
  ring

/-- The zonal harmonic solves the spherical angular equation
`(sin θ S_l')' = -l (l + 1) sin θ S_l`. -/
theorem hasDerivAt_sin_mul_zonalHarmonicDeriv (l : ℕ) (θ : ℝ) :
    HasDerivAt (fun t ↦ Real.sin t * zonalHarmonicDeriv l t)
      (-((l : ℝ) * (l + 1)) * (Real.sin θ * zonalHarmonic l θ)) θ := by
  set W : ℝ[X] := (1 - X ^ 2) * derivative (legendre l)
  have hfun : (fun t ↦ Real.sin t * zonalHarmonicDeriv l t) = fun t ↦ -W.eval (Real.cos t) := by
    funext t
    simp only [zonalHarmonicDeriv, W, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
    rw [← Real.sin_sq_add_cos_sq t]
    ring
  have h := ((W.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).neg
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [W, legendre_equation, eval_mul, eval_neg, eval_C, zonalHarmonic]
  ring

/-- The angular factor of the vector harmonic in the frame direction `k`: `S_l` for the radial
direction `k = 0` and `S_l'` for the polar and azimuthal directions `k = 1, 2`. -/
def vectorHarmonicProfile (l : ℕ) (k : Fin 3) (θ : ℝ) : ℝ :=
  if k = 0 then zonalHarmonic l θ else zonalHarmonicDeriv l θ

/-- The axisymmetric vector spherical harmonics along the meridian of azimuth zero:
`Y_l = S_l e_r` for `k = 0`, `X_l = S_l' e_θ` for `k = 1` and `Z_l = S_l' e_φ` for `k = 2`. -/
def vectorHarmonic (l : ℕ) (k : Fin 3) (θ : ℝ) : ℝ^3 :=
  vectorHarmonicProfile l k θ • frame θ 0 k

/-- The squared norm of the vector harmonic: `2 / (2l + 1)` for `Y_l` and
`2 l (l + 1) / (2l + 1)` for `X_l` and `Z_l`. -/
def vectorHarmonicNormSq (l : ℕ) (k : Fin 3) : ℝ :=
  if k = 0 then 2 / (2 * (l : ℝ) + 1) else 2 * (l : ℝ) * (l + 1) / (2 * l + 1)

/-- The parity of the vector harmonic under `θ ↦ π - θ` followed by the equatorial reflection:
`(-1)ˡ` for `Y_l` and `X_l`, and `(-1)ˡ⁺¹` for `Z_l`. -/
def vectorHarmonicParity (l : ℕ) (k : Fin 3) : ℝ :=
  if k = 2 then (-1) ^ (l + 1) else (-1) ^ l

/-- The zonal harmonic is continuous. -/
theorem continuous_zonalHarmonic (l : ℕ) : Continuous (zonalHarmonic l) := by
  unfold zonalHarmonic
  fun_prop

/-- The polar derivative of the zonal harmonic is continuous. -/
theorem continuous_zonalHarmonicDeriv (l : ℕ) : Continuous (zonalHarmonicDeriv l) := by
  unfold zonalHarmonicDeriv
  fun_prop

/-- The vector harmonics are continuous along the meridian. -/
theorem continuous_vectorHarmonic (l : ℕ) (k : Fin 3) : Continuous (vectorHarmonic l k) := by
  have hframe : Continuous fun θ : ℝ ↦ frame θ 0 k := by
    have h := (continuous_frame k).comp (Continuous.prodMk_left (X := ℝ) (0 : ℝ))
    exact h
  unfold vectorHarmonic vectorHarmonicProfile
  split_ifs
  · exact (continuous_zonalHarmonic l).smul hframe
  · exact (continuous_zonalHarmonicDeriv l).smul hframe

/-- The vector harmonic as an element of `L²((0, π), sin θ dθ; ℝ³)`. -/
def vectorHarmonicLp (l : ℕ) (k : Fin 3) : Lp (ℝ^3) 2 polarAngleMeasure :=
  (memLp_polarAngleMeasure (continuous_vectorHarmonic l k) 2).toLp (vectorHarmonic l k)

/-- The element `vectorHarmonicLp l k` is represented by the vector harmonic. -/
theorem coeFn_vectorHarmonicLp (l : ℕ) (k : Fin 3) :
    vectorHarmonicLp l k =ᵐ[polarAngleMeasure] vectorHarmonic l k :=
  MemLp.coeFn_toLp _

/-- The component `⟪e_k (θ), v (θ)⟫` of a field along the meridian in the spherical frame. -/
def frameComponent (k : Fin 3) (v : ℝ → ℝ^3) (θ : ℝ) : ℝ :=
  ⟪frame θ 0 k, v θ⟫

/-- The inner product with a vector harmonic picks out a frame component. -/
theorem inner_vectorHarmonic (l : ℕ) (k : Fin 3) (θ : ℝ) (w : ℝ^3) :
    ⟪vectorHarmonic l k θ, w⟫ = vectorHarmonicProfile l k θ * ⟪frame θ 0 k, w⟫ :=
  real_inner_smul_left _ _ _

/-- The inner product of a vector harmonic with a field `v` is the moment of the matching frame
component of `v`. -/
theorem inner_vectorHarmonicLp (l : ℕ) (k : Fin 3) (v : Lp (ℝ^3) 2 polarAngleMeasure) :
    ⟪vectorHarmonicLp l k, v⟫ =
      ∫ θ, vectorHarmonicProfile l k θ * frameComponent k v θ ∂polarAngleMeasure := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_vectorHarmonicLp l k] with θ hθ
  rw [hθ, inner_vectorHarmonic, frameComponent]

/-- The vector harmonics are mutually orthogonal, with squared norms `vectorHarmonicNormSq`. -/
theorem inner_vectorHarmonicLp_vectorHarmonicLp (l m : ℕ) (k j : Fin 3) :
    ⟪vectorHarmonicLp l k, vectorHarmonicLp m j⟫ =
      if l = m ∧ k = j then vectorHarmonicNormSq l k else 0 := by
  rw [inner_vectorHarmonicLp]
  have hframe (θ : ℝ) : ⟪frame θ 0 k, frame θ 0 j⟫ = if k = j then 1 else 0 :=
    orthonormal_iff_ite.mp (orthonormal_frame θ 0) k j
  have hcomp : ∀ᵐ θ ∂polarAngleMeasure, vectorHarmonicProfile l k θ *
      frameComponent k (vectorHarmonicLp m j) θ =
        if k = j then vectorHarmonicProfile l k θ * vectorHarmonicProfile m k θ else 0 := by
    filter_upwards [coeFn_vectorHarmonicLp m j] with θ hθ
    rw [frameComponent, hθ, vectorHarmonic, real_inner_smul_right, hframe]
    split_ifs with h
    · subst h
      ring
    · ring
  rw [integral_congr_ae hcomp]
  by_cases hkj : k = j
  · subst hkj
    simp only [ite_true, and_true]
    by_cases hk : k = 0
    · simp only [vectorHarmonicProfile, vectorHarmonicNormSq, hk, ite_true, zonalHarmonic]
      exact integral_legendre_mul_legendre_polarAngleMeasure l m
    · simp only [vectorHarmonicProfile, vectorHarmonicNormSq, hk, ite_false,
        zonalHarmonicDeriv, neg_mul_neg]
      exact integral_sin_mul_derivative_legendre_polarAngleMeasure l m
  · simp [hkj]

/-- The polar derivative of `S_0 = 1` vanishes, so `X_0 = Z_0 = 0`. -/
theorem zonalHarmonicDeriv_zero : zonalHarmonicDeriv 0 = 0 := by
  funext θ
  simp [zonalHarmonicDeriv]

/-- The vector harmonics `X_0` and `Z_0` vanish. -/
theorem vectorHarmonicLp_zero_of_ne {k : Fin 3} (hk : k ≠ 0) : vectorHarmonicLp 0 k = 0 := by
  have h : vectorHarmonic 0 k = 0 := by
    funext θ
    simp [vectorHarmonic, vectorHarmonicProfile, hk, zonalHarmonicDeriv_zero]
  simp only [vectorHarmonicLp, h]
  exact MemLp.toLp_zero _

/-- A frame component of a square-integrable field is square integrable. -/
theorem memLp_frameComponent (k : Fin 3) (v : Lp (ℝ^3) 2 polarAngleMeasure) :
    MemLp (frameComponent k v) 2 polarAngleMeasure := by
  refine (Lp.memLp v).of_le ?_ (ae_of_all _ fun θ ↦ ?_)
  · exact ((continuous_frame k).comp (Continuous.prodMk_left 0)).aestronglyMeasurable.inner
      (Lp.aestronglyMeasurable v)
  · rw [frameComponent, Real.norm_eq_abs]
    calc |⟪frame θ 0 k, (v : ℝ → ℝ^3) θ⟫| ≤ ‖frame θ 0 k‖ * ‖(v : ℝ → ℝ^3) θ‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖(v : ℝ → ℝ^3) θ‖ := by rw [(orthonormal_frame θ 0).1 k, one_mul]

/-- **Completeness of the vector harmonics.** A field orthogonal to every `Y_l`, every `X_l`
and every `Z_l` is zero. -/
theorem eq_zero_of_forall_inner_vectorHarmonicLp_eq_zero {v : Lp (ℝ^3) 2 polarAngleMeasure}
    (h : ∀ l k, ⟪vectorHarmonicLp l k, v⟫ = 0) : v = 0 := by
  have hcomp (k : Fin 3) : frameComponent k v =ᵐ[polarAngleMeasure] 0 := by
    have hk := memLp_frameComponent k v
    have hzero : hk.toLp _ = 0 := by
      by_cases hk0 : k = 0
      · subst hk0
        refine eq_zero_of_forall_inner_eq_zero_of_dense legendre_complete fun l ↦ ?_
        rw [legendreLp, inner_cosPolynomialLp, ← h l 0, inner_vectorHarmonicLp]
        refine integral_congr_ae ?_
        filter_upwards [hk.coeFn_toLp] with θ hθ
        simp [hθ, vectorHarmonicProfile, zonalHarmonic]
      · refine eq_zero_of_forall_inner_eq_zero_of_dense associatedLegendre_complete
          fun l ↦ ?_
        rw [associatedLegendreLp, inner_sinCosPolynomialLp, ← neg_eq_zero, ← h (l + 1) k,
          inner_vectorHarmonicLp, ← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards [hk.coeFn_toLp] with θ hθ
        simp [hθ, vectorHarmonicProfile, hk0, zonalHarmonicDeriv]
    exact hk.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hcomp 0, hcomp 1, hcomp 2] with θ h₀ h₁ h₂
  rw [← (frameBasis θ 0).sum_repr' ((v : ℝ → ℝ^3) θ)]
  simp only [frameBasis_apply, Fin.sum_univ_three]
  simp only [frameComponent, Pi.zero_apply] at h₀ h₁ h₂
  rw [h₀, h₁, h₂]
  simp

/-- The indices `(l, k)` of the nonzero vector harmonics: every `Y_l`, and `X_l`, `Z_l` for
`l ≥ 1`. -/
def vectorHarmonicIndices : Set (ℕ × Fin 3) :=
  {i | i.2 = 0 ∨ i.1 ≠ 0}

/-- The squared norm of a nonzero vector harmonic is positive. -/
theorem vectorHarmonicNormSq_pos (i : vectorHarmonicIndices) :
    0 < vectorHarmonicNormSq i.1.1 i.1.2 := by
  obtain ⟨⟨l, k⟩, hi⟩ := i
  rcases hi with hk | hl
  · have hk' : k = 0 := hk
    simp only [vectorHarmonicNormSq, hk', ite_true]
    positivity
  · by_cases hk : k = 0
    · simp only [vectorHarmonicNormSq, hk, ite_true]
      positivity
    · have hl' : (0 : ℝ) < l := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)
      simp only [vectorHarmonicNormSq, hk, ite_false]
      positivity

/-- The nonzero vector harmonics are orthogonal with squared norms `vectorHarmonicNormSq`. -/
theorem inner_vectorHarmonicLp_indices (i j : vectorHarmonicIndices) :
    ⟪vectorHarmonicLp i.1.1 i.1.2, vectorHarmonicLp j.1.1 j.1.2⟫ =
      if i = j then vectorHarmonicNormSq i.1.1 i.1.2 else 0 := by
  rw [inner_vectorHarmonicLp_vectorHarmonicLp]
  congr 1
  rw [← Subtype.coe_inj, Prod.ext_iff]

/-- **Completeness of the vector harmonics.** The nonzero `Y_l`, `X_l` and `Z_l` span a dense
subspace of `L²((0, π), sin θ dθ; ℝ³)`. -/
theorem vectorHarmonic_complete :
    (Submodule.span ℝ (range fun i : vectorHarmonicIndices ↦
      vectorHarmonicLp i.1.1 i.1.2)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_orthogonal] at hv
  refine eq_zero_of_forall_inner_vectorHarmonicLp_eq_zero fun l k ↦ ?_
  by_cases hi : (l, k) ∈ vectorHarmonicIndices
  · exact hv _ (Submodule.subset_span ⟨⟨(l, k), hi⟩, rfl⟩)
  · have hk : k ≠ 0 := fun hk ↦ hi (Or.inl hk)
    have hl : l = 0 := by
      by_contra hl
      exact hi (Or.inr hl)
    rw [hl, vectorHarmonicLp_zero_of_ne hk, inner_zero_left]

/-- The Hilbert basis of `L²((0, π), sin θ dθ; ℝ³)` formed by the normalized nonzero vector
harmonics. -/
def vectorHarmonicBasis : HilbertBasis vectorHarmonicIndices ℝ (Lp (ℝ^3) 2 polarAngleMeasure) :=
  hilbertBasisOfOrthogonal vectorHarmonicNormSq_pos inner_vectorHarmonicLp_indices
    vectorHarmonic_complete

/-- The elements of the vector harmonic Hilbert basis. -/
theorem vectorHarmonicBasis_apply (i : vectorHarmonicIndices) :
    vectorHarmonicBasis i =
      (Real.sqrt (vectorHarmonicNormSq i.1.1 i.1.2))⁻¹ • vectorHarmonicLp i.1.1 i.1.2 :=
  hilbertBasisOfOrthogonal_apply _ _ _ i

/-- The coefficient `⟪Y, v⟫ / ‖Y‖²` of a field `v` on the vector harmonic `Y = Y_l, X_l, Z_l`;
it vanishes for `X_0` and `Z_0`. -/
def vectorHarmonicCoeff (v : Lp (ℝ^3) 2 polarAngleMeasure) (l : ℕ) (k : Fin 3) : ℝ :=
  ⟪vectorHarmonicLp l k, v⟫ / vectorHarmonicNormSq l k

/-- Every field along the meridian is the `L²` sum of its vector harmonic expansion
`∑_l (u_l^Y Y_l + u_l^X X_l + u_l^Z Z_l)`. -/
theorem hasSum_vectorHarmonicCoeff_smul (v : Lp (ℝ^3) 2 polarAngleMeasure) :
    HasSum (fun l ↦ ∑ k : Fin 3, vectorHarmonicCoeff v l k • vectorHarmonicLp l k) v := by
  have h := hasSum_inner_div_smul_of_orthogonal vectorHarmonicNormSq_pos
    inner_vectorHarmonicLp_indices vectorHarmonic_complete v
  have hsupp : Function.support (fun i : ℕ × Fin 3 ↦
      vectorHarmonicCoeff v i.1 i.2 • vectorHarmonicLp i.1 i.2) ⊆ vectorHarmonicIndices := by
    intro i hi
    by_contra hni
    have hk : i.2 ≠ 0 := fun hk ↦ hni (Or.inl hk)
    have hl : i.1 = 0 := by
      by_contra hl
      exact hni (Or.inr hl)
    apply hi
    simp only [hl, vectorHarmonicLp_zero_of_ne hk, smul_zero]
  have hF := (hasSum_subtype_iff_of_support_subset hsupp).mp h
  exact hF.prod_fiberwise fun l ↦ hasSum_fintype _

/-- Parseval's identity for the vector harmonic expansion:
`‖v‖² = ∑_l ∑_k ‖Y_{l,k}‖² · (u_l^k)²`. -/
theorem hasSum_sq_vectorHarmonicCoeff (v : Lp (ℝ^3) 2 polarAngleMeasure) :
    HasSum (fun l ↦ ∑ k : Fin 3, vectorHarmonicNormSq l k * vectorHarmonicCoeff v l k ^ 2)
      (‖v‖ ^ 2) := by
  have h := hasSum_inner_sq_div_of_orthogonal vectorHarmonicNormSq_pos
    inner_vectorHarmonicLp_indices vectorHarmonic_complete v
  have hterm (l : ℕ) (k : Fin 3) : vectorHarmonicNormSq l k * vectorHarmonicCoeff v l k ^ 2 =
      ⟪vectorHarmonicLp l k, v⟫ ^ 2 / vectorHarmonicNormSq l k := by
    rw [vectorHarmonicCoeff]
    by_cases hc : vectorHarmonicNormSq l k = 0
    · simp [hc]
    · field_simp
  simp only [hterm]
  have hsupp : Function.support (fun i : ℕ × Fin 3 ↦
      ⟪vectorHarmonicLp i.1 i.2, v⟫ ^ 2 / vectorHarmonicNormSq i.1 i.2) ⊆
        vectorHarmonicIndices := by
    intro i hi
    by_contra hni
    have hk : i.2 ≠ 0 := fun hk ↦ hni (Or.inl hk)
    have hl : i.1 = 0 := by
      by_contra hl
      exact hni (Or.inr hl)
    apply hi
    simp only [hl, vectorHarmonicLp_zero_of_ne hk, inner_zero_left]
    simp
  have hF := (hasSum_subtype_iff_of_support_subset hsupp).mp h
  exact hF.prod_fiberwise fun l ↦ hasSum_fintype _

/-- The coefficients of a convergent vector harmonic expansion are the vector harmonic
coefficients. -/
theorem vectorHarmonicCoeff_eq_of_hasSum {v : Lp (ℝ^3) 2 polarAngleMeasure}
    {a : ℕ → Fin 3 → ℝ} (hv : HasSum (fun l ↦ ∑ k : Fin 3, a l k • vectorHarmonicLp l k) v)
    {l : ℕ} {k : Fin 3} (hlk : (l, k) ∈ vectorHarmonicIndices) :
    vectorHarmonicCoeff v l k = a l k := by
  have hpos := vectorHarmonicNormSq_pos ⟨(l, k), hlk⟩
  have h := hv.mapL (innerSL ℝ (vectorHarmonicLp l k))
  simp only [innerSL_apply_apply, inner_sum, real_inner_smul_right,
    inner_vectorHarmonicLp_vectorHarmonicLp] at h
  have h' : HasSum (fun m ↦ if m = l then a l k * vectorHarmonicNormSq l k else 0)
      ⟪vectorHarmonicLp l k, v⟫ := by
    convert h using 1
    funext m
    by_cases hm : m = l
    · subst hm
      simp only [ite_true, true_and]
      rw [Finset.sum_eq_single k (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
      simp
    · simp [hm, Ne.symm hm]
  have hinner := h'.unique (hasSum_ite_eq l (a l k * vectorHarmonicNormSq l k))
  rw [vectorHarmonicCoeff, hinner, mul_div_cancel_right₀ _ hpos.ne']

/-- The vector harmonic coefficient of a square-integrable function, as an interval
integral. -/
theorem vectorHarmonicCoeff_toLp {v : ℝ → ℝ^3} (hv : MemLp v 2 polarAngleMeasure) (l : ℕ)
    (k : Fin 3) :
    vectorHarmonicCoeff (hv.toLp v) l k =
      (∫ θ in (0 : ℝ)..Real.pi, vectorHarmonicProfile l k θ * ⟪frame θ 0 k, v θ⟫ *
        Real.sin θ) / vectorHarmonicNormSq l k := by
  rw [vectorHarmonicCoeff, inner_vectorHarmonicLp, ← integral_polarAngleMeasure_eq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hv.coeFn_toLp] with θ hθ
  rw [frameComponent, hθ]

/-- **Completeness of the vector harmonics**, pointwise form: a function that is square
integrable for `sin θ dθ` on `(0, π)` and orthogonal to every `Y_l`, `X_l` and `Z_l` vanishes
almost everywhere on `(0, π)`. -/
theorem ae_eq_zero_of_forall_integral_vectorHarmonic_eq_zero {v : ℝ → ℝ^3}
    (hv : MemLp v 2 polarAngleMeasure)
    (h : ∀ l k, ∫ θ in (0 : ℝ)..Real.pi,
      vectorHarmonicProfile l k θ * ⟪frame θ 0 k, v θ⟫ * Real.sin θ = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo 0 Real.pi), v θ = 0 := by
  have hzero : hv.toLp v = 0 := by
    refine eq_zero_of_forall_inner_vectorHarmonicLp_eq_zero fun l k ↦ ?_
    rw [inner_vectorHarmonicLp, ← h l k, ← integral_polarAngleMeasure_eq]
    refine integral_congr_ae ?_
    filter_upwards [hv.coeFn_toLp] with θ hθ
    rw [frameComponent, hθ]
  have hv0 : v =ᵐ[polarAngleMeasure] 0 :=
    hv.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  exact volume_restrict_Ioo_absolutelyContinuous.ae_le hv0

section Parity

open PDE.Common

/-- The zonal harmonic has the parity `(-1)ˡ` under `θ ↦ π - θ`. -/
theorem zonalHarmonic_pi_sub (l : ℕ) (θ : ℝ) :
    zonalHarmonic l (Real.pi - θ) = (-1) ^ l * zonalHarmonic l θ :=
  legendre_eval_cos_pi_sub l θ

/-- The polar derivative of the zonal harmonic has the parity `(-1)ˡ⁺¹` under `θ ↦ π - θ`. -/
theorem zonalHarmonicDeriv_pi_sub (l : ℕ) (θ : ℝ) :
    zonalHarmonicDeriv l (Real.pi - θ) = (-1) ^ (l + 1) * zonalHarmonicDeriv l θ := by
  rw [zonalHarmonicDeriv, zonalHarmonicDeriv, sin_mul_derivative_legendre_eval_cos_pi_sub]
  ring

/-- **Parity of the vector harmonics.** `Y_l (π - θ) = (-1)ˡ σ Y_l (θ)`,
`X_l (π - θ) = (-1)ˡ σ X_l (θ)` and `Z_l (π - θ) = (-1)ˡ⁺¹ σ Z_l (θ)`, where `σ` is the
equatorial reflection. -/
theorem vectorHarmonic_pi_sub (l : ℕ) (k : Fin 3) (θ : ℝ) :
    vectorHarmonic l k (Real.pi - θ) =
      vectorHarmonicParity l k • coordinateReflection 2 (vectorHarmonic l k θ) := by
  have hsmul (a : ℝ) (x : ℝ^3) :
      coordinateReflection 2 (a • x) = a • coordinateReflection 2 x :=
    (coordinateReflectionLinearIsometryEquiv 2).map_smul a x
  fin_cases k
  · simp only [vectorHarmonic, vectorHarmonicProfile, vectorHarmonicParity, hsmul, frame,
      zonalHarmonic_pi_sub, radialFrame_pi_sub]
    simp [smul_smul]
  · simp only [vectorHarmonic, vectorHarmonicProfile, vectorHarmonicParity, hsmul, frame,
      zonalHarmonicDeriv_pi_sub, polarFrame_pi_sub]
    simp [smul_smul, pow_succ]
  · simp only [vectorHarmonic, vectorHarmonicProfile, vectorHarmonicParity, hsmul, frame]
    simp [smul_smul, zonalHarmonicDeriv_pi_sub, coordinateReflection_azimuthalFrame]

/-- The parity of a vector harmonic is a sign. -/
theorem vectorHarmonicParity_sq (l : ℕ) (k : Fin 3) : vectorHarmonicParity l k ^ 2 = 1 := by
  unfold vectorHarmonicParity
  split_ifs <;> rw [← pow_mul, mul_comm, pow_mul] <;> simp

/-- If `v (π - θ) = ε σ (v θ)` almost everywhere, the inner product of `v` with a vector harmonic
of parity `p` satisfies `⟪Y, v⟫ = p ε ⟪Y, v⟫`. -/
theorem inner_vectorHarmonicLp_eq_mul_of_parity {v : Lp (ℝ^3) 2 polarAngleMeasure} {ε : ℝ}
    (hv : ∀ᵐ θ ∂polarAngleMeasure, v (Real.pi - θ) = ε • coordinateReflection 2 (v θ))
    (l : ℕ) (k : Fin 3) :
    ⟪vectorHarmonicLp l k, v⟫ = vectorHarmonicParity l k * ε * ⟪vectorHarmonicLp l k, v⟫ := by
  have hY : ⟪vectorHarmonicLp l k, v⟫ =
      ∫ θ, ⟪vectorHarmonic l k θ, (v : ℝ → ℝ^3) θ⟫ ∂polarAngleMeasure := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_vectorHarmonicLp l k] with θ hθ
    rw [hθ]
  calc ⟪vectorHarmonicLp l k, v⟫
      = ∫ θ, ⟪vectorHarmonic l k θ, (v : ℝ → ℝ^3) θ⟫ ∂polarAngleMeasure := hY
    _ = ∫ θ, ⟪vectorHarmonic l k (Real.pi - θ), (v : ℝ → ℝ^3) (Real.pi - θ)⟫
          ∂polarAngleMeasure :=
        (integral_polarAngleMeasure_comp_pi_sub fun θ ↦
          ⟪vectorHarmonic l k θ, (v : ℝ → ℝ^3) θ⟫).symm
    _ = ∫ θ, vectorHarmonicParity l k * ε * ⟪vectorHarmonic l k θ, (v : ℝ → ℝ^3) θ⟫
          ∂polarAngleMeasure := by
        refine integral_congr_ae ?_
        filter_upwards [hv] with θ hθ
        rw [vectorHarmonic_pi_sub, hθ, real_inner_smul_left, real_inner_smul_right]
        change _ * (_ * ⟪coordinateReflectionLinearIsometryEquiv 2 _,
          coordinateReflectionLinearIsometryEquiv 2 _⟫) = _
        rw [LinearIsometryEquiv.inner_map_map]
        ring
    _ = vectorHarmonicParity l k * ε * ⟪vectorHarmonicLp l k, v⟫ := by
        rw [integral_const_mul, hY]

/-- **Parity selection.** If `v (π - θ) = ε σ (v θ)` almost everywhere, the coefficient of `v`
on a vector harmonic vanishes unless its parity is `ε`. -/
theorem vectorHarmonicCoeff_eq_zero_of_parity {v : Lp (ℝ^3) 2 polarAngleMeasure} {ε : ℝ}
    (hv : ∀ᵐ θ ∂polarAngleMeasure, v (Real.pi - θ) = ε • coordinateReflection 2 (v θ))
    {l : ℕ} {k : Fin 3} (hlk : ε ≠ vectorHarmonicParity l k) :
    vectorHarmonicCoeff v l k = 0 := by
  rw [vectorHarmonicCoeff, eq_zero_of_eq_mul_of_ne (vectorHarmonicParity_sq l k)
    (inner_vectorHarmonicLp_eq_mul_of_parity hv l k) hlk, zero_div]

/-- **Parity selection** for a square-integrable function: if `v (π - θ) = ε σ (v θ)` almost
everywhere, the coefficient of `v` on a vector harmonic vanishes unless its parity is `ε`. -/
theorem vectorHarmonicCoeff_toLp_eq_zero_of_parity {v : ℝ → ℝ^3}
    (hv : MemLp v 2 polarAngleMeasure) {ε : ℝ}
    (hpar : ∀ᵐ θ ∂polarAngleMeasure, v (Real.pi - θ) = ε • coordinateReflection 2 (v θ))
    {l : ℕ} {k : Fin 3} (hlk : ε ≠ vectorHarmonicParity l k) :
    vectorHarmonicCoeff (hv.toLp v) l k = 0 := by
  refine vectorHarmonicCoeff_eq_zero_of_parity ?_ hlk
  have h₁ := hv.coeFn_toLp
  have h₂ := QuasiMeasurePreserving.ae_eq_comp
    measurePreserving_pi_sub_polarAngleMeasure.quasiMeasurePreserving h₁
  filter_upwards [h₁, h₂, hpar] with θ hθ₁ hθ₂ hθ₃
  simp only [Function.comp_apply] at hθ₂
  rw [hθ₂, hθ₁, hθ₃]

/-- **Expansion in axisymmetric vector spherical harmonics.** Every profile
`v ∈ L²((0, π), sin θ dθ; ℝ³)` is the `L²` sum `∑_l (u_l^Y Y_l + u_l^X X_l + u_l^Z Z_l)` of its
components on `Y_l = S_l e_r`, `X_l = S_l' e_θ` and `Z_l = S_l' e_φ`. If `v (π - θ) = ε σ (v θ)`
almost everywhere, where `σ` is the equatorial reflection, then every coefficient on a mode
whose parity differs from `ε` vanishes: the parity is `(-1)ˡ` for `Y_l` and `X_l` and `(-1)ˡ⁺¹`
for `Z_l`.

The theorem is stated for the meridian profile `v θ = u (point 1 θ 0)` of an axisymmetric field
`u` rather than for `u` in `L²` of the sphere. The two forms are related by the identity
`‖u‖²_{L²(S²)} = 2π ‖v‖²`, a property of the sphere measure that is not proved in this module,
and the profile form is the one applied radius by radius on the ball. -/
theorem axisymmetric_vectorHarmonic_expansion (v : Lp (ℝ^3) 2 polarAngleMeasure) :
    HasSum (fun l ↦ ∑ k : Fin 3, vectorHarmonicCoeff v l k • vectorHarmonicLp l k) v ∧
      ∀ ε : ℝ, (∀ᵐ θ ∂polarAngleMeasure, v (Real.pi - θ) = ε • coordinateReflection 2 (v θ)) →
        ∀ l k, ε ≠ vectorHarmonicParity l k → vectorHarmonicCoeff v l k = 0 :=
  ⟨hasSum_vectorHarmonicCoeff_smul v, fun _ hv _ _ hlk ↦
    vectorHarmonicCoeff_eq_zero_of_parity hv hlk⟩

/-- A field of parity `ε` is the `L²` sum of its expansion over the modes of parity `ε` alone. -/
theorem hasSum_vectorHarmonicCoeff_smul_of_parity {v : Lp (ℝ^3) 2 polarAngleMeasure} {ε : ℝ}
    (hv : ∀ᵐ θ ∂polarAngleMeasure, v (Real.pi - θ) = ε • coordinateReflection 2 (v θ)) :
    HasSum (fun l ↦ ∑ k with vectorHarmonicParity l k = ε,
      vectorHarmonicCoeff v l k • vectorHarmonicLp l k) v := by
  convert hasSum_vectorHarmonicCoeff_smul v using 2 with l
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs with h
  · rfl
  · rw [vectorHarmonicCoeff_eq_zero_of_parity hv (Ne.symm h), zero_smul]

end Parity

section Rotation

open PDE.CoordinateSystems

/-- Rotating a vector harmonic along the meridian gives the vector harmonic at azimuth `φ`. -/
theorem axisRotation_vectorHarmonic (φ : ℝ) (l : ℕ) (k : Fin 3) (θ : ℝ) :
    axisRotation φ (vectorHarmonic l k θ) = vectorHarmonicProfile l k θ • frame θ φ k := by
  rw [vectorHarmonic, axisRotation_smul, axisRotation_frame]

end Rotation

section MeridianExpansion

open Filter Topology Real

/-- The vector harmonics are orthogonal for `sin θ dθ` on `(0, π)`, with squared norms
`vectorHarmonicNormSq`. -/
theorem integral_inner_vectorHarmonic_mul_sin (l m : ℕ) (k j : Fin 3) :
    ∫ θ in (0 : ℝ)..π, ⟪vectorHarmonic l k θ, vectorHarmonic m j θ⟫ * sin θ =
      if l = m ∧ k = j then vectorHarmonicNormSq l k else 0 := by
  have h1 : ∫ θ, ⟪vectorHarmonic l k θ, vectorHarmonic m j θ⟫ ∂polarAngleMeasure =
      ⟪vectorHarmonicLp l k, vectorHarmonicLp m j⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_vectorHarmonicLp l k, coeFn_vectorHarmonicLp m j] with θ h1 h2
    rw [h1, h2]
  rw [← inner_vectorHarmonicLp_vectorHarmonicLp, ← h1, integral_polarAngleMeasure_eq]

/-- `‖X_l‖² = l (l + 1) ‖Y_l‖²`. -/
theorem vectorHarmonicNormSq_one (l : ℕ) :
    vectorHarmonicNormSq l 1 = l * (l + 1) * vectorHarmonicNormSq l 0 := by
  simp only [vectorHarmonicNormSq, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  ring

/-- `‖Y_l‖² > 0`. -/
theorem vectorHarmonicNormSq_zero_pos (l : ℕ) : 0 < vectorHarmonicNormSq l 0 := by
  simp only [vectorHarmonicNormSq, ↓reduceIte]
  positivity

/-- The squared norms of the vector harmonics are nonnegative. -/
theorem vectorHarmonicNormSq_nonneg (l : ℕ) (k : Fin 3) : 0 ≤ vectorHarmonicNormSq l k := by
  unfold vectorHarmonicNormSq
  split_ifs <;> positivity

/-- **Convergence of the meridian expansion with Bessel's bound.** For a square-integrable
profile `v` on `((0, π), sin θ dθ)` with vector harmonic coefficients `c`, the partial sums
`Q_N = ∑_{l < N} ∑_k c_{l,k} X_{l,k}` satisfy `∫ ‖v - Q_N‖² → 0` and `∫ ‖v - Q_N‖² ≤ 4 ∫ ‖v‖²`. -/
theorem tendsto_integral_norm_sub_partialSum {v : ℝ → ℝ^3} (hv : MemLp v 2 polarAngleMeasure) :
    Tendsto (fun N ↦ ∫ θ, ‖v θ - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
        vectorHarmonicCoeff (hv.toLp v) l k • vectorHarmonic l k θ‖ ^ 2 ∂polarAngleMeasure)
        atTop (𝓝 0) ∧
      (∀ N, ∫ θ, ‖v θ - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
        vectorHarmonicCoeff (hv.toLp v) l k • vectorHarmonic l k θ‖ ^ 2 ∂polarAngleMeasure ≤
          4 * ∫ θ, ‖v θ‖ ^ 2 ∂polarAngleMeasure) ∧
      ∀ N, Integrable (fun θ ↦ ‖v θ - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
        vectorHarmonicCoeff (hv.toLp v) l k • vectorHarmonic l k θ‖ ^ 2) polarAngleMeasure := by
  set V : Lp (ℝ^3) 2 polarAngleMeasure := hv.toLp v with hV
  set c : ℕ → Fin 3 → ℝ := vectorHarmonicCoeff V with hc
  set P : ℕ → Lp (ℝ^3) 2 polarAngleMeasure := fun N ↦
    ∑ l ∈ Finset.range N, ∑ k : Fin 3, c l k • vectorHarmonicLp l k with hP
  have hcoe (N : ℕ) : (V - P N : Lp (ℝ^3) 2 polarAngleMeasure) =ᵐ[polarAngleMeasure]
      fun θ ↦ v θ - ∑ l ∈ Finset.range N, ∑ k : Fin 3, c l k • vectorHarmonic l k θ := by
    have hPN : (P N : ℝ → ℝ^3) =ᵐ[polarAngleMeasure] ∑ l ∈ Finset.range N,
        ∑ k : Fin 3, fun θ ↦ c l k • vectorHarmonic l k θ := by
      refine (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun l _ ↦
        (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun k _ ↦ ?_))
      filter_upwards [Lp.coeFn_smul (c l k) (vectorHarmonicLp l k),
        coeFn_vectorHarmonicLp l k] with θ h1 h2
      rw [h1, Pi.smul_apply, h2]
    filter_upwards [Lp.coeFn_sub V (P N), hv.coeFn_toLp, hPN] with θ h1 h2 h3
    rw [h1, Pi.sub_apply, hV, h2, h3]
    simp only [Finset.sum_apply]
  have hnorm (N : ℕ) : ∫ θ, ‖v θ - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
      c l k • vectorHarmonic l k θ‖ ^ 2 ∂polarAngleMeasure = ‖V - P N‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hcoe N] with θ h
    rw [h, real_inner_self_eq_norm_sq]
  have hVn : ∫ θ, ‖v θ‖ ^ 2 ∂polarAngleMeasure = ‖V‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hv.coeFn_toLp] with θ h
    rw [hV, h, real_inner_self_eq_norm_sq]
  have hint (N : ℕ) : Integrable (fun θ ↦ ‖v θ - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
      c l k • vectorHarmonic l k θ‖ ^ 2) polarAngleMeasure := by
    have h := (Lp.memLp (V - P N)).ae_eq (hcoe N)
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  simp only [hnorm, hVn]
  refine ⟨?_, fun N ↦ ?_, hint⟩
  · have hsum := (hasSum_vectorHarmonicCoeff_smul V).tendsto_sum_nat
    have h := tendsto_iff_norm_sub_tendsto_zero.mp hsum
    have h' : Tendsto (fun N ↦ ‖V - P N‖) atTop (𝓝 0) := by
      simpa only [norm_sub_rev] using h
    simpa using h'.pow 2
  · -- Bessel's inequality for the partial sums
    have hPn : ‖P N‖ ^ 2 = ∑ l ∈ Finset.range N, ∑ k : Fin 3,
        vectorHarmonicNormSq l k * c l k ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [hP, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        inner_vectorHarmonicLp_vectorHarmonicLp]
      refine Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Finset.sum_eq_single l (fun l' _ hl' ↦ by simp [hl']) (fun h ↦ absurd hl h),
        Finset.sum_eq_single k (fun k' _ hk' ↦ by simp [hk']) (by simp)]
      simp only [and_self, ↓reduceIte]
      ring
    have hle : ‖P N‖ ^ 2 ≤ ‖V‖ ^ 2 := by
      rw [hPn]
      exact sum_le_hasSum (Finset.range N) (fun l _ ↦ Finset.sum_nonneg fun k _ ↦
        mul_nonneg (vectorHarmonicNormSq_nonneg l k) (sq_nonneg _))
        (hasSum_sq_vectorHarmonicCoeff V)
    have hle' : ‖P N‖ ≤ ‖V‖ := by
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle
    have htri : ‖V - P N‖ ≤ 2 * ‖V‖ := (norm_sub_le _ _).trans (by linarith)
    have h0 : 0 ≤ ‖V - P N‖ := norm_nonneg _
    nlinarith
end MeridianExpansion

end PDE.Analysis.SpecialFunctions
