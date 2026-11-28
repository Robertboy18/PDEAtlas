/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.Complexification
public import PDE.Analysis.InnerProductSpace.Complexification.Lift
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.EnergyConjugation

/-!
# Complex vector fields as pairs of real vector fields

The spectral theory of a real operator on real vector fields in `L²(ℝⁿ)` runs on the
complexification, where a pair `(f, g)` stands for `f + i g`. The Fourier side works with
families of complex `L²` functions instead. This module shows that the two models are the same
space: `(f, g) ↦ (fⱼ + i gⱼ)ⱼ` is a complex-linear bijection, for every number of components and
every dimension, and the Bessel energy of the complex field is the sum of the energies of `f`
and `g`, at every real order. At order zero, with Plancherel, this reads
`∑ⱼ ‖fⱼ + i gⱼ‖² = ∑ⱼ ‖fⱼ‖² + ∑ⱼ ‖gⱼ‖²`, so the map is an isometry onto the Hilbert sum of the
components. It is not stated as a linear isometry onto `PiLp 2`, and it is not one for the norm
of `Fin m → Lp ℂ 2`, which is the maximum of the norms of the components.

## Main results

* `realCoordinateL2`: a real coordinate of a complex `L²` function, as a real `L²` function;
  `complexifyL2CLM_realCoordinateL2_add_I_smul` writes `f = Re f + i Im f`.
* `complexFamily`, `complexFamilyEquiv`, `complexFamilyCLM`: the complex components of a pair of
  real vector fields, as a complex-linear map, as a complex-linear equivalence
  (`complexFamily_bijective`) and as a bounded operator (`continuous_complexFamily`).
* `besselEnergy_complexFamily`: `E_σ((fⱼ + i gⱼ)ⱼ) = E_σ(f) + E_σ(g)` for every real `σ`.

## How it works

The map is the complex-linear extension `PDE.Analysis.Complexification.lift` of the
complexification of the components, and its inverse takes real and imaginary parts
(`realCoordinateL2_re_add_I_smul`, `realCoordinateL2_im_add_I_smul`). The energy identity is
`besselEnergy_add_I_smul` in each component: the transform of a real function is Hermitian and
the weight is even. `reHs` and `imHs` take the same parts of an element of `H^s`; the maps here
are on `L²`, with values in the real `L²` space of the graph spaces.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.GraphSpace PDE.Analysis PDE.Analysis.Complexification
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.Fractional

variable {n m : ℕ}

/-! ## Real and imaginary parts -/

/-- A real coordinate `L ∘ f` of a complex `L²` function `f`, for a real-linear functional
`L : ℂ → ℝ`, as a real `L²` function. -/
def realCoordinateL2 (n : ℕ) (L : ℂ →L[ℝ] ℝ) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) →L[ℝ] DerivLp n 2 univ :=
  wholeSpaceL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L L.compLpL 2 volume

/-- The complexification of a real coordinate is that coordinate, almost everywhere. -/
theorem complexifyL2CLM_realCoordinateL2_ae (L : ℂ →L[ℝ] ℝ)
    (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (complexifyL2CLM n (realCoordinateL2 n L f) : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (L (f x) : ℂ) := by
  have h1 : complexifyL2CLM n (realCoordinateL2 n L f) =
      Complex.ofRealCLM.compLpL 2 volume (L.compLpL 2 volume f) := by
    simp [complexifyL2CLM, realCoordinateL2]
  rw [h1]
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (L.compLpL 2 volume f),
    L.coeFn_compLpL f] with x h2 h3
  rw [h2, h3, Complex.ofRealCLM_apply]

/-- **A complex `L²` function is its real part plus `i` times its imaginary part.** -/
theorem complexifyL2CLM_realCoordinateL2_add_I_smul (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    complexifyL2CLM n (realCoordinateL2 n Complex.reCLM f) +
      Complex.I • complexifyL2CLM n (realCoordinateL2 n Complex.imCLM f) = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (complexifyL2CLM n (realCoordinateL2 n Complex.reCLM f))
      (Complex.I • complexifyL2CLM n (realCoordinateL2 n Complex.imCLM f)),
    Lp.coeFn_smul Complex.I (complexifyL2CLM n (realCoordinateL2 n Complex.imCLM f)),
    complexifyL2CLM_realCoordinateL2_ae Complex.reCLM f,
    complexifyL2CLM_realCoordinateL2_ae Complex.imCLM f] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, mul_comm]
  exact Complex.re_add_im _

/-- A real coordinate of `u + i v` for real `u`, `v`, complexified. -/
private theorem complexifyL2CLM_realCoordinateL2_add (L : ℂ →L[ℝ] ℝ) (u v : DerivLp n 2 univ) :
    (complexifyL2CLM n (realCoordinateL2 n L
      (complexifyL2CLM n u + Complex.I • complexifyL2CLM n v)) : ℝ^n → ℂ) =ᵐ[volume]
        fun x ↦ (L ((u x : ℂ) + Complex.I * (v x : ℂ)) : ℂ) := by
  filter_upwards [complexifyL2CLM_realCoordinateL2_ae L
      (complexifyL2CLM n u + Complex.I • complexifyL2CLM n v),
    Lp.coeFn_add (complexifyL2CLM n u) (Complex.I • complexifyL2CLM n v),
    Lp.coeFn_smul Complex.I (complexifyL2CLM n v), complexifyL2CLM_ae u,
    complexifyL2CLM_ae v] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul]

/-- The real part of `u + i v` is `u`, for real `u`, `v`. -/
theorem realCoordinateL2_re_add_I_smul (u v : DerivLp n 2 univ) :
    realCoordinateL2 n Complex.reCLM
      (complexifyL2CLM n u + Complex.I • complexifyL2CLM n v) = u := by
  refine complexifyL2CLM_injective (Lp.ext ?_)
  filter_upwards [complexifyL2CLM_realCoordinateL2_add Complex.reCLM u v,
    complexifyL2CLM_ae u] with x h1 h2
  rw [h1, h2]
  simp

/-- The imaginary part of `u + i v` is `v`, for real `u`, `v`. -/
theorem realCoordinateL2_im_add_I_smul (u v : DerivLp n 2 univ) :
    realCoordinateL2 n Complex.imCLM
      (complexifyL2CLM n u + Complex.I • complexifyL2CLM n v) = v := by
  refine complexifyL2CLM_injective (Lp.ext ?_)
  filter_upwards [complexifyL2CLM_realCoordinateL2_add Complex.imCLM u v,
    complexifyL2CLM_ae v] with x h1 h2
  rw [h1, h2]
  simp

/-! ## Complex vector fields -/

/-- Real vector fields in `L²(ℝⁿ)` with `m` components. -/
local notation "RealField" => PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)

/-- The complexified components of a real vector field, a real-linear map. -/
def complexifyFamily (m n : ℕ) :
    PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ) →ₗ[ℝ] (Fin m → Lp ℂ 2 (volume : Measure (ℝ^n))) where
  toFun f i := complexifyL2CLM n (f i)
  map_add' f g := funext fun i ↦ map_add (complexifyL2CLM n) (f i) (g i)
  map_smul' r f := funext fun i ↦ map_smul (complexifyL2CLM n) r (f i)

/-- **The complex components of a complex vector field** given by its real and imaginary parts:
`(f, g) ↦ (fⱼ + i gⱼ)ⱼ`, a complex-linear map from the complexification of real vector `L²` to
the families of complex `L²` functions. -/
def complexFamily (m n : ℕ) :
    Complexification (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) →ₗ[ℂ]
      (Fin m → Lp ℂ 2 (volume : Measure (ℝ^n))) :=
  lift (complexifyFamily m n)

/-- The components of the complex field are `fⱼ + i gⱼ`. -/
theorem complexFamily_apply (z : Complexification RealField) (j : Fin m) :
    complexFamily m n z j =
      complexifyL2CLM n (z.re j) + Complex.I • complexifyL2CLM n (z.im j) := rfl

/-- **The two models of complex vector `L²` are the same**: the complex components are a
bijection from the complexification onto the families of complex `L²` functions. -/
theorem complexFamily_bijective : Function.Bijective (complexFamily m n) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
    have hj (j : Fin m) : complexifyL2CLM n (z.re j) +
        Complex.I • complexifyL2CLM n (z.im j) = 0 := congrFun hz j
    refine Complexification.ext (PiLp.ext fun j ↦ ?_) (PiLp.ext fun j ↦ ?_)
    · rw [← realCoordinateL2_re_add_I_smul (z.re j) (z.im j), hj j, map_zero]
      rfl
    · rw [← realCoordinateL2_im_add_I_smul (z.re j) (z.im j), hj j, map_zero]
      rfl
  · intro f
    refine ⟨Complexification.mk (WithLp.toLp 2 fun j ↦ realCoordinateL2 n Complex.reCLM (f j))
      (WithLp.toLp 2 fun j ↦ realCoordinateL2 n Complex.imCLM (f j)), funext fun j ↦ ?_⟩
    exact complexifyL2CLM_realCoordinateL2_add_I_smul (f j)

/-- The complexified components depend continuously on the real field. -/
theorem continuous_complexifyFamily : Continuous (complexifyFamily m n) :=
  continuous_pi fun j ↦ (complexifyL2CLM n).continuous.comp (PiLp.continuous_apply 2 _ j)

/-- The complex components depend continuously on the complex field. -/
theorem continuous_complexFamily : Continuous (complexFamily m n) :=
  continuous_lift continuous_complexifyFamily

/-- **The complex components as a bounded operator** from the complexification of real vector
`L²` to the families of complex `L²` functions. -/
def complexFamilyCLM (m n : ℕ) :
    Complexification (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) →L[ℂ]
      (Fin m → Lp ℂ 2 (volume : Measure (ℝ^n))) :=
  ⟨complexFamily m n, continuous_complexFamily⟩

/-- The bounded operator is the map of complex components. -/
@[simp]
theorem complexFamilyCLM_apply (z : Complexification RealField) :
    complexFamilyCLM m n z = complexFamily m n z := rfl

/-- The complex components as a complex-linear equivalence. -/
def complexFamilyEquiv (m n : ℕ) :
    Complexification (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) ≃ₗ[ℂ]
      (Fin m → Lp ℂ 2 (volume : Measure (ℝ^n))) :=
  LinearEquiv.ofBijective (complexFamily m n) complexFamily_bijective

/-- The equivalence is the map of complex components. -/
@[simp]
theorem complexFamilyEquiv_apply (z : Complexification RealField) :
    complexFamilyEquiv m n z = complexFamily m n z := rfl

/-- **The energy of a complex vector field is the sum of the energies of its real and imaginary
parts**, for every real order: `E_σ((fⱼ + i gⱼ)ⱼ) = E_σ(f) + E_σ(g)`. -/
theorem besselEnergy_complexFamily (σ : ℝ) (z : Complexification RealField) :
    besselEnergy σ (complexFamily m n z) =
      besselEnergy σ (complexifyFamily m n z.re) + besselEnergy σ (complexifyFamily m n z.im) := by
  rw [besselEnergy_eq_sum, besselEnergy_eq_sum (f := complexifyFamily m n z.re),
    besselEnergy_eq_sum (f := complexifyFamily m n z.im), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ besselEnergy_add_I_smul σ
    (isRealL2_complexifyL2CLM (z.re j)) (isRealL2_complexifyL2CLM (z.im j))

end SobolevSpace.Fractional
