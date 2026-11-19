/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Definitions

/-!
# The real fractional Sobolev space on `ℝ^n`

`BesselPotentialSpace` is a complex Hilbert space, and has to be:
`TemperedDistribution E F` requires `Module ℂ F`, so `𝓢'(ℝ^n, ℝ)` does not even
elaborate. The real space is carved out of the complex one as a real subspace.

A distribution is real when `conj u = u`. Mathlib has no `Star` structure on
`SchwartzMap` or `TemperedDistribution`, so realness is tested on `toLp u`, where the
bounded imaginary-part map `imaginaryPartL2` on `L²` is all that is needed, and
`hsRealSubmodule` is the kernel of that map composed with `BesselPotentialSpace.toLpₗᵢ`. The two
notions agree because the Bessel symbol `(1 + ‖ξ‖²) ^ (s / 2)` is real and even, so the Bessel
potential commutes with conjugation. That equivalence is proved in
`Fractional.WholeSpace.Conjugation`
(`isRealL2_toL2Fun_iff`, `mem_HsRealSubmodule_iff_toL2Fun`), so this
submodule is interchangeable with the function-representative condition used
elsewhere.

This is a submodule over `ℝ` and not over `ℂ`: it is not closed under
multiplication by `i`.

## Main definitions

* `SobolevSpace.Fractional.IsRealL2`: an `L²` function is real almost everywhere.
* `SobolevSpace.Fractional.imaginaryPartL2`: the imaginary-part map on complex `L²`.
* `SobolevSpace.Fractional.imaginaryPartHs`: the corresponding map on `H^s`.
* `SobolevSpace.Fractional.hsRealSubmodule`: the closed real subspace of `H^s`.
* `SobolevSpace.Fractional.HsSpaceReal`: the real fractional Sobolev space.

## Main results

* `SobolevSpace.Fractional.isRealL2_iff_imaginaryPartL2_eq_zero`: realness a.e. is
  vanishing of the bounded imaginary-part map.
* `SobolevSpace.Fractional.mem_HsRealSubmodule_iff`: membership in the real
  subspace is realness of the Bessel representative `toLp u`.
* `SobolevSpace.Fractional.instCompleteSpaceHsSpaceReal`: `H^s(ℝ^n; ℝ)` is
  complete, being a closed real subspace of `H^s(ℝ^n; ℂ)`, hence a real Hilbert
  space.
-/

@[expose] public section

open MeasureTheory TemperedDistribution
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

open BesselPotentialSpace

variable {n : ℕ} {s : ℝ}

/-- An `L²` function is real when its imaginary part vanishes almost everywhere. -/
def IsRealL2 (f : Lp ℂ 2 (volume : Measure (ℝ^n))) : Prop :=
  ∀ᵐ x ∂(volume : Measure (ℝ^n)), ((f : ℝ^n → ℂ) x).im = 0

/-- The zero function is real. -/
theorem isRealL2_zero : IsRealL2 (0 : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ^n))] with x hx
  rw [hx]
  simp

/-- A sum of a.e. real `L²` functions is a.e. real. -/
theorem IsRealL2.add {f g : Lp ℂ 2 (volume : Measure (ℝ^n))} (hf : IsRealL2 f) (hg : IsRealL2 g) :
    IsRealL2 (f + g) := by
  filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hfx hgx
  rw [hx]
  simp [hfx, hgx]

/-- A real scalar multiple of an a.e. real `L²` function is a.e. real. Only real scalars are
allowed here; multiplication by `i` destroys realness, which is why `hsRealSubmodule` is an
`ℝ`-submodule. -/
theorem IsRealL2.smul {f : Lp ℂ 2 (volume : Measure (ℝ^n))} (r : ℝ) (hf : IsRealL2 f) :
    IsRealL2 (r • f) := by
  filter_upwards [Lp.coeFn_smul (𝕜 := ℝ) r f, hf] with x hx hfx
  rw [hx]
  simp [hfx]

/-- The ambient complex Hilbert space `H^s` regarded as a real Hilbert space.

The real inner product is the real part of the complex inner product and induces
the norm. -/
noncomputable instance instRealInnerProductSpaceHs :
    InnerProductSpace ℝ (H^{s}(ℝ^n)) :=
  InnerProductSpace.rclikeToReal ℂ (H^{s}(ℝ^n))

/-- Take the imaginary part of a complex `L²` function pointwise. -/
noncomputable def imaginaryPartL2 (n : ℕ) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  Complex.imCLM.compLpL 2 (volume : Measure (ℝ^n))

/-- A complex `L²` function is real almost everywhere exactly when its
imaginary part vanishes as an element of real `L²`. -/
theorem isRealL2_iff_imaginaryPartL2_eq_zero (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    IsRealL2 f ↔ imaginaryPartL2 n f = 0 := by
  change IsRealL2 f ↔
    Complex.imCLM.compLpL 2 (volume : Measure (ℝ^n)) f = 0
  constructor
  · intro h
    apply Lp.ext
    filter_upwards [Complex.imCLM.coeFn_compLpL f,
      Lp.coeFn_zero ℝ 2 (volume : Measure (ℝ^n)), h] with x him hzero hx
    rw [him, hzero]
    exact hx
  · intro h
    filter_upwards [Complex.imCLM.coeFn_compLpL f,
      Lp.coeFn_zero ℝ 2 (volume : Measure (ℝ^n))] with x him hzero
    have hx :
        (Complex.imCLM.compLpL 2 (volume : Measure (ℝ^n)) f : ℝ^n → ℝ) x =
          (0 : Lp ℝ 2 (volume : Measure (ℝ^n))) x := by
      rw [h]
    rw [him, hzero] at hx
    exact hx

/-- Take the imaginary part of the Bessel `L²` representative of an `H^s`
element. -/
noncomputable def imaginaryPartHs (n : ℕ) (s : ℝ) :
    H^{s}(ℝ^n) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  (imaginaryPartL2 n).comp
    ((toLpₗᵢ (ℝ^n) ℂ s 2).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

/-- The real fractional Sobolev space as a closed `ℝ`-submodule of the complex
space.  It is not a `ℂ`-submodule because it is not stable under multiplication
by `i`. -/
noncomputable def hsRealSubmodule (n : ℕ) (s : ℝ) : Submodule ℝ (H^{s}(ℝ^n)) :=
  (imaginaryPartHs n s).ker

/-- The real subspace is closed in `H^s`, being the kernel of the continuous map
`imaginaryPartHs`. -/
instance instIsClosedHsRealSubmodule :
    IsClosed ((hsRealSubmodule n s : Submodule ℝ (H^{s}(ℝ^n))) : Set (H^{s}(ℝ^n))) := by
  change IsClosed (((imaginaryPartHs n s).ker : Submodule ℝ (H^{s}(ℝ^n))) :
    Set (H^{s}(ℝ^n)))
  exact (imaginaryPartHs n s).isClosed_ker

/-- The real fractional Sobolev space `H^s(ℝ^n; ℝ)`, realised inside the complex
one.  It is complete because it is the kernel of the bounded imaginary-part
map. -/
noncomputable abbrev HsSpaceReal (n : ℕ) (s : ℝ) : Type := ↥(hsRealSubmodule n s)

/-- `H^s(ℝ^n; ℝ)` is complete: a closed subspace of the complete space `H^s(ℝ^n; ℂ)`. -/
noncomputable instance instCompleteSpaceHsSpaceReal :
    CompleteSpace (HsSpaceReal n s) := by
  change CompleteSpace (imaginaryPartHs n s).ker
  infer_instance

/-- An element of `H^s` lies in the real subspace exactly when its Bessel `L²` representative
`toLp u` is real almost everywhere. -/
theorem mem_HsRealSubmodule_iff {u : H^{s}(ℝ^n)} :
    u ∈ hsRealSubmodule n s ↔ IsRealL2 (toLp u) := by
  change imaginaryPartL2 n ((toLpₗᵢ (ℝ^n) ℂ s 2) u) = 0 ↔ _
  rw [toLpₗᵢ_apply]
  exact (isRealL2_iff_imaginaryPartL2_eq_zero (toLp u)).symm

end SobolevSpace.Fractional
