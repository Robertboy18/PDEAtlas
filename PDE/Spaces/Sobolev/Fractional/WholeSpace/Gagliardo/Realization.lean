/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.Fourier
import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.ZeroDimensional
import PDE.Spaces.Sobolev.Fractional.WholeSpace.ZeroDimensional
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Notation

/-!
# The common physical realization of the two fractional spaces

For every dimension and `0 < s < 1`, the complete Gagliardo graph space and the real
Bessel-potential space have the same range in physical `L²(ℝ^n)`. We construct
the linear equivalence by this faithful realization. Norm estimates and continuity
are proved separately in `Gagliardo/Equivalence`.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace ENNReal FourierTransform SchwartzMap Sobolev

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

namespace GagliardoSpace

/-- The physical `L²(ℝ^n)` class of a whole-space Gagliardo element.
Composition with the identity removes the restriction of volume to `univ`. -/
def toL2CLM (n : ℕ) (s : ℝ) :
    GagliardoSpace n s Set.univ →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ id
    (by simpa only [Measure.restrict_univ] using
      (MeasurePreserving.id (volume : Measure (ℝ^n))))).toContinuousLinearMap.comp
        (toLp n s Set.univ)

/-- The physical realization has the same representatives as the graph's base coordinate. -/
theorem toL2CLM_apply_ae (u : GagliardoSpace n s Set.univ) :
    (toL2CLM n s u : ℝ^n → ℝ) =ᵐ[volume] (toLp n s Set.univ u : ℝ^n → ℝ) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Removing the redundant measure restriction preserves the base-coordinate norm. -/
theorem norm_toL2CLM_eq (u : GagliardoSpace n s Set.univ) :
    ‖toL2CLM n s u‖ = ‖toLp n s Set.univ u‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- The physical `L²` realization is faithful. -/
theorem toL2CLM_injective : Function.Injective (toL2CLM n s) := by
  intro u v huv
  apply toLp_injective
  apply Lp.ext
  simpa only [Measure.restrict_univ] using
    (toL2CLM_apply_ae u).symm.trans (huv ▸ toL2CLM_apply_ae v)

/-- The physical representative of a graph-space element satisfies the Gagliardo condition. -/
theorem memGagliardo_toL2CLM (u : GagliardoSpace n s Set.univ) :
    MemGagliardo n s Set.univ (toL2CLM n s u) := by
  apply (memGagliardo_iff_exists_gagliardoSpace _).mpr
  exact ⟨u, by simpa only [Measure.restrict_univ] using (toL2CLM_apply_ae u).symm⟩

/-- Constructing a graph element from a physical `L²` class preserves that class. -/
theorem toL2CLM_ofFunction (u : Lp ℝ 2 (volume : Measure (ℝ^n)))
    (hu : MemGagliardo n s Set.univ u) :
    toL2CLM n s (ofFunction (u : ℝ^n → ℝ) hu) = u := by
  apply Lp.ext
  exact (toL2CLM_apply_ae _).trans
    (by simpa only [Measure.restrict_univ] using toLp_ofFunction_apply_ae (u : ℝ^n → ℝ) hu)

end GagliardoSpace

/-- Complexification of a real `L²` class agrees with complexifying its representatives. -/
theorem ofReal_toLp_eq (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    (Lp.memLp u).ofReal.toLp (fun x ↦ (u x : ℂ)) =
      Complex.ofRealCLM.compLpL 2 volume u := by
  apply Lp.ext
  exact (Lp.memLp u).ofReal.coeFn_toLp.trans (Complex.ofRealCLM.coeFn_compLpL u).symm

/-- For real physical `L²` classes, Gagliardo membership is exactly Bessel regularity of
the associated complex tempered distribution. -/
theorem memGagliardo_univ_iff_memSobolev
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    MemGagliardo n s Set.univ u ↔
      MemSobolev s 2 (Complex.ofRealCLM.compLpL 2 volume u : 𝓢'(ℝ^n, ℂ)) := by
  rw [memGagliardo_univ_iff_fourierSq_lt_top hs0 hs1 (u : ℝ^n → ℝ) (Lp.memLp u).ofReal,
    ofReal_toLp_eq, ← memLp_homogeneousWeightedFourier_iff,
    ← memSobolev_iff_memLp_homogeneousWeightedFourier hs0.le (by linarith : s ≤ 2)]

namespace GagliardoSpace

/-- The complex physical class of a Gagliardo element has Bessel regularity. -/
theorem memSobolev_toL2CLM (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    MemSobolev s 2
      (Complex.ofRealCLM.compLpL 2 volume (toL2CLM n s u) : 𝓢'(ℝ^n, ℂ)) :=
  (memGagliardo_univ_iff_memSobolev hs0 hs1 _).mp (memGagliardo_toL2CLM u)

/-- Bessel realization of the physical distribution preserves the physical complex `L²` class. -/
theorem toL2Fun_besselRealization
    (hs0 : 0 < s) (hs1 : s < 1) (u : GagliardoSpace n s Set.univ) :
    toL2Fun hs0.le (memSobolev_toL2CLM hs0 hs1 u).toBesselPotentialSpace =
      Complex.ofRealCLM.compLpL 2 volume (toL2CLM n s u) := by
  apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
  simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply]
  simpa only [MemSobolev.toBesselPotentialSpace_toDistr] using
    (toDistr_eq_toL2Fun hs0.le
      (memSobolev_toL2CLM hs0 hs1 u).toBesselPotentialSpace).symm

/-- Realize a complete Gagliardo-space element as a real Bessel-potential element with
the same physical function. No norm comparison is assumed in this construction. -/
def toHsSpaceReal (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) : H^{s}(ℝ^n; ℝ) :=
  HsSpaceReal.ofPhysical hs0.le (memSobolev_toL2CLM hs0 hs1 u).toBesselPotentialSpace
    (by
      rw [toL2Fun_besselRealization hs0 hs1]
      filter_upwards [Complex.ofRealCLM.coeFn_compLpL (toL2CLM n s u)] with x hx
      simp only [hx, Complex.ofRealCLM_apply, Complex.ofReal_im])

/-- The realization agrees in physical real `L²`. -/
theorem toL2FunCLM_toHsSpaceReal
    (hs0 : 0 < s) (hs1 : s < 1) (u : GagliardoSpace n s Set.univ) :
    HsSpaceReal.toL2FunCLM n hs0.le (toHsSpaceReal hs0 hs1 u) = toL2CLM n s u := by
  apply Lp.ext
  filter_upwards [HsSpaceReal.toL2FunCLM_apply_ae hs0.le (toHsSpaceReal hs0 hs1 u),
    Complex.ofRealCLM.coeFn_compLpL (toL2CLM n s u)] with x hr hc
  rw [hr]
  change (toL2Fun hs0.le (memSobolev_toL2CLM hs0 hs1 u).toBesselPotentialSpace x).re = _
  rw [toL2Fun_besselRealization hs0 hs1, hc]
  rfl

/-- The map between the completed spaces is real linear. -/
def toHsSpaceRealLinear (hs0 : 0 < s) (hs1 : s < 1) :
    GagliardoSpace n s Set.univ →ₗ[ℝ] H^{s}(ℝ^n; ℝ) where
  toFun := toHsSpaceReal hs0 hs1
  map_add' u v := by
    apply HsSpaceReal.toL2FunCLM_injective hs0.le
    simp only [map_add, toL2FunCLM_toHsSpaceReal]
  map_smul' c u := by
    apply HsSpaceReal.toL2FunCLM_injective hs0.le
    simp only [map_smul, toL2FunCLM_toHsSpaceReal, RingHom.id_apply]

/-- Every real Bessel element is represented in the complete Gagliardo graph space. -/
theorem toHsSpaceReal_surjective (hs0 : 0 < s) (hs1 : s < 1) :
    Function.Surjective (toHsSpaceReal (n := n) hs0 hs1) := by
  intro u
  have hu : MemGagliardo n s Set.univ (HsSpaceReal.toL2FunCLM n hs0.le u) := by
    rw [memGagliardo_univ_iff_memSobolev hs0 hs1,
      HsSpaceReal.ofReal_toL2FunCLM, ← toDistr_eq_toL2Fun]
    exact u.1.memSobolev_toDistr
  refine ⟨ofFunction _ hu, ?_⟩
  apply HsSpaceReal.toL2FunCLM_injective hs0.le
  rw [toL2FunCLM_toHsSpaceReal, toL2CLM_ofFunction]

/-- The algebraic identification of the two complete spaces through physical `L²`.
`equivHsSpaceReal` equips this same map with explicit continuity bounds. -/
def linearEquivHsSpaceReal (hs0 : 0 < s) (hs1 : s < 1) :
    GagliardoSpace n s Set.univ ≃ₗ[ℝ] H^{s}(ℝ^n; ℝ) :=
  LinearEquiv.ofBijective (toHsSpaceRealLinear hs0 hs1)
    ⟨fun u v huv ↦ toL2CLM_injective (by
      change toHsSpaceReal hs0 hs1 u = toHsSpaceReal hs0 hs1 v at huv
      simpa only [toL2FunCLM_toHsSpaceReal] using
        congrArg (HsSpaceReal.toL2FunCLM n hs0.le) huv),
      toHsSpaceReal_surjective hs0 hs1⟩

end GagliardoSpace
end SobolevSpace.Fractional
