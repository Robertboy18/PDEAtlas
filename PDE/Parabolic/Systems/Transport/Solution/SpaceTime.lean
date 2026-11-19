/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Solution.Representatives
import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.TensorTesting

/-!
# The strong matrix diffusion equation in physical spacetime

The canonical Euclidean time-space splitting preserves the restricted
Lebesgue measure. Joint representatives therefore give weak spatial
derivatives and the full matrix PDE on one exceptional set in the physical
spacetime slab, for all components and derivative rows.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution

open MeasureTheory Set PDE.Common
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n m : ℕ} {ε a b : ℝ}
  {B : Fin n → SpaceTime n → Fin m → Fin m → ℝ}
  {f : Fin m → SpaceTime n → ℝ}
  {q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}
  {U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}

/-- All derivative rows have jointly measurable physical spacetime
representatives satisfying the full coupled equation almost everywhere. -/
theorem exists_spacetimeRepresentatives
    (h : IsStrongTransportDiffusionSolution ε a b
      (fun j y p q ↦ B j (timeSpaceCons y.1 y.2) p q)
      (fun p y ↦ f p (timeSpaceCons y.1 y.2)) q U G z)
    (hB : ∀ j p q, AEStronglyMeasurable
      (fun y : ℝ × ℝ^n ↦ B j (timeSpaceCons y.1 y.2) p q)
      ((volume.restrict (Ioc a b)).prod volume))
    (hf : ∀ p, AEStronglyMeasurable
      (fun y : ℝ × ℝ^n ↦ f p (timeSpaceCons y.1 y.2))
      ((volume.restrict (Ioc a b)).prod volume)) :
    ∃ (r : Fin m → DerivIndex n 3 → SpaceTime n → ℝ)
      (v : Fin m → DerivIndex n 1 → SpaceTime n → ℝ),
      (∀ p d, StronglyMeasurable (r p d) ∧
        MemLp (r p d) 2 (volume.restrict {y | y 0 ∈ Ioc a b})) ∧
      (∀ p d, StronglyMeasurable (v p d) ∧
        MemLp (v p d) 2 (volume.restrict {y | y 0 ∈ Ioc a b})) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p d,
        r p d (timeSpaceCons t x) = wkpCoordinateCLM d (U t p) x) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p d,
        v p d (timeSpaceCons t x) = wkpCoordinateCLM d (G t p) x) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ p d, HasWeakDerivativeOn univ d.toList
        (fun x ↦ r p (baseIndex n 3) (timeSpaceCons t x))
        (fun x ↦ r p d (timeSpaceCons t x))) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ p d, HasWeakDerivativeOn univ d.toList
        (fun x ↦ v p (baseIndex n 1) (timeSpaceCons t x))
        (fun x ↦ v p d (timeSpaceCons t x))) ∧
      (∀ᵐ y ∂volume.restrict {y : SpaceTime n | y 0 ∈ Ioc a b}, ∀ p,
        v p (baseIndex n 1) y -
          ε * (∑ j, r p ((pairDerivIndex n j j).castOrder (by decide : 2 ≤ 3)) y) +
          (∑ j, ∑ q, B j y p q *
            r q ((singleDerivIndex n j).castOrder (by decide : 1 ≤ 3)) y) = f p y) := by
  obtain ⟨r, v, hr, hv, hrU, hvG, hrweak, hvweak, heq⟩ :=
    h.exists_jointRepresentatives hB hf
  let e := timeSpaceContinuousLinearEquiv n
  have hm : MeasurePreserving e (volume.restrict {y | y 0 ∈ Ioc a b})
      ((volume.restrict (Ioc a b)).prod volume) :=
    MeasurePreserving.symm e.symm.toHomeomorph.toMeasurableEquiv
      (Slices.measurePreserving_timeSpaceCons_restrict (n := n) (Ioc a b))
  have he (t : ℝ) (x : ℝ^n) : e (timeSpaceCons t x) = (t, x) := by
    exact e.apply_symm_apply (t, x)
  refine ⟨fun p d ↦ r p d ∘ e, fun p d ↦ v p d ∘ e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p d ↦ ⟨(hr p d).1.comp_measurable e.continuous.measurable,
      (hr p d).2.comp_measurePreserving hm⟩
  · exact fun p d ↦ ⟨(hv p d).1.comp_measurable e.continuous.measurable,
      (hv p d).2.comp_measurePreserving hm⟩
  · simpa only [Function.comp_def, he] using hrU
  · simpa only [Function.comp_def, he] using hvG
  · simpa only [Function.comp_def, he] using hrweak
  · simpa only [Function.comp_def, he] using hvweak
  · have heq' := hm.quasiMeasurePreserving.ae heq
    have hinv (y : SpaceTime n) : timeSpaceCons (e y).1 (e y).2 = y :=
      e.symm_apply_apply y
    simpa only [Function.comp_def, hinv] using heq'

end PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution
