/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Solution
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Product

/-!
# Joint representatives of strong matrix diffusion solutions

A strong solution admits joint L² representatives of all spatial derivatives
through order three and of its velocity through order one. The same
representatives satisfy the full matrix equation on a single product null
set. This uses joint measurability to pass from sectionwise equalities to
product measure; no measurability of canonical point evaluation is assumed.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n m : ℕ} {ε a b : ℝ}
  {B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ}
  {f : Fin m → ℝ × ℝ^n → ℝ}
  {q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}
  {U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}

/-- All state and velocity derivatives have joint representatives, which are
spatial weak derivatives and satisfy the full matrix PDE off one null set. -/
theorem exists_jointRepresentatives
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z)
    (hB : ∀ j p q, AEStronglyMeasurable (fun y ↦ B j y p q)
      ((volume.restrict (Ioc a b)).prod volume))
    (hf : ∀ p, AEStronglyMeasurable (f p) ((volume.restrict (Ioc a b)).prod volume)) :
    ∃ (r : Fin m → DerivIndex n 3 → ℝ × ℝ^n → ℝ)
      (v : Fin m → DerivIndex n 1 → ℝ × ℝ^n → ℝ),
      (∀ p d, StronglyMeasurable (r p d) ∧
        MemLp (r p d) 2 ((volume.restrict (Ioc a b)).prod volume)) ∧
      (∀ p d, StronglyMeasurable (v p d) ∧
        MemLp (v p d) 2 ((volume.restrict (Ioc a b)).prod volume)) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p d,
        r p d (t, x) = wkpCoordinateCLM d (U t p) x) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p d,
        v p d (t, x) = wkpCoordinateCLM d (G t p) x) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ p d, HasWeakDerivativeOn univ d.toList
        (fun x ↦ r p (baseIndex n 3) (t, x)) (fun x ↦ r p d (t, x))) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ p d, HasWeakDerivativeOn univ d.toList
        (fun x ↦ v p (baseIndex n 1) (t, x)) (fun x ↦ v p d (t, x))) ∧
      (∀ᵐ y ∂(volume.restrict (Ioc a b)).prod volume, ∀ p,
        v p (baseIndex n 1) y -
          ε * (∑ j, r p ((pairDerivIndex n j j).castOrder (by decide : 2 ≤ 3)) y) +
          (∑ j, ∑ q, B j y p q *
            r q ((singleDerivIndex n j).castOrder (by decide : 1 ≤ 3)) y) = f p y) := by
  -- Fix the `PiLp` normed-space structures before elaborating the Bochner maps.
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{3,2}(ℝ^n))
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{1,2}(ℝ^n))
  let μ := volume.restrict (Ioc a b)
  let P₃ (p : Fin m) :
      PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) →L[ℝ] W^{3,2}(ℝ^n) :=
    PiLp.proj 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n)) p
  let P₁ (p : Fin m) :
      PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ] W^{1,2}(ℝ^n) :=
    PiLp.proj 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) p
  obtain ⟨r, hr, hrU, hrweak⟩ :=
    exists_joint_weakCoordinates (fun p ↦ (P₃ p).compLpL 2 μ U)
  obtain ⟨v, hv, hvG, hvweak⟩ :=
    exists_joint_weakCoordinates (fun p ↦ (P₁ p).compLpL 2 μ G)
  simp only [domainMeasure, Measure.restrict_univ] at hr hrU hv hvG
  have hU : ∀ᵐ t ∂μ, ∀ p, (P₃ p).compLpL 2 μ U t = U t p :=
    ae_all_iff.mpr fun p ↦ (P₃ p).coeFn_compLpL U
  have hG : ∀ᵐ t ∂μ, ∀ p, (P₁ p).compLpL 2 μ G t = G t p :=
    ae_all_iff.mpr fun p ↦ (P₁ p).coeFn_compLpL G
  have hrrep : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume, ∀ p d,
      r p d (t, x) = wkpCoordinateCLM d (U t p) x := by
    filter_upwards [hrU, hU] with t ht hUt
    exact ht.mono fun x hx p d ↦ by simpa only [hUt p] using hx p d
  have hvrep : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume, ∀ p d,
      v p d (t, x) = wkpCoordinateCLM d (G t p) x := by
    filter_upwards [hvG, hG] with t ht hGt
    exact ht.mono fun x hx p d ↦ by simpa only [hGt p] using hx p d
  refine ⟨r, v, hr, hv, hrrep, hvrep, hrweak, hvweak, ?_⟩
  apply ae_all_iff.mpr
  intro p
  let R (y : ℝ × ℝ^n) :=
    v p (baseIndex n 1) y -
      ε * (∑ j, r p ((pairDerivIndex n j j).castOrder (by decide : 2 ≤ 3)) y) +
      ∑ j, ∑ q, B j y p q *
        r q ((singleDerivIndex n j).castOrder (by decide : 1 ≤ 3)) y
  have hR : AEStronglyMeasurable R (μ.prod volume) := by
    apply AEStronglyMeasurable.add
    · apply (hv p (baseIndex n 1)).1.aestronglyMeasurable.sub
      apply aestronglyMeasurable_const.mul
      exact Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦
        (hr p _).1.aestronglyMeasurable
    · exact Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦
        Finset.aestronglyMeasurable_fun_sum _ fun q _ ↦
          (hB j p q).mul (hr q _).1.aestronglyMeasurable
  apply ae_eq_prod_of_ae_eq_sections hR (hf p)
  filter_upwards [h.equation, hrrep, hvrep] with t ht hrt hvt
  filter_upwards [ht, hrt, hvt] with x hx hrx hvx
  dsimp only [R]
  simpa only [hrx, hvx, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply] using hx p

end PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution
