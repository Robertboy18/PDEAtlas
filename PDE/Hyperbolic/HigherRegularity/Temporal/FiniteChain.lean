/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Temporal.IntegrateAutonomous

/-!
# Constructing a finite chain of differentiated weak waves

A solution of the highest differentiated equation determines the lower waves by
integration. Compatibility fixes each integration constant in the spatial equation.
The construction retains the two initial identities, the equations and the
weak time derivatives. It requires neither common trial spaces nor simultaneous
approximations of the initial data.

Indices run in reverse derivative order: zero is the highest differentiated wave
and `Fin.last m` is the original wave.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
  {B : V →L[ℝ] StrongDual ℝ V}

/-- Integrate downward from one highest weak wave. Every lower wave has the
prescribed compatible initial data; the top wave is preserved exactly. -/
theorem exists_finite_weakWaveChain {m : ℕ}
    (ell : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (ell₀ : Fin m → StrongDual ℝ V) (q : Fin (m + 1) → V) (p : Fin (m + 1) → H)
    (hforcing : ∀ r : Fin m, ∀ᵐ t ∂volume.restrict (Ioc a b),
      ell r.succ t = ell₀ r + ∫ s in a..t, ell r.castSucc s)
    (hposition : ∀ r : Fin m, p r.succ = T.inclusion (q r.castSucc))
    (hcompat : ∀ r : Fin m, T.pivotToDual (p r.castSucc) + B (q r.succ) = ell₀ r)
    (u₀ : Lp V 2 (volume.restrict (Ioc a b))) (v₀ : Lp H 2 (volume.restrict (Ioc a b)))
    (w₀ : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (htop : IsGelfandWeakWaveSolution T (fun _ ↦ B) (ell 0) u₀ v₀ w₀ (q 0) (p 0)) :
    ∃ (u : Fin (m + 1) → Lp V 2 (volume.restrict (Ioc a b)))
      (v : Fin (m + 1) → Lp H 2 (volume.restrict (Ioc a b)))
      (w : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      u 0 = u₀ ∧ v 0 = v₀ ∧ w 0 = w₀ ∧
      (∀ r, IsGelfandWeakWaveSolution T (fun _ ↦ B) (ell r) (u r) (v r) (w r) (q r) (p r)) ∧
      (∀ r : Fin m, v r.succ = T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) (u r.castSucc)) ∧
      (∀ r : Fin m, w r.succ = T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) (v r.castSucc)) ∧
      (∀ r : Fin m, HasWeakTimeDerivativeOn (Ioo a b) (u r.succ) (u r.castSucc)) ∧
      ∀ r : Fin m, ∀ᵐ t ∂volume.restrict (Ioc a b),
        u r.succ t = q r.succ + ∫ s in a..t, u r.castSucc s := by
  induction m with
  | zero =>
      refine ⟨fun _ ↦ u₀, fun _ ↦ v₀, fun _ ↦ w₀, rfl, rfl, rfl, fun r ↦ ?_,
        Fin.elim0, Fin.elim0, Fin.elim0, fun r ↦ Fin.elim0 r⟩
      obtain rfl : r = 0 := Fin.ext (by omega)
      exact htop
  | succ m ih =>
      obtain ⟨u, v, w, hu₀, hv₀, hw₀, hwave, hvelocity, hacceleration, hderivative, hprimitive⟩ :=
        ih (ell := fun r ↦ ell r.castSucc) (ell₀ := fun r ↦ ell₀ r.castSucc)
          (q := fun r ↦ q r.castSucc) (p := fun r ↦ p r.castSucc)
          (hforcing := fun r ↦ by simpa only [Fin.succ_castSucc] using hforcing r.castSucc)
          (hposition := fun r ↦ by simpa only [Fin.succ_castSucc] using hposition r.castSucc)
          (hcompat := fun r ↦ by simpa only [Fin.succ_castSucc] using hcompat r.castSucc)
          (htop := by simpa using htop)
      obtain ⟨U, hU, hUderivative, hUprimitive⟩ :=
        (hwave (Fin.last m)).exists_integral_weakWave_with_primitive
          (hforcing (Fin.last m)) (hcompat (Fin.last m))
      have hUwave : IsGelfandWeakWaveSolution T (fun _ ↦ B) (ell (Fin.last (m + 1))) U
          (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) (u (Fin.last m)))
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) (v (Fin.last m)))
          (q (Fin.last (m + 1))) (p (Fin.last (m + 1))) := by
        rw [← Fin.succ_last, hposition (Fin.last m)]
        exact hU
      refine ⟨Fin.lastCases U u,
        Fin.lastCases (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) (u (Fin.last m))) v,
        Fin.lastCases (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) (v (Fin.last m))) w,
        (Fin.lastCases_castSucc (motive := fun _ ↦ _) (0 : Fin (m + 1))).trans hu₀,
        (Fin.lastCases_castSucc (motive := fun _ ↦ _) (0 : Fin (m + 1))).trans hv₀,
        (Fin.lastCases_castSucc (motive := fun _ ↦ _) (0 : Fin (m + 1))).trans hw₀,
        fun r ↦ Fin.lastCases ?_ (fun s ↦ ?_) r,
        fun r ↦ Fin.lastCases ?_ (fun s ↦ ?_) r, fun r ↦ Fin.lastCases ?_ (fun s ↦ ?_) r,
        fun r ↦ Fin.lastCases ?_ (fun s ↦ ?_) r, fun r ↦ Fin.lastCases ?_ (fun s ↦ ?_) r⟩
      · simpa only [Fin.lastCases_last] using hUwave
      · simpa only [Fin.lastCases_castSucc] using hwave s
      · simp only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc]
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hvelocity s
      · simp only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc]
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hacceleration s
      · simpa only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc] using hUderivative
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hderivative s
      · simpa only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc] using hUprimitive
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hprimitive s

end Hyperbolic.Variational
