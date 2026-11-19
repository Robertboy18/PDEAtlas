/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.BallChain
public import PDE.Analysis.Geometry.BallChain.Segment

/-!
# Comparisons along time-ordered ball chains

The interior-ball graph `ballChainGraph` joins any two points of a connected open set.
Each of its finitely many edges receives a positive time interval, and the
segment subdivision theorem fits that interval exactly. Even a stationary
spatial path uses a positive elapsed time.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local parabolic comparison propagates between any two interior points
at strictly ordered times, with a constant chosen before the field. -/
theorem exists_forward_comparison_of_isPreconnected
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {ℓ T L ρ κ A s t : ℝ}
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hκ : 0 < κ) (hA : 0 < A)
    (x y : U) (hs : ℓ < s) (hst : s < t) (ht : t ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ → ℝ,
      (∀ (p q : E) (r a : ℝ), 0 < r → r ≤ ρ →
        closedBall p (L * r) ⊆ U → dist p q ≤ r → ℓ < a - 2 * r ^ 2 →
        a + κ * r ^ 2 ≤ T → u p a ≤ A * u q (a + κ * r ^ 2)) →
      u x.1 s ≤ C * u y.1 t := by
  obtain ⟨w⟩ := ballChainGraph_reachable hU hconn (by positivity : 0 ≤ L + 1) hρ x y
  have hwalk {p q : U} (w : (ballChainGraph U (L + 1) ρ).Walk p q) :
      ∀ a b : ℝ, ℓ < a → a < b → b ≤ T →
        ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ → ℝ,
          (∀ (p q : E) (r a : ℝ), 0 < r → r ≤ ρ →
            closedBall p (L * r) ⊆ U → dist p q ≤ r → ℓ < a - 2 * r ^ 2 →
            a + κ * r ^ 2 ≤ T → u p a ≤ A * u q (a + κ * r ^ 2)) →
          u p.1 a ≤ C * u q.1 b := by
    induction w with
    | @nil p =>
        intro a b ha hab hb
        obtain ⟨R, hR, hRρ, hball⟩ := exists_ballChain_radius hU hL hρ p
        obtain ⟨C, hC, hcompare⟩ :=
          exists_forward_comparison_on_segment (U := U) hL hκ hA hR hRρ ha hab hb
        exact ⟨C, hC, fun u hu ↦
          hcompare u hu p.1 p.1 (by simpa only [dist_self] using hR.le) hball⟩
    | @cons p q z hpq w ih =>
        intro a b ha hab hb
        have hlinked : BallChainLinked U (L + 1) ρ p q := by
          rcases ((SimpleGraph.fromRel_adj _ p q).mp hpq).2 with h | h
          · exact h
          · exact ballChainLinked_symm h
        obtain ⟨R, hR, hRρ, hpqR, hball, _⟩ := hlinked
        have ham : a < (a + b) / 2 := by linarith
        have hmb : (a + b) / 2 < b := by linarith
        obtain ⟨C, hC, hcompare⟩ := exists_forward_comparison_on_segment (U := U)
          hL hκ hA hR hRρ ha ham (hmb.le.trans hb)
        obtain ⟨D, hD, htail⟩ := ih _ _ (ha.trans ham) hmb hb
        refine ⟨C * D, mul_pos hC hD, ?_⟩
        intro u hu
        calc
          u p.1 a ≤ C * u q.1 ((a + b) / 2) := hcompare u hu _ _ hpqR hball
          _ ≤ C * (D * u z.1 b) := mul_le_mul_of_nonneg_left (htail u hu) hC.le
          _ = (C * D) * u z.1 b := (mul_assoc _ _ _).symm
  exact hwalk w s t hs hst ht

end PDE.Analysis
