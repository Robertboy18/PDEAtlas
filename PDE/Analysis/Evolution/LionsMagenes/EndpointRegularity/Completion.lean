/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Cutoff

/-!
# Closed-interval completion of a Gelfand evolution

The cutoff-reflected global evolution restricts to a representative continuous
on `[a,b]`. This is the endpoint-inclusive Lions–Magenes theorem used by the
finite-interval evolution theory. Evans reaches the endpoints by extending `u` to a larger
interval before mollifying (§5.9.2, proof of Theorem 3); here the extension is the
reflection of `PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.ReflectedExtension`,
cut off away from `[a,b]`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*,
  Vol. I, Springer, 1972, Chapter 1 (Hilbert theory of trace and interpolation spaces).
  <https://doi.org/10.1007/978-3-642-65161-8>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section Completion

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Endpoint completion of the finite-interval Lions–Magenes theorem.
An open-interval evolution whose state and derivative are in the natural
Bochner `L²` spaces has one pivot-space representative continuous on the
entire closed interval, including both endpoint traces.  Its integrated
dual derivative and exact energy identity also hold with endpoint times.

This is Evans §5.9.2, Theorem 3, in the abstract Gelfand-triple formulation. -/
theorem ContinuousPivotEvolutionOnOpen.toContinuousPivotEvolutionOn
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (hab : a < b) (hu : MemLp u 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    Nonempty (ContinuousPivotEvolutionOn T u g a b) := by
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨χ, hχ, hχcompact, hχsupp, hχone, ⟨Eχ⟩⟩ :=
    E.exists_reflectedCutoffEvolution T hab hu hg ht₀
  let uR : ℝ → V := reflectedIntervalExtension a b u
  let gR : ℝ → StrongDual ℝ V := reflectedDerivativeExtension a b g
  let uχ : ℝ → V := fun t ↦ χ t • uR t
  let gχ : ℝ → StrongDual ℝ V := fun t ↦ χ t • gR t + deriv χ t • T.energyToDual (uR t)
  change ContinuousPivotEvolution T uχ gχ at Eχ
  -- on `(a, b]` the cutoff is `1` near every point, so the cut-off evolution is the original one
  have huχEq : ∀ t ∈ Ioc a b, uχ t = u t := fun t ht ↦ by
    simp [uχ, uR, reflectedIntervalExtension, not_lt_of_ge ht.1.le, not_lt_of_ge ht.2,
      intervalZeroExtension, indicator_of_mem ht, (hχone t (Ioc_subset_Icc_self ht)).eq_of_nhds]
  have hgχEq : ∀ t ∈ Ioc a b, gχ t = g t := fun t ht ↦ by
    simp [gχ, gR, uR, reflectedDerivativeExtension, not_lt_of_ge ht.1.le, not_lt_of_ge ht.2,
      intervalZeroExtension, indicator_of_mem ht, (hχone t (Ioc_subset_Icc_self ht)).eq_of_nhds,
      (hχone t (Ioc_subset_Icc_self ht)).deriv_eq]
  have hsub {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) : uIoc s t ⊆ Ioc a b :=
    (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hs ht)).trans
      (uIoc_of_le hab.le).subset
  have hae : Eχ.representative =ᵐ[volume.restrict (uIcc a b)] fun t ↦ T.inclusion (u t) := by
    refine Eχ.ae_eq_inclusion.restrict.trans ?_
    filter_upwards [ae_restrict_mem measurableSet_uIcc,
      (Measure.ae_ne volume a).filter_mono ae_restrict_le] with t ht hta
    rw [uIcc_of_le hab.le] at ht
    exact congrArg T.inclusion (huχEq t ⟨ht.1.lt_of_ne' hta, ht.2⟩)
  have hcut := Eχ.integratedDerivative a b
  refine ⟨{
    representative := Eχ.representative
    continuousOn := Eχ.continuous.continuousOn
    ae_eq_inclusion := hae
    integratedDerivative := ⟨hcut.intervalIntegrable.congr fun t ht ↦
        hgχEq t (by simpa only [uIoc_of_le hab.le] using ht), fun t ht ↦ ?_⟩
    energyIdentity := fun s t hs ht ↦ ?_ }⟩
  · have hprimitive : dualPrimitive gχ a t = dualPrimitive g a t :=
      intervalIntegral.integral_congr_ae (.of_forall fun r hr ↦ hgχEq r (hsub left_mem_uIcc ht hr))
    exact hprimitive ▸ hcut.eq_add_integral t ht
  · have hpairing : (∫ r in s..t, gχ r (uχ r)) = ∫ r in s..t, g r (u r) :=
      intervalIntegral.integral_congr_ae (.of_forall fun r hr ↦ by
        simp only [hgχEq r (hsub hs ht hr), huχEq r (hsub hs ht hr)])
    exact hpairing ▸ Eχ.energyIdentity s t

end Completion

end PDE.Analysis.Evolution
