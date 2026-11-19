/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Compatibility.Values
public import PDE.Hyperbolic.HigherRegularity.Data.WaveProblem

/-!
# Compatibility conditions for higher-order wave regularity

`WaveProblemData.IsCompatible` asserts the existence of typed Sobolev values
realizing Evans's compatibility recurrence. The transfer theorem proves that
compatibility descends by one order when the wave equation is differentiated
in time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, compatibility conditions (62), and step 2
  of its proof, equations (67)-(69).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
Concrete `m`-th order compatibility for an Evans wave problem.

The endpoint traces are generated from the verified forcing jet. Each
Sobolev-scale application in the recurrence is certified against the same
weak operator `A`.
-/
def WaveProblemData.IsCompatible
    (D : WaveProblemData n m Omega t0 t1)
    (A :
      H¹₀(Omega) →L[ℝ]
        StrongDual ℝ (H¹₀(Omega)))
    (spatialOperator :
      ∀ r : ℕ,
        W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega)) : Prop :=
  ∃ Q : WaveCompatibilityValues n Omega m,
    Q.Realizes A spatialOperator D.forcingTraces
      D.displacement D.velocity

namespace WaveProblemData.IsCompatible

/--
Evans's compatibility hypotheses descend by one order after
time-differentiating the wave equation.

The supplied `q₂ ∈ H^m(Omega)` realizes `f(t0) - L_m g`; all remaining
Sobolev orders, zero-trace conditions, and operator-identification
certificates are inherited from the tail of the original family.
-/
theorem timeDerivative {D : WaveProblemData n (m + 1) Omega t0 t1}
    {A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega))}
    {spatialOperator : ∀ r : ℕ, W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega)}
    (hD : D.IsCompatible A spatialOperator) (q2 : W^{m,2}(Omega))
    (hq2 : q2 = D.forcingTraces.head - spatialOperator m D.displacement) :
    (D.timeDerivative q2).IsCompatible A spatialOperator := by
  obtain ⟨Q, hQ⟩ := hD
  refine ⟨Q.tail, ?_⟩
  have htail := hQ.timeDerivative
  have hcanonical : (D.timeDerivative q2).forcingTraces =
        D.forcingTraces.timeDerivative := by
    unfold WaveProblemData.forcingTraces
    simpa only [WaveProblemData.timeDerivative_forcing] using
      (InitialTraceData.ofJet_timeDerivative D.forcing D.time_lt).symm
  rw [hcanonical]
  simpa only [WaveProblemData.timeDerivative_forcing, WaveProblemData.timeDerivative_displacement,
    WaveProblemData.timeDerivative_velocity, hq2] using htail

end WaveProblemData.IsCompatible

end Hyperbolic.HigherRegularity
