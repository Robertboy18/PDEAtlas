/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.InitialTrace

/-!
# Higher-regularity wave problem data

`WaveProblemData` bundles the time interval, initial displacement and
velocity, and verified forcing jet used in Evans's higher-regularity theorem
(Evans, §7.2.3, Theorem 6): `g ∈ H^{m+1}`, `h ∈ H^m`, and
`∂ₜᵏ f ∈ L²_t H^{m-k}_x` for `0 ≤ k ≤ m`.  We also construct its
canonical forcing traces and the data obtained by differentiating the problem
once in time, which is the inductive step of Evans's argument.

## Main definitions

* `WaveProblemData`: the data of an order-`m` problem.
* `WaveProblemData.forcingTraces`: canonical initial traces of the forcing jet.
* `WaveProblemData.timeDerivative`: the order-`m` problem for `u_t`, given the
  compatibility value `q₂` used as its initial velocity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6 and step 2 of its proof,
  equations (67)-(69).
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
The analytic data in Evans, §7.2.3, Theorem 6 for regularity order `m`.

The initial data satisfy `g ∈ H^{m+1}(Omega)` and `h ∈ H^m(Omega)`, while
the forcing jet records `∂ₜᵏ f ∈ L²_t H^{m-k}_x` for `0 ≤ k ≤ m`.
-/
structure WaveProblemData
    (n m : ℕ) (Omega : Set (ℝ^n)) (t0 t1 : ℝ) where
  /-- The time interval is nondegenerate. -/
  time_lt : t0 < t1
  /-- Initial displacement `g ∈ H^{m+1}(Omega)`. -/
  displacement : W^{(m + 1),2}(Omega)
  /-- Initial velocity `h ∈ H^m(Omega)`. -/
  velocity : W^{m,2}(Omega)
  /-- The forcing and all weak time derivatives through order `m`. -/
  forcing : SobolevTimeJet n m Omega t0 t1

namespace WaveProblemData

/--
Canonical endpoint traces of the forcing and all of its stored weak time
derivatives.
-/
noncomputable def forcingTraces
    (D : WaveProblemData n m Omega t0 t1) :
    InitialTraceData (F := D.forcing) :=
  InitialTraceData.ofJet D.forcing D.time_lt

/--
The wave problem obtained by differentiating once in time.

For an order-`m+1` problem, the new displacement is the old velocity, the new
velocity is the supplied value `q₂ ∈ H^m(Omega)`, and the new forcing is the
time derivative of the old forcing.
-/
def timeDerivative
    (D : WaveProblemData n (m + 1) Omega t0 t1)
    (q2 : W^{m,2}(Omega)) :
    WaveProblemData n m Omega t0 t1 where
  time_lt := D.time_lt
  displacement := D.velocity
  velocity := q2
  forcing := D.forcing.timeDerivative

/-- The differentiated problem starts from the original velocity. -/
@[simp]
theorem timeDerivative_displacement (D : WaveProblemData n (m + 1) Omega t0 t1)
    (q2 : W^{m,2}(Omega)) :
    (D.timeDerivative q2).displacement = D.velocity :=
  rfl

/-- The differentiated problem's initial velocity is the supplied compatibility value `q₂`. -/
@[simp]
theorem timeDerivative_velocity (D : WaveProblemData n (m + 1) Omega t0 t1) (q2 : W^{m,2}(Omega)) :
    (D.timeDerivative q2).velocity = q2 :=
  rfl

/-- The differentiated problem is forced by the time derivative of the original forcing jet. -/
@[simp]
theorem timeDerivative_forcing (D : WaveProblemData n (m + 1) Omega t0 t1) (q2 : W^{m,2}(Omega)) :
    (D.timeDerivative q2).forcing = D.forcing.timeDerivative :=
  rfl

end WaveProblemData

end Hyperbolic.HigherRegularity
