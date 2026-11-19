/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS
public import PDE.Symbolic.Command.CAS.SphericalBessel

/-!
# Spherical Bessel functions and Legendre polynomials in the calculator

The calculator evaluates the spherical Bessel functions `j_l` of the library at rational points to
any number of digits, lists their zeros in an interval with a proof that the list is complete, and
expands the Legendre polynomials `P_n`. The commands at the end of this file run in the build, each
inside `#guard_msgs`, which checks its report.

The values are `0.127349283688408215647240947230`, `7.4447277416610768908 × 10^-190` (the
series is evaluated in the regime where the Rayleigh form cancels) and
`-0.05440211108893698134047476`. The zeros of `j_1` in `(0, 20]` are

`4.49340945790906417530, 7.72525183693770716419, 10.90412165942889982714,`
`14.06619391283147347997, 17.22075527193076873957`,

from a cover of 324 cells checked by the kernel, and the theorem states that each of the five
decimal intervals of width `10 ^ (-20)` contains exactly one zero and that there are no other
zeros in `(0, 20]`. The two zeros of `j_2` in `(0, 10]` are `5.7634591968` and `9.0950113304`.
The Legendre polynomials print as `63/8*x^5 - 35/4*x^3 + 15/8*x` and
`46189/256*x^10 - 109395/256*x^8 + 45045/128*x^6 - 15015/128*x^4 + 3465/256*x^2 - 63/256`, each
with the identity `∀ x, (legendre n).eval x = …`, and `P_5 (1 / 3) = 1 / 3` exactly.

The compiled theorems below state the same facts directly. The closed checks are proved by
`cega` in the kernel.
-/

public section

namespace PDE.Examples.SymbolicSpecialFunctions

open CAS.Analysis.SpecialFunctions
open CAS.Continuum PDE.Analysis.SpecialFunctions

/-- Thirty digits of `j_2 (3 / 2)` from the series on a binary grid. -/
theorem sphericalBesselJ_two_three_halves :
    (127349283688408215647240947230 / 10 ^ 30 : ℝ) ≤ sphericalBesselJ 2 (3 / 2) ∧
      sphericalBesselJ 2 (3 / 2) < (127349283688408215647240947230 + 1) / 10 ^ 30 := by
  have h := RationalInterval.of_decimalLowerCheck
    (sphericalBesselGridInterval_sound 169 2 63 (3 / 2))
    (m := 127349283688408215647240947230) (k := 30) (by cega)
  simpa using h

/-- The first positive zero of `j_1` is the only zero in `(4.4934, 4.4935)`. -/
theorem existsUnique_sphericalBesselJ_one_zero :
    ∃! z, z ∈ Set.Ioo (44934 / 10000 : ℝ) (44935 / 10000) ∧ sphericalBesselJ 1 z = 0 := by
  have h := existsUnique_sphericalBesselJ_eq_zero_of_rootCellCheck (l := 1)
    (a := 44934 / 10000) (b := 44935 / 10000) (by cega)
  simpa using h

/-- `P_5 (x) = (63 x ^ 5 - 70 x ^ 3 + 15 x) / 8`. -/
theorem legendre_five (x : ℝ) :
    (legendre 5).eval x = 63 / 8 * x ^ 5 - 35 / 4 * x ^ 3 + 15 / 8 * x := by
  rw [legendre_eval_eq_sum_coeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show legendreMonomialCoeff 5 0 = 0 by cega,
    show legendreMonomialCoeff 5 1 = 15 / 8 by cega,
    show legendreMonomialCoeff 5 2 = 0 by cega,
    show legendreMonomialCoeff 5 3 = -35 / 4 by cega,
    show legendreMonomialCoeff 5 4 = 0 by cega,
    show legendreMonomialCoeff 5 5 = 63 / 8 by cega]
  push_cast
  ring

end PDE.Examples.SymbolicSpecialFunctions

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [N 30]
Domain: spherical Bessel function at a rational point
Input (scalar ℝ): (SphericalBesselJ 2 (3 / 2))
Output (first 30 significant digits, truncated): 0.127349283688408215647240947230

[CAS.Command.details] More details
  [CAS.Command.computation] Certified series evaluation
    Series of j_2 with 65 terms on the grid 2^-169
    Guarantee: every printed digit is a digit of the real value, truncated toward zero
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Certified decimal digits
        Proposition: 127349283688408215647240947230 / 10 ^ 30 ≤
            PDE.Analysis.SpecialFunctions.sphericalBesselJ 2 (3 / 2) ∧
          PDE.Analysis.SpecialFunctions.sphericalBesselJ 2 (3 / 2) < (127349283688408215647240947230
+ 1) / 10 ^ 30
        Validation: proof term checked by the kernel against this proposition
        Theorem: PDE.Analysis.SpecialFunctions.sphericalBesselGridInterval_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 30] (SphericalBesselJ 2 (3 / 2))

/--
info: #cas [N 20]
Domain: spherical Bessel function at a rational point
Input (scalar ℝ): (SphericalBesselJ 100 1)
Output (first 20 significant digits, truncated): 7.4447277416610768908 × 10^-190

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 20] (SphericalBesselJ 100 1)

/--
info: #cas [N 25]
Domain: spherical Bessel function at a rational point
Input (scalar ℝ): (SphericalBesselJ 0 10)
Output (first 25 significant digits, truncated): -0.05440211108893698134047476

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 25] (SphericalBesselJ 0 10)

/--
info: #cas [zeros x in [0, 20]]
Domain: x ∈ (0, 20]
Input (scalar ℝ): (SphericalBesselJ 1 x)
Output (all 5 zeros, 20 decimals each, truncated): 4.49340945790906417530, 7.72525183693770716419,
10.90412165942889982714, 14.06619391283147347997, 17.22075527193076873957

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [zeros x in [0, 20]] (SphericalBesselJ 1 x)

/--
info: #cas (digits := 10) [zeros x in [0, 10]]
Domain: x ∈ (0, 10]
Input (scalar ℝ): (SphericalBesselJ 2 x)
Output (all 2 zeros, 10 decimals each, truncated): 5.7634591968, 9.0950113304

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 10) [zeros x in [0, 10]] (SphericalBesselJ 2 x)

/--
info: #cas (LegendreP 5 x)
Domain: x ∈ ℝ
Input (polynomial in x): LegendreP 5 x
Output (polynomial with exact rational coefficients): 63/8*x^5 - 35/4*x^3 + 15/8*x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (LegendreP 5 x)

/--
info: #cas (LegendreP 10 x)
Domain: x ∈ ℝ
Input (polynomial in x): LegendreP 10 x
Output (polynomial with exact rational coefficients): 46189/256*x^10 - 109395/256*x^8 +
45045/128*x^6 - 15015/128*x^4 + 3465/256*x^2 - 63/256

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (LegendreP 10 x)

set_option linter.style.longLine false in
/--
info: #cas [N 20]
Domain: Legendre polynomial at a rational point
Input (scalar ℝ): (LegendreP 5 (1 / 3))
Output (exact rational value and its first 20 significant digits, truncated): 1/3 ≈ 0.33333333333333333333

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 20] (LegendreP 5 (1 / 3))

