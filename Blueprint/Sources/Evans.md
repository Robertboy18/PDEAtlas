# Partial Differential Equations

Lawrence C. Evans, *Partial Differential Equations*, second edition.

Graduate Studies in Mathematics, volume 19, American Mathematical Society, 2010.
ISBN 978-0-8218-4974-3. [Publisher record](https://www.ams.org/bookpages/gsm-19-r).

Every Evans citation in the Blueprint refers to this edition.
We contacted Evans about following his book, and he was excited about the project.

## Section locators

Section and page numbers refer to the 2010 second edition, with the page of
its contents (printed pages vii–xv) in parentheses. A section citation locates
the mathematical background; the Lean statement on the card specifies the
proved hypotheses and conclusion.

The solution cards `hyperbolic.wave.kirchhoff_poisson_solution`,
`hyperbolic.wave.odd_dimensional_solution`, and
`hyperbolic.wave.even_dimensional_solution` use §2.4.1, starting at page 67
(contents, p. viii).

The cards `foundations.cauchy.convergent_formal_solution`,
`foundations.cauchy.analytic_zero_data`, `methods.power_series.analytic_evolution`,
`methods.power_series.analytic_uniqueness`, and `methods.power_series.analytic_hypersurface`
use §4.6.3, starting at page 239. The cards `foundations.cauchy.noncharacteristic_jets`
and `methods.power_series.analytic_hypersurface` use §4.6.1, starting at page 232, for
noncharacteristic data (contents, p. ix).

The cards `fluid.solenoidal_weak_closure`,
`parabolic.bochner_linear_constraints`, `parabolic.weak_quadratic_energy_limit`,
and `parabolic.weak_strong_duality_limit` use Appendix D.4, starting at page 723
(contents, p. xv), for weak convergence.

The cards `parabolic.galerkin.gram_operator`, `parabolic.galerkin.gram_properties`,
`parabolic.galerkin.spectral_density`, and `parabolic.galerkin.h10_l2_trial_system`
use Appendix D.6, starting at page 728, and §7.1.2, starting at page 375
(contents, pp. xv and xi), for symmetric operators and
parabolic existence.

## Section starts by topic

| Blueprint material | Section starts (2010) |
| --- | --- |
| Harmonic energy | §2.2.5: 41 (viii) |
| Characteristics; Hamilton–Jacobi formulas | §3.2: 96; §3.3.2: 120 (viii) |
| Analytic models | §4.6.1: 232; §4.6.2: 237; §4.6.3: 239 (ix) |
| Hölder and weak-derivative foundations | §5.1: 254; §5.2.1: 255 (ix, x) |
| Approximation, extension, traces | §5.3: 264; §5.4: 268; §5.5: 271 (x) |
| Sobolev inequalities, compactness, Poincaré | §5.6.1: 276; §5.6.2: 280; §5.7: 286; §5.8.1: 289 (x) |
| Dual spaces and time-dependent spaces | §5.9.1: 299; §5.9.2: 301 (x) |
| Weak elliptic existence | §6.1.2: 313; §6.2.1: 315; §6.2.2: 317; §6.2.3: 320 (x) |
| Elliptic regularity | §6.3.1: 327; §6.3.2: 334 (xi) |
| Weak parabolic existence, regularity, maximum principles | §7.1.1: 372; §7.1.2: 375; §7.1.3: 380; §7.1.4: 389 (xi) |
| Weak waves and higher regularity | §7.2.1: 398; §7.2.2: 401; §7.2.3: 408 (xi) |
| Canonical form; symmetric systems; semigroups | §7.2.5: 418; §7.3.2: 423; §7.4.1: 434 (xi) |
| Variations and direct methods | §8.1.2: 454; §8.1.3: 458; §8.2: 465; §8.2.3: 472 (xii) |
| Fixed-point arguments; blowup | §9.2.1: 534; §9.3: 543; §9.4.1: 547 (xii, xiii) |
| Viscosity solutions; systems of conservation laws | Chapter 10: 579; §11.1.1: 612; §11.4.2: 646 (xiii, xiv) |
| Nonlinear wave energy and propagation | Chapter 12: 659; §§12.1.1–12.1.2: 660 (xiv) |
| Boundary calculus; weak compactness; Fredholm background | Appendix C.2: 711; D.4: 723; D.5: 724; D.6: 728 (xv) |

## Other sources for the Harnack inequalities

The elliptic and parabolic Harnack sections also follow Cyril Imbert and Luis
Silvestre, *Introduction to fully nonlinear parabolic equations*,
[HAL version 1](https://hal.science/hal-00798300v1), 8 March 2013.
Its §4.1 develops the monotone envelope and contact Jacobian, and
§§4.2.2–4.2.3 give the barrier and basic measure estimate. The Lean argument
uses classical contact maps, then measure and peak propagation, with drift and
a signed potential.

## Potential functions (§4.4.2)

The cards `fluid.euler.potential_flow` and `fluid.euler.potential_solution`
cite §4.4.2, *Potential functions*. That passage assumes a velocity potential
and a force potential, reduces incompressibility to spatial harmonicity, and
recovers the pressure from the time derivative of the potential and the
kinetic energy. LeanPDE proves this reduction in every spatial dimension and
builds a global smooth solution from a given smooth harmonic potential. The passage
is on printed page 208 of the second edition, with the harmonicity condition (15)
and the pressure identity (16).

## Chapter 12: nonlinear wave equations

For §12.1.1, Theorem 1, the card `hyperbolic.semiwave.compact_slice_energy`
proves conservation of energy in every positive dimension for a normalized
C² potential, hence a C¹ reaction, and a C² wave on the closed forward
half-space. The displacement is assumed to have compact support at each time
separately; the equation then supplies a common support on each finite time
slab. The initial energy uses the right time derivative at t = 0.

A normalized C¹ potential, hence a continuous reaction, gives conservation for
a C³ wave in one dimension and for a C⁴ wave in two dimensions
(`hyperbolic.semiwave.continuous_reaction_energy_low_dimensions`), and for a C²
wave in every positive dimension when the potential satisfies V(z) ≥ −Cz² near
zero (`hyperbolic.semiwave.quadratic_lower_energy`). These results also assume
compact displacement support at each nonnegative time separately.

For §12.3.2, Theorem 2, the card `hyperbolic.semiwave.maximal_smooth_wave`
constructs a maximal smooth wave for smooth compactly supported Cauchy data in
three dimensions and any smooth scalar reaction with f(0) = 0. If the lifespan
T* is finite, the displacement is unbounded on every terminal strip
[a, T*) × ℝ³.

## Further page references

The minimal-surface Legendre calculation is in §4.4.3(b), equations (24)–(30),
printed page 210, in this second edition.

The energy and admissible class of Dirichlet's principle (§2.2.5(b),
Theorem 17) are on printed pages 42–43. The terminal-control value
statement (§10.3.3, Theorem 2) is on printed page 596, and the
three-dimensional smooth-wave theorem (§12.3.2, Theorem 2) on printed page 674.

The Fourier convention and the Plancherel theorem are in
§4.3.1(a), equations (1)–(2) and Theorem 1, printed page 187. Periodic elliptic
homogenization is Example 5 of §4.5.4, printed pages 229–232; the corrector problem
(69) appears on page 231 and the homogenized coefficients (74) on page 232.

For the half-space Poisson formula, Theorem 14 of §2.2.4(b) is on printed
page 37; the mass-one identity (34) and boundedness argument are on page 38.
Finite propagation is Theorem 8 of §7.2.4, printed pages 416–417. LeanPDE's
incoming-wave example records why compact optical sublevels matter on an
unbounded domain. The fixed-slab viscous energy estimate follows §7.3.2(c),
Theorem 2, equation (17), printed page 426, with its proof on pages 426–427.
The forcing norm includes its time derivative.
