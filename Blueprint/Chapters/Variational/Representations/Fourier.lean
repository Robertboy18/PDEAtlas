/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.Representations.ColeHopf
import PDE.Analysis.Fourier.HilbertTransform
import PDE.Analysis.Fourier.HilbertTransform.RealPair.Poisson
import PDE.Analysis.Fourier.LaplacianEnergy
import PDE.Analysis.Fourier.SchwartzDifferentialOperators
import PDE.Elliptic.Classical.OneDimensional.FourierResolvent
import PDE.Hyperbolic.Models.Wave.Fourier.Cauchy
import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Cauchy
import PDE.Hyperbolic.Transport.Laplace
import PDE.Parabolic.Heat.Fourier.Cauchy

/-!
# Fourier and Laplace representations

Derivative symbols, constant-coefficient multipliers, the Hilbert transform,
the Fourier energy of the Laplacian, and the shifted elliptic resolvent.
Inverse transforms construct heat and wave solutions; vertical
Laplace inversion reconstructs boundary-driven transport.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Fourier and Laplace Representations" =>

# Fourier transform and elliptic resolvents

Every statement in this section depends on one normalization. Mathlib's
transform is $`\widehat f(\xi)=\int_{\mathbb R}e^{-2\pi ix\xi}f(x)\,dx`,
under which differentiation becomes multiplication by $`2\pi i\xi` with no
further constant; a transform without the $`2\pi` in the exponent would
give the multiplier $`i\xi` instead, and the opposite sign in the exponent
would flip the sign of the multiplier.

:::definition "methods.fourier.derivative_symbol" (parent := "methods.representations") (lean := "PDE.Analysis.Fourier.fourierDerivativeSymbol1D")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under Mathlib's Fourier convention, the one-dimensional derivative symbol is
$`2\pi i\xi`.
:::

The derivative symbol is unbounded, so the derivative is only a partial
operator on $`L^2`. The Hilbert transform is the opposite kind of
multiplier: its symbol $`-i\operatorname{sign}(\xi)` has modulus one away
from $`\xi=0`, so the operator it defines is bounded on all of
$`L^2(\mathbb R;\mathbb C)`, and it is realized through the unitary $`L^2`
transform rather than on Schwartz functions.

:::definition "methods.fourier.hilbert_transform" (parent := "methods.representations") (lean := "PDE.Analysis.hilbertSymbol, PDE.Analysis.hilbertTransform")
On complex $`L^2(\mathbb R)`, the Hilbert transform is the Fourier multiplier

$$`
\widehat{Hf}(\xi)=-i\,\operatorname{sign}(\xi)\widehat f(\xi),
`

with the symbol assigned the harmless value zero at $`\xi=0`. The operator
is this multiplier conjugated by Mathlib's unitary $`L^2` Fourier transform.
:::

Because the symbol takes only the values $`\pm i` off a null set, the
algebra of $`H` is the algebra of that symbol: modulus one gives the
isometry, $`(-i\operatorname{sign}\xi)^2=-1` gives $`H^2=-I`, and the two
together give skew-adjointness. Conjugation by a unitary transports each
identity from multipliers to operators without loss.

:::theorem "methods.fourier.hilbert_transform_structure" (parent := "methods.representations") (lean := "PDE.Analysis.hilbertTransform_sq, PDE.Analysis.norm_hilbertTransform, PDE.Analysis.inner_hilbertTransform_left") (uses := "methods.fourier.hilbert_transform")
For every $`f,g\in L^2(\mathbb R;\mathbb C)`, the transform is an isometry,
squares to minus the identity, and is skew-adjoint:

$$`
\|Hf\|_2=\|f\|_2,\qquad H(Hf)=-f,\qquad
\langle Hf,g\rangle=-\langle f,Hg\rangle.
`
:::

:::proof "methods.fourier.hilbert_transform_structure"
Away from the null singleton $`\{0\}`, the multiplier has norm one and its
square is $`-1`. Transfer those pointwise identities to $`L^2`, conjugate by
the unitary Fourier transform, and combine preservation of the inner product
with $`H^2=-I` to obtain skew-adjointness.
:::

Two Fourier multipliers commute wherever both are defined, since
multiplication of functions is commutative. The content of the commutation
theorem is therefore about domains: the derivative multiplier $`2\pi i\xi`
is unbounded, and one must check that multiplying $`\widehat f` by a
unimodular symbol does not leave the set on which
$`(2\pi i\xi)\widehat f\in L^2`.

:::theorem "methods.fourier.hilbert_derivative_commutes" (parent := "methods.representations") (lean := "PDE.Analysis.fourierDerivative_hilbertTransform") (uses := "methods.fourier.derivative_symbol, methods.fourier.hilbert_transform")
Let $`D` be the partial linear operator on complex $`L^2(\mathbb R)` whose
natural Fourier domain consists of functions satisfying

$$`
(2\pi i\xi)\widehat f(\xi)\in L^2(\mathbb R).
`

The Hilbert transform preserves this domain, and every $`f` in it satisfies
$`D(Hf)=H(Df)`.
:::

:::proof "methods.fourier.hilbert_derivative_commutes"
Both operators are scalar Fourier multipliers on the common domain. Their
symbols $`2\pi i\xi` and $`-i\operatorname{sign}(\xi)` commute pointwise, and
the Hilbert symbol, of norm at most one, preserves square integrability of the derivative
multiplier.
:::

Explicit Hilbert pairs come from the Poisson kernel. For $`\varepsilon>0`
the function $`i/(x+i\varepsilon)` is the boundary value of
$`i/(z+i\varepsilon)`, which is holomorphic in the upper half plane, and its
real and imaginary parts are the Poisson kernel and its conjugate.

:::theorem "methods.fourier.hilbert_poisson_pair" (parent := "methods.representations") (lean := "PDE.Analysis.IsHilbertPair, PDE.Analysis.isHilbertPair_poisson, PDE.Analysis.fourierInv_exp_neg_abs, PDE.Analysis.IsHilbertPair.rotate") (uses := "methods.fourier.hilbert_transform, methods.fourier.hilbert_transform_structure")
Real functions $`\omega,v` on $`\mathbb R` form a Hilbert pair when
$`\omega` agrees almost everywhere with some $`f\in L^2(\mathbb R;\mathbb C)`
and $`v` with $`Hf`. For every $`\varepsilon>0`,

$$`
H\Big[\frac{\varepsilon}{\varepsilon^2+x^2}\Big]=\frac{x}{\varepsilon^2+x^2}.
`

The Poisson kernel is the inverse Fourier transform of the Abel weight,
$`\mathcal F^{-1}\big[e^{-2\pi\varepsilon|\xi|}\big](x)=\varepsilon/(\pi(\varepsilon^2+x^2))`.
Since $`H^2=-I`, a Hilbert pair $`(\omega,v)` gives the pair $`(v,-\omega)`.
:::

:::proof "methods.fourier.hilbert_poisson_pair"
Both kernels are inverse Fourier transforms of integrable functions in
$`L^2`. The Poisson kernel $`\varepsilon/(\pi(\varepsilon^2+x^2))` is that of
$`e^{-2\pi\varepsilon|\xi|}`: split at $`\xi=0`, the integral is a sum of two
decaying exponentials. The conjugate kernel $`x/(\pi(\varepsilon^2+x^2))` is
that of the damped symbol $`-i\operatorname{sign}(\xi)e^{-2\pi\varepsilon|\xi|}`.
These integrals agree almost everywhere with the $`L^2` inverse transform, and
on the Fourier side $`H` multiplies by $`-i\operatorname{sign}(\xi)`, so the
two kernels form a Hilbert pair. Multiplying both by $`\pi` removes the
normalization. The rotation is $`H(Hf)=-f`.
:::

On the Schwartz class the domain question disappears, because $`\partial_x`
maps $`\mathcal S(\mathbb R)` to itself. Iterating the one-derivative rule
$`\widehat{\partial_xf}=(2\pi i\xi)\widehat f` gives the $`n`th power of the
same symbol, and the case $`n=0` is included so that the result applies
uniformly to every term of a polynomial in $`\partial_x`.

:::theorem "methods.fourier.iterated_derivative" (parent := "methods.representations") (lean := "Real.fourier_iteratedDeriv") (uses := "methods.fourier.derivative_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let `n` be a nonnegative integer and let `f` map the line into a complex normed space.
Assume it is `n` times continuously differentiable, with `f` and those derivatives integrable.
Then the transform turns the derivative of that order into multiplication by $`(2\pi i\xi)^n`.
:::

:::proof "methods.fourier.iterated_derivative" (uses := "methods.fourier.derivative_symbol")
Induct on `n`, applying Mathlib's Fourier rule for one Fréchet derivative at the
successor step and combining the two multipliers; then restrict to the line.
:::

Linearity of the transform combines the powers into a polynomial: the
operator $`\sum_na_n\partial_x^n` with complex coefficients becomes
multiplication by $`\sum_na_n(2\pi i\xi)^n`.

:::theorem "methods.fourier.constant_coefficient_operator" (parent := "methods.representations") (lean := "PDE.Analysis.Fourier.fourier_constant_coeff_operator_multiplier") (uses := "methods.fourier.iterated_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
An arbitrary finite one-dimensional constant-coefficient differential
operator on Schwartz functions is diagonalized by the Fourier transform: the
same finite coefficient polynomial is evaluated at the symbol $`2\pi i\xi`.
:::

:::proof "methods.fourier.constant_coefficient_operator" (uses := "methods.fourier.iterated_derivative")
Use linearity of the Fourier transform to distribute over the finite sum,
apply the iterated-derivative multiplier theorem term by term, and factor out
the common transformed function.
:::

The Laplacian on $`\mathbb R^n` is the constant-coefficient operator
$`\sum_j\partial_{x_j}^2`, whose symbol is
$`\sum_j(2\pi i\xi_j)^2=-(2\pi)^2\|\xi\|^2`. Combining that multiplier with
Plancherel, which holds in the same normalization without extra constants,
turns the $`L^2` norm of $`\Delta f` into a weighted $`L^2` norm of
$`\widehat f`; squaring the symbol is what produces the fourth powers.

:::theorem "methods.fourier.laplacian_energy" (parent := "methods.representations") (lean := "PDE.Analysis.Fourier.integral_norm_sq_laplacian_eq_fourier") (uses := "methods.fourier.constant_coefficient_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a Schwartz map $`f:\mathbb R^n\to H` into a complex Hilbert space,
Mathlib's Fourier convention gives the exact Plancherel identity

$$`
  \int_{\mathbb R^n}\!\lVert\Delta f(x)\rVert^2\,dx
  =(2\pi)^4\int_{\mathbb R^n}\!
    \lVert\xi\rVert^4\lVert\widehat f(\xi)\rVert^2\,d\xi.
`

The fourth power of $`2\pi` is forced by squaring the Laplacian multiplier
$`-(2\pi)^2\lVert\xi\rVert^2`.
:::

:::proof "methods.fourier.laplacian_energy"
Apply Plancherel to $`\Delta f`, rewrite its Fourier transform using Mathlib's
multidimensional Laplacian multiplier theorem, take the squared norm of the
scalar multiple, and normalize the real absolute values using positivity of
$`\pi` and nonnegativity of the Euclidean norm.
:::

In one dimension the shifted operator $`-\partial_{xx}+\lambda` has symbol
$`-(2\pi i\xi)^2+\lambda=(2\pi\xi)^2+\lambda`, which is real and, for
$`\lambda>0`, bounded below by $`\lambda`. That lower bound is the whole
mechanism of the resolvent estimate, and it is why the elliptic sign
convention $`-\partial_{xx}` rather than $`\partial_{xx}` is used.

:::definition "methods.fourier.shifted_symbol" (parent := "methods.representations") (lean := "PDE.Elliptic.Classical.OneDimensional.Fourier.shiftedEllipticSymbol1D, PDE.Elliptic.Classical.OneDimensional.Fourier.shiftedEllipticSymbol1D_eq_ofReal")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Fourier symbol of the one-dimensional shifted elliptic operator
$`-\partial_{xx}+\lambda` is

$$`(2\pi\xi)^2+\lambda.`

The factor $`2\pi` comes from Mathlib's normalization.
:::

The multiplier identity holds for every real shift $`\lambda`; positivity of
$`\lambda` enters only when the symbol is divided out.

:::theorem "methods.fourier.shifted_multiplier" (parent := "methods.representations") (lean := "PDE.Elliptic.Classical.OneDimensional.Fourier.fourier_shifted_negative_second_derivative_multiplier") (uses := "methods.fourier.shifted_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On Schwartz functions, Fourier transformation diagonalizes
$`-\partial_{xx}+\lambda`: the transformed operator is pointwise
multiplication by its shifted elliptic symbol. This shifted resolvent
specializes Evans's constant-coefficient transform method.
:::

:::proof "methods.fourier.shifted_multiplier"
Linearity sends $`-u''+\lambda u` to
$`-\widehat{u''}+\lambda\widehat u`. The second-derivative multiplier is
$`(2\pi i\xi)^2=-(2\pi\xi)^2`; the leading minus sign therefore changes it
to $`(2\pi\xi)^2`. Factoring $`\widehat u` yields the shifted symbol
$`((2\pi\xi)^2+\lambda)\widehat u`.
:::

Once the operator is a multiplier, the equation
$`(-\partial_{xx}+\lambda)u=f` becomes the scalar equation
$`((2\pi\xi)^2+\lambda)\widehat u=\widehat f` at each frequency, and
dividing is legitimate exactly when the symbol is nonzero, which
$`\lambda>0` guarantees. The characterization is pointwise in $`\xi`.

:::theorem "methods.fourier.shifted_resolvent" (parent := "methods.representations") (lean := "PDE.Elliptic.Classical.OneDimensional.Fourier.fourier_shifted_elliptic_equation_iff") (uses := "methods.fourier.shifted_multiplier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For Schwartz functions $`u,f` and $`\lambda>0`, fix a frequency $`\xi`.
The transformed equation
$`\widehat{(-\partial_{xx}+\lambda)u}(\xi)=\widehat f(\xi)` is equivalent to

$$`\widehat u(\xi)=
\frac{\widehat f(\xi)}{(2\pi\xi)^2+\lambda}.`
:::

:::proof "methods.fourier.shifted_resolvent"
Apply the shifted-multiplier identity at the chosen frequency. Since
$`\lambda>0` and $`(2\pi\xi)^2\geq0`, the symbol is strictly positive,
so division gives the displayed formula. Multiplying by the symbol recovers
the transformed equation at that frequency.
:::

The lower bound $`(2\pi\xi)^2+\lambda\ge\lambda` turns the division formula
into an estimate. The bound is uniform in $`\xi`, so integrating it with
Plancherel would give the $`L^2` resolvent estimate
$`\|u\|_2\le\lambda^{-1}\|f\|_2`.

:::theorem "methods.fourier.shifted_resolvent_bound" (parent := "methods.representations") (lean := "PDE.Elliptic.Classical.OneDimensional.Fourier.fourier_shifted_elliptic_solution_norm_le") (uses := "methods.fourier.shifted_resolvent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "187-192"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\lambda>0`. Every Schwartz solution of $`-u''+\lambda u=f` with
Schwartz $`f` satisfies, at every frequency $`\xi`, the estimate

$$`|\widehat u(\xi)|\le \frac{|\widehat f(\xi)|}{\lambda}.`
:::

:::proof "methods.fourier.shifted_resolvent_bound"
Take absolute values in the resolvent formula. The denominator is real and
satisfies $`(2\pi\xi)^2+\lambda\geq\lambda>0`, so its reciprocal is at most
$`1/\lambda`. Multiplying by $`|\widehat f(\xi)|` gives the pointwise
estimate.
:::

# Reconstructing heat and waves

For evolution equations, the multiplier depends on time. Heat damps high
frequencies by $`e^{-4\pi^2t|\xi|^2}`; waves rotate the displacement and
velocity modes by cosine and sine. The figure fixes the initial displacement
of each mode at one and its initial velocity at zero. The higher frequency
decays faster under heat flow and oscillates faster under the wave equation.
These are the same spatial modes, with two different time evolutions.

{leanpde_figure "fourier-evolution"}

To reconstruct a classical solution, we also have to justify the derivatives
of the inverse integral and recover the initial data.

:::theorem "methods.fourier.heat_cauchy" (parent := "methods.representations") (lean := "HeatEquation.fourierSolution_eq_integral, HeatEquation.contDiffAt_fourierSolution_timeSpace, HeatEquation.deriv_fourierSolution_time_eq_laplacian, HeatEquation.fourierSolution_initial_trace, HeatEquation.fourierSolution_isPointwiseInitialValueSolution, HeatEquation.fourierSolution_schwartz_isPointwiseInitialValueSolution") (uses := "methods.fourier.derivative_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4, §4.3.1, Fourier transform"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\in\mathbb N` and let $`g:\mathbb R^n\to\mathbb R` be bounded,
continuous, and integrable. For $`t>0`, the inverse Fourier formula

$$`
u(x,t)=\mathcal F^{-1}
\bigl(e^{-4\pi^2t|\xi|^2}\widehat g(\xi)\bigr)(x)
`

is real, jointly smooth, and satisfies $`u_t=\Delta u`. As
$`(t,x)\to(0,x_0)` from positive times, $`u(x,t)\to g(x_0)`.
The evolved Fourier data are integrable at positive time even when
$`\widehat g\notin L^1`.

If $`\widehat g\in L^1` as well, the same formula at $`t=0` equals
$`g` pointwise and satisfies the full pointwise heat Cauchy predicate.
Real Schwartz data satisfy all these hypotheses.
:::

:::proof "methods.fourier.heat_cauchy"
The Fourier transform of an integrable datum is bounded. Multiplication by
the positive-time Gaussian therefore produces an integrable frequency
profile. Fourier pairing and the Gaussian transform identify its inverse as
$`\int G_t(x-y)g(y)\,dy`. The proved heat-kernel construction then supplies
joint smoothness, the analytic heat equation, and the joint initial trace.
At exactly zero time the multiplier is one, so ordinary Fourier inversion
uses the additional integrability of $`\widehat g`. Schwartz decay supplies
that assumption in the final corollary.
:::

:::theorem "methods.fourier.wave_cauchy" (parent := "methods.representations") (lean := "WaveEquation.fourierSolution_eq_characteristicIntegral, WaveEquation.contDiff_two_fourierSolution1D, WaveEquation.waveOperator_fourierSolution1D, WaveEquation.fourierSolution1D_satisfiesResidualAssignedCauchyData, WaveEquation.tendsto_fourierSolution1D_initial_position, WaveEquation.tendsto_partialDeriv_fourierSolution1D_initial_velocity, WaveEquation.fourierSolution1D_schwartz_satisfiesResidualAssignedCauchyData") (uses := "methods.fourier.derivative_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4, §4.3.1, Fourier transform"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let the real displacement $`g\in C^2(\mathbb R)` and velocity
$`h\in C^1(\mathbb R)` be integrable, with both Fourier transforms
integrable. Then

$$`
u(x,t)=\mathcal F^{-1}\!
\left(\cos(2\pi\xi t)\widehat g(\xi)
+t\,\operatorname{sinc}(2\pi\xi t)\widehat h(\xi)\right)(x)
`

is real and jointly $`C^2` at every real time, and satisfies
$`u_{tt}-u_{xx}=0`, $`u(x,0)=g(x)`, and $`u_t(x,0)=h(x)`.
The field and its actual time derivative also have the corresponding joint
space-time initial traces. Here $`\operatorname{sinc}(z)=\sin z/z`
with value one at zero, so the zero-frequency velocity multiplier is $`t`.
Real Schwartz data give the stated Cauchy solution without extra
integrability assumptions.
:::

:::proof "methods.fourier.wave_cauchy"
Fourier inversion sends the cosine mode to
$`(g(x+t)+g(x-t))/2`. Express the sinc mode as an integral of phases
over $`[-1,1]`; integrability justifies Fubini, and inversion gives
$`\frac12\int_{x-t}^{x+t}h(y)\,dy`. Thus the full formula, including
the velocity contribution, equals d'Alembert's solution. Its established
regularity, wave equation, assigned data, and joint derivative trace
transfer through this identity.
:::

In higher dimensions, replace $`|\xi|` by the Euclidean norm
$`\|\xi\|`. Each frequency still solves the same scalar oscillator
equation. The extra analytic work is in putting the frequencies back
together: two spatial derivatives multiply the integrand by two frequency
factors, and those factors must remain integrable. Schwartz data give us
exactly this room to differentiate.

:::theorem "methods.fourier.wave_schwartz" (parent := "methods.representations") (lean := "WaveEquation.Fourier.contDiff_two_realSolution, WaveEquation.Fourier.waveOperator_realSolution, WaveEquation.Fourier.realSolution_initial_position, WaveEquation.Fourier.partialDeriv_realSolution_initial_velocity, WaveEquation.Fourier.realSolution_satisfiesResidualAssignedCauchyData, WaveEquation.Fourier.tendsto_realSolution_initial_position, WaveEquation.Fourier.tendsto_partialDeriv_realSolution_initial_velocity") (uses := "methods.fourier.derivative_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4, §4.3.1, Fourier transform"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`g,h\in\mathcal S(\mathbb R^n;\mathbb R)`. Set
$`\omega(\xi)=2\pi\|\xi\|` and define

$$`
u(x,t)=\operatorname{Re}\mathcal F^{-1}\!
\left(\cos(\omega(\xi)t)\widehat g(\xi)
+t\,\operatorname{sinc}(\omega(\xi)t)\widehat h(\xi)\right)(x).
`

Then $`u` is jointly $`C^2` on all of $`\mathbb R\times\mathbb R^n` and

$$`
u_{tt}-\Delta u=0,\qquad u(x,0)=g(x),\qquad u_t(x,0)=h(x).
`

Both initial values are also joint limits as $`(t,x)\to(0,x_0)`.
The real part in the definition gives a real field directly. The formula
includes $`\xi=0`, where the velocity multiplier is $`t`, and every
finite spatial dimension, including $`n=0`.
:::

:::proof "methods.fourier.wave_schwartz"
The cosine and sinc modes solve $`v_{tt}=-\omega^2v`. On each bounded
time interval, their values and first two time derivatives are bounded by
polynomials in $`\|\xi\|` times $`|\widehat g|+|\widehat h|`.
Mathlib's Schwartz Fourier transform supplies integrable bounds for all
these moments.

Apply the parameter integral theorem twice, the second time to an integral
with values in continuous linear maps. This gives the joint Hessian.
Its time-time entry and the sum of its spatial diagonal entries agree
because $`\omega^2=4\pi^2\|\xi\|^2`. Taking real parts preserves that
identity. At time zero, the cosine multiplier is one and the sinc
multiplier vanishes; their time derivatives are zero and one.
Fourier inversion therefore recovers $`g` and $`h`, and joint continuity
of the field and its first derivative gives the two traces.
:::

# One-sided Laplace inversion

A time transform retains the initial value when it transforms a derivative.
It also introduces a convergence choice: on the vertical line
$`s=a+2\pi i\xi`, the one-sided Laplace transform is the Fourier transform
of the exponentially damped causal extension. The same Fourier
normalization therefore determines the inverse integral.

:::theorem "methods.laplace.vertical_inversion" (parent := "methods.representations") (lean := "PDE.Analysis.Laplace.transform_vertical_eq_fourier, PDE.Analysis.Laplace.inversion, PDE.Analysis.Laplace.integrable_transform_vertical, PDE.Analysis.Laplace.inversion_of_contDiff_hasCompactSupport")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4, Laplace transform"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a complex Banach-valued function $`f`, write
$`Lf(s)=\int_0^\infty e^{-st}f(t)\,dt`. Fix $`a\in\mathbb R`.
If the damped causal extension
$`\mathbf1_{(0,\infty)}(t)e^{-at}f(t)` and the vertical trace
$`\xi\mapsto Lf(a+2\pi i\xi)` are integrable, then at every
$`t>0` where $`f` is continuous,

$$`
f(t)=e^{at}\int_{\mathbb R}e^{2\pi i\xi t}Lf(a+2\pi i\xi)\,d\xi.
`

For globally smooth, compactly supported $`f` vanishing at nonpositive
times, both integrability conditions are derived for every real $`a`.
The inversion integral converges absolutely.
:::

:::proof "methods.laplace.vertical_inversion"
Rewrite the half-line transform on $`a+2\pi i\xi` as the Fourier
transform of the damped causal extension. At a positive continuity point,
Fourier inversion recovers $`e^{-at}f(t)`, and multiplication by
$`e^{at}` gives the formula. A smooth compactly supported causal
function remains smooth and compactly supported after damping. Its Schwartz
Fourier transform is integrable, which proves convergence rather than
leaving it as an assumption in that case.
:::

:::theorem "methods.laplace.initial_term" (parent := "methods.representations") (lean := "PDE.Analysis.Laplace.transform_derivative, PDE.Analysis.Laplace.transform_deriv_of_hasCompactSupport") (uses := "methods.laplace.vertical_inversion")
For complex-valued $`f`, the operational rule is

$$`L(f')(s)=sLf(s)-f(0).`

The general theorem assumes right continuity at zero, pointwise
differentiability at positive times, integrability of $`e^{-st}f(t)`
and $`e^{-st}f'(t)` on the positive half-line, and
$`e^{-st}f(t)\to0` at infinity. A globally $`C^1`, compactly
supported function satisfies these conditions for every complex $`s`.
:::

:::proof "methods.laplace.initial_term"
Integrate
$`(e^{-st}f(t))'=e^{-st}f'(t)-s e^{-st}f(t)`.
The boundary value at infinity is zero, while the lower endpoint, using
the right-hand trace at zero, contributes $`-f(0)`. The improper fundamental
theorem of calculus and the two integrability hypotheses justify this
calculation.
:::

:::theorem "methods.laplace.boundary_transport" (parent := "methods.representations") (lean := "PDE.Hyperbolic.Transport.boundarySolution_transport, PDE.Hyperbolic.Transport.boundarySolution_initial, PDE.Hyperbolic.Transport.boundarySolution_boundary, PDE.Hyperbolic.Transport.transform_boundarySolution, PDE.Hyperbolic.Transport.transform_time_deriv_boundarySolution, PDE.Hyperbolic.Transport.hasDerivAt_transformed_boundarySolution, PDE.Hyperbolic.Transport.boundarySolution_laplace_representation") (uses := "methods.laplace.vertical_inversion, methods.laplace.initial_term")
Let $`g:\mathbb R\to\mathbb C` be globally smooth, compactly supported,
and zero at nonpositive times. The field $`u(t,x)=g(t-x)` solves
$`u_t+u_x=0` on $`x\ge0`, has zero initial data there, and satisfies
$`u(t,0)=g(t)`. Its time transform is
$`U(s,x)=e^{-sx}Lg(s)`, with $`\partial_xU=-sU`.
For every real $`a`, $`t>0`, and $`x\ge0`, the actual field is
reconstructed by the absolutely convergent integral

$$`
u(t,x)=e^{at}\int_{\mathbb R}
e^{2\pi i\xi t}e^{-(a+2\pi i\xi)x}Lg(a+2\pi i\xi)\,d\xi.
`
:::

:::proof "methods.laplace.boundary_transport"
The chain rule verifies the transport PDE for $`g(t-x)`. Causality
gives $`g(-x)=0` when $`x\ge0`, and setting $`x=0` gives the boundary
signal. Translating the time integral yields the delay factor $`e^{-sx}`.
The initial-term rule transforms $`u_t` to $`sU`, and differentiating
the exponential profile gives $`U_x=-sU`. For each fixed nonnegative
$`x`, the delayed signal remains smooth, compactly supported, and causal.
Apply vertical inversion to it to obtain the displayed reconstruction.
:::
