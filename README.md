# First-Order Methods for Smooth Convex Optimization in Isabelle/HOL

This repository is a work-in-progress Isabelle/HOL formalization project for first-order methods in smooth convex optimization.

The current development started from projected gradient descent, but the broader goal is to build a reusable optimization library for Isabelle/HOL. The project develops general infrastructure for differentiable convex functions, smoothness inequalities, descent estimates, gradient-type algorithms, Euclidean projection, variational inequalities, and convergence-rate proofs.

Projected gradient descent is intended to be a central application of this framework, rather than the only contribution.

The project is designed with an AFP-style structure in mind. Definitions should be modular, theorem statements should be reusable, and algorithmic convergence proofs should be separated from low-level analytic facts whenever possible.

## Project vision

The long-term goal is to provide a reusable formal library for first-order convex optimization in Isabelle/HOL.

The intended scope includes:

1. gradient and differentiability infrastructure for real inner product spaces;
2. first-order optimality certificates for convex differentiable functions;
3. smoothness assumptions and quadratic upper-bound inequalities;
4. abstract descent estimates and telescoping proof patterns;
5. gradient descent and its convergence guarantees;
6. Euclidean projection onto convex feasible sets;
7. projection variational inequalities and fixed-point characterizations;
8. projected gradient descent for constrained smooth convex minimization;
9. optional extensions to strong convexity, projected gradient mappings, and concrete examples.

The central mathematical theme is that many first-order methods can be proved correct by combining a small number of reusable ingredients:

```text
convex first-order lower bounds
+ smooth upper bounds
+ geometric projection inequalities
+ norm algebra
+ telescoping estimates
= convergence guarantees for first-order methods
```

The current repository therefore aims to formalize not only one algorithm, but also the surrounding proof infrastructure that can later support related methods.

## Main algorithmic target

The motivating algorithm is projected gradient descent:

```text
x_{k+1} = P_C (x_k - alpha * grad f x_k)
```

Here:

* `C` is a feasible set;
* `P_C` is Euclidean projection onto `C`;
* `f` is a convex differentiable function;
* `grad f` is its gradient;
* `alpha` is a step size.

The intended final convergence theorem is the standard O(1 / N) rate for smooth convex minimization over a closed convex feasible set.

A typical target statement has the form:

```text
f (x_N) - f x_star <= norm (x_0 - x_star)^2 / (2 * alpha * N)
```

under suitable assumptions on convexity, smoothness, feasibility, existence of a minimizer, and the step size.

## Current status

The current development contains the following theory files:

```text
Gradient_Preliminaries.thy
Convex_Differentiable.thy
Smooth_Convex.thy
Gradient_Descent.thy
```

Together, these files provide the first part of the formal infrastructure needed for gradient descent and projected gradient descent.

The currently completed layers are:

* gradient preliminaries;
* named gradient fields on sets;
* first-order convex optimality certificates;
* smooth upper-bound interfaces;
* one-step descent estimates for gradient steps;
* gradient descent recurrences;
* monotonicity of objective values along gradient descent iterates.

The projected-gradient layer is not yet complete.

## Theory files

### `Gradient_Preliminaries.thy`

This file introduces a lightweight optimization-oriented wrapper around Isabelle/HOL's Fréchet derivative infrastructure.

Main components include:

* pointwise gradients, via `has_gradient`;
* gradients within a set, via `has_gradient_within`;
* named gradient fields on sets, via `has_gradient_on`;
* uniqueness of gradients;
* the gradient operator `gradient`;
* elementary gradient rules;
* affine-line restrictions;
* directional derivatives along lines;
* inner-product and squared-norm algebra used later in descent and convergence proofs.

This theory is intentionally independent of convexity and smoothness.

Its role is to let later files state optimization results in terms of gradients and inner products, rather than repeatedly unfolding raw derivative maps.

### `Convex_Differentiable.thy`

This file develops the first-order language of convex differentiable optimization.

Main components include:

* global minimizers on feasible sets, via `global_min_on`;
* first-order variational inequalities, via `first_order_condition_at`;
* supporting affine lower bounds, via `supports_at` and `supports_on`;
* gradient lower bounds, via `gradient_lower_bound_on`;
* convex differentiability with a named gradient field, via `convex_differentiable_on`;
* a locale form for convex differentiable functions.

The main theorem of this file is the first-order supporting-hyperplane property for convex differentiable functions:

```text
convex_on S f
has_gradient f x g
x in S
y in S
==> f x + inner g (y - x) <= f y
```

This is formalized as:

```text
convex_has_gradient_supports
```

and then packaged into reusable consequences such as:

```text
convex_differentiable_on_supporting_hyperplanes
convex_differentiable_on_first_order_sufficient
```

The second theorem states the usual first-order sufficient condition for global optimality in convex optimization: for a convex differentiable function, a feasible point satisfying the variational first-order condition is a global minimizer.

This layer is intended to be reusable for projected gradient descent, Frank-Wolfe-type methods, constrained optimality conditions, and other first-order convex optimization developments.

### `Smooth_Convex.thy`

This file introduces the smoothness layer used for descent proofs.

The central interface is the quadratic upper-bound property:

```text
f y <= f x + inner (G x) (y - x) + (L / 2) * norm (y - x)^2
```

This is the standard descent-lemma form of smoothness. The file packages this property directly as:

```text
smooth_upper_bound_on L S f G
```

so that later algorithmic proofs can use it without repeatedly unfolding analytic details.

Main components include:

* Lipschitz-gradient fields, via `lipschitz_gradient_on`;
* quadratic smooth upper bounds, via `smooth_upper_bound_on`;
* smooth convex functions, via `smooth_convex_on`;
* the explicit gradient step map `gradient_step`;
* algebraic identities for gradient steps;
* one-step descent estimates from the smooth upper-bound property;
* a locale form for smooth convex functions.

The main one-step estimate has the form:

```text
f (gradient_step alpha G x)
<= f x - alpha * norm (G x)^2
   + (L / 2) * alpha^2 * norm (G x)^2
```

Under the step-size condition `alpha * L <= 1`, this yields the cleaner decrease estimate:

```text
f (gradient_step alpha G x)
<= f x - (alpha / 2) * norm (G x)^2
```

These results serve as the core descent estimates for the gradient descent theory and the later projected gradient descent theory.

### `Gradient_Descent.thy`

This file lifts the one-step estimates from `Smooth_Convex.thy` to gradient descent sequences.

Main components include:

* the gradient descent recurrence, via `gradient_descent_iterates`;
* feasible iterates, via `feasible_iterates`;
* objective values along a sequence;
* one-step descent for gradient descent iterates;
* nonincreasing objective values;
* a locale form for gradient descent.

The recurrence has the form:

```text
x (Suc n) = gradient_step alpha G (x n)
```

The current main conclusion is that, under the smooth upper-bound assumptions and a suitable step size, the objective values along gradient descent iterates are nonincreasing.

This file is the first algorithmic layer of the project. It is deliberately structured so that later convergence-rate proofs can reuse the recurrence and monotonicity results.

## Planned library structure

The intended final development is broader than a single projected-gradient theorem.

A possible AFP-style structure is:

```text
Projected_Gradient_Descent/
  ROOT
  README.md

  Gradient_Preliminaries.thy
  Convex_Differentiable.thy
  Smooth_Convex.thy
  Gradient_Descent.thy

  Gradient_Descent_Rates.thy

  Projection_Optimization.thy
  Projected_Gradient_Descent.thy
  Projected_Gradient_Descent_Rates.thy

  Strong_Convex.thy
  Strong_Convex_Rates.thy

  Examples_Quadratic.thy
  Examples_Least_Squares.thy
```

The current repository still uses a flat theory layout. The structure above describes the intended mathematical organization, not necessarily the current physical directory layout.

## Mathematical roadmap

The development is organized around the following proof pipeline.

### 1. Gradient infrastructure

The first layer packages Fréchet derivatives into optimization-style gradient statements.

This makes later proofs read in terms of gradients and inner products rather than raw derivative maps.

### 2. First-order convex certificates

The second layer proves that convex differentiability implies supporting affine lower bounds.

This gives the bridge:

```text
convex differentiability
==> supporting affine lower bounds
==> first-order optimality certificates
==> global minimizers
```

This layer is useful beyond gradient descent. It is the basic first-order optimality interface for differentiable convex optimization.

### 3. Smooth upper bounds

The third layer packages the smoothness upper-bound inequality used in descent proofs.

This avoids committing too early to a particular analytic derivation of the descent lemma. The current interface can later be connected to more primitive Lipschitz-gradient assumptions.

The key reusable idea is:

```text
smooth upper bound + algorithmic step identity
==> one-step descent inequality
```

### 4. Gradient descent

The fourth layer defines gradient descent iterates and proves basic descent properties.

The current theory already defines the recurrence and proves monotonicity of the objective values under suitable assumptions.

The next goal for this layer is to prove convergence-style estimates, such as:

```text
sum of squared gradient norms is bounded
minimum gradient norm has an O(1 / N) bound
function-value gap has an O(1 / N) bound under convexity
```

These results should be organized so that later methods can reuse the same telescoping patterns.

### 5. Projection theory

The next major layer will formalize the geometry of Euclidean projection onto convex feasible sets.

The intended components include:

* projection belongs to the feasible set;
* projection minimizes distance to the original point;
* projection variational inequality;
* nonexpansiveness of projection;
* fixed-point characterizations of projected steps;
* projected gradient mapping.

The key projected-gradient inequality is expected to come from the projection variational inequality:

```text
inner (x - P_C x) (y - P_C x) <= 0
```

for every feasible point `y`.

### 6. Projected gradient descent

The projected-gradient layer will combine:

* the smooth upper-bound inequality;
* the projection variational inequality;
* convex first-order lower bounds;
* squared-norm algebra;
* telescoping estimates.

The target update is:

```text
x (Suc n) = P_C (x n - alpha * grad f (x n))
```

The intended first milestones are:

* feasibility of all iterates;
* one-step projected descent;
* monotonicity of objective values, when applicable;
* a basic O(1 / N) convergence rate for smooth convex minimization.

### 7. Strong convexity and linear rates

A later extension may add strong convexity.

The intended components include:

* `strongly_convex_on`;
* equivalent lower-bound formulations;
* uniqueness of minimizers under strong convexity;
* linear convergence of gradient descent;
* linear convergence of projected gradient descent under suitable assumptions.

This layer is not required for the first AFP submission, but it would make the library substantially more useful.

### 8. Concrete examples

The final development should include examples showing that the framework can be instantiated.

Possible examples include:

* quadratic objectives;
* least-squares objectives;
* simple box constraints;
* Euclidean ball constraints;
* affine subspace constraints.

These examples are intended to demonstrate that the abstract assumptions are usable in concrete optimization problems.

## Design principles

The development follows several design principles.

### Reusable interfaces

Core mathematical assumptions are packaged as reusable predicates, for example:

```text
has_gradient_on
convex_differentiable_on
smooth_upper_bound_on
smooth_convex_on
gradient_descent_iterates
```

This keeps later algorithmic theorems independent of unnecessary low-level details.

### Named gradient fields

The project consistently uses a named gradient field `G` rather than repeatedly writing `gradient f x`.

This makes theorem statements cleaner and avoids unnecessary dependence on choice-style definitions.

### Separation of analytic and algorithmic layers

The smoothness upper-bound property is currently treated as an explicit interface.

This allows the algorithmic gradient descent proofs to proceed independently of the more delicate analytic proof that Lipschitz gradients imply the descent lemma.

A later extension may prove that implication as an additional theorem.

### Abstract descent templates

A major goal is to avoid proving every convergence theorem from scratch.

The project should eventually include abstract proof templates of the following form:

```text
one-step progress inequality
+ telescoping
==> convergence rate
```

This would make the library reusable for future formalizations of other first-order methods.

### AFP-style structure

The repository is being developed with an AFP-style submission in mind:

* theory files should build cleanly;
* definitions should be reusable;
* theorem names should be stable and descriptive;
* text blocks should explain the mathematical role of each layer;
* the final development should avoid experimental or unfinished material;
* the README should clearly distinguish completed results from planned extensions.

## Build instructions

From the repository root, run:

```bash
isabelle build -D .
```

For AFP-style document checking, the intended final command will be close to:

```bash
isabelle build -v -o browser_info -o "document=pdf" \
  -o "document_variants=document:outline=/proof,/ML" -D .
```

The document-generation setup may require additional AFP-style files before submission.

## Current next steps

The immediate next step is no longer to add `Gradient_Descent.thy`; that file is now present.

The next milestones are:

1. strengthen `Gradient_Descent.thy` with finite-sum and convergence-rate estimates;
2. introduce `Projection_Optimization.thy`;
3. prove the projection variational inequality and related projection facts;
4. define projected gradient descent iterates;
5. prove feasibility and one-step projected descent;
6. prove the basic projected-gradient convergence theorem;
7. add examples showing how the framework can be instantiated.

A minimal next milestone is:

```text
Gradient_Descent_Rates.thy
```

with results such as:

```text
bounded sum of squared gradient norms
minimum gradient norm bound
basic function-value convergence rate
```

After that, the project should move to projection theory.

## Repository status

This repository is currently under active development.

Completed or partially completed layers:

* gradient preliminaries;
* first-order convex optimality certificates;
* smooth upper-bound interfaces;
* one-step descent estimates for gradient steps;
* gradient descent recurrence;
* monotonicity of objective values for gradient descent iterates.

Not yet complete:

* convergence-rate theorems for gradient descent;
* Euclidean projection theory;
* projected gradient descent;
* projected-gradient convergence rates;
* concrete examples;
* AFP document setup.

The projected-gradient convergence theorem is not yet complete.

## Intended contribution

The intended contribution is a reusable Isabelle/HOL development for smooth convex optimization and first-order methods.

The project aims to be useful not only as a formalization of projected gradient descent, but also as infrastructure for future formalizations of optimization algorithms.

In particular, the reusable parts are expected to be:

* optimization-oriented gradient interfaces;
* first-order convexity certificates;
* smooth upper-bound descent lemmas;
* abstract descent and telescoping patterns;
* projection inequalities for constrained optimization;
* algorithmic convergence proofs for gradient-type methods.

The long-term goal is that future Isabelle/HOL developments in convex optimization can import this project instead of rebuilding these foundations from scratch.