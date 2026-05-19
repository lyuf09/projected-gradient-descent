# Projected Gradient Descent in Isabelle/HOL

This repository is a work-in-progress Isabelle/HOL formalization project for first-order methods in smooth convex optimization, with a focus on projected gradient descent.

The long-term goal is to develop a reusable formal library for convex differentiable optimization, smoothness inequalities, gradient descent, Euclidean projection, and projected gradient descent.  The project is designed with an AFP-style structure in mind: definitions should be modular, theorem statements should be reusable, and the development should avoid unnecessary commitment to concrete finite-dimensional coordinates whenever the Isabelle/HOL-Analysis library already provides a more general abstraction.

## Project overview

The project aims to formalize a sequence of standard results from convex optimization:

1. gradient preliminaries for real inner product spaces;
2. first-order optimality certificates for convex differentiable functions;
3. smoothness assumptions and quadratic upper bounds;
4. one-step descent estimates for gradient steps;
5. convergence guarantees for gradient descent;
6. Euclidean projection and projection variational inequalities;
7. projected gradient descent for smooth convex minimization;
8. examples illustrating the framework.

The intended final theorem family is centered around projected gradient descent for a smooth convex function over a nonempty closed convex feasible set.

Mathematically, the central algorithm is

```text
x_{k+1} = P_C (x_k - alpha * grad f x_k),
```

where `C` is a feasible set, `P_C` is Euclidean projection onto `C`, `f` is a convex differentiable function with a smoothness upper bound, and `alpha` is a suitable step size.

## Current status

The current development contains the following theory files:

```text
Gradient_Preliminaries.thy
Convex_Differentiable.thy
Smooth_Convex.thy
```

Together, these files provide the first part of the formal infrastructure needed for gradient descent and projected gradient descent.

### `Gradient_Preliminaries.thy`

This file introduces a lightweight optimization-oriented wrapper around Isabelle/HOL's Fréchet derivative infrastructure.

Main components include:

- pointwise gradients, via `has_gradient`;
- gradients within a set, via `has_gradient_within`;
- named gradient fields on sets, via `has_gradient_on`;
- uniqueness of gradients;
- the gradient operator `gradient`;
- elementary gradient rules;
- affine-line restrictions;
- directional derivatives along lines;
- inner-product and squared-norm algebra used later in descent and convergence proofs.

This theory is intentionally independent of convexity.

### `Convex_Differentiable.thy`

This file develops the first-order language of convex differentiable optimization.

Main components include:

- global minimizers on feasible sets, via `global_min_on`;
- first-order variational inequalities, via `first_order_condition_at`;
- supporting affine lower bounds, via `supports_at` and `supports_on`;
- gradient lower bounds, via `gradient_lower_bound_on`;
- convex differentiability with a named gradient field, via `convex_differentiable_on`;
- a locale form for convex differentiable functions.

The main theorem of this file is the first-order supporting-hyperplane property for convex differentiable functions:

```text
convex_on S f
has_gradient f x g
x \<in> S
y \<in> S
\<Longrightarrow> f x + inner g (y - x) \<le> f y
```

This is formalized as

```text
convex_has_gradient_supports
```

and then packaged into reusable consequences such as

```text
convex_differentiable_on_supporting_hyperplanes
convex_differentiable_on_first_order_sufficient
```

The second theorem states the usual first-order sufficient condition for global optimality in convex optimization: for a convex differentiable function, a feasible point satisfying the variational first-order condition is a global minimizer.

### `Smooth_Convex.thy`

This file introduces the smoothness layer used later for gradient descent and projected gradient descent.

The central interface is the quadratic upper-bound property

```text
f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x)^2.
```

This is the standard descent-lemma form of smoothness.  The file packages this property directly as

```text
smooth_upper_bound_on L S f G
```

so that later algorithmic proofs can use it without repeatedly unfolding analytic details.

Main components include:

- Lipschitz-gradient fields, via `lipschitz_gradient_on`;
- quadratic smooth upper bounds, via `smooth_upper_bound_on`;
- smooth convex functions, via `smooth_convex_on`;
- the explicit gradient step map

```text
gradient_step alpha G x = x - alpha *\<^sub>R G x
```

- algebraic identities for gradient steps;
- one-step descent estimates from the smooth upper-bound property;
- a locale form for smooth convex functions.

The main one-step estimate has the form

```text
f (gradient_step alpha G x)
\<le> f x - alpha * norm (G x)^2
    + (L / 2) * alpha^2 * norm (G x)^2.
```

Under the step-size condition `alpha * L \<le> 1`, this yields the cleaner decrease estimate

```text
f (gradient_step alpha G x)
\<le> f x - (alpha / 2) * norm (G x)^2.
```

These results are intended to serve as the core descent estimates for the later gradient descent theory.

## Planned theory structure

The intended final structure is:

```text
Projected_Gradient_Descent/
  ROOT
  README.md
  Gradient_Preliminaries.thy
  Convex_Differentiable.thy
  Smooth_Convex.thy
  Gradient_Descent.thy
  Projection_Optimization.thy
  Projected_Gradient_Descent.thy
  Examples.thy
```

The next planned theory is:

```text
Gradient_Descent.thy
```

This file is expected to build on `Smooth_Convex.thy` and formalize descent and convergence properties for unconstrained gradient descent sequences.

After that, the projected-gradient part will be developed through a projection layer:

```text
Projection_Optimization.thy
Projected_Gradient_Descent.thy
```

The projection layer should provide the variational inequality and nonexpansiveness properties needed for projected gradient descent.

## Mathematical roadmap

The development is organized around the following proof pipeline.

### 1. Gradient infrastructure

The first layer packages Fréchet derivatives into optimization-style gradient statements.

This makes later proofs read in terms of gradients and inner products rather than raw derivative maps.

### 2. First-order convex certificates

The second layer proves that convex differentiability implies supporting affine lower bounds.

This gives the formal bridge

```text
convex differentiability
\<Longrightarrow> supporting hyperplanes
\<Longrightarrow> first-order optimality certificates
\<Longrightarrow> global minimizers.
```

### 3. Smooth upper bounds

The third layer packages the smoothness upper bound used in descent proofs.

This avoids committing too early to a particular analytic derivation of the descent lemma.  The current interface can later be connected to more primitive Lipschitz-gradient assumptions.

### 4. Gradient descent

The next layer will define gradient descent iterates and use the one-step descent estimate to prove monotonicity and convergence-style inequalities.

Typical statements should have the form

```text
x (Suc n) = gradient_step alpha G (x n)
\<Longrightarrow> f (x (Suc n)) \<le> f (x n)
```

under suitable assumptions on `alpha`, `L`, and membership in the feasible set.

### 5. Projection and projected gradient descent

The final projected-gradient layer will combine smooth upper bounds with projection variational inequalities.

The target update is

```text
x_{k+1} = P_C (x_k - alpha * grad f x_k).
```

The proof strategy is to combine:

- the smooth upper-bound inequality;
- the projection variational inequality;
- convex first-order lower bounds;
- squared-norm algebra;
- telescoping estimates.

## Design principles

The development follows several design principles.

### Modular interfaces

Core mathematical assumptions are packaged as reusable predicates, for example:

```text
has_gradient_on
convex_differentiable_on
smooth_upper_bound_on
smooth_convex_on
```

This keeps later algorithmic theorems independent of unnecessary low-level details.

### Named gradient fields

The project consistently uses a named gradient field `G` rather than repeatedly writing `gradient f x`.

This makes statements cleaner and avoids unnecessary dependence on choice-style definitions.

### Separation of analytic and algorithmic layers

The smoothness upper-bound property is currently treated as an explicit interface.  This allows the algorithmic gradient descent proofs to proceed independently of the more delicate analytic proof that Lipschitz gradients imply the descent lemma.

A later extension may prove that implication as an additional theorem.

### AFP-style structure

The repository is being developed with an AFP-style submission in mind:

- theory files should build cleanly;
- definitions should be reusable;
- theorem names should be stable and descriptive;
- text blocks should explain the mathematical role of each layer;
- the final development should avoid experimental or unfinished material.

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

The immediate next step is to add

```text
Gradient_Descent.thy
```

and use the one-step descent estimates from `Smooth_Convex.thy` to formalize basic properties of gradient descent sequences.

A minimal next milestone is:

1. define gradient descent recurrence;
2. prove the one-step descent theorem for the recurrence;
3. prove monotonicity of the objective values;
4. prepare the algebra needed for convergence-rate statements.

After that, the project can move to projection theory and projected gradient descent.

## Repository status

This repository is currently under active development.  The completed layers are:

- gradient preliminaries;
- first-order convex optimality certificates;
- smooth upper-bound interfaces;
- one-step descent estimates for gradient steps.

The projected-gradient convergence theorem is not yet complete.