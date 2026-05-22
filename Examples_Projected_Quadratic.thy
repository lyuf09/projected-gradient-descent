theory Examples_Projected_Quadratic
  imports
    Examples_Quadratic
    Projected_Gradient_Descent_Residual_Convergence
begin

section \<open>Projected quadratic examples\<close>

text \<open>
This theory gives concrete constrained examples for the projected-gradient
descent library.

The objective is the one-dimensional quadratic f x = x^2 / 2 with gradient
field G x = x.  The previous example theory instantiated the smoothness,
convexity, and strong-convexity interfaces for this objective.  Here we use
those facts to instantiate the projected-gradient mapping residual bounds and
the finite-horizon epsilon-stationarity certificates.
\<close>


subsection \<open>A reusable constrained quadratic template\<close>

text \<open>
The first group of lemmas works for any closed convex feasible set containing
the unconstrained minimizer 0.  This gives a small reusable template for
instantiating the abstract projected-gradient descent theorems on concrete
quadratic constrained problems.
\<close>

lemma quadratic_real_projected_gradient_descent_exists_small_residual_sq:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq C alpha quadratic_real_gradient (x n)
        \<le> (2 / (alpha * real N)) * quadratic_real (x 0)"
proof -
  have smooth: "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real 0"
    by (rule quadratic_real_global_min_on_zero[OF zero_mem])

  have step_size': "alpha * 1 \<le> 1"
    using step_size by simp

  have result:
    "\<exists>n<N.
      projected_gradient_residual_sq C alpha quadratic_real_gradient (x n)
        \<le> (2 / (alpha * real N)) * (quadratic_real (x 0) - quadratic_real 0)"
    by (rule projected_gradient_descent_exists_small_residual_sq_to_minimizer[
      OF smooth closed convex pgd x0_mem alpha_pos step_size' minimizer N_pos])

  then show ?thesis
    by simp
qed

lemma quadratic_real_projected_gradient_descent_exists_epsilon_residual:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha quadratic_real_gradient (x n) \<le> eps"
proof -
  have smooth: "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real 0"
    by (rule quadratic_real_global_min_on_zero[OF zero_mem])

  have step_size': "alpha * 1 \<le> 1"
    using step_size by simp

  have horizon':
    "2 * (quadratic_real (x 0) - quadratic_real 0)
      \<le> alpha * real N * eps ^ 2"
    using horizon by simp

  show ?thesis
    by (rule projected_gradient_descent_exists_epsilon_residual_to_minimizer_product[
      OF smooth closed convex pgd x0_mem alpha_pos step_size' minimizer
         N_pos eps_pos horizon'])
qed

lemma quadratic_real_projected_gradient_residual_zero_imp_zero:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual C alpha quadratic_real_gradient x = 0"
  shows "x = 0"
proof -
  have smooth: "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real x"
    by (rule projected_gradient_residual_zero_imp_global_min_on[
      OF smooth closed convex x_mem alpha_pos zero])

  show "x = 0"
    by (rule quadratic_real_unique_global_min_on[
      OF convex zero_mem minimizer])
qed


subsection \<open>The nonnegative half-line\<close>

text \<open>
We now specialize the previous template to the concrete closed convex feasible
set [0,\<infinity>).  This is a simple constrained problem whose minimizer lies on the
feasible set and whose projected-gradient residual certificates follow directly
from the abstract theory.
\<close>

definition nonnegative_real :: "real set"
where
  "nonnegative_real = {0..}"

lemma nonnegative_real_iff [simp]:
  "x \<in> nonnegative_real \<longleftrightarrow> 0 \<le> x"
  unfolding nonnegative_real_def by simp

lemma zero_mem_nonnegative_real [simp]:
  "0 \<in> nonnegative_real"
  unfolding nonnegative_real_def by simp

lemma closed_nonnegative_real:
  "closed nonnegative_real"
  unfolding nonnegative_real_def by simp

lemma convex_nonnegative_real:
  "convex nonnegative_real"
  unfolding nonnegative_real_def by simp

lemma quadratic_real_smooth_convex_on_nonnegative:
  "smooth_convex_on 1 nonnegative_real quadratic_real quadratic_real_gradient"
  by (rule quadratic_real_smooth_convex_on[OF convex_nonnegative_real])

lemma quadratic_real_strongly_smooth_convex_on_nonnegative:
  "strongly_smooth_convex_on 1 1 nonnegative_real
    quadratic_real quadratic_real_gradient"
  by (rule quadratic_real_strongly_smooth_convex_on[OF convex_nonnegative_real])

lemma quadratic_real_global_min_on_nonnegative_zero:
  "global_min_on nonnegative_real quadratic_real 0"
  by (rule quadratic_real_global_min_on_zero) simp

lemma quadratic_real_unique_global_min_on_nonnegative:
  assumes minimizer: "global_min_on nonnegative_real quadratic_real x"
  shows "x = 0"
  by (rule quadratic_real_unique_global_min_on[
    OF convex_nonnegative_real zero_mem_nonnegative_real minimizer])


subsection \<open>Projected-gradient step on the nonnegative half-line\<close>

text \<open>
The projected-gradient step for the quadratic objective can be unfolded to the
projection of the scalar point (1 - alpha) * x onto the half-line.  We do not
need a closed-form formula for this projection in order to instantiate the
convergence theory.
\<close>

lemma nonnegative_quadratic_projected_gradient_step_unfold:
  "projected_gradient_step nonnegative_real alpha quadratic_real_gradient x =
    closest_point nonnegative_real ((1 - alpha) * x)"
  unfolding projected_gradient_step_def gradient_step_def quadratic_real_gradient_def
  by (simp add: algebra_simps)

lemma nonnegative_quadratic_projected_gradient_mapping_unfold:
  "projected_gradient_mapping nonnegative_real alpha quadratic_real_gradient x =
    (1 / alpha) * (x - closest_point nonnegative_real ((1 - alpha) * x))"
  unfolding projected_gradient_mapping_def
  by (simp add: nonnegative_quadratic_projected_gradient_step_unfold)

lemma nonnegative_quadratic_projected_gradient_residual_unfold:
  "projected_gradient_residual nonnegative_real alpha quadratic_real_gradient x =
    norm ((1 / alpha) * (x - closest_point nonnegative_real ((1 - alpha) * x)))"
  unfolding projected_gradient_residual_def
  by (simp add: nonnegative_quadratic_projected_gradient_mapping_unfold)

lemma nonnegative_quadratic_projected_gradient_residual_sq_unfold:
  "projected_gradient_residual_sq nonnegative_real alpha quadratic_real_gradient x =
    norm ((1 / alpha) * (x - closest_point nonnegative_real ((1 - alpha) * x))) ^ 2"
  unfolding projected_gradient_residual_sq_def
  by (simp add: nonnegative_quadratic_projected_gradient_mapping_unfold)


subsection \<open>Function-value convergence on the half-line\<close>

lemma nonnegative_quadratic_projected_gradient_descent_function_value_gap_bound:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "quadratic_real (x N)
      \<le> norm (x 0) ^ 2 / (2 * alpha * real N)"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_function_value_gap_bound_simplified[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size N_pos])
qed

lemma nonnegative_quadratic_projected_gradient_descent_distance_linear_rate:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
  shows
    "norm (x N) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha 1 ^ N * norm (x 0) ^ 2"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_distance_linear_rate_simplified[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size])
qed


subsection \<open>Projected-gradient residual bounds on the half-line\<close>

lemma nonnegative_quadratic_projected_gradient_descent_exists_small_residual_sq:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq nonnegative_real alpha
        quadratic_real_gradient (x n)
        \<le> (2 / (alpha * real N)) * quadratic_real (x 0)"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_exists_small_residual_sq[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size N_pos])
qed

lemma nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N.
      projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient (x n) \<le> eps"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_exists_epsilon_residual[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size N_pos eps_pos horizon])
qed

lemma nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual_product_form:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "quadratic_real (x 0) \<le> (alpha * real N * eps ^ 2) / 2"
  shows
    "\<exists>n<N.
      projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient (x n) \<le> eps"
proof -
  have horizon':
    "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
    using horizon by simp

  show ?thesis
    by (rule nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual[
      OF pgd x0_nonneg alpha_pos step_size N_pos eps_pos horizon'])
qed


subsection \<open>Residual-zero certificate on the half-line\<close>

lemma nonnegative_quadratic_projected_gradient_residual_zero_imp_zero:
  assumes x_nonneg: "0 \<le> x"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient x = 0"
  shows "x = 0"
proof -
  have x_mem: "x \<in> nonnegative_real"
    using x_nonneg by simp

  show "x = 0"
    by (rule quadratic_real_projected_gradient_residual_zero_imp_zero[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         x_mem alpha_pos zero])
qed

lemma nonnegative_quadratic_projected_gradient_residual_zero_imp_global_min:
  assumes x_nonneg: "0 \<le> x"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient x = 0"
  shows "global_min_on nonnegative_real quadratic_real x"
proof -
  have x_mem: "x \<in> nonnegative_real"
    using x_nonneg by simp

  show ?thesis
    by (rule projected_gradient_residual_zero_imp_global_min_on[
      OF quadratic_real_smooth_convex_on_nonnegative
         closed_nonnegative_real convex_nonnegative_real
         x_mem alpha_pos zero])
qed


text \<open>
The most important concrete consequences in this file are:
  @{thm nonnegative_quadratic_projected_gradient_descent_function_value_gap_bound},
  @{thm nonnegative_quadratic_projected_gradient_descent_exists_small_residual_sq},
  @{thm nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual},
  and
  @{thm nonnegative_quadratic_projected_gradient_residual_zero_imp_zero}.

Together, they show that the abstract projected-gradient convergence and
residual-stationarity theorems can be instantiated on a simple constrained
smooth strongly convex quadratic problem.
\<close>

end