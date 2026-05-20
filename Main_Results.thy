theory Main_Results
  imports Examples_Quadratic
begin

section \<open>Main reusable theorem interface\<close>

text \<open>
This theory collects the main reusable facts of the entry.  It is intended as
a stable public theorem surface for users who want to import the development
without searching through the internal proof files.
\<close>

subsection \<open>Gradient interfaces\<close>

lemmas gradient_pointwise_interface =
  has_gradientI
  has_gradientD
  has_gradient_unique
  gradient_eqI
  has_gradient_gradient

lemmas gradient_field_interface =
  has_gradient_onD
  has_gradient_within_onD
  has_gradient_on_subset

lemmas gradient_rule_interface =
  has_gradient_const
  has_gradient_add
  has_gradient_minus
  has_gradient_diff
  has_gradient_scale_const
  has_gradient_mult
  has_gradient_inner_left
  has_gradient_inner_right

subsection \<open>Convex first-order certificates\<close>

lemmas global_min_interface =
  global_min_onI
  global_min_onD_mem
  global_min_onD

lemmas first_order_condition_interface =
  first_order_condition_atI
  first_order_condition_atD_mem
  first_order_condition_atD

lemmas convex_first_order_results =
  convex_has_gradient_supports
  convex_differentiable_on_imp_gradient_lower_bound_on
  convex_differentiable_on_supporting_hyperplanes
  convex_differentiable_on_first_order_sufficient

subsection \<open>Smooth convex interfaces and descent lemmas\<close>

lemmas smooth_upper_bound_interface =
  smooth_upper_bound_onI
  smooth_upper_bound_onD_nonneg
  smooth_upper_bound_onD
  smooth_upper_bound_on_subset
  smooth_upper_bound_on_mono_L

lemmas smooth_convex_interface =
  smooth_convex_onI
  smooth_convex_onD_convex_differentiable
  smooth_convex_onD_smooth_upper_bound
  smooth_convex_onD_convex_on
  smooth_convex_onD_has_gradient_on
  smooth_convex_on_subset

lemmas gradient_step_interface =
  gradient_step_diff
  gradient_step_inner
  gradient_step_norm_sq

lemmas gradient_step_descent_results =
  smooth_upper_bound_gradient_step
  smooth_upper_bound_gradient_step_decrease
  smooth_upper_bound_gradient_step_decrease_inverse_L

subsection \<open>Abstract descent and telescoping\<close>

lemmas abstract_descent_results =
  sum_progress_le_initial_gap
  sum_progress_le_initial_minus_lower_bound
  exists_le_average_of_sum_bound
  exists_le_average_of_nonnegative_sum
  sequence_linear_rate_from_step

subsection \<open>Gradient descent\<close>

lemmas gradient_descent_iteration_interface =
  gradient_descent_iteratesI
  gradient_descent_iteratesD
  gradient_descent_iteratesE
  feasible_iteratesI
  feasible_iteratesD
  feasible_iterates_subset

lemmas gradient_descent_one_step_results =
  gradient_descent_one_step_bound
  gradient_descent_one_step_decrease
  gradient_descent_objective_mono_step
  gradient_descent_objective_nonincreasing
  gradient_descent_step_progress

lemmas gradient_descent_rate_results =
  gradient_descent_sum_weighted_gradient_norm_sq_bound
  gradient_descent_sum_gradient_norm_sq_bound
  gradient_descent_average_gradient_norm_sq_bound
  gradient_descent_exists_small_gradient_norm_sq
  gradient_descent_exists_small_weighted_gradient_norm_sq

lemmas gradient_descent_convergence_results =
  gradient_descent_one_step_distance_bound_to_point
  gradient_descent_one_step_distance_bound_to_minimizer
  gradient_descent_sum_function_value_gaps_bound_to_point
  gradient_descent_sum_function_value_gaps_bound_to_minimizer
  gradient_descent_last_gap_times_N_bound
  gradient_descent_function_value_gap_bound

subsection \<open>Projection geometry\<close>

lemmas projection_geometry_results =
  projection_variational_inequality
  three_point_inner_identity
  projected_gradient_inner_bound_from_vi

subsection \<open>Projected gradient steps\<close>

lemmas projected_gradient_step_interface =
  projected_gradient_step_in_set
  projected_gradient_step_in_set_if_base_mem
  projected_gradient_step_variational_inequality
  projected_gradient_inner_bound

lemmas projected_gradient_step_descent_results =
  projected_gradient_one_step_distance_bound_to_point
  projected_gradient_one_step_distance_bound_to_minimizer

subsection \<open>Projected gradient descent\<close>

lemmas projected_gradient_descent_iteration_interface =
  projected_gradient_descent_iteratesI
  projected_gradient_descent_iteratesD
  projected_gradient_descent_iteratesE
  projected_gradient_descent_next_mem
  projected_gradient_descent_feasible_from_initial

lemmas projected_gradient_descent_one_step_results =
  projected_gradient_descent_one_step_distance_bound_to_point
  projected_gradient_descent_one_step_distance_bound_to_minimizer
  projected_gradient_descent_objective_nonincreasing

lemmas projected_gradient_descent_convergence_results =
  projected_gradient_descent_sum_function_value_gaps_bound_to_point
  projected_gradient_descent_sum_function_value_gaps_bound_to_minimizer
  projected_gradient_descent_last_gap_times_N_bound
  projected_gradient_descent_function_value_gap_bound_feasible
  projected_gradient_descent_function_value_gap_bound

subsection \<open>Projected-gradient mappings\<close>

lemmas projected_gradient_mapping_interface =
  projected_gradient_mapping_step_relation
  projected_gradient_step_eq_sub_mapping
  projected_gradient_mapping_zero_iff_fixed_point
  gradient_step_minus_projected_gradient_step_eq_mapping_residual
  projected_gradient_mapping_variational_inequality

lemmas projected_gradient_mapping_optimality_results =
  projected_gradient_fixed_point_iff_first_order_condition
  projected_gradient_mapping_zero_iff_first_order_condition
  projected_gradient_fixed_point_imp_global_min_on
  projected_gradient_mapping_zero_imp_global_min_on
  first_order_condition_imp_global_min_on_smooth_convex

subsection \<open>Strong convexity\<close>

lemmas strong_convex_interface =
  strong_convex_lower_bound_onI
  strong_convex_lower_bound_onD_nonneg
  strong_convex_lower_bound_onD
  strong_convex_lower_bound_on_subset
  strong_convex_lower_bound_on_mono_mu

lemmas strongly_convex_interface =
  strongly_convex_differentiable_onI
  strongly_convex_differentiable_onD_convex_differentiable
  strongly_convex_differentiable_onD_strong
  strongly_smooth_convex_onI
  strongly_smooth_convex_onD_smooth
  strongly_smooth_convex_onD_strong

lemmas strong_convex_optimality_results =
  convex_differentiable_on_global_min_imp_first_order_condition
  strong_convex_foc_distance_gap
  strongly_convex_global_min_distance_gap
  strongly_smooth_convex_global_min_distance_gap
  strongly_convex_global_min_unique
  strongly_smooth_convex_global_min_unique
  strongly_smooth_projected_mapping_zero_distance_gap
  strongly_smooth_projected_mapping_zero_unique_global_min

subsection \<open>Linear convergence for projected gradient descent\<close>

lemmas projected_gradient_linear_rate_factor_results =
  projected_gradient_linear_rate_denominator_pos
  projected_gradient_linear_rate_factor_nonnegative
  projected_gradient_linear_rate_factor_positive
  projected_gradient_linear_rate_factor_le_one
  projected_gradient_linear_rate_factor_lt_one

lemmas projected_gradient_descent_linear_rate_results =
  projected_gradient_descent_strong_one_step_distance_contract
  projected_gradient_descent_strong_one_step_distance_contract_factor
  projected_gradient_descent_distance_sq_linear_rate
  projected_gradient_descent_function_value_linear_rate_Suc
  projected_gradient_descent_function_value_linear_rate
  projected_gradient_descent_strict_rate_factor

subsection \<open>Lipschitz smoothness interface\<close>

lemmas lipschitz_smoothness_interface =
  line_descent_bound_onI
  line_descent_bound_onD_nonneg
  line_descent_bound_onD
  line_descent_bound_on_imp_smooth_upper_bound_on
  smooth_upper_bound_on_imp_line_descent_bound_on
  line_descent_bound_on_iff_smooth_upper_bound_on
  lipschitz_smooth_onI
  lipschitz_smooth_onD_has_gradient_on
  lipschitz_smooth_onD_lipschitz_gradient
  lipschitz_smooth_onD_line_descent
  lipschitz_smooth_onD_smooth_upper_bound
  lipschitz_smooth_convex_onI
  lipschitz_smooth_convex_on_imp_smooth_convex_on
  smooth_convex_on_and_lipschitz_gradient_imp_lipschitz_smooth_convex_on

subsection \<open>Quadratic examples\<close>

lemmas quadratic_real_example_results =
  quadratic_real_has_gradient
  quadratic_real_has_gradient_on_UNIV
  quadratic_real_convex_on_UNIV
  quadratic_real_convex_differentiable_on_UNIV
  quadratic_real_smooth_upper_bound_on_UNIV
  quadratic_real_lipschitz_gradient_on_UNIV
  quadratic_real_smooth_convex_on_UNIV
  quadratic_real_lipschitz_smooth_on_UNIV
  quadratic_real_lipschitz_smooth_convex_on_UNIV
  quadratic_real_strong_lower_bound_on_UNIV
  quadratic_real_strongly_smooth_convex_on_UNIV
  quadratic_real_global_min_on_zero

text \<open>
The most commonly cited top-level convergence theorems are:

  \<^enum> @{thm gradient_descent_function_value_gap_bound}
  \<^enum> @{thm projected_gradient_descent_function_value_gap_bound}
  \<^enum> @{thm projected_gradient_mapping_zero_iff_first_order_condition}
  \<^enum> @{thm projected_gradient_mapping_zero_imp_global_min_on}
  \<^enum> @{thm strongly_smooth_convex_global_min_distance_gap}
  \<^enum> @{thm projected_gradient_descent_distance_sq_linear_rate}
  \<^enum> @{thm projected_gradient_descent_function_value_linear_rate}
\<close>

end