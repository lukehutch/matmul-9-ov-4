/-
  AxiomAudit.lean

  Exhaustive `#print axioms` verification across every key exported theorem of
  all 5 modules in `MatMul94`. Every theorem must depend ONLY on standard Lean
  foundations `{propext, Classical.choice, Quot.sound}` (or empty `{}`) — ZERO
  `sorryAx`, ZERO `Lean.ofReduceBool`, ZERO `Lean.trustCompiler`, ZERO custom axioms.
-/

import MatMul94

open MatMul94

-- Module 1: Log2Bracket
#print axioms pow10_301_le_pow2_1000
#print axioms pow2_1000_le_pow10_302
#print axioms pow10_1000_le_pow2_3322
#print axioms pow2_3321_le_pow10_1000
#print axioms add_two_pow_lt_eight
#print axioms add_two_div_sub_one_pow_lt_22
#print axioms sixteen_mul_sub_one_pow_le

-- Module 2: LayerConstraints
#print axioms pure_telescoping_zero_gain
#print axioms primal_telescoping_identity
#print axioms gap_window_disjoint
#print axioms effort_surplus_positive
#print axioms same_slot_multi_eps_collision
#print axioms cubic_rate_gap
#print axioms pass_rate_strictly_above_9_4
#print axioms c_min_polynomial_bound
#print axioms cauchy_schwarz_balanced_words
#print axioms lagrange_uncoupling_constraints
#print axioms inner_eta_pole_clearing_necessity
#print axioms openai_5M_tight_eps_deg
#print axioms slabbing_barrier
#print axioms exact_Lk_sandwich
#print axioms pole_cascade_exact
#print axioms multivariate_bini_worse
#print axioms hidden_constant_bounds
#print axioms finite_schonhage

-- Module 3: UniversalBounds
#print axioms universal_round_necessary
#print axioms w18_vk9_lt_Ek4
#print axioms universal_vk_pow_gt_w_pow
#print axioms universal_c_min_all
#print axioms universal_vk_lb_2807
#print axioms universal_vk_lb_2800
#print axioms universal_vk_lb_2695
#print axioms universal_vk_lb_2500
#print axioms universal_vk_lb_2371
#print axioms universal_vk_lb_2321
#print axioms universal_vk_lb_2300
#print axioms universal_vk_lb_2260
#print axioms universal_vk_lb_2251
#print axioms universal_post_bini_lb_2807
#print axioms universal_post_bini_lb_2800
#print axioms universal_post_bini_lb_2695
#print axioms universal_post_bini_lb_2500
#print axioms universal_post_bini_lb_2371
#print axioms universal_post_bini_lb_2321
#print axioms universal_post_bini_lb_2300
#print axioms universal_post_bini_lb_2260
#print axioms universal_post_bini_lb_2251

-- Module 4: ConstructiveWitnesses
#print axioms witness_pre_2800
#print axioms witness_pre_2695
#print axioms witness_pre_2500
#print axioms witness_pre_2371
#print axioms witness_pre_2321
#print axioms witness_pre_2300
#print axioms witness_pre_2260
#print axioms witness_pre_2251
#print axioms witness_post_2800
#print axioms witness_post_2695
#print axioms witness_post_2500
#print axioms witness_post_2371
#print axioms witness_post_2321
#print axioms witness_post_2300
#print axioms witness_post_2260
#print axioms witness_post_2251
#print axioms natChoose_central_bounds
#print axioms witness_str3_direct_sum_2807
#print axioms witness_str3_single_matrix_2807
#print axioms witness_str3_single_matrix_2500
#print axioms witness_str3_single_matrix_2371

-- Module 5: GeneralLimits
#print axioms remark45_universal_round_necessary
#print axioms remark45_universal_vk_pow_gt_w_pow
#print axioms general_bini_deg_horizon
#print axioms counterexample_strassen_1969
#print axioms counterexample_pan_1978
#print axioms counterexample_str3_beats_pass_2807
#print axioms counterexample_str3_beats_pass_2500
#print axioms counterexample_str3_beats_pass_2371
#print axioms supermultiplicative_bound_le_9_4
#print axioms bernoulli_add_one_lt_two
#print axioms small_V_consistent_with_9_4_general
#print axioms small_V_16_witness_2251
#print axioms exact_V_16_witness_9_4
