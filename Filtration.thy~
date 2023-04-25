theory Filtration
imports "HOL-Probability.Stopping_Time" "HOL-Probability.Probability_Measure" Sigma_Utils "HOL-Probability.Conditional_Expectation"
begin

locale filtered_prob_space = prob_space M + filtration "space M" F for M F +
  assumes subalgebra: "\<And>i. F i \<subseteq> M"

locale sigma_finite_filtration = filtration +
  assumes sigma_finite: "\<And>i. sigma_finite_measure (restr_to_subalg M (F i))"

definition natural_filtration :: "'a measure \<Rightarrow> 's measure \<Rightarrow> ('t \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> 't :: {second_countable_topology, linorder_topology} \<Rightarrow> 'a measure" where
  "natural_filtration M N Y = (\<lambda>t. sigma_gen (space M) N {Y i | i. i \<le> t})"

interpretation natural_filtration: filtration "space M" "natural_filtration M N Y"
proof (unfold_locales, goal_cases)
  case (1 i)
  then show ?case by (simp add: natural_filtration_def)
next
  case (2 i j)
  have "{Y ia |ia. ia \<le> i} \<subseteq> {Y ia |ia. ia \<le> j}" using 2 by force
  hence "(\<Union>f\<in>{Y ia |ia. ia \<le> i}. {f -` A \<inter> space M |A. A \<in> sets N}) \<subseteq> (\<Union>f\<in>{Y ia |ia. ia \<le> j}. {f -` A \<inter> space M |A. A \<in> sets N})" by blast
  thus ?case unfolding natural_filtration_def sets_sigma_gen by (rule sigma_sets_subseteq)
qed

end