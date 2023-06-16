theory Filtration
imports "HOL-Probability.Probability" Sigma_Utils
begin

locale filtered_sigma_finite_measure = sigma_finite_measure M + filtration "space M" F for M and F :: "'t:: {second_countable_topology, linorder_topology, order_bot} \<Rightarrow> 'a measure" +
  assumes subalgebra: "\<And>i. subalgebra M (F i)"
      and sigma_finite: "sigma_finite_measure (restr_to_subalg M (F bot))"

sublocale filtered_sigma_finite_measure \<subseteq> sigma_finite_subalgebra M "F i" by (metis bot.extremum sigma_finite sigma_finite_subalgebra.intro subalgebra sets_F_mono sigma_finite_subalgebra.nested_subalg_is_sigma_finite subalgebra_def)

definition natural_filtration :: "'a measure \<Rightarrow> 's measure \<Rightarrow> ('t \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> 't :: {second_countable_topology, linorder_topology, order_bot} \<Rightarrow> 'a measure" where
  "natural_filtration M N Y = (\<lambda>t. restr_to_subalg M (sigma_gen (space M) N {Y i | i. i \<le> t}))"

lemma 
  assumes "\<And>i. Y i \<in> M \<rightarrow>\<^sub>M N"
  shows sets_natural_filtration[simp]: "sets (natural_filtration M N Y t) = sigma_sets (space M) (\<Union>i \<le> t. {Y i -` A \<inter> space M | A. A \<in> N})" 
    and space_natural_filtration[simp]: "space (natural_filtration M N Y t) = space M"
  by (standard; (subst natural_filtration_def, subst sets_restr_to_subalg)) (auto simp add: natural_filtration_def space_restr_to_subalg subalgebra_def intro!: sets.sigma_sets_subset measurable_sets[OF assms] sigma_sets_mono)



end