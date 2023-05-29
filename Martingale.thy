theory Martingale          
  imports Filtration Banach_Conditional_Expectation
begin

locale stochastic_process = prob_space M for M +
  fixes X :: "'t :: {second_countable_topology,linorder_topology} \<Rightarrow> 'a \<Rightarrow> 'b :: topological_space"
  assumes random_variable[measurable]: "\<And>i. X i \<in> borel_measurable M"

sublocale stochastic_process \<subseteq> natural_filtration: filtered_prob_space M "natural_filtration M borel X"
proof (unfold_locales, goal_cases)
  case (1 i)
  have "{X ia |ia. ia \<le> i} \<subseteq> borel_measurable M" using random_variable by blast
  thus ?case unfolding natural_filtration_def using measurable_iff_contains_sigma_gen' by meson
qed

locale adapted_process = filtered_prob_space M F + stochastic_process M X for M F X +
  assumes adapted[measurable]: "\<And>i. (X i) \<in> borel_measurable (F i)"

sublocale stochastic_process \<subseteq> natural_filtration: adapted_process M "natural_filtration M borel X"
  using measurable_space[OF random_variable]
  by (unfold_locales, subst natural_filtration_def, intro measurable_sigma_gen, auto)

locale martingale = adapted_process M F X for M F X +
  assumes integrable: "\<And>i. integrable M (X i)"
      and martingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>"

locale submartingale = adapted_process M F "X :: _ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, preorder, real_normed_vector}" for M F X +
  assumes integrable: "\<And>i. integrable M (X i)"
      and submartingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>"

locale supermartingale = adapted_process M F "X :: _ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, preorder, real_normed_vector}" for M F X +
  assumes integrable: "\<And>i. integrable M (X i)"
      and supermartingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>"

lemma (in sigma_finite_filtered_prob_space) martingale_const:
  shows "martingale M F (\<lambda>_ _. c)"
  using sgf.cond_exp_indicator
AE_symmetric[OF ]
  apply (unfold_locales)
     apply (auto simp add: measurable_const space_F subalgebra subalgebra_def intro!: )


lemma (in filtered_prob_space) martingale_const_fun:
  assumes "\<And>i. f \<in> borel_measurable (F i)" "integrable M f"
  shows "martingale M F (\<lambda>_. f)"
  using assms borel_measurable_integrable
  apply (unfold_locales) 
  apply (auto simp add: measurable_const space_F subalgebra subalgebra_def)
  
lemma (in martingale) martingale_set_integral:
  assumes "A \<in> F i" "i \<le> j"
  shows "\<integral> x \<in> A. X i x \<partial>M = \<integral> x \<in> A. X j x \<partial>M"
proof -
  have "\<integral>x \<in> A. X i x \<partial>M = \<integral>x \<in> A. cond_exp M (F i) (X j) x \<partial>M"
    using martingale_property[OF assms(2)]
    by (intro set_lebesgue_integral_cong_AE[OF subalgebra[THEN subsetD], OF assms(1) random_variable cond_exp.measurable, OF _ integrable])
       (auto simp add: subalgebra space_F subalgebra_def)
  also have "... = \<integral>x \<in> A. X j x \<partial>M" 
    using assms
    by (intro cond_exp.set_integral[OF _ integrable, symmetric]) (auto simp add: subalgebra space_F subalgebra_def)
  finally show ?thesis .
qed 

lemma (in filtered_prob_space) martingale_cond_exp:
  assumes "integrable M X"
  shows "martingale M F (\<lambda>i. cond_exp M (F i) X)"
proof (unfold_locales, goal_cases)
  case (1 i)
  then show ?case using assms by (intro cond_exp.measurable, auto simp add: subalgebra space_F subalgebra_def)
next
  case (2 i)
  then show ?case using assms by (intro cond_exp.measurable', auto simp add: subalgebra space_F subalgebra_def)
next
  case (3 i)
  then show ?case using assms by (intro cond_exp.integrable, auto simp add: subalgebra space_F subalgebra_def)
next
  case (4 i j)
  have "set_lebesgue_integral M A (cond_exp M (F j) X) = set_lebesgue_integral M A (cond_exp M (F i) X)" if "A \<in> F i" for A
    using cond_exp.set_integral[of "F i" X A] cond_exp.set_integral[of "F j" X A] assms that sets_F_mono[OF 4] 
    by (fastforce simp add: subalgebra space_F subalgebra_def)
  then show ?case by (intro AE_symmetric[OF cond_exp.characterization], (fastforce simp add: assms subalgebra space_F subalgebra_def intro!: cond_exp.integrable cond_exp.measurable')+)
qed

(* This does not work, why?

sublocale filtered_prob_space \<subseteq> martingale M F "(\<lambda>i. cond_exp M (F i) X)"
proof -
  show "martingale M F (\<lambda>i. cond_exp M (F i) X)" sorry
qed

*)

lemma martingale_is_submartingale:
  assumes "martingale M F (X :: _ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, preorder, real_normed_vector})"
  shows "submartingale M F X"
  using assms
  apply (intro_locales)
  sorry


end