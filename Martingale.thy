theory Martingale
  imports Filtration Banach_Conditional_Expectation
begin

locale stochastic_process = sigma_finite_measure M for M +
  fixes X :: "'t :: {second_countable_topology,linorder_topology} \<Rightarrow> 'a \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}"
  assumes random_variable[measurable]: "\<And>i. X i \<in> borel_measurable M"

locale adapted_process = filtered_sigma_finite_measure M F + stochastic_process M X for M F X +
  assumes adapted[measurable]: "\<And>i. (X i) \<in> borel_measurable (F i)"

locale martingale = adapted_process M F X for M F and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, banach}" +
  assumes integrable: "\<And>i. integrable M (X i)"
      and martingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>"

locale martingale_preorder = martingale M F X for M F and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, preorder, banach}"

locale submartingale = adapted_process M F "X :: _ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, preorder, banach}" for M F X +
  assumes integrable: "\<And>i. integrable M (X i)"
      and submartingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>"

locale supermartingale = adapted_process M F "X :: _ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, preorder, banach}" for M F X +
  assumes integrable: "\<And>i. integrable M (X i)"
      and supermartingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>"

sublocale martingale_preorder \<subseteq> submartingale using martingale_property by (unfold_locales) (force simp add: integrable)+

sublocale martingale_preorder \<subseteq> supermartingale using martingale_property by (unfold_locales) (force simp add: integrable)+

lemma (in filtered_sigma_finite_measure) martingale_const:  
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f" "f \<in> borel_measurable (F bot)"
  shows "martingale M F (\<lambda>_. f)"
proof (unfold_locales, goal_cases)
  case (1 i)
  then show ?case using assms by (simp add: borel_measurable_integrable)
next
  case (2 i)
  then show ?case using assms by (metis bot.extremum measurable_from_subalg sets_F_mono space_F subalgebra_def)
next
  case (3 i)
  then show ?case using assms by blast
next
  case (4 i j)
  then show ?case using cond_exp_F_meas[OF assms(1), THEN AE_symmetric] assms by (metis (mono_tags, lifting) borel_measurable_subalgebra bot_least filtration.sets_F_mono filtration_axioms space_F)
qed 

lemma (in martingale) martingale_set_integral:
  assumes "A \<in> F i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)"
proof -
  have "\<integral>x \<in> A. X i x \<partial>M = \<integral>x \<in> A. cond_exp M (F i) (X j) x \<partial>M" using martingale_property[OF assms(2)] borel_measurable_cond_exp' assms(1) subalgebra subalgebra_def by (intro set_lebesgue_integral_cong_AE[OF _ random_variable]) fastforce+
  also have "... = \<integral>x \<in> A. X j x \<partial>M" using assms(1) by (auto simp: integrable intro: cond_exp_set_integral[symmetric])
  finally show ?thesis .
qed

lemma (in martingale) martingale_const_scaleR:
  shows "martingale M F (\<lambda>i x. c *\<^sub>R X i x)"
proof -
  {
    fix i j :: 'b assume "i \<le> j"
    hence "AE x in M. c *\<^sub>R X i x = cond_exp M (F i) (\<lambda>x. c *\<^sub>R X j x) x" using cond_exp_scaleR_right[OF integrable, of i c, THEN AE_symmetric] martingale_property by force
  }
  thus ?thesis by (unfold_locales) (auto simp add: borel_measurable_const_scaleR adapted random_variable integrable)
qed

lemma (in martingale) martingale_uminus:
  shows "martingale M F (- X)" 
  using martingale_const_scaleR[of "-1"] by (force intro: back_subst[of "martingale M F"])


(* The following locale is created to simplify proofs *)
locale\<^marker>\<open>tag unimportant\<close> binop_martingale = m1: martingale M F X + m2?: martingale M F Y for M F and X Y :: "_ \<Rightarrow> _ \<Rightarrow> 'c :: {second_countable_topology, banach}"
begin

lemma martingale_add:
  shows "martingale M F (\<lambda>i x. X i x + Y i x)"

  


end