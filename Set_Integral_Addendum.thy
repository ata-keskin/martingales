theory Set_Integral_Addendum
  imports "HOL-Analysis.Set_Integral" Bochner_Integration_Addendum
  begin

lemma set_integral_scaleR_left: 
  assumes "A \<in> sets M" "c \<noteq> 0 \<Longrightarrow> integrable M f"
  shows "LINT t:A|M. f t *\<^sub>R c = (LINT t:A|M. f t) *\<^sub>R c"
  unfolding set_lebesgue_integral_def 
  using integrable_mult_indicator[OF assms]
  by (subst integral_scaleR_left[symmetric], auto)

lemma nn_set_integral_eq_set_integral:
  assumes [measurable]:"integrable M f"
      and "AE x \<in> A in M. 0 \<le> f x" "A \<in> sets M"
    shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = (\<integral> x \<in> A. f x \<partial>M)"
proof-
  have "(\<integral>\<^sup>+x. indicator A x *\<^sub>R f x \<partial>M) = (\<integral> x \<in> A. f x \<partial>M)"
  unfolding set_lebesgue_integral_def using assms(2) by (intro nn_integral_eq_integral[of _ "\<lambda>x. indicat_real A x *\<^sub>R f x"], blast intro: assms integrable_mult_indicator, fastforce)
  moreover have "(\<integral>\<^sup>+x. indicator A x *\<^sub>R f x \<partial>M) = (\<integral>\<^sup>+x\<in>A. f x \<partial>M)"  by (metis ennreal_0 indicator_simps(1) indicator_simps(2) mult.commute mult_1 mult_zero_left real_scaleR_def)
  ultimately show ?thesis by argo
qed

lemma set_integral_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "set_lebesgue_integral (restrict_space M \<Omega>) A f = set_lebesgue_integral M A (\<lambda>x. indicator \<Omega> x *\<^sub>R f x)"
  unfolding set_lebesgue_integral_def 
  by (subst integral_restrict_space, auto intro!: integrable_mult_indicator assms simp: mult.commute)

lemma set_integral_const:
  fixes c :: "'b::{banach, second_countable_topology}"
  assumes "A \<in> sets M" "emeasure M A \<noteq> \<infinity>"
  shows "set_lebesgue_integral M A (\<lambda>_. c) = measure M A *\<^sub>R c"
  unfolding set_lebesgue_integral_def 
  using assms by (metis has_bochner_integral_indicator has_bochner_integral_integral_eq infinity_ennreal_def less_top)

lemma set_integral_mono_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
  using assms unfolding set_integrable_def set_lebesgue_integral_def
  by (auto intro: integral_mono_banach split: split_indicator)

lemma set_integral_mono_AE_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "set_integrable M A f" "set_integrable M A g" "AE x\<in>A in M. f x \<le> g x"
  shows "set_lebesgue_integral M A f \<le> set_lebesgue_integral M A g" using assms unfolding set_lebesgue_integral_def by (auto simp add: set_integrable_def intro!: integral_mono_AE_banach[of M "\<lambda>x. indicator A x *\<^sub>R f x" "\<lambda>x. indicator A x *\<^sub>R g x"], simp add: indicator_def)

end