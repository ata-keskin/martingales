theory Conditional_Expectation_Banach                                                                            
imports "HOL-Probability.Conditional_Expectation" Sigma_Finite_Measure_Addendum Bochner_Integration_Addendum Elementary_Metric_Spaces_Addendum
begin                                           

definition has_cond_exp :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}) \<Rightarrow> bool" where 
  "has_cond_exp M F f g = ((\<forall>A \<in> sets F. (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M))
                        \<and> integrable M f 
                        \<and> integrable M g 
                        \<and> g \<in> borel_measurable F)"

lemma has_cond_expI'[intro]:
  assumes "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M)"
          "integrable M f"
          "integrable M g"
          "g \<in> borel_measurable F"
  shows "has_cond_exp M F f g"
  using assms unfolding has_cond_exp_def by simp

lemma has_cond_expD:
  assumes "has_cond_exp M F f g"
  shows "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M)"
        "integrable M f"
        "integrable M g"
        "g \<in> borel_measurable F"
  using assms unfolding has_cond_exp_def by simp+

(* This definition provides the conditional expectation function cond_exp for a given function f with respect to measures M and F. 
It uses the Hilbert choice operator (SOME) to select a suitable function g that satisfies the properties of conditional expectation. 
If no such g exists, it returns the zero function. *)

definition cond_exp :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{banach, second_countable_topology})" where
  "cond_exp M F f = (if \<exists>g. has_cond_exp M F f g then (SOME g. has_cond_exp M F f g) else (\<lambda>_. 0))"

lemma borel_measurable_cond_exp[measurable]: "cond_exp M F f \<in> borel_measurable F" 
  by (metis cond_exp_def someI has_cond_exp_def borel_measurable_const)

lemma integrable_cond_exp[intro]: "integrable M (cond_exp M F f)" 
  by (metis cond_exp_def has_cond_expD(3) integrable_zero someI)

lemma set_integrable_cond_exp[intro]:
  assumes "A \<in> sets M"
shows "set_integrable M A (cond_exp M F f)" using integrable_mult_indicator[OF assms integrable_cond_exp, of F f] by (auto simp add: set_integrable_def intro!: integrable_mult_indicator[OF assms integrable_cond_exp])

context sigma_finite_subalgebra
begin

lemma borel_measurable_cond_exp'[measurable]: "cond_exp M F f \<in> borel_measurable M"
  by (metis cond_exp_def someI has_cond_exp_def borel_measurable_const subalg measurable_from_subalg)

lemma cond_exp_null: 
  assumes "\<nexists>g. has_cond_exp M F f g" 
  shows "cond_exp M F f = (\<lambda>_. 0)"
  unfolding cond_exp_def using assms by argo

lemma has_cond_exp_charact:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "has_cond_exp M F f g"
  shows "has_cond_exp M F f (cond_exp M F f)"
        "AE x in M. cond_exp M F f x = g x"
proof -
  show cond_exp: "has_cond_exp M F f (cond_exp M F f)" using assms someI cond_exp_def by metis
  let ?MF = "restr_to_subalg M F"
  interpret sigma_finite_measure ?MF by (rule sigma_fin_subalg)
  {
    fix A assume "A \<in> sets ?MF"
    then have [measurable]: "A \<in> sets F" using sets_restr_to_subalg[OF subalg] by simp
    have "(\<integral>x \<in> A. g x \<partial>?MF) = (\<integral>x \<in> A. g x \<partial>M)" using assms subalg by (auto simp add: integral_subalgebra2 set_lebesgue_integral_def dest!: has_cond_expD)
    also have "... = (\<integral>x \<in> A. cond_exp M F f x \<partial>M)" using assms cond_exp by (simp add: has_cond_exp_def)
    also have "... = (\<integral>x \<in> A. cond_exp M F f x \<partial>?MF)" using subalg by (auto simp add: integral_subalgebra2 set_lebesgue_integral_def)
    finally have "(\<integral>x \<in> A. g x \<partial>?MF) = (\<integral>x \<in> A. cond_exp M F f x \<partial>?MF)" by simp
  }
  hence "AE x in ?MF. cond_exp M F f x = g x" using cond_exp assms subalg by (intro density_unique, auto dest: has_cond_expD intro!: integrable_in_subalg)
  then show "AE x in M. cond_exp M F f x = g x" using AE_restr_to_subalg[OF subalg] by simp
qed

lemma cond_exp_F_meas[intro, simp]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
          "f \<in> borel_measurable F"
    shows "AE x in M. cond_exp M F f x = f x"
  by (rule has_cond_exp_charact(2), auto intro: assms)

text \<open>Congruence\<close>

lemma has_cond_exp_cong:
  assumes "integrable M f" "\<And>x. x \<in> space M \<Longrightarrow> f x = g x" "has_cond_exp M F g h"
  shows "has_cond_exp M F f h"
proof (intro has_cond_expI'[OF _ assms(1)], goal_cases)
  case (1 A)
  hence "set_lebesgue_integral M A f = set_lebesgue_integral M A g" by (intro set_lebesgue_integral_cong) (meson assms(2) subalg in_mono subalgebra_def sets.sets_into_space subalgebra_def subsetD)+
  then show ?case using 1 assms(3) by (simp add: has_cond_exp_def)
qed (auto simp add: has_cond_expD[OF assms(3)])

lemma cond_exp_cong:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "integrable M g" "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "AE x in M. cond_exp M F f x = cond_exp M F g x"
proof (cases "\<exists>h. has_cond_exp M F f h")
  case True
  then obtain h where h: "has_cond_exp M F f h" "has_cond_exp M F g h" using has_cond_exp_cong assms by metis 
  show ?thesis using h[THEN has_cond_exp_charact(2)] by fastforce
next
  case False
  moreover have "\<nexists>h. has_cond_exp M F g h" using False has_cond_exp_cong assms by auto
  ultimately show ?thesis unfolding cond_exp_def by auto
qed

lemma has_cond_exp_cong_AE:
  assumes "integrable M f" "AE x in M. f x = g x" "has_cond_exp M F g h"
  shows "has_cond_exp M F f h"
  using assms(1,2) subalg subalgebra_def subset_iff 
  by (intro has_cond_expI', subst set_lebesgue_integral_cong_AE[OF _ assms(1)[THEN borel_measurable_integrable] borel_measurable_integrable(1)[OF has_cond_expD(2)[OF assms(3)]]]) 
     (fast intro: has_cond_expD[OF assms(3)] integrable_cong_AE_imp[OF _ _ AE_symmetric])+

lemma has_cond_exp_cong_AE':
  assumes "h \<in> borel_measurable F" "AE x in M. h x = h' x" "has_cond_exp M F f h'"
  shows "has_cond_exp M F f h"
  using assms(1, 2) subalg subalgebra_def subset_iff
  using AE_restr_to_subalg2[OF subalg assms(2)] measurable_from_subalg
  by (intro has_cond_expI' , subst set_lebesgue_integral_cong_AE[OF _ measurable_from_subalg(1,1)[OF subalg], OF _ assms(1) has_cond_expD(4)[OF assms(3)]])
     (fast intro: has_cond_expD[OF assms(3)] integrable_cong_AE_imp[OF _ _ AE_symmetric])+

lemma cond_exp_cong_AE:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x = g x"
  shows "AE x in M. cond_exp M F f x = cond_exp M F g x"
proof (cases "\<exists>h. has_cond_exp M F f h")
  case True
  then obtain h where h: "has_cond_exp M F f h" "has_cond_exp M F g h" using has_cond_exp_cong_AE assms by (metis (mono_tags, lifting) eventually_mono)
  show ?thesis using h[THEN has_cond_exp_charact(2)] by fastforce
next
  case False
  moreover have "\<nexists>h. has_cond_exp M F g h" using False has_cond_exp_cong_AE assms by auto
  ultimately show ?thesis unfolding cond_exp_def by auto
qed

lemma has_cond_exp_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "has_cond_exp M F f (real_cond_exp M F f)"
  by (standard, auto intro!: real_cond_exp_intA assms)

lemma cond_exp_real[intro]:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F f x = real_cond_exp M F f x" 
  using has_cond_exp_charact has_cond_exp_real assms by blast

lemma cond_exp_cmult:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F (\<lambda>x. c * f x) x = c * cond_exp M F f x"
  using real_cond_exp_cmult[OF assms(1), of c] assms(1)[THEN cond_exp_real] assms(1)[THEN integrable_mult_right, THEN cond_exp_real, of c] by fastforce

text \<open>Indicator functions\<close>

lemma has_cond_exp_indicator:
  assumes "A \<in> sets M" "emeasure M A < \<infinity>"
  shows "has_cond_exp M F (\<lambda>x. indicat_real A x *\<^sub>R y) (\<lambda>x. real_cond_exp M F (indicator A) x *\<^sub>R y)"
proof (intro has_cond_expI', goal_cases)
  case (1 B)
  have "\<integral>x\<in>B. (indicat_real A x *\<^sub>R y) \<partial>M  = (\<integral>x\<in>B. indicat_real A x \<partial>M) *\<^sub>R y" using assms by (intro set_integral_scaleR_left, meson 1 in_mono subalg subalgebra_def, blast)
  also have "... = (\<integral>x\<in>B. real_cond_exp M F (indicator A) x \<partial>M) *\<^sub>R y" using 1 assms by (subst real_cond_exp_intA, auto)
  also have "... = \<integral>x\<in>B. (real_cond_exp M F (indicator A) x *\<^sub>R y) \<partial>M" using assms by (intro set_integral_scaleR_left[symmetric], meson 1 in_mono subalg subalgebra_def, blast)
  finally show ?case .
next
  case 2
  then show ?case using integrable_scaleR_left integrable_real_indicator assms by blast
next
  case 3
  show ?case using assms by (intro integrable_scaleR_left, intro real_cond_exp_int, blast+)
next
  case 4
  then show ?case by (intro borel_measurable_scaleR, intro Conditional_Expectation.borel_measurable_cond_exp, simp)
qed

lemma cond_exp_indicator[intro]:
  fixes y :: "'b::{second_countable_topology,banach}"
  assumes [measurable]: "A \<in> sets M" "emeasure M A < \<infinity>"
  shows "AE x in M. cond_exp M F (\<lambda>x. indicat_real A x *\<^sub>R y) x = cond_exp M F (indicator A) x *\<^sub>R y"
proof -
  have "AE x in M. cond_exp M F (\<lambda>x. indicat_real A x *\<^sub>R y) x = real_cond_exp M F (indicator A) x *\<^sub>R y" using has_cond_exp_indicator[OF assms] has_cond_exp_charact by blast
  thus ?thesis using cond_exp_real[OF integrable_real_indicator, OF assms] by fastforce
qed

text \<open>Addition\<close>

lemma has_cond_exp_add:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "has_cond_exp M F f f'" "has_cond_exp M F g g'"
  shows "has_cond_exp M F (\<lambda>x. f x + g x) (\<lambda>x. f' x + g' x)"
proof (intro has_cond_expI', goal_cases)
  case (1 A)
  have "\<integral>x\<in>A. (f x + g x)\<partial>M = (\<integral>x\<in>A. f x \<partial>M) + (\<integral>x\<in>A. g x \<partial>M)" using assms[THEN has_cond_expD(2)] subalg 1 by (intro set_integral_add(2), auto simp add: subalgebra_def set_integrable_def intro: integrable_mult_indicator)
  also have "... = (\<integral>x\<in>A. f' x \<partial>M) + (\<integral>x\<in>A. g' x \<partial>M)" using assms[THEN has_cond_expD(1)[OF _ 1]] by argo
  also have "... = \<integral>x\<in>A. (f' x + g' x)\<partial>M" using assms[THEN has_cond_expD(3)] subalg 1 by (intro set_integral_add(2)[symmetric], auto simp add: subalgebra_def set_integrable_def intro: integrable_mult_indicator)
  finally show ?case .
next
  case 2
  then show ?case by (metis Bochner_Integration.integrable_add assms has_cond_expD(2))
next
  case 3
  then show ?case by (metis Bochner_Integration.integrable_add assms has_cond_expD(3))
next
  case 4
  then show ?case using assms borel_measurable_add has_cond_expD(4) by blast
qed

lemma has_cond_exp_scaleR_right:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "has_cond_exp M F f f'"
  shows "has_cond_exp M F (\<lambda>x. c *\<^sub>R f x) (\<lambda>x. c *\<^sub>R f' x)"
  using has_cond_expD[OF assms] by (intro has_cond_expI', auto)

lemma cond_exp_scaleR_right:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F (\<lambda>x. c *\<^sub>R f x) x = c *\<^sub>R cond_exp M F f x"
proof (cases "\<exists>f'. has_cond_exp M F f f'")
  case True
  then show ?thesis using assms has_cond_exp_charact has_cond_exp_scaleR_right by metis
next
  case False
  show ?thesis
  proof (cases "c = 0")
    case True
    then show ?thesis by simp
  next
    case c_nonzero: False
    have "\<nexists>f'. has_cond_exp M F (\<lambda>x. c *\<^sub>R f x) f'"
    proof (standard, goal_cases)
      case 1
      then obtain f' where f': "has_cond_exp M F (\<lambda>x. c *\<^sub>R f x) f'" by blast
      have "has_cond_exp M F f (\<lambda>x. inverse c *\<^sub>R f' x)" using has_cond_expD[OF f'] divideR_right[OF c_nonzero] assms by (intro has_cond_expI', auto)
      then show ?case using False by blast
    qed
    then show ?thesis using cond_exp_null[OF False] cond_exp_null by force
  qed 
qed

lemma cond_exp_uminus:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f"
  shows "AE x in M. cond_exp M F (\<lambda>x. - f x) x = - cond_exp M F f x"
  using cond_exp_scaleR_right[OF assms, of "-1"] by force

lemma has_cond_exp_simple:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  shows "has_cond_exp M F f (cond_exp M F f)"
  using assms
proof (induction rule: simple_integrable_function_induct)
  case (cong f g)
  then show ?case using has_cond_exp_cong by (metis (no_types, opaque_lifting) Bochner_Integration.integrable_cong has_cond_expD(2) has_cond_exp_charact(1))
next
  case (indicator A y)
  then show ?case using has_cond_exp_charact[OF has_cond_exp_indicator] by fast
next
  case (add u v)
  then show ?case using has_cond_exp_add has_cond_exp_charact(1) by blast
qed

lemma cond_exp_contraction_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes integrable[measurable]: "integrable M f"
  shows "AE x in M. norm (cond_exp M F f x) \<le> cond_exp M F (\<lambda>x. norm (f x)) x"
proof-
  have int: "integrable M (\<lambda>x. norm (f x))" using assms by blast
  have *: "AE x in M. 0 \<le> cond_exp M F (\<lambda>x. norm (f x)) x" using cond_exp_real[THEN AE_symmetric, OF integrable_norm[OF integrable]] real_cond_exp_ge_c[OF integrable_norm[OF integrable], of 0] norm_ge_zero by fastforce
  have **: "A \<in> sets F \<Longrightarrow> \<integral>x\<in>A. \<bar>f x\<bar> \<partial>M = \<integral>x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M" for A unfolding real_norm_def using assms integrable_abs real_cond_exp_intA by blast
  
  have norm_int: "A \<in> sets F \<Longrightarrow> (\<integral>x\<in>A. \<bar>f x\<bar> \<partial>M) = (\<integral>\<^sup>+x\<in>A. \<bar>f x\<bar> \<partial>M)" for A using assms by (intro nn_set_integral_eq_set_integral[symmetric], blast, fastforce) (meson subalg subalgebra_def subsetD)
  
  have "AE x in M. real_cond_exp M F (\<lambda>x. norm (f x)) x \<ge> 0" using int real_cond_exp_ge_c by force
  hence cond_exp_norm_int: "A \<in> sets F \<Longrightarrow> (\<integral>x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M) = (\<integral>\<^sup>+x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M)" for A using assms by (intro nn_set_integral_eq_set_integral[symmetric], blast, fastforce) (meson subalg subalgebra_def subsetD)
  
  have "A \<in> sets F \<Longrightarrow> \<integral>\<^sup>+x\<in>A. \<bar>f x\<bar>\<partial>M = \<integral>\<^sup>+x\<in>A. real_cond_exp M F (\<lambda>x. norm (f x)) x \<partial>M" for A using ** norm_int cond_exp_norm_int by (auto simp add: nn_integral_set_ennreal)
  moreover have "(\<lambda>x. ennreal \<bar>f x\<bar>) \<in> borel_measurable M" by measurable
  moreover have "(\<lambda>x. ennreal (real_cond_exp M F (\<lambda>x. norm (f x)) x)) \<in> borel_measurable F" by measurable
  ultimately have "AE x in M. nn_cond_exp M F (\<lambda>x. ennreal \<bar>f x\<bar>) x = real_cond_exp M F (\<lambda>x. norm (f x)) x" by (intro nn_cond_exp_charact[THEN AE_symmetric], auto)
    hence "AE x in M. nn_cond_exp M F (\<lambda>x. ennreal \<bar>f x\<bar>) x \<le> cond_exp M F (\<lambda>x. norm (f x)) x" using cond_exp_real[OF int] by force
  moreover have "AE x in M. \<bar>real_cond_exp M F f x\<bar> = norm (cond_exp M F f x)" unfolding real_norm_def using cond_exp_real[OF assms] * by force
  ultimately have "AE x in M. ennreal (norm (cond_exp M F f x)) \<le> cond_exp M F (\<lambda>x. norm (f x)) x" using real_cond_exp_abs[OF assms[THEN borel_measurable_integrable]] by fastforce
  hence "AE x in M. enn2real (ennreal (norm (cond_exp M F f x))) \<le> enn2real (cond_exp M F (\<lambda>x. norm (f x)) x)" using ennreal_le_iff2 by force
  thus ?thesis using * by fastforce
qed

lemma cond_exp_contraction_simple:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  shows "AE x in M. norm (cond_exp M F f x) \<le> cond_exp M F (\<lambda>x. norm (f x)) x"
  using assms
proof (induction rule: simple_integrable_function_induct)
  case (cong f g)
  hence ae: "AE x in M. f x = g x" by blast
  hence "AE x in M. cond_exp M F f x = cond_exp M F g x" using cong has_cond_exp_simple by (subst cond_exp_cong_AE) (auto intro!: has_cond_expD(2))
  hence "AE x in M. norm (cond_exp M F f x) = norm (cond_exp M F g x)" by force
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm (f x)) x = cond_exp M F (\<lambda>x. norm (g x)) x"  using ae cong has_cond_exp_simple by (subst cond_exp_cong_AE) (auto dest: has_cond_expD)
  ultimately show ?case using cong(6) by fastforce
next
  case (indicator A y)
  hence "AE x in M. cond_exp M F (\<lambda>a. indicator A a *\<^sub>R y) x = cond_exp M F (indicator A) x *\<^sub>R y" by blast
  hence *: "AE x in M. norm (cond_exp M F (\<lambda>a. indicat_real A a *\<^sub>R y) x) \<le> norm y * cond_exp M F (\<lambda>x. norm (indicat_real A x)) x" using cond_exp_contraction_real[OF integrable_real_indicator, OF indicator] by fastforce

  have "AE x in M. norm y * cond_exp M F (\<lambda>x. norm (indicat_real A x)) x = norm y * real_cond_exp M F (\<lambda>x. norm (indicat_real A x)) x" using cond_exp_real[OF integrable_real_indicator, OF indicator] by fastforce
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm y * norm (indicat_real A x)) x = real_cond_exp M F (\<lambda>x. norm y * norm (indicat_real A x)) x" using indicator by (intro cond_exp_real, auto)
  ultimately have "AE x in M. norm y * cond_exp M F (\<lambda>x. norm (indicat_real A x)) x = cond_exp M F (\<lambda>x. norm y * norm (indicat_real A x)) x" using real_cond_exp_cmult[of "\<lambda>x. norm (indicat_real A x)" "norm y"] indicator by fastforce
  moreover have "(\<lambda>x. norm y * norm (indicat_real A x)) = (\<lambda>x. norm (indicat_real A x *\<^sub>R y))" by force
  ultimately show ?case using * by force
next
  case (add u v)
  have "AE x in M. norm (cond_exp M F (\<lambda>a. u a + v a) x) = norm (cond_exp M F u x + cond_exp M F v x)" using has_cond_exp_charact(2)[OF has_cond_exp_add, OF has_cond_exp_simple(1,1), OF add(1,2,3,4)] by fastforce
  moreover have "AE x in M. norm (cond_exp M F u x + cond_exp M F v x) \<le> norm (cond_exp M F u x) + norm (cond_exp M F v x)" using norm_triangle_ineq by blast
  moreover have "AE x in M. norm (cond_exp M F u x) + norm (cond_exp M F v x) \<le> cond_exp M F (\<lambda>x. norm (u x)) x + cond_exp M F (\<lambda>x. norm (v x)) x" using add(6,7) by fastforce
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm (u x)) x + cond_exp M F (\<lambda>x. norm (v x)) x = cond_exp M F (\<lambda>x. norm (u x) + norm (v x)) x" using integrable_simple_function[OF add(1,2)] integrable_simple_function[OF add(3,4)] by (intro has_cond_exp_charact(2)[OF has_cond_exp_add[OF has_cond_exp_charact(1,1)], THEN AE_symmetric], auto intro: has_cond_exp_real)
  moreover have "AE x in M. cond_exp M F (\<lambda>x. norm (u x) + norm (v x)) x = cond_exp M F (\<lambda>x. norm (u x + v x)) x" using add(5) integrable_simple_function[OF add(1,2)] integrable_simple_function[OF add(3,4)] by (intro cond_exp_cong, auto)
  ultimately show ?case by force
qed

lemma has_cond_exp_lim:
    fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes integrable[measurable]: "integrable M f"
      and "\<And>i. simple_function M (s i)"
      and "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>"
      and "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
  obtains r 
  where "has_cond_exp M F f (\<lambda>x. lim (\<lambda>i. cond_exp M F (s (r i)) x))" 
        "AE x in M. convergent (\<lambda>i. cond_exp M F (s (r i)) x)"
        "strict_mono r"
proof -
  have [measurable]: "(s i) \<in> borel_measurable M" for i using assms(2) by (simp add: borel_measurable_simple_function)
  have integrable_s: "integrable M (\<lambda>x. s i x)" for i using assms(2) assms(3) integrable_simple_function by blast
  have integrable_4f: "integrable M (\<lambda>x. 4 * norm (f x))" using assms(1) by simp
  have integrable_2f: "integrable M (\<lambda>x. 2 * norm (f x))" using assms(1) by simp
  have integrable_2_cond_exp_norm_f: "integrable M (\<lambda>x. 2 * cond_exp M F (\<lambda>x. norm (f x)) x)" by fast

  have "emeasure M {y \<in> space M. s i y - s j y \<noteq> 0} \<le>  emeasure M {y \<in> space M. s i y \<noteq> 0} + emeasure M {y \<in> space M. s j y \<noteq> 0}" for i j using simple_functionD(2)[OF assms(2)] by (intro order_trans[OF emeasure_mono emeasure_subadditive], auto)
  hence fin_sup: "emeasure M {y \<in> space M. s i y - s j y \<noteq> 0} \<noteq> \<infinity>" for i j using assms(3) by (metis (mono_tags) ennreal_add_eq_top linorder_not_less top.not_eq_extremum infinity_ennreal_def)

  have "emeasure M {y \<in> space M. norm (s i y - s j y) \<noteq> 0} \<le>  emeasure M {y \<in> space M. s i y \<noteq> 0} + emeasure M {y \<in> space M. s j y \<noteq> 0}" for i j using simple_functionD(2)[OF assms(2)] by (intro order_trans[OF emeasure_mono emeasure_subadditive], auto)
  hence fin_sup_norm: "emeasure M {y \<in> space M. norm (s i y - s j y) \<noteq> 0} \<noteq> \<infinity>" for i j using assms(3) by (metis (mono_tags) ennreal_add_eq_top linorder_not_less top.not_eq_extremum infinity_ennreal_def)

  have Cauchy: "Cauchy (\<lambda>n. s n x)" if "x \<in> space M" for x using assms(4) LIMSEQ_imp_Cauchy that by blast
  hence bounded_range_s: "bounded (range (\<lambda>n. s n x))" if "x \<in> space M" for x using that cauchy_imp_bounded by fast

  have "AE x in M. (\<lambda>n. diameter {s i x | i. n \<le> i}) \<longlonglongrightarrow> 0" using Cauchy cauchy_iff_diameter_tends_to_zero_and_bounded by fast
  moreover have "(\<lambda>x. diameter {s i x |i. n \<le> i}) \<in> borel_measurable M" for n using bounded_range_s borel_measurable_diameter by measurable
  moreover have "AE x in M. norm (diameter {s i x |i. n \<le> i}) \<le> 4 * norm (f x)" for n
  proof - 
    {
      fix x assume x: "x \<in> space M"
      have "diameter {s i x |i. n \<le> i} \<le> 2 * norm (f x) + 2 * norm (f x)" by (intro diameter_le, blast, subst dist_norm[symmetric], intro dist_triangle3[THEN order_trans, of 0], intro add_mono) (auto intro: assms(5)[OF x])
      hence "norm (diameter {s i x |i. n \<le> i}) \<le> 4 * norm (f x)" using diameter_ge_0[OF bounded_subset[OF bounded_range_s], OF x, of "{s i x |i. n \<le> i}"] by force
    }
    thus ?thesis by fast
  qed
  ultimately have diameter_tendsto_zero: "(\<lambda>n. LINT x|M. diameter {s i x | i. n \<le> i}) \<longlonglongrightarrow> 0" by (intro integral_dominated_convergence[OF borel_measurable_const[of 0] _ integrable_4f, simplified]) (fast+)
  
  have diameter_integrable: "integrable M (\<lambda>x. diameter {s i x | i. n \<le> i})" for n using assms(1,5) by (intro integrable_bound_diameter[OF bounded_range_s integrable_2f], auto)

  have dist_integrable: "integrable M (\<lambda>x. dist (s i x) (s j x))" for i j 
    using assms(5) dist_triangle3[of "s i _" _ 0, THEN order_trans, OF add_mono, of _ "2 * norm (f _)"]
    by (intro Bochner_Integration.integrable_bound[OF integrable_4f]) fastforce+
   
  hence dist_norm_integrable: "integrable M (\<lambda>x. norm (s i x - s j x))" for i j unfolding dist_norm by presburger

  have "\<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. LINT x|M. dist (cond_exp M F (s i) x) (cond_exp M F (s j) x) < e" if e_pos: "e > 0" for e
  proof -
    obtain N where *: "LINT x|M. diameter {s i x | i. n \<le> i} < e" if "n \<ge> N" for n using that order_tendsto_iff[THEN iffD1, OF diameter_tendsto_zero, unfolded eventually_sequentially] e_pos by presburger
    {
      fix i j x assume asm: "i \<ge> N" "j \<ge> N" "x \<in> space M"
      have "case_prod dist ` ({s i x |i. N \<le> i} \<times> {s i x |i. N \<le> i}) = case_prod (\<lambda>i j. dist (s i x) (s j x)) ` ({N..} \<times> {N..})" by fast
      hence "diameter {s i x | i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x))" unfolding diameter_def by auto
      moreover have "(SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x)) \<ge> dist (s i x) (s j x)" using asm bounded_imp_bdd_above[OF bounded_imp_dist_bounded, OF bounded_range_s] by (intro cSup_upper, auto)
      ultimately have "diameter {s i x | i. N \<le> i} \<ge> dist (s i x) (s j x)" by presburger
    }
    hence "LINT x|M. dist (s i x) (s j x) < e" if "i \<ge> N" "j \<ge> N" for i j using that * by (intro integral_mono[OF dist_integrable diameter_integrable, THEN order.strict_trans1], blast+)
    moreover have "LINT x|M. dist (cond_exp M F (s i) x) (cond_exp M F (s j) x) \<le> LINT x|M. dist (s i x) (s j x)" for i j
    proof-
      have "LINT x|M. dist (cond_exp M F (s i) x) (cond_exp M F (s j) x) = LINT x|M. norm (cond_exp M F (s i) x + - 1 *\<^sub>R cond_exp M F (s j) x)" unfolding dist_norm by simp
      also have "... = LINT x|M. norm (cond_exp M F (\<lambda>x. s i x - s j x) x)" using has_cond_exp_charact(2)[OF has_cond_exp_add[OF _ has_cond_exp_scaleR_right, OF has_cond_exp_charact(1,1), OF has_cond_exp_simple(1,1)[OF assms(2,3)]], THEN AE_symmetric, of i "-1" j] by (intro integral_cong_AE) force+      
      also have "... \<le> LINT x|M. cond_exp M F (\<lambda>x. norm (s i x - s j x)) x" using cond_exp_contraction_simple[OF _ fin_sup, of i j] integrable_cond_exp assms(2) by (intro integral_mono_AE, fast+)
      also have "... = LINT x|M. norm (s i x - s j x)" unfolding set_integral_space(1)[OF integrable_cond_exp, symmetric] set_integral_space[OF dist_norm_integrable, symmetric] by (intro has_cond_expD(1)[OF has_cond_exp_simple[OF _ fin_sup_norm], symmetric]) (metis assms(2) simple_function_compose1 simple_function_diff, metis sets.top subalg subalgebra_def)
      finally show ?thesis unfolding dist_norm .  
    qed
    ultimately show ?thesis using order.strict_trans1 by meson
  qed
  then obtain r where strict_mono_r: "strict_mono r" and AE_Cauchy: "AE x in M. Cauchy (\<lambda>i. cond_exp M F (s (r i)) x)" by (rule cauchy_L1_AE_cauchy_subseq[OF integrable_cond_exp], auto)
  hence ae_lim_cond_exp: "AE x in M. (\<lambda>n. cond_exp M F (s (r n)) x) \<longlonglongrightarrow> lim (\<lambda>n. cond_exp M F (s (r n)) x)" using Cauchy_convergent_iff convergent_LIMSEQ_iff by fastforce

  have cond_exp_bounded: "AE x in M. norm (cond_exp M F (s (r n)) x) \<le> cond_exp M F (\<lambda>x. 2 * norm (f x)) x" for n
  proof -
    have "AE x in M. norm (cond_exp M F (s (r n)) x) \<le> cond_exp M F (\<lambda>x. norm (s (r n) x)) x" by (rule cond_exp_contraction_simple[OF assms(2,3)])
    moreover have "AE x in M. real_cond_exp M F (\<lambda>x. norm (s (r n) x)) x \<le> real_cond_exp M F (\<lambda>x. 2 * norm (f x)) x" using integrable_s integrable_2f assms(5) by (intro real_cond_exp_mono, auto) 
    ultimately show ?thesis using cond_exp_real[OF integrable_norm, OF integrable_s, of "r n"] cond_exp_real[OF integrable_2f] by force
  qed
  have lim_integrable: "integrable M (\<lambda>x. lim (\<lambda>i. cond_exp M F (s (r i)) x))" by (intro integrable_dominated_convergence[OF _ borel_measurable_cond_exp' integrable_cond_exp ae_lim_cond_exp cond_exp_bounded], simp)

  {
    fix A assume A_in_sets_F: "A \<in> sets F"
    have "AE x in M. norm (indicator A x *\<^sub>R cond_exp M F (s (r n)) x) \<le> cond_exp M F (\<lambda>x. 2 * norm (f x)) x" for n
    proof -
      have "AE x in M. norm (indicator A x *\<^sub>R cond_exp M F (s (r n)) x) \<le> norm (cond_exp M F (s (r n)) x)" unfolding indicator_def by simp
      thus ?thesis using cond_exp_bounded[of n] by force
    qed
    hence lim_cond_exp_int: "(\<lambda>n. LINT x:A|M. cond_exp M F (s (r n)) x) \<longlonglongrightarrow> LINT x:A|M. lim (\<lambda>n. cond_exp M F (s (r n)) x)" 
      using ae_lim_cond_exp measurable_from_subalg[OF subalg borel_measurable_indicator, OF A_in_sets_F] cond_exp_bounded
      unfolding set_lebesgue_integral_def
      by (intro integral_dominated_convergence[OF borel_measurable_scaleR borel_measurable_scaleR integrable_cond_exp]) (fastforce simp add: tendsto_scaleR)+

    have "AE x in M. norm (indicator A x *\<^sub>R s (r n) x) \<le> 2 * norm (f x)" for n
    proof -
      have "AE x in M. norm (indicator A x *\<^sub>R s (r n) x) \<le> norm (s (r n) x)" unfolding indicator_def by simp
      thus ?thesis using assms(5)[of _ "r n"] by fastforce
    qed
    hence lim_s_int: "(\<lambda>n. LINT x:A|M. s (r n) x) \<longlonglongrightarrow> LINT x:A|M. f x"
      using measurable_from_subalg[OF subalg borel_measurable_indicator, OF A_in_sets_F] LIMSEQ_subseq_LIMSEQ[OF assms(4) strict_mono_r] assms(5)
      unfolding set_lebesgue_integral_def comp_def
      by (intro integral_dominated_convergence[OF borel_measurable_scaleR borel_measurable_scaleR integrable_2f]) (fastforce simp add: tendsto_scaleR)+

    have "LINT x:A|M. lim (\<lambda>n. cond_exp M F (s (r n)) x) = lim (\<lambda>n. LINT x:A|M. cond_exp M F (s (r n)) x)" using limI[OF lim_cond_exp_int] by argo
    also have "... = lim (\<lambda>n. LINT x:A|M. s (r n) x)" using has_cond_expD(1)[OF has_cond_exp_simple[OF assms(2,3)] A_in_sets_F, symmetric] by presburger
    also have "... = LINT x:A|M. f x" using limI[OF lim_s_int] by argo
    finally have "LINT x:A|M. lim (\<lambda>n. cond_exp M F (s (r n)) x) = LINT x:A|M. f x" .
  }
  hence "has_cond_exp M F f (\<lambda>x. lim (\<lambda>i. cond_exp M F (s (r i)) x))" using assms(1) lim_integrable by (intro has_cond_expI', auto) 
  thus thesis using AE_Cauchy Cauchy_convergent strict_mono_r by (auto intro!: that)
qed

lemma cond_exp_lim:
    fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes [measurable]:"integrable M f"
      and "\<And>i. simple_function M (s i)"
      and "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>"
      and "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
  obtains r where "AE x in M. (\<lambda>i. cond_exp M F (s (r i)) x) \<longlonglongrightarrow> cond_exp M F f x" "strict_mono r"
proof -
  obtain r where "AE x in M. cond_exp M F f x = lim (\<lambda>i. cond_exp M F (s (r i)) x)" "AE x in M. convergent (\<lambda>i. cond_exp M F (s (r i)) x)" "strict_mono r" using has_cond_exp_charact(2) by (auto intro: has_cond_exp_lim[OF assms])
  thus ?thesis by (auto intro!: that[of r] simp: convergent_LIMSEQ_iff)
qed
  
lemma has_cond_expI:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f"
  shows "has_cond_exp M F f (cond_exp M F f)"
  using assms
proof (induction rule: integrable_induct')
  case (base A c)
  show ?case using has_cond_exp_indicator[OF base(1,2)] has_cond_exp_charact(1) by blast
next
  case (add u v)
  show ?case using has_cond_exp_add[OF add(3,4)] has_cond_exp_charact(1) by blast
next
  case (lim f s)
  show ?case using has_cond_exp_lim[OF lim(1,3,4,5,6)] has_cond_exp_charact(1) by meson
qed

lemma has_cond_exp_nested_subalg:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "subalgebra G F" "has_cond_exp M F f h" "has_cond_exp M G f h'"
  shows "has_cond_exp M F h' h"
  by standard (metis assms has_cond_expD in_mono subalgebra_def)+

lemma cond_exp_nested_subalg:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "subalgebra M G" "subalgebra G F"
  shows "AE \<xi> in M. cond_exp M F f \<xi> = cond_exp M F (cond_exp M G f) \<xi>"
  using has_cond_expI assms sigma_finite_subalgebra_def by (auto intro!: has_cond_exp_nested_subalg[THEN has_cond_exp_charact(2), THEN AE_symmetric] sigma_finite_subalgebra.has_cond_expI[OF sigma_finite_subalgebra.intro[OF assms(2)]] nested_subalg_is_sigma_finite)

lemma cond_exp_set_integral:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "A \<in> sets F"
  shows "(\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. cond_exp M F f x \<partial>M)"
  using has_cond_expD(1)[OF has_cond_expI, OF assms] by argo

lemma cond_exp_add:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f" "integrable M g"
  shows "AE x in M. cond_exp M F (\<lambda>x. f x + g x) x = cond_exp M F f x + cond_exp M F g x"
  using has_cond_exp_add[OF has_cond_expI(1,1), OF assms, THEN has_cond_exp_charact(2)] .

lemma cond_exp_diff:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "integrable M f" "integrable M g"
  shows "AE x in M. cond_exp M F (\<lambda>x. f x - g x) x = cond_exp M F f x - cond_exp M F g x"
  using has_cond_exp_add[OF _ has_cond_exp_scaleR_right, OF has_cond_expI(1,1), OF assms, THEN has_cond_exp_charact(2), of "-1"] by simp

lemma cond_exp_diff':
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "integrable M f" "integrable M g"
  shows "AE x in M. cond_exp M F (f - g) x = cond_exp M F f x - cond_exp M F g x"
  unfolding fun_diff_def using assms by (rule cond_exp_diff)

lemma cond_exp_contraction:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
  shows "AE x in M. norm (cond_exp M F f x) \<le> cond_exp M F (\<lambda>x. norm (f x)) x" 
proof -
  obtain s where s: "\<And>i. simple_function M (s i)" "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" 
    by (blast intro: integrable_implies_simple_function_sequence[OF assms])

  obtain r where r: "AE x in M. (\<lambda>i. cond_exp M F (s (r i)) x) \<longlonglongrightarrow> cond_exp M F f x" "strict_mono r" using cond_exp_lim[OF assms s] by blast

  have norm_s_r: "\<And>i. simple_function M (\<lambda>x. norm (s (r i) x))" "\<And>i. emeasure M {y \<in> space M. norm (s (r i) y) \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. norm (s (r i) x)) \<longlonglongrightarrow> norm (f x)" "\<And>i x. x \<in> space M \<Longrightarrow> norm (norm (s (r i) x)) \<le> 2 * norm (norm (f x))" 
    using s by (auto intro: LIMSEQ_subseq_LIMSEQ[OF tendsto_norm r(2), unfolded comp_def] simple_function_compose1) 
  
  obtain r' where r': "AE x in M. (\<lambda>i. (cond_exp M F (\<lambda>x. norm (s (r (r' i)) x)) x)) \<longlonglongrightarrow> cond_exp M F (\<lambda>x. norm (f x)) x" "strict_mono r'" using cond_exp_lim[OF integrable_norm norm_s_r, OF assms] by blast

  have "AE x in M. \<forall>i. norm (cond_exp M F (s (r (r' i))) x) \<le> cond_exp M F (\<lambda>x. norm (s (r (r' i)) x)) x" using s by (auto intro: cond_exp_contraction_simple simp add: AE_all_countable)
  moreover have "AE x in M. (\<lambda>i. norm (cond_exp M F (s (r (r' i))) x)) \<longlonglongrightarrow> norm (cond_exp M F f x)" using r LIMSEQ_subseq_LIMSEQ[OF tendsto_norm r'(2), unfolded comp_def] by fast
  ultimately show ?thesis using LIMSEQ_le r'(1) by fast
qed
  
lemma cond_exp_sum [intro, simp]:
  fixes f :: "'t \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,banach}"
  assumes [measurable]: "\<And>i. integrable M (f i)"
  shows "AE x in M. cond_exp M F (\<lambda>x. \<Sum>i\<in>I. f i x) x = (\<Sum>i\<in>I. cond_exp M F (f i) x)"
proof (rule has_cond_exp_charact, intro has_cond_expI')
  fix A assume [measurable]: "A \<in> sets F"
  then have A_meas [measurable]: "A \<in> sets M" by (meson subsetD subalg subalgebra_def)

  have "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x. (\<Sum>i\<in>I. indicator A x *\<^sub>R f i x)\<partial>M)" unfolding set_lebesgue_integral_def by (simp add: scaleR_sum_right)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x *\<^sub>R f i x \<partial>M))" using assms by (auto intro!: Bochner_Integration.integral_sum integrable_mult_indicator)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x *\<^sub>R cond_exp M F (f i) x \<partial>M))" using cond_exp_set_integral[OF assms] by (simp add: set_lebesgue_integral_def)
  also have "... = (\<integral>x. (\<Sum>i\<in>I. indicator A x *\<^sub>R cond_exp M F (f i) x)\<partial>M)" using assms by (auto intro!: Bochner_Integration.integral_sum[symmetric] integrable_mult_indicator)
  also have "... = (\<integral>x\<in>A. (\<Sum>i\<in>I. cond_exp M F (f i) x)\<partial>M)" unfolding set_lebesgue_integral_def by (simp add: scaleR_sum_right)
  finally show "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x\<in>A. (\<Sum>i\<in>I. cond_exp M F (f i) x)\<partial>M)" by auto
qed (auto simp add: assms integrable_cond_exp)

subsection "Ordered Banach Spaces"

lemma cond_exp_gr_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f"  "AE x in M. f x > c"
  shows "AE x in M. cond_exp M F f x > c"
proof -
  define X where "X = {x \<in> space M. cond_exp M F f x \<le> c}"
  have [measurable]: "X \<in> sets F" unfolding X_def by measurable (metis sets.top subalg subalgebra_def)
  hence X_in_M: "X \<in> sets M" using sets_restr_to_subalg subalg subalgebra_def by blast
  have "emeasure M X = 0"
  proof (rule ccontr)
    assume "emeasure M X \<noteq> 0"
    have "emeasure (restr_to_subalg M F) X = emeasure M X" by (simp add: emeasure_restr_to_subalg subalg)
    hence "emeasure (restr_to_subalg M F) X > 0" using \<open>\<not>(emeasure M X) = 0\<close> gr_zeroI by auto
    then obtain A where A: "A \<in> sets (restr_to_subalg M F)" "A \<subseteq> X" "emeasure (restr_to_subalg M F) A > 0" "emeasure (restr_to_subalg M F) A < \<infinity>"
      using sigma_fin_subalg by (metis emeasure_notin_sets ennreal_0 infinity_ennreal_def le_less_linear neq_top_trans not_gr_zero order_refl sigma_finite_measure.approx_PInf_emeasure_with_finite)
    hence [simp]: "A \<in> sets F" using subalg sets_restr_to_subalg by blast
    hence [simp]: "A \<in> sets M" using sets_restr_to_subalg subalg subalgebra_def by blast
    have [simp]: "set_integrable M A (\<lambda>x. c)" using A subalg by (auto simp add: set_integrable_def emeasure_restr_to_subalg) 
    have [simp]: "set_integrable M A f" unfolding set_integrable_def by (rule integrable_mult_indicator, auto simp add: assms(1))
    have "AE x in M. indicator A x *\<^sub>R c = indicator A x *\<^sub>R f x"
    proof (rule integral_eq_mono_AE_eq_AE)
      show "LINT x|M. indicator A x *\<^sub>R c = LINT x|M. indicator A x *\<^sub>R f x" 
      proof (simp only: set_lebesgue_integral_def[symmetric], rule antisym)
        show "(\<integral>x\<in>A. c \<partial>M) \<le> (\<integral>x\<in>A. f x \<partial>M)" using assms(2) by (intro set_integral_mono_AE_banach) auto
        have "(\<integral>x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. cond_exp M F f x \<partial>M)" by (rule cond_exp_set_integral, auto simp add: \<open>integrable M f\<close>)
        also have "... \<le> (\<integral>x\<in>A. c \<partial>M)" using A by (auto intro!: set_integral_mono_banach simp add: X_def)
        finally show "(\<integral>x\<in>A. f x \<partial>M) \<le> (\<integral>x\<in>A. c \<partial>M)" by simp
      qed
      then have "measure M A *\<^sub>R c = LINT x|M. indicator A x *\<^sub>R f x" using A by (auto simp: set_lebesgue_integral_def emeasure_restr_to_subalg subalg)
      show "AE x in M. indicator A x *\<^sub>R c \<le> indicator A x *\<^sub>R f x" using assms by (auto simp add: X_def indicator_def)
    qed (auto simp add: set_integrable_def[symmetric])
    then have "AE x\<in>A in M. c = f x" by auto
    then have "AE x\<in>A in M. False" using assms(2) by auto
    have "A \<in> null_sets M" unfolding ae_filter_def by (meson AE_iff_null_sets \<open>A \<in> sets M\<close> \<open>AE x\<in>A in M. False\<close>)
    then show False using A(3)by (simp add: emeasure_restr_to_subalg null_setsD1 subalg)
  qed
  then show ?thesis using AE_iff_null_sets[OF X_in_M] unfolding X_def by auto
qed

lemma cond_exp_less_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "AE x in M. f x < c"
  shows "AE x in M. cond_exp M F f x < c"
proof -
  have "AE x in M. cond_exp M F f x = - cond_exp M F (\<lambda>x. - f x) x" using cond_exp_uminus[OF assms(1)] by auto
  moreover have "AE x in M. cond_exp M F (\<lambda>x. -f x) x > -c"  using assms by (intro cond_exp_gr_c) auto
  ultimately show ?thesis by (force simp add: minus_less_iff)
qed

lemma cond_exp_mono_strict:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x < g x"
  shows "AE x in M. cond_exp M F f x < cond_exp M F g x"
  using cond_exp_less_c[OF Bochner_Integration.integrable_diff, OF assms(1,2), of 0] 
        cond_exp_diff[OF assms(1,2)] assms(3) by auto

lemma cond_exp_ge_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes [measurable]: "integrable M f"                                                               
      and "AE x in M. f x \<ge> c"
  shows "AE x in M. cond_exp M F f x \<ge> c"
proof -
  let ?F = "restr_to_subalg M F"
  interpret sigma_finite_measure "restr_to_subalg M F" using sigma_fin_subalg by auto
  { 
    fix A assume asm: "A \<in> sets ?F" "0 < measure ?F A"
    have [simp]: "sets ?F = sets F" "measure ?F A = measure M A" using asm by (auto simp add: measure_def sets_restr_to_subalg[OF subalg] emeasure_restr_to_subalg[OF subalg])
    have M_A: "emeasure M A < \<infinity>" using measure_zero_top asm by (force simp add: top.not_eq_extremum)
    hence F_A: "emeasure ?F A < \<infinity>" using asm(1) emeasure_restr_to_subalg subalg by fastforce
    have "set_lebesgue_integral M A (\<lambda>_. c) \<le> set_lebesgue_integral M A f" using assms asm M_A subalg by (intro set_integral_mono_AE_banach, auto simp add: set_integrable_def integrable_mult_indicator subalgebra_def sets_restr_to_subalg)
    also have "... = set_lebesgue_integral M A (cond_exp M F f)" using cond_exp_set_integral[OF assms(1)] asm by auto
    also have "... = set_lebesgue_integral ?F A (cond_exp M F f)" unfolding set_lebesgue_integral_def using asm borel_measurable_cond_exp by (intro integral_subalgebra2[OF subalg, symmetric], simp)
    finally have "(1 / measure ?F A) *\<^sub>R set_lebesgue_integral ?F A (cond_exp M F f) \<in> {c..}" using asm subalg M_A by (auto simp add: set_integral_const subalgebra_def intro!: pos_divideR_le_eq[THEN iffD1]) 
  }
  thus ?thesis using AE_restr_to_subalg[OF subalg] averaging_theorem[OF integrable_in_subalg closed_atLeast, OF subalg borel_measurable_cond_exp integrable_cond_exp] by auto
qed

lemma cond_exp_le_c:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f"
      and "AE x in M. f x \<le> c"
  shows "AE x in M. cond_exp M F f x \<le> c"
proof -
  have "AE x in M. cond_exp M F f x = - cond_exp M F (\<lambda>x. - f x) x" using cond_exp_uminus[OF assms(1)] by force
  moreover have "AE x in M. cond_exp M F (\<lambda>x. - f x) x \<ge> - c" using assms by (intro cond_exp_ge_c) auto
  ultimately show ?thesis by (force simp add: minus_le_iff)
qed

lemma cond_exp_mono:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x \<le> g x"
  shows "AE x in M. cond_exp M F f x \<le> cond_exp M F g x"
  using cond_exp_le_c[OF Bochner_Integration.integrable_diff, OF assms(1,2), of 0] 
        cond_exp_diff[OF assms(1,2)] assms(3) by auto
                                      
lemma cond_exp_min:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> min (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
proof -
  have "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> cond_exp M F f \<xi>" by (intro cond_exp_mono integrable_min assms, simp)
  moreover have "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> cond_exp M F g \<xi>" by (intro cond_exp_mono integrable_min assms, simp)
  ultimately show "AE \<xi> in M. cond_exp M F (\<lambda>x. min (f x) (g x)) \<xi> \<le> min (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)" by fastforce
qed

lemma cond_exp_max:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> max (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
proof -
  have "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> cond_exp M F f \<xi>" by (intro cond_exp_mono integrable_max assms, simp)
  moreover have "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> cond_exp M F g \<xi>" by (intro cond_exp_mono integrable_max assms, simp)
  ultimately show "AE \<xi> in M. cond_exp M F (\<lambda>x. max (f x) (g x)) \<xi> \<ge> max (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)" by fastforce
qed

lemma cond_exp_inf:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector, lattice}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. inf (f x) (g x)) \<xi> \<le> inf (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
  unfolding inf_min using assms by (rule cond_exp_min)

lemma cond_exp_sup:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector, lattice}"
  assumes "integrable M f" "integrable M g"
  shows "AE \<xi> in M. cond_exp M F (\<lambda>x. sup (f x) (g x)) \<xi> \<ge> sup (cond_exp M F f \<xi>) (cond_exp M F g \<xi>)"
  unfolding sup_max using assms by (rule cond_exp_max)

end

end