theory Banach_Conditional_Expectation
  imports Main "HOL-Probability.Conditional_Expectation" "HOL-Analysis.Analysis" "HOL-Analysis.Bochner_Integration" Misc
begin

abbreviation "sb_integrable \<equiv> Bochner_Integration.simple_bochner_integrable"
abbreviation "sb_integral \<equiv> Bochner_Integration.simple_bochner_integral"

lemma banach_density_unique:
  fixes f f'::"_ \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes M[measurable]: "integrable M f" "integrable M f'"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
  sorry

lemma set_integrableI:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "A \<in> sets M"
      and "integrable M f"
    shows "set_integrable M A f"
  unfolding set_integrable_def using assms by (rule integrable_mult_indicator)


definition\<^marker>\<open>tag important\<close> simple_cond_exp :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> 'b::real_vector) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "simple_cond_exp M F f = (\<lambda>x. \<Sum>y\<in>f`space M. real_cond_exp M F (indicator {z\<in>space M. f z = y}) x *\<^sub>R y)"

definition has_cond_exp :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}) \<Rightarrow> bool" where 
  "has_cond_exp M F f g = ((\<forall>A \<in> sets F. (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M))
                        \<and> integrable M f 
                        \<and> integrable M g 
                        \<and> g \<in> borel_measurable F)"

lemma has_cond_expI:
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

definition cond_exp :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{real_normed_vector, second_countable_topology})" where
  "cond_exp M F f = (if \<exists>g. has_cond_exp M F f g then (SOME g. has_cond_exp M F f g) else (\<lambda>_. 0))"


lemma borel_measurable_cond_exp[measurable]: "cond_exp M F f \<in> borel_measurable F" 
  by (metis cond_exp_def someI has_cond_exp_def borel_measurable_const)

context sigma_finite_subalgebra
begin

lemma borel_measurable_cond_exp'[measurable]: "cond_exp M F f \<in> borel_measurable M"
  by (metis cond_exp_def someI has_cond_exp_def borel_measurable_const subalg measurable_from_subalg)

lemma cond_exp_charact:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "has_cond_exp M F f g"
  shows "has_cond_exp M F f (cond_exp M F f)"
        "AE x in M. cond_exp M F f x = g x"
proof -
  show cond_exp: "has_cond_exp M F f (cond_exp M F f)" using assms someI cond_exp_def by metis
  let ?MF = "restr_to_subalg M F"
  {
    fix A assume "A \<in> sets ?MF"
    then have [measurable]: "A \<in> sets F" using sets_restr_to_subalg[OF subalg] by simp
    have "(\<integral>x \<in> A. g x \<partial>?MF) = (\<integral>x \<in> A. g x \<partial>M)" using assms subalg by (auto simp add: integral_subalgebra2 set_lebesgue_integral_def dest!: has_cond_expD)
    also have "... = (\<integral>x \<in> A. cond_exp M F f x \<partial>M)" using assms cond_exp by (simp add: has_cond_exp_def)
    also have "... = (\<integral>x \<in> A. cond_exp M F f x \<partial>?MF)" using subalg by (auto simp add: integral_subalgebra2 set_lebesgue_integral_def dest: has_cond_expD)
    finally have "(\<integral>x \<in> A. g x \<partial>?MF) = (\<integral>x \<in> A. cond_exp M F f x \<partial>?MF)" by simp
  }
  hence "AE x in ?MF. cond_exp M F f x = g x" using cond_exp assms subalg by (intro banach_density_unique, auto intro!: integrable_in_subalg dest: has_cond_expD)
  then show "AE x in M. cond_exp M F f x = g x" using AE_restr_to_subalg[OF subalg] by simp
qed

lemma cond_exp_indicator:
  assumes "A \<in> sets M" "emeasure M A < \<infinity>"
  shows "has_cond_exp M F (\<lambda>x. indicat_real A x *\<^sub>R y) (\<lambda>x. real_cond_exp M F (indicator A) x *\<^sub>R y)"
proof (intro has_cond_expI, goal_cases)
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

lemma cond_exp_add:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "has_cond_exp M F f f'" "has_cond_exp M F g g'"
  shows "has_cond_exp M F (\<lambda>x. f x + g x) (\<lambda>x. f' x + g' x)"
proof (intro has_cond_expI, goal_cases)
  case (1 A)
  have "\<integral>x\<in>A. (f x + g x)\<partial>M = (\<integral>x\<in>A. f x \<partial>M) + (\<integral>x\<in>A. g x \<partial>M)" using assms[THEN has_cond_expD(2)] subalg 1 by (intro set_integral_add(2), auto simp add: subalgebra_def intro!: set_integrableI)
  also have "... = (\<integral>x\<in>A. f' x \<partial>M) + (\<integral>x\<in>A. g' x \<partial>M)" using assms[THEN has_cond_expD(1)[OF _ 1]] by argo
  also have "... = \<integral>x\<in>A. (f' x + g' x)\<partial>M" using assms[THEN has_cond_expD(3)] subalg 1 by (intro set_integral_add(2)[symmetric], auto simp add: subalgebra_def intro!: set_integrableI)
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

lemma cond_exp_cong:
  assumes "integrable M f" "integrable M g" "\<And>x. x \<in> space M \<Longrightarrow> f x = g x" "has_cond_exp M F g h"
  shows "has_cond_exp M F f h"
proof (intro has_cond_expI[OF _ assms(1)], goal_cases)
    case (1 A)
    hence "set_lebesgue_integral M A f = set_lebesgue_integral M A g" 
      by (intro set_lebesgue_integral_cong) (meson assms(3) subalg in_mono subalgebra_def sets.sets_into_space subalgebra_def subsetD)+
    then show ?case using 1 assms(4) by (simp add: has_cond_exp_def)
qed (auto simp add: has_cond_expD[OF assms(4)])

lemma cond_exp_simple:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "sb_integrable M f"
  shows "has_cond_exp M F f (simple_cond_exp M F f)"
proof -
  have sf: "simple_function M f" using assms simple_bochner_integrable.cases by blast
  let ?f = "(\<lambda>x. \<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"
  have "has_cond_exp M F ?f (simple_cond_exp M F ?f)" using simple_functionD(1)[OF sf]
  proof (induction rule: finite_induct)
    case empty
    then show ?case unfolding simple_cond_exp_def using cond_exp_indicator[of "{}" 0] by (auto simp add: image_def sum.neutral)
  next
    case (insert a A)
    have *: "(\<Sum>y\<in>insert a A. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y) = (\<Sum>y\<in>A. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y) + indicat_real (f -` {a} \<inter> space M) x *\<^sub>R a" for x using insert(2) by (subst sum.insert_remove[OF insert(1)], auto)

    show ?case unfolding *
      using cond_exp_add[OF insert(3) cond_exp_indicator, OF simple_functionD(2)[OF sf], of "{a}" a] 
      sorry
 
  qed
  have "AE x in M. f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"
    using banach_simple_function_indicator_representation_AE sorry
  thus ?thesis sorry
qed

lemma cond_exp_lim:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
      and "\<And>i. sb_integrable M (s i)"
      and "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
    shows "has_cond_exp M F f (\<lambda>x. lim (\<lambda>i. simple_cond_exp M F (s i) x))"
          "\<And>i. has_cond_exp M F (s i) (simple_cond_exp M F (s i))" 
proof (intro has_cond_expI)
  show simple_cond_exp: "has_cond_exp M F (s i) (simple_cond_exp M F (s i))" for i using cond_exp_simple[OF assms(2)] by blast
  show "(\<lambda>x. lim (\<lambda>i. simple_cond_exp M F (s i) x)) \<in> borel_measurable F" using has_cond_expD(4)[OF simple_cond_exp, THEN borel_measurable_lim_metric] .
  hence [measurable]:"(\<lambda>x. lim (\<lambda>i. simple_cond_exp M F (s i) x)) \<in> borel_measurable M" using measurable_from_subalg subalg by blast
  have "set_lebesgue_integral M A (s i) = set_lebesgue_integral M A (simple_cond_exp M F (s i))" if "A \<in> sets F" for A i using has_cond_expD[OF simple_cond_exp] that by blast
  have intA: "has_bochner_integral M (\<lambda>x. indicator A x *\<^sub>R lim (\<lambda>i. simple_cond_exp M F (s i) x)) (set_lebesgue_integral M A f)" if "A \<in> sets F" for A
  proof -
    let ?s = "\<lambda>i x. indicator A x *\<^sub>R s i x"
    have "(\<lambda>x. indicator A x *\<^sub>R lim (\<lambda>i. simple_cond_exp M F (s i) x)) \<in> borel_measurable M" by (intro borel_measurable_scaleR) (meson borel_measurable_indicator measurable_from_subalg subalg that, simp)
    have "\<And>i. sb_integrable M (?s i)" sorry

    have "(\<lambda>i. s i x) \<longlonglongrightarrow> f x" if "x \<in> space M" for x using banach_simple_function_indicator_representation that assms(2)[THEN simple_bochner_integrable.cases, THEN simple_functionD(1)] 

    have "(\<lambda>i. simple_cond_exp M F (s i) x) \<longlonglongrightarrow> lim (\<lambda>i. simple_cond_exp M F (s i) x)" for x sorry
    have "(\<lambda>i. \<integral>\<^sup>+ x. ennreal (norm (lim (\<lambda>i. simple_cond_exp M F (s i) x) - s i x)) \<partial>M) \<longlonglongrightarrow> 0" sorry

    have "(\<lambda>i. \<integral>\<^sup>+ x. ennreal (norm (indicat_real A x *\<^sub>R lim (\<lambda>i. simple_cond_exp M F (s i) x) - ?s i x)) \<partial>M) \<longlonglongrightarrow> 0" sorry
    have "(\<lambda>i. sb_integral M (?s i)) \<longlonglongrightarrow> set_lebesgue_integral M A f" sorry
    thus ?thesis sorry
  qed
    
  show "set_lebesgue_integral M A f = \<integral>x\<in>A. lim (\<lambda>i. simple_cond_exp M F (s i) x) \<partial>M" if "A \<in> sets F" for A using intA[OF that] by (simp add: has_bochner_integral_integral_eq set_lebesgue_integral_def)
  have "space M \<in> sets F" using sets.top subalg subalgebra_def by metis
  moreover have "AE x in M. indicat_real (space M) x *\<^sub>R lim (\<lambda>i. simple_cond_exp M F (s i) x) = lim (\<lambda>i. simple_cond_exp M F (s i) x)" by auto
  ultimately show "integrable M (\<lambda>x. lim (\<lambda>i. simple_cond_exp M F (s i) x))" using integrable_cong_AE[THEN iffD1, OF borel_measurable_has_bochner_integral[OF intA] _ _ intA[THEN integrable.intros]] by fastforce 
qed (simp add: assms)

lemma cond_exp_exists:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "integrable M f"
  shows "has_cond_exp M F f (cond_exp M F f)"
  using assms
proof (induction rule: integrable_induct')
  case (base A c)
  show ?case using cond_exp_indicator[OF base(1,2)] cond_exp_charact(1) by blast
next
  case (add u v)
  show ?case using cond_exp_add[OF add(3,4)] cond_exp_charact(1) by blast
next
  case (lim f s)
  show ?case using cond_exp_lim[OF lim(4,1,2,3)] cond_exp_charact(1) by blast
qed

lemma cond_exp_cong':
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes "AE x in M. f x = g x"
      and [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
    shows "AE x in M. cond_exp M F f x = cond_exp M F g x"
  sorry
  

lemma cond_exp_intA:
    fixes f :: "'a \<Rightarrow>'b :: {second_countable_topology,real_normed_vector}"
  assumes [measurable]: "integrable M f" "A \<in> sets F"
  shows "has_cond_exp M F f \<cc>\<^sub>f" "integrable F \<cc>\<^sub>f"
          "(\<integral> x \<in> A. f x \<partial>F) = (\<integral> x \<in> A. \<cc>\<^sub>f x \<partial>F)"
  sorry

lemma cond_exp_ae_eq:
  assumes "has_cond_exp M F f g"
  shows "AE x in M. cond_exp M F f x = g x"
proof -
  have "AE x in M. g x = lim (\<lambda>i. simple_cond_exp M F ((SOME s. (\<forall>i. sb_integrable M (s i)) \<and> (\<lambda>i. \<integral>\<^sup>+x. norm (f x - s i x) \<partial>M) \<longlonglongrightarrow> 0) i) x)"
oops

lemma real_cond_exp_int [intro]:
  assumes "integrable M f"
  obtains \<cc>\<^sub>f 
    where "has_cond_exp M F f \<cc>\<^sub>f" "integrable M \<cc>\<^sub>f" 
          "(\<integral>x. \<cc>\<^sub>f x \<partial>M) = (\<integral>x. f x \<partial>M)"
  sorry

lemma real_cond_exp_charact:
  assumes "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M)"
      and [measurable]: "integrable M f" "integrable M g"
          "g \<in> borel_measurable F"
  shows "AE x in M. real_cond_exp M F f x = g x"
  sorry

lemma real_cond_exp_F_meas [intro, simp]:
  assumes "integrable M f"
          "f \<in> borel_measurable F"
  shows "AE x in M. real_cond_exp M F f x = f x"
  sorry
lemma real_cond_exp_mult:
  assumes [measurable]:"f \<in> borel_measurable F" "g \<in> borel_measurable M" "integrable M (\<lambda>x. f x * g x)"
  shows "AE x in M. real_cond_exp M F (\<lambda>x. f x * g x) x = f x * real_cond_exp M F g x"
  sorry
lemma real_cond_exp_add [intro]:
  assumes [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_cond_exp M F (\<lambda>x. f x + g x) x = real_cond_exp M F f x + real_cond_exp M F g x"
  sorry
lemma real_cond_exp_cong:
  assumes ae: "AE x in M. f x = g x" and [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "AE x in M. real_cond_exp M F f x = real_cond_exp M F g x"
  sorry

lemma real_cond_exp_cmult [intro, simp]:
  fixes c::real
  assumes "integrable M f"
  shows "AE x in M. real_cond_exp M F (\<lambda>x. c * f x) x = c * real_cond_exp M F f x"
  sorry

lemma real_cond_exp_cdiv [intro, simp]:
  fixes c::real
  assumes "integrable M f"
  shows "AE x in M. real_cond_exp M F (\<lambda>x. f x / c) x = real_cond_exp M F f x / c"
  sorry

lemma real_cond_exp_diff [intro, simp]:
  assumes [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_cond_exp M F (\<lambda>x. f x - g x) x = real_cond_exp M F f x - real_cond_exp M F g x"
  sorry

lemma real_cond_exp_pos [intro]:
  assumes "AE x in M. f x \<ge> 0" and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. real_cond_exp M F f x \<ge> 0"
  sorry

lemma real_cond_exp_mono:
  assumes "AE x in M. f x \<le> g x" and [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_cond_exp M F f x \<le> real_cond_exp M F g x"
  sorry

lemma real_cond_exp_gr_c:
  assumes [measurable]: "integrable M f"
      and AE: "AE x in M. f x > c"
  shows "AE x in M. real_cond_exp M F f x > c"
  sorry

lemma real_cond_exp_less_c:
  assumes [measurable]: "integrable M f"
      and "AE x in M. f x < c"
  shows "AE x in M. real_cond_exp M F f x < c"
  sorry

lemma real_cond_exp_ge_c:
  assumes [measurable]: "integrable M f"
      and "AE x in M. f x \<ge> c"
  shows "AE x in M. real_cond_exp M F f x \<ge> c"
  sorry

lemma real_cond_exp_le_c:
  assumes [measurable]: "integrable M f"
      and "AE x in M. f x \<le> c"
  shows "AE x in M. real_cond_exp M F f x \<le> c"
  sorry

lemma real_cond_exp_mono_strict:
  assumes "AE x in M. f x < g x" and [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_cond_exp M F f x < real_cond_exp M F g x"
  sorry

lemma real_cond_exp_nested_subalg [intro, simp]:
  assumes "subalgebra M G" "subalgebra G F"
      and [measurable]: "integrable M f"
  shows "AE x in M. real_cond_exp M F (real_cond_exp M G f) x = real_cond_exp M F f x"
  sorry

lemma real_cond_exp_sum [intro, simp]:
  fixes f::"'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes [measurable]: "\<And>i. integrable M (f i)"
  shows "AE x in M. real_cond_exp M F (\<lambda>x. \<Sum>i\<in>I. f i x) x = (\<Sum>i\<in>I. real_cond_exp M F (f i) x)"
  sorry

theorem real_cond_exp_jensens_inequality:
  fixes q :: "real \<Rightarrow> real"
  assumes X: "integrable M X" "AE x in M. X x \<in> I"
  assumes I: "I = {a <..< b} \<or> I = {a <..} \<or> I = {..< b} \<or> I = UNIV"
  assumes q: "integrable M (\<lambda>x. q (X x))" "convex_on I q" "q \<in> borel_measurable borel"
  shows "AE x in M. real_cond_exp M F X x \<in> I"
        "AE x in M. q (real_cond_exp M F X x) \<le> real_cond_exp M F (\<lambda>x. q (X x)) x"
  sorry


lemma integrable_convex_cond_exp:
  fixes q :: "real \<Rightarrow> real"
  assumes X: "integrable M X" "AE x in M. X x \<in> I"
  assumes I: "I = {a <..< b} \<or> I = {a <..} \<or> I = {..< b} \<or> I = UNIV"
  assumes q: "integrable M (\<lambda>x. q (X x))" "convex_on I q" "q \<in> borel_measurable borel"
  assumes H: "emeasure M (space M) = \<infinity> \<Longrightarrow> 0 \<in> I"
  shows "integrable M (\<lambda>x. q (real_cond_exp M F X x))"
  sorry

end


subsection  \<open>Introduce binder for cond_exp\<close>

syntax
  "_cond_exp" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>((/cond'_exp _ _ _ = _/))\<close>)

translations  "cond_exp M F f = g" => "CONST has_cond_exp M F f g"

end