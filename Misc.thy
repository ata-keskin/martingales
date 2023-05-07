theory Misc
  imports "HOL-Analysis.Measure_Space" "HOL-Analysis.Bochner_Integration" "HOL-Analysis.Set_Integral"
begin

lemma banach_simple_function_indicator_representation:
  fixes f ::"'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "simple_function M f" and x: "x \<in> space M"
  shows "f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"
  (is "?l = ?r")
proof -
  have "?r = (\<Sum>y \<in> f ` space M.
    (if y = f x then indicator (f -` {y} \<inter> space M) x *\<^sub>R y else 0))" by (auto intro!: sum.cong)
  also have "... =  indicator (f -` {f x} \<inter> space M) x *\<^sub>R f x" using assms by (auto dest: simple_functionD)
  also have "... = f x" using x by (auto simp: indicator_def)
  finally show ?thesis by auto
qed

lemma banach_simple_function_indicator_representation_AE:
  fixes f ::"'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "simple_function M f"
  shows "AE x in M. f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"  
  by (metis (mono_tags, lifting) AE_I2 banach_simple_function_indicator_representation f)


lemma integrable_induct''[consumes 1, case_names cong set add seq]:
  fixes P :: "('a \<Rightarrow> 'b :: {second_countable_topology, banach}) \<Rightarrow> bool"
  assumes u: "integrable M u"
  assumes cong: "\<And>f g. integrable M f \<Longrightarrow> integrable M g \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P g \<Longrightarrow> P f"
  assumes set: "\<And>A y. A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>u v. P u \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. u x + v x)"
  assumes seq: "\<And>s. (\<And>i. Bochner_Integration.simple_bochner_integrable M (s i)) \<Longrightarrow> ((\<lambda>i. \<integral>\<^sup>+x. norm (u x - s i x) \<partial>M) \<longlonglongrightarrow> 0) \<Longrightarrow> (\<And>i. P (s i)) \<Longrightarrow> P u"
  shows "P u"
proof-
  obtain I where "has_bochner_integral M u I" using u integrable.cases by auto
  then obtain s where s_is: "Bochner_Integration.simple_bochner_integrable M (s i)" 
                            "((\<lambda>i. \<integral>\<^sup>+x. norm (u x - s i x) \<partial>M) \<longlonglongrightarrow> 0)" for i using has_bochner_integral.cases by force
        
  have s_simple: "simple_function M (s i)" for i using s_is simple_bochner_integrable.simps by blast

  have "s i -` {0} \<inter> space M \<in> sets M" for i using simple_functionD[OF s_simple] by blast
  hence "space M - (s i -` {0} \<inter> space M) \<in> sets M" for i by blast
  moreover have "{x \<in> space M. s i x \<noteq> 0} = space M - (s i -` {0} \<inter> space M)" for i by blast
  moreover have "emeasure M {x \<in> space M. s i x \<noteq> 0} \<noteq> \<infinity>" for i using s_is simple_bochner_integrable.simps by blast
  moreover have "s i -` {y} \<inter> space M \<subseteq> {x \<in> space M. s i x \<noteq> 0}" if "y \<noteq> 0" for i y using that by fast
  ultimately have "emeasure M (s i -` {y} \<inter> space M) < \<infinity>" if "y \<noteq> 0" for i y by (metis (no_types, lifting) emeasure_mono that infinity_ennreal_def linorder_not_less top.not_eq_extremum)
  hence P_set: "P (\<lambda>x. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" if "y \<noteq> 0" for i y using set s_simple simple_functionD(2) that by meson
  
  have P_add: "P (\<lambda>x. \<Sum>y \<in> F. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" if "finite F" "F \<subseteq> s i ` space M" for i F using that
  proof (induction rule: finite_induct)
    case empty
    then show ?case using set[of "{}"] by simp
  next
    case (insert x F)
    hence asm: "F \<subseteq> s i ` space M" by fast
    have *: "(\<Sum>y\<in>insert x F. indicat_real (s i -` {y} \<inter> space M) z *\<^sub>R y) = indicat_real (s i -` {x} \<inter> space M) z *\<^sub>R x + (\<Sum>y\<in>F. indicat_real (s i -` {y} \<inter> space M) z *\<^sub>R y)" for z using insert(2) by (subst sum.insert_remove[OF insert(1)], auto)
    show ?case
    proof (cases "x = 0")
      case True
      show ?thesis using * by (fastforce simp add: insert(3)[OF asm] True)
    next
      case False
      show ?thesis using * insert(3)[OF asm] P_set[OF False, of i] add by presburger
    qed
  qed

  have s_i_integrable: "integrable M (s i)" for i by (simp add: integrableI_simple_bochner_integrable s_is(1))
  moreover have s_i_rep: "s i x = (\<Sum>y \<in> s i ` space M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" if "x \<in> space M" for x i using banach_simple_function_indicator_representation[OF s_simple that] by blast
  moreover have "integrable M (\<lambda>x. \<Sum>y \<in> s i ` space M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" for i using s_i_rep s_i_integrable by (rule integrable_cong[OF refl, of M "s i", THEN iffD1], blast)
  ultimately have "P (s i)" for i using cong P_add[OF simple_functionD(1)[OF s_simple] order.refl] by meson
  thus ?thesis using seq s_is by blast
qed

proposition integrable_induct'[consumes 1, case_names base add lim, induct pred: integrable]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  assumes base: "\<And>A c. A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R c)"
  assumes add: "\<And>f g. integrable M f \<Longrightarrow> P f \<Longrightarrow> integrable M g \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  assumes lim: "\<And>f s. integrable M f
                  \<Longrightarrow> (\<And>i. integrable M (s i)) 
                  \<Longrightarrow> (\<And>i. simple_function M (s i)) 
                  \<Longrightarrow> (\<And>i. emeasure M {y\<in>space M. s i y \<noteq> 0} \<noteq> \<infinity>) 
                  \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x) 
                  \<Longrightarrow> (\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)) 
                  \<Longrightarrow> (\<And>i. P (s i)) \<Longrightarrow> P f"
  shows "P f"
proof -
  from \<open>integrable M f\<close> have f: "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>"
    unfolding integrable_iff_bounded by auto
  from borel_measurable_implies_sequence_metric[OF f(1)]
  obtain s where s: "\<And>i. simple_function M (s i)" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
    "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
    unfolding norm_conv_dist by metis

  { fix f A
    have [simp]: "P (\<lambda>x. 0)"
      using base[of "{}" undefined] by simp
    have "(\<And>i::'b. i \<in> A \<Longrightarrow> integrable M (f i::'a \<Rightarrow> 'b)) \<Longrightarrow>
    (\<And>i. i \<in> A \<Longrightarrow> P (f i)) \<Longrightarrow> P (\<lambda>x. \<Sum>i\<in>A. f i x)"
    by (induct A rule: infinite_finite_induct) (auto intro!: add) }
  note sum = this

  define s' where [abs_def]: "s' i z = indicator (space M) z *\<^sub>R s i z" for i z
  then have s'_eq_s: "\<And>i x. x \<in> space M \<Longrightarrow> s' i x = s i x"
    by simp

  have sf[measurable]: "\<And>i. simple_function M (s' i)"
    unfolding s'_def using s(1)
    by (intro simple_function_compose2[where h="(*\<^sub>R)"] simple_function_indicator) auto

  { fix i
    have "\<And>z. {y. s' i z = y \<and> y \<in> s' i ` space M \<and> y \<noteq> 0 \<and> z \<in> space M} =
        (if z \<in> space M \<and> s' i z \<noteq> 0 then {s' i z} else {})"
      by (auto simp add: s'_def split: split_indicator)
    then have "\<And>z. s' i = (\<lambda>z. \<Sum>y\<in>s' i`space M - {0}. indicator {x\<in>space M. s' i x = y} z *\<^sub>R y)"
      using sf by (auto simp: fun_eq_iff simple_function_def s'_def) }
  note s'_eq = this

  show "P f"
  proof (rule lim)
    fix i

    have "(\<integral>\<^sup>+x. norm (s' i x) \<partial>M) \<le> (\<integral>\<^sup>+x. ennreal (2 * norm (f x)) \<partial>M)"
      using s by (intro nn_integral_mono) (auto simp: s'_eq_s)
    also have "\<dots> < \<infinity>"
      using f by (simp add: nn_integral_cmult ennreal_mult_less_top ennreal_mult)
    finally have sbi: "Bochner_Integration.simple_bochner_integrable M (s' i)"
      using sf by (intro simple_bochner_integrableI_bounded) auto
    thus "integrable M (s' i)" "simple_function M (s' i)" "emeasure M {y\<in>space M. s' i y \<noteq> 0} \<noteq> \<infinity>" by (auto intro: integrableI_simple_bochner_integrable simple_bochner_integrable.cases)

    { fix x assume"x \<in> space M" "s' i x \<noteq> 0"
      then have "emeasure M {y \<in> space M. s' i y = s' i x} \<le> emeasure M {y \<in> space M. s' i y \<noteq> 0}"
        by (intro emeasure_mono) auto
      also have "\<dots> < \<infinity>"
        using sbi by (auto elim: simple_bochner_integrable.cases simp: less_top)
      finally have "emeasure M {y \<in> space M. s' i y = s' i x} \<noteq> \<infinity>" by simp }
    then show "P (s' i)"
      by (subst s'_eq) (auto intro!: sum base simp: less_top)

    fix x assume "x \<in> space M" with s show "(\<lambda>i. s' i x) \<longlonglongrightarrow> f x"
      by (simp add: s'_eq_s)
    show "norm (s' i x) \<le> 2 * norm (f x)"
      using \<open>x \<in> space M\<close> s by (simp add: s'_eq_s)
  qed fact
qed

lemma set_integral_scaleR_left: 
  assumes "A \<in> sets M" "c \<noteq> 0 \<Longrightarrow> integrable M f"
  shows "LINT t:A|M. f t *\<^sub>R c = (LINT t:A|M. f t) *\<^sub>R c"
  unfolding set_lebesgue_integral_def 
  using integrable_mult_indicator[OF assms]
  by (subst integral_scaleR_left[symmetric], auto)

lemmas simple_function_scaleR = simple_function_compose2[where h="(*\<^sub>R)"]

end