theory Bochner_Integration_Addendum
  imports "HOL-Analysis.Bochner_Integration"
begin

subsection "Simple Functions"
  
lemma integrable_implies_simple_function_sequence:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  obtains s where "\<And>i. simple_function M (s i)"
      and "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>"
      and "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
proof-
  have f: "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>" using assms unfolding integrable_iff_bounded by auto
  obtain s where s: "\<And>i. simple_function M (s i)" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" using borel_measurable_implies_sequence_metric[OF f(1)] unfolding norm_conv_dist by metis
  {
    fix i
    have "(\<integral>\<^sup>+x. norm (s i x) \<partial>M) \<le> (\<integral>\<^sup>+x. ennreal (2 * norm (f x)) \<partial>M)" using s by (intro nn_integral_mono, auto)
    also have "\<dots> < \<infinity>" using f by (simp add: nn_integral_cmult ennreal_mult_less_top ennreal_mult)
    finally have sbi: "Bochner_Integration.simple_bochner_integrable M (s i)" using s by (intro simple_bochner_integrableI_bounded) auto
    hence "emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>" by (auto intro: integrableI_simple_bochner_integrable simple_bochner_integrable.cases)
  }
  thus ?thesis using that s by blast
  qed

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

lemmas simple_function_scaleR[intro] = simple_function_compose2[where h="(*\<^sub>R)"]

lemma integrable_simple_function:
  assumes "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  shows "integrable M f"
  using assms has_bochner_integral_simple_bochner_integrable integrable.simps simple_bochner_integrable.simps by blast

lemma\<^marker>\<open>tag important\<close> simple_integrable_function_induct[consumes 2, case_names cong indicator add, induct set: simple_function]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes indicator: "\<And>A y. A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>z. z \<in> space M \<Longrightarrow> norm (f z + g z) = norm (f z) + norm (g z)) \<Longrightarrow>
                      P f \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  shows "P f"
proof-
  let ?f = "\<lambda>x. (\<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
  have f_ae_eq: "f x = ?f x" if "x \<in> space M" for x using banach_simple_function_indicator_representation[OF f(1) that] .
  moreover have "emeasure M {y \<in> space M. ?f y \<noteq> 0} \<noteq> \<infinity>" by (metis (no_types, lifting) Collect_cong calculation f(2))
  moreover have "P (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "simple_function M (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "emeasure M {y \<in> space M. (\<Sum>x\<in>S. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<noteq> \<infinity>"
                if "S \<subseteq> f ` space M" for S using simple_functionD(1)[OF assms(1), THEN rev_finite_subset, OF that] that 
  proof (induction rule: finite_induct)
    case empty
    {
      case 1
      then show ?case using indicator[of "{}"] by force
    next
      case 2
      then show ?case by force 
    next
      case 3
      then show ?case by force 
    }
  next
    case (insert x F)
    have "(f -` {x} \<inter> space M) \<subseteq> {y \<in> space M. f y \<noteq> 0}" if "x \<noteq> 0" using that by blast
    moreover have "{y \<in> space M. f y \<noteq> 0} = space M - (f -` {0} \<inter> space M)" by blast
    moreover have "space M - (f -` {0} \<inter> space M) \<in> sets M" using simple_functionD(2)[OF f(1)] by blast
    ultimately have fin_0: "emeasure M (f -` {x} \<inter> space M) < \<infinity>" if "x \<noteq> 0" using that by (metis emeasure_mono f(2) infinity_ennreal_def top.not_eq_extremum top_unique)
    hence fin_1: "emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0} \<noteq> \<infinity>" if "x \<noteq> 0" by (metis (mono_tags, lifting) emeasure_mono f(1) indicator_simps(2) linorder_not_less mem_Collect_eq scaleR_eq_0_iff simple_functionD(2) subsetI that)

    have *: "(\<Sum>y\<in>insert x F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) = (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) xa *\<^sub>R x" for xa by (metis (no_types, lifting) Diff_empty Diff_insert0 add.commute insert.hyps(1) insert.hyps(2) sum.insert_remove)
    have **: "{y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<subseteq> {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}" unfolding * by fastforce    
    {
      case 1
      hence x: "x \<in> f ` space M" and F: "F \<subseteq> f ` space M" by auto
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert(3)[OF F] by simp
      next
        case False
        have norm_argument: "norm ((\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x) = norm (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + norm (indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x)" if z: "z \<in> space M" for z
        proof (cases "f z = x")
          case True
          have "indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y = 0" if "y \<in> F" for y using True insert(2) z that 1 unfolding indicator_def by force
          hence "(\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) = 0" by (meson sum.neutral)
          then show ?thesis by force
        next
          case False
          then show ?thesis by force
        qed
        show ?thesis using False simple_functionD(2)[OF f(1)] insert(3,5)[OF F] simple_function_scaleR fin_0 fin_1 by (subst *, subst add, subst simple_function_sum) (blast intro: norm_argument indicator)+
      qed 
    next
      case 2
      hence x: "x \<in> f ` space M" and F: "F \<subseteq> f ` space M" by auto
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert(4)[OF F] by simp
      next
        case False
        then show ?thesis unfolding * using insert(4)[OF F] simple_functionD(2)[OF f(1)] by fast
      qed
    next
      case 3
      hence x: "x \<in> f ` space M" and F: "F \<subseteq> f ` space M" by auto
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert(5)[OF F] by simp
      next
        case False
        have "emeasure M {y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<le> emeasure M ({y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0})"
          using ** simple_functionD(2)[OF insert(4)[OF F]] simple_functionD(2)[OF f(1)] by (intro emeasure_mono, force+)
        also have "... \<le> emeasure M {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} + emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}"
          using simple_functionD(2)[OF insert(4)[OF F]] simple_functionD(2)[OF f(1)] by (intro emeasure_subadditive, force+)
        also have "... < \<infinity>" using insert(5)[OF F] fin_1[OF False] by (simp add: less_top)
        finally show ?thesis by simp
      qed
    }
  qed
  moreover have "simple_function M (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" using calculation by blast
  moreover have "P (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" using calculation by blast
  ultimately show ?thesis by (intro cong[OF _ _ f(1,2)], blast, presburger+) 
qed

lemma\<^marker>\<open>tag important\<close> simple_integrable_function_induct_nonneg[consumes 3, case_names cong indicator add, induct set: simple_function]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes f: "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<longrightarrow> f x \<ge> 0"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> g x \<ge> 0) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes indicator: "\<And>A y. y \<ge> 0 \<Longrightarrow> A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>f g. (\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>x. x \<in> space M \<Longrightarrow> g x \<ge> 0) \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>z. z \<in> space M \<Longrightarrow> norm (f z + g z) = norm (f z) + norm (g z)) \<Longrightarrow>
                      P f \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  shows "P f"
proof-
  let ?f = "\<lambda>x. (\<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
  have f_ae_eq: "f x = ?f x" if "x \<in> space M" for x using banach_simple_function_indicator_representation[OF f(1) that] .
  moreover have "emeasure M {y \<in> space M. ?f y \<noteq> 0} \<noteq> \<infinity>" by (metis (no_types, lifting) Collect_cong calculation f(2))
  moreover have "P (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "simple_function M (\<lambda>x. \<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                "emeasure M {y \<in> space M. (\<Sum>x\<in>S. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<noteq> \<infinity>"
                "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> (\<Sum>y\<in>S. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)"
                if "S \<subseteq> f ` space M" for S using simple_functionD(1)[OF assms(1), THEN rev_finite_subset, OF that] that 
  proof (induction rule: finite_subset_induct')
    case empty
    {
      case 1
      then show ?case using indicator[of 0 "{}"] by force
    next
      case 2
      then show ?case by force 
    next
      case 3
      then show ?case by force 
    next
      case 4
      then show ?case by force 
    }
  next
    case (insert x F)
    have "(f -` {x} \<inter> space M) \<subseteq> {y \<in> space M. f y \<noteq> 0}" if "x \<noteq> 0" using that by blast
    moreover have "{y \<in> space M. f y \<noteq> 0} = space M - (f -` {0} \<inter> space M)" by blast
    moreover have "space M - (f -` {0} \<inter> space M) \<in> sets M" using simple_functionD(2)[OF f(1)] by blast
    ultimately have fin_0: "emeasure M (f -` {x} \<inter> space M) < \<infinity>" if "x \<noteq> 0" using that by (metis emeasure_mono f(2) infinity_ennreal_def top.not_eq_extremum top_unique)
    hence fin_1: "emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0} \<noteq> \<infinity>" if "x \<noteq> 0" by (metis (mono_tags, lifting) emeasure_mono f(1) indicator_simps(2) linorder_not_less mem_Collect_eq scaleR_eq_0_iff simple_functionD(2) subsetI that)

    have nonneg_x: "x \<ge> 0" using insert f by blast
    have *: "(\<Sum>y\<in>insert x F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) = (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) xa *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) xa *\<^sub>R x" for xa by (metis (no_types, lifting) add.commute insert.hyps(1) insert.hyps(4) sum.insert)
    have **: "{y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<subseteq> {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}" unfolding * by fastforce    
    {
      case 1
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert by simp
      next
        case False
        have norm_argument: "norm ((\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x) = norm (\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) + norm (indicat_real (f -` {x} \<inter> space M) z *\<^sub>R x)" if z: "z \<in> space M" for z
        proof (cases "f z = x")
          case True
          have "indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y = 0" if "y \<in> F" for y using True insert z that 1 unfolding indicator_def by force
          hence "(\<Sum>y\<in>F. indicat_real (f -` {y} \<inter> space M) z *\<^sub>R y) = 0" by (meson sum.neutral)
          thus ?thesis by force
        qed (force)
        show ?thesis using False fin_0 fin_1 f norm_argument by (subst *, subst add, presburger add: insert, intro insert, intro insert, fastforce simp add: indicator_def intro!: insert(2) f(3), auto intro!: indicator insert nonneg_x)
      qed 
    next
      case 2
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert by simp
      next
        case False
        then show ?thesis unfolding * using insert simple_functionD(2)[OF f(1)] by fast
      qed
    next
      case 3
      show ?case 
      proof (cases "x = 0")
        case True
        then show ?thesis unfolding * using insert by simp
      next
        case False
        have "emeasure M {y \<in> space M. (\<Sum>x\<in>insert x F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<le> emeasure M ({y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} \<union> {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0})"
          using ** simple_functionD(2)[OF insert(6)] simple_functionD(2)[OF f(1)] insert.IH(2) by (intro emeasure_mono, blast, simp) 
        also have "... \<le> emeasure M {y \<in> space M. (\<Sum>x\<in>F. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x) \<noteq> 0} + emeasure M {y \<in> space M. indicat_real (f -` {x} \<inter> space M) y *\<^sub>R x \<noteq> 0}"
          using simple_functionD(2)[OF insert(6)] simple_functionD(2)[OF f(1)] by (intro emeasure_subadditive, force+)
        also have "... < \<infinity>" using insert(7) fin_1[OF False] by (simp add: less_top)
        finally show ?thesis by simp
      qed
    next
      case (4 \<xi>)
      thus ?case using insert nonneg_x f(3) by (auto simp add: scaleR_nonneg_nonneg intro: sum_nonneg)
    }
  qed
  moreover have "simple_function M (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" using calculation by blast
  moreover have "P (\<lambda>x. \<Sum>y\<in>f ` space M. indicat_real (f -` {y} \<inter> space M) x *\<^sub>R y)" using calculation by blast
  moreover have "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x" using f(3) by simp
  ultimately show ?thesis by (intro cong[OF _ _ _ f(1,2)], blast, blast, fast) presburger+
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
  have f: "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. norm (f x) \<partial>M) < \<infinity>" using assms(1) unfolding integrable_iff_bounded by auto
  obtain s where s: "\<And>i. simple_function M (s i)" "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" "\<And>i x. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" using borel_measurable_implies_sequence_metric[OF f(1)] unfolding norm_conv_dist by metis

  { 
    fix f A
    have [simp]: "P (\<lambda>x. 0)" using base[of "{}" undefined] by simp
    have "(\<And>i::'b. i \<in> A \<Longrightarrow> integrable M (f i::'a \<Rightarrow> 'b)) \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> P (f i)) \<Longrightarrow> P (\<lambda>x. \<Sum>i\<in>A. f i x)" by (induct A rule: infinite_finite_induct) (auto intro!: add) 
  }
  note sum = this

  define s' where [abs_def]: "s' i z = indicator (space M) z *\<^sub>R s i z" for i z
  hence s'_eq_s: "\<And>i x. x \<in> space M \<Longrightarrow> s' i x = s i x" by simp

  have sf[measurable]: "\<And>i. simple_function M (s' i)" unfolding s'_def using s(1) by (intro simple_function_compose2[where h="(*\<^sub>R)"] simple_function_indicator) auto

  { 
    fix i
    have "\<And>z. {y. s' i z = y \<and> y \<in> s' i ` space M \<and> y \<noteq> 0 \<and> z \<in> space M} = (if z \<in> space M \<and> s' i z \<noteq> 0 then {s' i z} else {})" by (auto simp add: s'_def split: split_indicator)
    then have "\<And>z. s' i = (\<lambda>z. \<Sum>y\<in>s' i`space M - {0}. indicator {x\<in>space M. s' i x = y} z *\<^sub>R y)" using sf by (auto simp: fun_eq_iff simple_function_def s'_def) 
  }
  note s'_eq = this

  show "P f"
  proof (rule lim)
    fix i
    have "(\<integral>\<^sup>+x. norm (s' i x) \<partial>M) \<le> (\<integral>\<^sup>+x. ennreal (2 * norm (f x)) \<partial>M)" using s by (intro nn_integral_mono) (auto simp: s'_eq_s)
    also have "\<dots> < \<infinity>" using f by (simp add: nn_integral_cmult ennreal_mult_less_top ennreal_mult)
    finally have sbi: "Bochner_Integration.simple_bochner_integrable M (s' i)" using sf by (intro simple_bochner_integrableI_bounded) auto
    thus "integrable M (s' i)" "simple_function M (s' i)" "emeasure M {y\<in>space M. s' i y \<noteq> 0} \<noteq> \<infinity>" by (auto intro: integrableI_simple_bochner_integrable simple_bochner_integrable.cases)

    { 
      fix x assume"x \<in> space M" "s' i x \<noteq> 0"
      then have "emeasure M {y \<in> space M. s' i y = s' i x} \<le> emeasure M {y \<in> space M. s' i y \<noteq> 0}" by (intro emeasure_mono) auto
      also have "\<dots> < \<infinity>" using sbi by (auto elim: simple_bochner_integrable.cases simp: less_top)
      finally have "emeasure M {y \<in> space M. s' i y = s' i x} \<noteq> \<infinity>" by simp 
    }
    then show "P (s' i)" by (subst s'_eq) (auto intro!: sum base simp: less_top)

    fix x assume "x \<in> space M" 
    thus "(\<lambda>i. s' i x) \<longlonglongrightarrow> f x" using s by (simp add: s'_eq_s)
    show "norm (s' i x) \<le> 2 * norm (f x)" using \<open>x \<in> space M\<close> s by (simp add: s'_eq_s)
  qed fact
qed

lemma finite_nn_integral_imp_ae_finite:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>"
  shows "AE x in M. f x < \<infinity>"
proof (rule ccontr, goal_cases)
  case 1
  let ?A = "space M \<inter> {x. f x = \<infinity>}"
  have *: "emeasure M ?A > 0" using 1 assms(1) by (metis (mono_tags, lifting) assms(2) eventually_mono infinity_ennreal_def nn_integral_noteq_infinite top.not_eq_extremum)
  have "(\<integral>\<^sup>+x. f x * indicator ?A x \<partial>M) = (\<integral>\<^sup>+x. \<infinity> * indicator ?A x \<partial>M)" by (metis (mono_tags, lifting) indicator_inter_arith indicator_simps(2) mem_Collect_eq mult_eq_0_iff)
  also have "... = \<infinity> * emeasure M ?A" using assms(1) by (intro nn_integral_cmult_indicator, simp)
  also have "... = \<infinity>" using * by fastforce
  finally have "(\<integral>\<^sup>+x. f x * indicator ?A x \<partial>M) = \<infinity>" .
  moreover have "(\<integral>\<^sup>+x. f x * indicator ?A x \<partial>M) \<le> (\<integral>\<^sup>+x. f x \<partial>M)" by (intro nn_integral_mono, simp add: indicator_def)
  ultimately show ?case using assms(2) by simp
qed

lemma cauchy_L1_AE_cauchy_subseq:
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "\<And>n. integrable M (s n)"
      and "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. LINT x|M. dist (s i x) (s j x) < e"
  obtains r where "strict_mono r" "AE x in M. Cauchy (\<lambda>i. s (r i) x)"
proof-
  have "\<exists>r. \<forall>n. (\<forall>i\<ge>r n. \<forall>j\<ge> r n. LINT x|M. dist (s i x) (s j x) < (1 / 2) ^ n) \<and> (r (Suc n) > r n)"
  proof (intro dependent_nat_choice, goal_cases)
    case 1
    then show ?case using assms(2) by presburger
  next
    case (2 x n)
    obtain N where *: "LINT x|M. dist (s i x) (s j x) < (1 / 2) ^ Suc n" if "i \<ge> N" "j \<ge> N" for i j using assms(2)[of "(1 / 2) ^ Suc n"] by auto
    {
      fix i j assume "i \<ge> max N (Suc x)" "j \<ge> max N (Suc x)"
      hence "integral\<^sup>L M (\<lambda>x. dist (s i x) (s j x)) < (1 / 2) ^ Suc n" using * by fastforce
    }
    then show ?case by fastforce
  qed
  then obtain r where strict_mono: "strict_mono r" and "\<forall>i\<ge>r n. \<forall>j\<ge> r n. LINT x|M. dist (s i x) (s j x) < (1 / 2) ^ n" for n using strict_mono_Suc_iff by blast
  hence r_is: "LINT x|M. dist (s (r (Suc n)) x) (s (r n) x) < (1 / 2) ^ n" for n by (simp add: strict_mono_leD)

  define g where "g = (\<lambda>n x. (\<Sum>i\<le>n. ennreal (dist (s (r (Suc i)) x) (s (r i) x))))"
  define g' where "g' = (\<lambda>x. \<Sum>i. ennreal (dist (s (r (Suc i)) x) (s (r i) x)))"

  have integrable_g: "(\<integral>\<^sup>+ x. g n x \<partial>M) < 2" for n
  proof -
    have "(\<integral>\<^sup>+ x. g n x \<partial>M) = (\<integral>\<^sup>+ x. (\<Sum>i\<le>n. ennreal (dist (s (r (Suc i)) x) (s (r i) x))) \<partial>M)" using g_def by simp
    also have "... = (\<Sum>i\<le>n. (\<integral>\<^sup>+ x. ennreal (dist (s (r (Suc i)) x) (s (r i) x)) \<partial>M))" by (intro nn_integral_sum, simp)
    also have "... = (\<Sum>i\<le>n. LINT x|M. dist (s (r (Suc i)) x) (s (r i) x))" unfolding dist_norm using assms(1) by (subst nn_integral_eq_integral[OF integrable_norm], auto)
    also have "... < ennreal (\<Sum>i\<le>n. (1 / 2) ^ i)" by (intro ennreal_lessI[OF sum_pos sum_strict_mono[OF finite_atMost _ r_is]], auto)
    also have "... \<le> ennreal 2" unfolding sum_gp0[of "1 / 2" n] by (intro ennreal_leI, auto)
    finally show "(\<integral>\<^sup>+ x. g n x \<partial>M) < 2" by simp
  qed

  have integrable_g': "(\<integral>\<^sup>+ x. g' x \<partial>M) \<le> 2"
  proof -
    have "incseq (\<lambda>n. g n x)" for x by (intro incseq_SucI, auto simp add: g_def ennreal_leI)
    hence "convergent (\<lambda>n. g n x)" for x unfolding convergent_def using LIMSEQ_incseq_SUP by fast
    hence "(\<lambda>n. g n x) \<longlonglongrightarrow> g' x" for x unfolding g_def g'_def by (intro summable_iff_convergent'[THEN iffD2, THEN summable_LIMSEQ'], blast)
    hence "(\<integral>\<^sup>+ x. g' x \<partial>M) = (\<integral>\<^sup>+ x. liminf (\<lambda>n. g n x) \<partial>M)" by (metis lim_imp_Liminf trivial_limit_sequentially)
    also have "... \<le> liminf (\<lambda>n. \<integral>\<^sup>+ x. g n x \<partial>M)" by (intro nn_integral_liminf, simp add: g_def)
    also have "... \<le> liminf (\<lambda>n. 2)" using integrable_g by (intro Liminf_mono) (simp add: order_le_less)
    also have "... = 2" using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
    finally show ?thesis .
  qed
  hence "AE x in M. g' x < \<infinity>" by (intro finite_nn_integral_imp_ae_finite) (auto simp add: order_le_less_trans g'_def)
  moreover have "summable (\<lambda>i. dist (s (r (Suc i)) x) (s (r i) x))" if "g' x \<noteq> \<infinity>" for x using that unfolding g'_def by (intro summable_suminf_not_top, intro zero_le_dist, fastforce) 
  ultimately have ae_summable: "AE x in M. summable (\<lambda>i. s (r (Suc i)) x - s (r i) x)" using summable_norm_cancel unfolding dist_norm by force

  {
    fix x assume "summable (\<lambda>i. s (r (Suc i)) x - s (r i) x)"
    hence "(\<lambda>n. \<Sum>i<n. s (r (Suc i)) x - s (r i) x) \<longlonglongrightarrow> (\<Sum>i. s (r (Suc i)) x - s (r i) x)" using summable_LIMSEQ by blast
    moreover have "(\<lambda>n. (\<Sum>i<n. s (r (Suc i)) x - s (r i) x)) = (\<lambda>n. s (r n) x - s (r 0) x)" using sum_lessThan_telescope by fastforce
    ultimately have "(\<lambda>n. s (r n) x - s (r 0) x) \<longlonglongrightarrow> (\<Sum>i. s (r (Suc i)) x - s (r i) x)" by argo
    hence "(\<lambda>n. s (r n) x - s (r 0) x + s (r 0) x) \<longlonglongrightarrow> (\<Sum>i. s (r (Suc i)) x - s (r i) x) + s (r 0) x" by (intro isCont_tendsto_compose[of _ "\<lambda>z. z + s (r 0) x"], auto)
    hence "Cauchy (\<lambda>n. s (r n) x)" by (simp add: LIMSEQ_imp_Cauchy)
  }

  hence "AE x in M. Cauchy (\<lambda>i. s (r i) x)" using ae_summable by fast
  thus ?thesis by (rule that[OF strict_mono(1)])
qed

lemma integrable_max[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology}"
  assumes fg[measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. max (f x) (g x))"
proof (rule Bochner_Integration.integrable_bound)
  {
    fix x y :: 'b                                             
    have "norm (max x y) \<le> max (norm x) (norm y)" by linarith
    also have "... \<le> norm x + norm y" by simp
    finally have "norm (max x y) \<le> norm (norm x + norm y)" by simp
  }
  thus "AE x in M. norm (max (f x) (g x)) \<le> norm (norm (f x) + norm (g x))" by simp
qed (auto intro: Bochner_Integration.integrable_add[OF integrable_norm[OF fg(1)] integrable_norm[OF fg(2)]])

lemma integrable_min[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology}"
  assumes [measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. min (f x) (g x))"
proof -
  have "norm (min (f x) (g x)) \<le> norm (f x) \<or> norm (min (f x) (g x)) \<le> norm (g x)" for x by linarith
  thus ?thesis by (intro integrable_bound[OF integrable_max[OF integrable_norm(1,1), OF assms]], auto)
qed

(* Versions of \<^thm>\<open>Bochner_Integration.integral_mono_AE\<close> for arbitrary orders *)

lemma integral_nonneg_AE_banach:                        
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes [measurable]: "f \<in> borel_measurable M" and nonneg: "AE x in M. 0 \<le> f x"
  shows "0 \<le> integral\<^sup>L M f"
proof cases
  assume integrable: "integrable M f"
  hence max: "(\<lambda>x. max 0 (f x)) \<in> borel_measurable M" "\<And>x. 0 \<le> max 0 (f x)" "integrable M (\<lambda>x. max 0 (f x))" by auto
  hence "0 \<le> integral\<^sup>L M (\<lambda>x. max 0 (f x))"
  proof -
  obtain s where *: "\<And>i. simple_function M (s i)" 
                    "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>" 
                    "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x" 
                    "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)" using integrable_implies_simple_function_sequence[OF integrable] by blast
    have simple: "\<And>i. simple_function M (\<lambda>x. max 0 (s i x))" using * by fast
    have "\<And>i. {y \<in> space M. max 0 (s i y) \<noteq> 0} \<subseteq> {y \<in> space M. s i y \<noteq> 0}" unfolding max_def by force
    moreover have "\<And>i. {y \<in> space M. s i y \<noteq> 0} \<in> sets M" using * by measurable
    ultimately have "\<And>i. emeasure M {y \<in> space M. max 0 (s i y) \<noteq> 0} \<le> emeasure M {y \<in> space M. s i y \<noteq> 0}" by (rule emeasure_mono) 
    hence **:"\<And>i. emeasure M {y \<in> space M. max 0 (s i y) \<noteq> 0} \<noteq> \<infinity>" using *(2) by (auto intro: order.strict_trans1 simp add:  top.not_eq_extremum)
    have "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. max 0 (s i x)) \<longlonglongrightarrow> max 0 (f x)" using *(3) tendsto_max by blast
    moreover have "\<And>x i. x \<in> space M \<Longrightarrow> norm (max 0 (s i x)) \<le> norm (2 *\<^sub>R f x)" using *(4) unfolding max_def by auto
    ultimately have tendsto: "(\<lambda>i. integral\<^sup>L M (\<lambda>x. max 0 (s i x))) \<longlonglongrightarrow> integral\<^sup>L M (\<lambda>x. max 0 (f x))" 
      using borel_measurable_simple_function simple integrable by (intro integral_dominated_convergence[OF max(1) _ integrable_norm[OF integrable_scaleR_right], of _ 2 f], blast+)
    {
      fix h :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}" 
      assume "simple_function M h" "emeasure M {y \<in> space M. h y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<longrightarrow> h x \<ge> 0"
      hence *: "integral\<^sup>L M h \<ge> 0"
      proof (induct rule: simple_integrable_function_induct_nonneg)
        case (cong f g)                   
        then show ?case using Bochner_Integration.integral_cong by force
      next
        case (indicator A y)
        hence "A \<noteq> {} \<Longrightarrow> y \<ge> 0" using sets.sets_into_space by fastforce
        then show ?case using indicator by (cases "A = {}", auto simp add: scaleR_nonneg_nonneg)
      next
        case (add f g)
        then show ?case by (simp add: integrable_simple_function)
      qed
    }
    thus ?thesis using LIMSEQ_le_const[OF tendsto, of 0] ** simple by fastforce
  qed
  also have "\<dots> = integral\<^sup>L M f" using nonneg by (auto intro: integral_cong_AE)
  finally show ?thesis .
qed (simp add: not_integrable_integral_eq)

lemma integral_mono_AE_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
  using integral_nonneg_AE_banach[of "\<lambda>x. g x - f x"] assms Bochner_Integration.integral_diff[OF assms(1,2)] by force

lemma integral_mono_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "\<And>x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
  using integral_mono_AE_banach assms by blast

end