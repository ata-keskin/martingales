theory Elementary_Metric_Spaces_Addendum
  imports "HOL-Analysis.Elementary_Metric_Spaces" "HOL-Analysis.Bochner_Integration"
begin

lemma diameter_comp_strict_mono:
  fixes s :: "nat \<Rightarrow> 'a :: real_normed_vector"
  assumes "strict_mono r" "bounded {s i |i. r n \<le> i}"
  shows "diameter {s (r i) | i. n \<le> i} \<le> diameter {s i | i. r n \<le> i}"
proof (rule diameter_subset)
  show "{s (r i) | i. n \<le> i} \<subseteq> {s i | i. r n \<le> i}" using assms(1) monotoneD strict_mono_mono by fastforce
qed (intro assms(2))

lemma diameter_bounded_bound':
  fixes S :: "'a :: metric_space set"
  assumes S: "bdd_above (case_prod dist ` (S\<times>S))" "x \<in> S" "y \<in> S"
  shows "dist x y \<le> diameter S"
proof -
  have "(x,y) \<in> S\<times>S" using S by auto
  then have "dist x y \<le> (SUP (x,y)\<in>S\<times>S. dist x y)" by (rule cSUP_upper2[OF assms(1)]) simp
  with \<open>x \<in> S\<close> show ?thesis by (auto simp: diameter_def)
qed

lemma bounded_imp_dist_bounded:
  assumes "bounded (range s)"
  shows "bounded ((\<lambda>(i, j). dist (s i) (s j)) ` ({n..} \<times> {n..}))"
  using bounded_dist_comp[OF bounded_fst bounded_snd, OF bounded_Times(1,1)[OF assms(1,1)]] by (rule bounded_subset, force) 

lemma cauchy_iff_diameter_tends_to_zero_and_bounded:
  fixes s :: "nat \<Rightarrow> 'a :: real_normed_vector"
  shows "Cauchy s \<longleftrightarrow> ((\<lambda>n. diameter {s i | i. i \<ge> n}) \<longlonglongrightarrow> 0 \<and> bounded (range s))"
proof -
  have "{s i |i. N \<le> i} \<noteq> {}" for N by blast
  hence diameter_SUP: "diameter {s i |i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i) (s j))" for N unfolding diameter_def by (auto intro!: arg_cong[of _ _ Sup])
  show ?thesis 
  proof ((standard ; clarsimp), goal_cases)
    case 1
    have "\<exists>N. \<forall>n\<ge>N. norm (diameter {s i |i. n \<le> i}) < e" if e_pos: "e > 0" for e
    proof -
      obtain N where dist_less: "dist (s n) (s m) < (1/2) * e" if "n \<ge> N" "m \<ge> N" for n m using 1 CauchyD e_pos dist_norm by (metis mult_pos_pos zero_less_divide_iff zero_less_numeral zero_less_one)
      {
        fix r assume "r \<ge> N"
        hence "dist (s n) (s m) < (1/2) * e" if "n \<ge> r" "m \<ge> r" for n m using dist_less that by simp
        hence "(SUP (i, j) \<in> {r..} \<times> {r..}. dist (s i) (s j)) \<le> (1/2) * e" by (intro cSup_least) fastforce+
        also have "... < e" using e_pos by simp
        finally have "diameter {s i |i. r \<le> i} < e" using diameter_SUP by presburger
      }
      moreover have "diameter {s i |i. r \<le> i} \<ge> 0" for r unfolding diameter_SUP using bounded_imp_dist_bounded[OF cauchy_imp_bounded, THEN bounded_imp_bdd_above, OF 1] by (intro cSup_upper2, auto)
      ultimately show ?thesis by auto
    qed                 
    thus ?case using cauchy_imp_bounded[OF 1] by (simp add: LIMSEQ_iff)
  next
    case 2
    have "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (s n) (s m) < e" if e_pos: "e > 0" for e
    proof -
      obtain N where diam_less: "diameter {s i |i. r \<le> i} < e" if "r \<ge> N" for r using LIMSEQ_D 2(1) e_pos by fastforce
      {
        fix n m assume "n \<ge> N" "m \<ge> N"
        hence "dist (s n) (s m) < e" using cSUP_lessD[OF bounded_imp_dist_bounded[THEN bounded_imp_bdd_above], OF 2(2) diam_less[unfolded diameter_SUP]] by auto
      }
      thus ?thesis by blast
    qed
    then show ?case by (intro CauchyI, simp add: dist_norm)
  qed            
qed

context
  fixes s r :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, real_normed_vector, banach}" and M
  assumes bounded: "\<And>x. x \<in> space M \<Longrightarrow> bounded (range (\<lambda>i. s i x))"
begin

lemma borel_measurable_diameter: 
  assumes [measurable]: "\<And>i. (s i) \<in> borel_measurable M"
  shows "(\<lambda>x. diameter {s i x |i. n \<le> i}) \<in> borel_measurable M"
proof -
  have "{s i x |i. N \<le> i} \<noteq> {}" for x N by blast
  hence diameter_SUP: "diameter {s i x |i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x))" for x N unfolding diameter_def by (auto intro!: arg_cong[of _ _ Sup])
  
  have "case_prod dist ` ({s i x |i. n \<le> i} \<times> {s i x |i. n \<le> i}) = ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..}))" for x by fast
  hence *: "(\<lambda>x. diameter {s i x |i. n \<le> i}) =  (\<lambda>x. Sup ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..})))" using diameter_SUP by (simp add: case_prod_beta')
  
  have "bounded ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..}))" if "x \<in> space M" for x by (rule bounded_imp_dist_bounded[OF bounded, OF that])
  hence bdd: "bdd_above ((\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..}))" if "x \<in> space M" for x using that bounded_imp_bdd_above by presburger
  have "fst p \<in> borel_measurable M" "snd p \<in> borel_measurable M" if "p \<in> s ` {n..} \<times> s ` {n..}" for p using that by fastforce+
  hence "(\<lambda>x. fst p x - snd p x) \<in> borel_measurable M" if "p \<in> s ` {n..} \<times> s ` {n..}" for p using that borel_measurable_diff by simp
  hence "(\<lambda>x. case p of (f, g) \<Rightarrow> dist (f x) (g x)) \<in> borel_measurable M" if "p \<in> s ` {n..} \<times> s ` {n..}" for p unfolding dist_norm using that by measurable
  moreover have "countable (s ` {n..} \<times> s ` {n..})" by (intro countable_SIGMA countable_image, auto)
  ultimately show ?thesis unfolding * by (auto intro!: borel_measurable_cSUP bdd)
qed

lemma integrable_bound_diameter:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f" 
      and [measurable]: "\<And>i. (s i) \<in> borel_measurable M"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> f x"
    shows "integrable M (\<lambda>x. diameter {s i x |i. n \<le> i})"
proof -
  have "{s i x |i. N \<le> i} \<noteq> {}" for x N by blast
  hence diameter_SUP: "diameter {s i x |i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i x) (s j x))" for x N unfolding diameter_def by (auto intro!: arg_cong[of _ _ Sup])
  {
    fix x assume x: "x \<in> space M"
    let ?S = "(\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..})"
    have "case_prod dist ` ({s i x |i. n \<le> i} \<times> {s i x |i. n \<le> i}) = (\<lambda>(i, j). dist (s i x) (s j x)) ` ({n..} \<times> {n..})" by fast
    hence *: "diameter {s i x |i. n \<le> i} =  Sup ?S" using diameter_SUP by (simp add: case_prod_beta')
    
    have "bounded ?S" by (rule bounded_imp_dist_bounded[OF bounded[OF x]])
    hence Sup_S_nonneg:"0 \<le> Sup ?S" by (auto intro!: cSup_upper2 x bounded_imp_bdd_above)

    have "dist (s i x) (s j x) \<le>  2 * f x" for i j by (intro dist_triangle2[THEN order_trans, of _ 0]) (metis norm_conv_dist assms(3) x add_mono mult_2)
    hence "\<forall>c \<in> ?S. c \<le> 2 * f x" by force
    hence "Sup ?S \<le> 2 * f x" by (intro cSup_least, auto)
    hence "norm (Sup ?S) \<le> 2 * norm (f x)" using Sup_S_nonneg by auto
    also have "... = norm (2 *\<^sub>R f x)" by simp
    finally have "norm (diameter {s i x |i. n \<le> i}) \<le> norm (2 *\<^sub>R f x)" unfolding * .
  }
  hence "AE x in M. norm (diameter {s i x |i. n \<le> i}) \<le> norm (2 *\<^sub>R f x)" by blast
  thus  "integrable M (\<lambda>x. diameter {s i x |i. n \<le> i})" using borel_measurable_diameter by (intro Bochner_Integration.integrable_bound[OF assms(1)[THEN integrable_scaleR_right[of 2]]], measurable)
qed
end    
  
end