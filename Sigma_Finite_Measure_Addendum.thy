theory Sigma_Finite_Measure_Addendum
imports Set_Integral_Addendum
begin

(* Eneglking's book General Topology *)
lemma balls_countable_basis:
  obtains D :: "'a :: {metric_space, second_countable_topology} set" 
  where "topological_basis (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))"
    and "countable D"
    and "D \<noteq> {}"    
proof -
  obtain D :: "'a set" where dense_subset: "countable D" "D \<noteq> {}" "\<lbrakk>open U; U \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>y \<in> D. y \<in> U" for U using countable_dense_exists by blast
  have "topological_basis (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))"
  proof (intro topological_basis_iff[THEN iffD2], fast, clarify)
    fix U and x :: 'a assume asm: "open U" "x \<in> U"
    obtain e where e: "e > 0" "ball x e \<subseteq> U" using asm openE by blast
    obtain y where y: "y \<in> D" "y \<in> ball x (e / 3)" using dense_subset(3)[OF open_ball, of x "e / 3"] centre_in_ball[THEN iffD2, OF divide_pos_pos[OF e(1), of 3]] by force
    obtain r where r: "r \<in> \<rat> \<inter> {e/3<..<e/2}" unfolding Rats_def using of_rat_dense[OF divide_strict_left_mono[OF _ e(1)], of 2 3] by auto

    have *: "x \<in> ball y r" using r y by (simp add: dist_commute)
    hence "ball y r \<subseteq> U" using r by (intro order_trans[OF _ e(2)], simp, metric)
    moreover have "ball y r \<in> (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))" using y(1) r by force
    ultimately show "\<exists>B'\<in>(case_prod ball ` (D \<times> (\<rat> \<inter> {0<..}))). x \<in> B' \<and> B' \<subseteq> U" using * by meson
  qed
  thus ?thesis using that dense_subset by blast
qed

context sigma_finite_measure
begin         

lemma sigma_finite_measure_induct[case_names finite_measure, consumes 0]:
  assumes "\<And>(N :: 'a measure) \<Omega>. finite_measure N 
                              \<Longrightarrow> N = restrict_space M \<Omega>
                              \<Longrightarrow> \<Omega> \<in> sets M 
                              \<Longrightarrow> emeasure N \<Omega> \<noteq> \<infinity> 
                              \<Longrightarrow> emeasure N \<Omega> \<noteq> 0 
                              \<Longrightarrow> almost_everywhere N Q"
      and [measurable]: "Measurable.pred M Q"
  shows "almost_everywhere M Q"
proof -
  have *: "almost_everywhere N Q" if "finite_measure N" "N = restrict_space M \<Omega>" "\<Omega> \<in> sets M" "emeasure N \<Omega> \<noteq> \<infinity>" for N \<Omega> using that by (cases "emeasure N \<Omega> = 0", auto intro: emeasure_0_AE assms(1))

  obtain A :: "nat \<Rightarrow> 'a set" where A: "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" and emeasure_finite: "emeasure M (A i) \<noteq> \<infinity>" for i using sigma_finite by metis
  note A(1)[measurable]
  have space_restr: "space (restrict_space M (A i)) = A i" for i unfolding space_restrict_space by simp
  {
    fix i    
    have *: "{x \<in> A i \<inter> space M. Q x} = {x \<in> space M. Q x} \<inter> (A i)" by fast
    have "Measurable.pred (restrict_space M (A i)) Q" using A by (intro measurableI, auto simp add: space_restr intro!: sets_restrict_space_iff[THEN iffD2], measurable, auto)
  }
  note this[measurable]
  {
    fix i
    have "finite_measure (restrict_space M (A i))" using emeasure_finite by (intro finite_measureI, subst space_restr, subst emeasure_restrict_space, auto)
    hence "emeasure (restrict_space M (A i)) {x \<in> A i. \<not>Q x} = 0" using emeasure_finite by (intro AE_iff_measurable[THEN iffD1, OF _ _ *], measurable, subst space_restr[symmetric], intro sets.top, auto simp add: emeasure_restrict_space)
    hence "emeasure M {x \<in> A i. \<not> Q x} = 0" by (subst emeasure_restrict_space[symmetric], auto)
  }
  hence "emeasure M (\<Union>i. {x \<in> A i. \<not> Q x}) = 0" by (intro emeasure_UN_eq_0, auto)
  moreover have "(\<Union>i. {x \<in> A i. \<not> Q x}) = {x \<in> space M. \<not> Q x}" using A by auto
  ultimately show ?thesis by (intro AE_iff_measurable[THEN iffD2], auto)
qed

(* Real Functional Analysis - Lang*)
lemma averaging_theorem:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes [measurable]:"integrable M f" 
      and closed: "closed S"
      and "\<And>A. A \<in> sets M \<Longrightarrow> measure M A > 0 \<Longrightarrow> (1 / measure M A) *\<^sub>R set_lebesgue_integral M A f \<in> S"
    shows "AE x in M. f x \<in> S"
proof (induct rule: sigma_finite_measure_induct)
  case (finite_measure N \<Omega>)

  interpret finite_measure N by (rule finite_measure)
  
  have integrable[measurable]: "integrable N f" using assms finite_measure by (auto simp: integrable_restrict_space integrable_mult_indicator)
  have average: "(1 / Sigma_Algebra.measure N A) *\<^sub>R set_lebesgue_integral N A f \<in> S" if "A \<in> sets N" "measure N A > 0" for A
  proof -
    have *: "A \<in> sets M" using that by (simp add: sets_restrict_space_iff finite_measure)
    have "A = A \<inter> \<Omega>" by (metis finite_measure(2,3) inf.orderE sets.sets_into_space space_restrict_space that(1))
    hence "set_lebesgue_integral N A f = set_lebesgue_integral M A f" unfolding finite_measure by (subst set_integral_restrict_space, auto simp add: finite_measure set_lebesgue_integral_def indicator_inter_arith[symmetric])
    moreover have "measure N A = measure M A" using that by (auto intro!: measure_restrict_space simp add: finite_measure sets_restrict_space_iff)
    ultimately show ?thesis using that * assms(3) by presburger
  qed

  obtain D :: "'b set" where balls_basis: "topological_basis (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))" and countable_D: "countable D" using balls_countable_basis by blast
  have countable_balls: "countable (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))" using countable_rat countable_D by blast

  obtain B where B_balls: "B \<subseteq> case_prod ball ` (D \<times> (\<rat> \<inter> {0<..}))" "\<Union>B = -S" using topological_basis[THEN iffD1, OF balls_basis] open_Compl[OF assms(2)] by meson
  hence countable_B: "countable B" using countable_balls countable_subset by fast

  define b where "b = from_nat_into (B \<union> {{}})"
  have "B \<union> {{}} \<noteq> {}" by simp
  have range_b: "range b = B \<union> {{}}" using countable_B by (auto simp add: b_def intro!: range_from_nat_into)
  have open_b: "open (b i)" for i unfolding b_def using B_balls open_ball from_nat_into[of "B \<union> {{}}" i] by force
  have Union_range_b: "\<Union>(range b) = -S" using B_balls range_b by simp

  {
    fix v r assume ball_in_Compl: "ball v r \<subseteq> -S"
    define A where "A = f -` ball v r \<inter> space N"
    have dist_less: "dist (f x) v < r" if "x \<in> A" for x using that unfolding A_def vimage_def by (simp add: dist_commute)
    hence AE_less: "AE x \<in> A in N. norm (f x - v) < r" by (auto simp add: dist_norm)
    have *: "A \<in> sets N" unfolding A_def by simp
    have "emeasure N A = 0" 
    proof -
      {
        assume asm: "emeasure N A > 0"
        hence measure_pos: "measure N A > 0" unfolding emeasure_eq_measure by simp
        hence "(1 / measure N A) *\<^sub>R set_lebesgue_integral N A f - v = (1 / measure N A) *\<^sub>R set_lebesgue_integral N A (\<lambda>x. f x - v)" using integrable integrable_const * by (subst set_integral_diff(2), auto simp add: set_integrable_def set_integral_const[OF *] algebra_simps intro!: integrable_mult_indicator)
        moreover have "norm (\<integral>x\<in>A. (f x - v)\<partial>N) \<le> (\<integral>x\<in>A. norm (f x - v)\<partial>N)" using * by (auto intro!: integral_norm_bound[of N "\<lambda>x. indicator A x *\<^sub>R (f x - v)", THEN order_trans] integrable_mult_indicator integrable simp add: set_lebesgue_integral_def)
        ultimately have "norm ((1 / measure N A) *\<^sub>R set_lebesgue_integral N A f - v) \<le>  set_lebesgue_integral N A (\<lambda>x. norm (f x - v)) / measure N A" using asm by (auto intro: divide_right_mono)
        also have "... < set_lebesgue_integral N A (\<lambda>x. r) / measure N A" 
          unfolding set_lebesgue_integral_def 
          using asm * integrable integrable_const AE_less measure_pos
          by (intro divide_strict_right_mono integral_less_AE[of _ _ A] integrable_mult_indicator)
            (fastforce simp add: dist_less dist_norm indicator_def)+
        also have "... = r" using * measure_pos by (simp add: set_integral_const)
        finally have "dist ((1 / measure N A) *\<^sub>R set_lebesgue_integral N A f) v < r" by (subst dist_norm)
        hence "False" using average[OF * measure_pos] by (metis ComplD dist_commute in_mono mem_ball ball_in_Compl)
      }
      thus ?thesis by fastforce
    qed
  }
  note * = this
  {
    fix b' assume "b' \<in> B"
    hence ball_subset_Compl: "b' \<subseteq> -S" and ball_radius_pos: "\<exists>v \<in> D. \<exists>r>0. b' = ball v r" using B_balls by (blast, fast)
  }
  note ** = this
  hence "emeasure N (f -` b i \<inter> space N) = 0" for i by (cases "b i = {}", simp) (metis UnE singletonD  * range_b[THEN eq_refl, THEN range_subsetD])
  hence "emeasure N (\<Union>i. f -` b i \<inter> space N) = 0" using open_b by (intro emeasure_UN_eq_0) fastforce+
  moreover have "(\<Union>i. f -` b i \<inter> space N) = f -` (\<Union>(range b)) \<inter> space N" by blast
  ultimately have "emeasure N (f -` (-S) \<inter> space N) = 0" using Union_range_b by argo
  hence "AE x in N. f x \<notin> -S" using open_Compl[OF assms(2)] by (intro AE_iff_measurable[THEN iffD2], auto)
  thus ?case by force
qed (simp add: pred_sets2[OF borel_closed] assms(2))

lemma density_nonneg:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" 
      and "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f \<ge> 0"
    shows "AE x in M. f x \<ge> 0"
  using averaging_theorem[OF assms(1), of "{0..}", OF closed_atLeast] assms(2)
  by (simp add: scaleR_nonneg_nonneg)
  
lemma density_zero:
  fixes f::"'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
      and density_0: "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f = 0"
  shows "AE x in M. f x = 0"
  using averaging_theorem[OF assms(1), of "{0}"] assms(2)
  by (simp add: scaleR_nonneg_nonneg)

lemma density_unique:
  fixes f f'::"'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f" "integrable M f'"
      and density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f = set_lebesgue_integral M A f'"
  shows "AE x in M. f x = f' x"
proof-
  { 
    fix A assume asm: "A \<in> sets M"
    hence "LINT x|M. indicat_real A x *\<^sub>R (f x - f' x) = 0" using density_eq assms(1,2) by (simp add: set_lebesgue_integral_def algebra_simps Bochner_Integration.integral_diff[OF integrable_mult_indicator(1,1)])
  }
  thus ?thesis using density_zero[OF Bochner_Integration.integrable_diff[OF assms(1,2)]] by (simp add: set_lebesgue_integral_def)
qed

lemma integral_nonneg_AE_eq_0_iff_AE:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes f[measurable]: "integrable M f" and nonneg: "AE x in M. 0 \<le> f x"
  shows "integral\<^sup>L M f = 0 \<longleftrightarrow> (AE x in M. f x = 0)"
proof 
  assume *: "integral\<^sup>L M f = 0"
  {
    fix A assume asm: "A \<in> sets M"
    have "0 \<le> integral\<^sup>L M (\<lambda>x. indicator A x *\<^sub>R f x)" using nonneg by (subst integral_zero[of M, symmetric], intro integral_mono_AE_banach integrable_mult_indicator asm f integrable_zero, auto simp add: indicator_def)
    moreover have "... \<le> integral\<^sup>L M f" using nonneg by (intro integral_mono_AE_banach integrable_mult_indicator asm f, auto simp add: indicator_def)
    ultimately have "set_lebesgue_integral M A f = 0" unfolding set_lebesgue_integral_def using * by force
  }
  thus "AE x in M. f x = 0" by (intro density_zero f, blast)
qed (auto simp add: integral_eq_zero_AE)

lemma integral_eq_mono_AE_eq_AE:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "integral\<^sup>L M f = integral\<^sup>L M g" "AE x in M. f x \<le> g x" 
  shows "AE x in M. f x = g x"
proof -
  define h where "h = (\<lambda>x. g x - f x)"
  have "AE x in M. h x = 0" unfolding h_def using assms by (subst integral_nonneg_AE_eq_0_iff_AE[symmetric]) auto
  then show ?thesis unfolding h_def by auto
qed

end

end