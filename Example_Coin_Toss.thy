theory Example_Coin_Toss                                                                                                
  imports Martingale "HOL-Probability.Stream_Space" "HOL-Probability.Probability_Mass_Function"
begin

definition bernoulli_stream :: "real \<Rightarrow> (bool stream) measure" where
  "bernoulli_stream p = stream_space (measure_pmf (bernoulli_pmf p))"

lemma space_bernoulli_stream[simp]: "space (bernoulli_stream p) = UNIV" by (simp add: bernoulli_stream_def space_stream_space)

text \<open>We define the fortune of the player at time \<^term>\<open>n\<close> to be the number of heads minus number of tails.\<close>

definition fortune :: "nat \<Rightarrow> bool stream \<Rightarrow> real" where
  "fortune n = (\<lambda>s. \<Sum>b \<leftarrow> stake (Suc n) s. if b then 1 else -1)"

definition toss :: "nat \<Rightarrow> bool stream \<Rightarrow> real" where
  "toss n = (\<lambda>s. if snth s n then 1 else -1)"

lemma fortune_Suc: "fortune (Suc n) s = fortune n s + toss (Suc n) s"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def)+

lemma fortune_toss_sum: "fortune n s = (\<Sum>i \<in> {..n}. toss i s)"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def, simp add: fortune_Suc)

lemma fortune_bound: "norm (fortune n s) \<le> Suc n" by (induction n) (force simp add: fortune_toss_sum toss_def)+

interpretation prob_space "bernoulli_stream p" unfolding bernoulli_stream_def by (simp add: measure_pmf.prob_space_axioms prob_space.prob_space_stream_space)

abbreviation "toss_filtration p \<equiv> nat_natural_filtration (bernoulli_stream p) toss"

interpretation toss: nat_stochastic_process "bernoulli_stream p" toss unfolding toss_def by (unfold_locales, auto simp add: bernoulli_stream_def)

interpretation fortune: nat_finite_adapted_process "bernoulli_stream p" "toss_filtration p" fortune unfolding fortune_toss_sum 
  by (intro nat_finite_adapted_process.intro finite_adapted_process.intro)
     (presburger add: toss.adapted_natural.partial_sum_adapted atMost_atLeast0, intro_locales) 

lemma integrable_fortune: "integrable (bernoulli_stream p) (fortune n)" using fortune_bound 
  by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ "Suc n"] fortune.random_variable]) auto

context
  fixes p :: real
  assumes p_eq_half: "p = 1/2"
begin

interpretation nat_martingale "bernoulli_stream p" "toss_filtration p" fortune
proof (intro fortune.martingale_of_set_integral_eq_Suc integrable_fortune)
  fix A n
  assume asm: "A \<in> toss_filtration p n"
  hence "A \<in> sigma_sets UNIV (\<Union>i\<in>{..n}. {toss i -` A | A. A \<in> range atLeast})" by (simp add: sets_natural_filtration_ci atLeastAtMost_def)

  have [measurable]: "A \<in> bernoulli_stream p" by (meson asm toss.subalgebra_natural_filtration in_mono subalgebra_def)
  have measurable_snth[measurable]: "{s. s !! j} \<in> bernoulli_stream p" for j using measurable_sets[OF measurable_snth, of "{True}" "measure_pmf (bernoulli_pmf p)" j, folded bernoulli_stream_def] by (simp add: vimage_def)

  have prob_eq: "prob p (A \<inter> {s. snth s (Suc n)}) = prob p (A \<inter> - {s. snth s (Suc n)})"
  proof -
    note emeasure_stream_space = prob_space.emeasure_stream_space[OF prob_space_measure_pmf, of _ "bernoulli_pmf p", folded bernoulli_stream_def, unfolded emeasure_eq_measure]
    have "ennreal (prob p (A \<inter> {s. snth s (Suc n)})) = ennreal (prob p (A \<inter> - {s. snth s (Suc n)}))" 
    thus ?thesis by simp
  qed

  have "fortune (Suc n) s - fortune n s = toss (Suc n) s" for s by (force simp add: fortune_toss_sum)
  moreover have "A = (A \<inter> {s. s !! (Suc n)}) \<union> (A \<inter> - {s. s !! (Suc n)})" by blast
  ultimately have "(LINT s:A|bernoulli_stream p. fortune (Suc n) s) - (LINT s:A|bernoulli_stream p. fortune n s) = (LINT s:(A \<inter> {s. s !! (Suc n)}) \<union> (A \<inter> - {s. s !! (Suc n)})|bernoulli_stream p. toss (Suc n) s)" 
    by (subst set_integral_diff(2)[symmetric], auto simp only: set_integrable_def integrable_fortune measurable intro!: integrable_mult_indicator)
  also have "... = (LINT s:A \<inter> {s. snth s (Suc n)}|bernoulli_stream p. toss (Suc n) s) + (LINT s:A \<inter> -{s. snth s (Suc n)}|bernoulli_stream p. toss (Suc n) s)"
    by (subst set_integral_Un, blast) (blast | intro integrableI_bounded_set_indicator[folded set_integrable_def], simp only: measurable Diff_eq[symmetric], simp, simp add: emeasure_eq_measure, force simp: toss_def)+
  also have "... = (LINT s:A \<inter> {s. snth s (Suc n)}|bernoulli_stream p. 1) + (LINT s:A \<inter> -{s. snth s (Suc n)}|bernoulli_stream p. -1)"
    by (blast | subst set_lebesgue_integral_cong[of "A \<inter> {s. s !! (Suc n)}" _ "\<lambda>_. 1" "toss (Suc n)"] set_lebesgue_integral_cong[of "A \<inter> -{s. s !! (Suc n)}" _ "\<lambda>_. -1" "toss (Suc n)"], simp only: measurable Diff_eq[symmetric], simp add: toss_def)+
  also have "... = prob p (A \<inter> {s. snth s (Suc n)}) - prob p (A \<inter> -{s. snth s (Suc n)})" unfolding set_lebesgue_integral_def by simp
  finally show "(LINT s:A|bernoulli_stream p. fortune n s) = (LINT s:A|bernoulli_stream p. fortune (Suc n) s)" using prob_eq by fastforce
qed

end

end