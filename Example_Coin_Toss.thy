theory Example_Coin_Toss
imports Martingale "HOL-Probability.Stream_Space" "HOL-Probability.Probability_Mass_Function"
begin

definition bernoulli_stream :: "real \<Rightarrow> (bool stream) measure" where
  "bernoulli_stream p = stream_space (measure_pmf (bernoulli_pmf p))"
                             
lemma space_bernoulli_stream[simp]: "space (bernoulli_stream p) = UNIV" by (simp add: bernoulli_stream_def space_stream_space)

text \<open>We define the fortune of the player at time \<^term>\<open>n\<close> to be the number of heads minus number of tails.\<close>

definition fortune :: "nat \<Rightarrow> bool stream \<Rightarrow> real" where
  "fortune n s = (\<Sum>b \<leftarrow> stake n s. if b then 1 else -1)"

lemma fortune_Suc: "fortune (Suc n) s = fortune n s + (if snth s n then 1 else -1)"
  by (induction n arbitrary: s) (simp add: fortune_def)+

lemma fortune_snth_def: "fortune n s = (\<Sum>i \<in> {..<n}. if snth s i then 1 else -1)"
  by (induction n arbitrary: s) (simp add: fortune_def, simp add: fortune_Suc)

lemma fortune_bound: "norm (fortune n s) \<le> n" by (induction n) (force simp add: fortune_snth_def)+

interpretation prob_space "bernoulli_stream p" unfolding bernoulli_stream_def by (simp add: measure_pmf.prob_space_axioms prob_space.prob_space_stream_space)

interpretation fortune: nat_stochastic_process "bernoulli_stream (p :: real)" fortune unfolding fortune_snth_def by (unfold_locales, intro borel_measurable_sum, auto simp add: bernoulli_stream_def)

interpretation fortune: nat_finite_adapted_process "bernoulli_stream p" "nat_natural_filtration (bernoulli_stream p) fortune" fortune ..

lemma integrable_fortune: "integrable (bernoulli_stream p) (fortune n)" using fortune_bound by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ n] fortune.random_variable]) auto

context
  fixes p :: real
  assumes p_eq_half: "p = 1/2"
begin

interpretation nat_martingale "bernoulli_stream p" "nat_natural_filtration (bernoulli_stream p) fortune" fortune
proof (intro fortune.martingale_of_set_integral_eq_Suc integrable_fortune)
  fix A i
  assume asm: "A \<in> sets (nat_natural_filtration (bernoulli_stream p) fortune i)"
  hence "A \<in> sigma_sets UNIV (\<Union>i\<in>{..i}. {fortune i -` A | A. open A})" unfolding fortune.sets_natural_filtration by (simp add: atLeastAtMost_def)

  have [measurable]: "A \<in> bernoulli_stream p" by (meson asm fortune.subalgebra_natural_filtration in_mono subalgebra_def)
  have measurable_snth[measurable]: "{s. s !! j} \<in> bernoulli_stream p" for j using measurable_sets[OF measurable_snth, of "{True}" "measure_pmf (bernoulli_pmf p)" j, folded bernoulli_stream_def] by (simp add: vimage_def)

  have prob_eq: "prob p (A \<inter> {s. snth s i}) = prob p (A \<inter> - {s. snth s i})"
  proof -
    note emeasure_stream_space = prob_space.emeasure_stream_space[OF prob_space_measure_pmf, of _ "bernoulli_pmf p", folded bernoulli_stream_def, unfolded emeasure_eq_measure]
    have "ennreal (prob p (A \<inter> {s. snth s i})) = ennreal (prob p (A \<inter> - {s. snth s i}))"
    proof (induction i)
      case 0
      have "prob p {x. True ## x \<in> A} = prob p {x. False ## x \<in> A}" sorry

      have t_True: "{x \<in> space (bernoulli_stream p). t ## x \<in> A \<inter> {s. s !! 0}} = {x. True ## x \<in> A \<and> t = True}" for t by auto
      have t_False: "{x \<in> space (bernoulli_stream p). t ## x \<in> A \<inter> - {s. s !! 0}} = {x. False ## x \<in> A \<and> t = False}" for t by auto
      have "prob p (A \<inter> {s. s !! 0}) = \<integral>\<^sup>+ t. (prob p {x. True ## x \<in> A \<and> t = True}) \<partial>measure_pmf (bernoulli_pmf p)"
        by (subst emeasure_stream_space, fastforce intro: measurable_snth[of 0], simp only: t_True)
      also have "... = (prob p {x. True ## x \<in> A}) * ennreal (1 / 2)" by (subst nn_integral_bernoulli_pmf[of p]) (auto simp add: p_eq_half)
      then show ?case using measurable_snth[of 0] apply (subst emeasure_stream_space, simp) sorry
    next
      case (Suc i)
      then show ?case sorry
    qed
    thus ?thesis by simp
  qed

  let ?ite = "\<lambda>s. (if snth s i then 1 else -1)"
  have "fortune (Suc i) s - fortune i s = ?ite s" for s by (force simp add: fortune_snth_def)
  moreover have "A = (A \<inter> {s. s !! i}) \<union> (A \<inter> - {s. s !! i})" by blast
  ultimately have "(LINT s:A|bernoulli_stream p. fortune (Suc i) s) - (LINT s:A|bernoulli_stream p. fortune i s) = (LINT s:(A \<inter> {s. s !! i}) \<union> (A \<inter> - {s. s !! i})|bernoulli_stream p. ?ite s)" 
    by (subst set_integral_diff(2)[symmetric], auto simp only: set_integrable_def integrable_fortune measurable intro!: integrable_mult_indicator)
  also have "... = (LINT s:A \<inter> {s. snth s i}|bernoulli_stream p. ?ite s) + (LINT s:A \<inter> -{s. snth s i}|bernoulli_stream p. ?ite s)" 
    by (subst set_integral_Un, blast) (blast | (intro integrableI_bounded_set_indicator[folded set_integrable_def], simp, simp add: bernoulli_stream_def, simp add: bernoulli_stream.emeasure_eq_measure, force))+
  also have "... = (LINT s:A \<inter> {s. snth s i}|bernoulli_stream p. 1) + (LINT s:A \<inter> -{s. snth s i}|bernoulli_stream p. -1)" 
    by (simp add: set_lebesgue_integral_cong[of "A \<inter> {s. s !! i}" _ "\<lambda>_. 1" ?ite] set_lebesgue_integral_cong[of "A \<inter> -{s. s !! i}" _ "\<lambda>_. -1" ?ite])   
  also have "... = bernoulli_stream.prob p (A \<inter> {s. snth s i}) - bernoulli_stream.prob p (A \<inter> -{s. snth s i})" unfolding set_lebesgue_integral_def by simp
  finally show "(LINT s:A|bernoulli_stream p. fortune i s) = (LINT s:A|bernoulli_stream p. fortune (Suc i) s)"  using prob_eq by fastforce
qed

end

end