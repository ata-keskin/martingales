(*  Author:     Ata Keskin, TU München 
*)

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

lemma toss_indicator_def: "toss n = indicator {s. s !! n} - indicator {s. \<not> s !! n}"
  unfolding toss_def indicator_def by force

lemma fortune_Suc: "fortune (Suc n) s = fortune n s + toss (Suc n) s"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def)+

lemma fortune_toss_sum: "fortune n s = (\<Sum>i \<in> {..n}. toss i s)"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def, simp add: fortune_Suc)

lemma fortune_bound: "norm (fortune n s) \<le> Suc n" by (induction n) (force simp add: fortune_toss_sum toss_def)+

interpretation prob_space "bernoulli_stream p" unfolding bernoulli_stream_def by (simp add: measure_pmf.prob_space_axioms prob_space.prob_space_stream_space)

abbreviation "toss_filtration p \<equiv> nat_natural_filtration (bernoulli_stream p) toss"

interpretation toss: nat_stochastic_process "bernoulli_stream p" toss unfolding toss_def by (unfold_locales, auto simp add: bernoulli_stream_def)

interpretation fortune: nat_finite_adapted_process "bernoulli_stream p" "toss_filtration p" fortune 
  unfolding fortune_toss_sum   
  by (intro nat_finite_adapted_process.intro finite_adapted_process.intro toss.adapted_natural.partial_sum_adapted[folded atMost_atLeast0]) intro_locales

lemma integrable_toss: "integrable (bernoulli_stream p) (toss n)" 
  using toss.random_variable
  by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ "1 :: real"]]) (auto simp add: toss_def)

lemma integrable_fortune: "integrable (bernoulli_stream p) (fortune n)" using fortune_bound 
  by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ "Suc n"] fortune.random_variable]) auto

context
  fixes p :: real
  assumes p_eq_half: "p = 1/2"
begin

interpretation nat_martingale "bernoulli_stream p" "toss_filtration p" fortune
proof (intro fortune.martingale_of_cond_exp_diff_Suc_eq_zero integrable_fortune)
  fix n
  have "indep_set p (sets (toss_filtration p n)) (sets (vimage_algebra (space (bernoulli_stream p)) (toss (Suc n)) borel))" sorry
  moreover have "fortune (Suc n) s - fortune n s = toss (Suc n) s" for s by (force simp add: fortune_toss_sum)
  moreover have "expectation p (toss (Suc n)) = 0"
  proof -
    have "expectation p (toss (Suc n)) = \<P>(v in bernoulli_stream p. v !! Suc n) *\<^sub>R 1 + \<P>(v in bernoulli_stream p. \<not> v !! Suc n) *\<^sub>R -1"
      unfolding toss_indicator_def using p_eq_half apply simp
      
  ultimately show "AE \<xi> in bernoulli_stream p. cond_exp (bernoulli_stream p) (toss_filtration p n)
                      (\<lambda>\<xi>. fortune (Suc n) \<xi> - fortune n \<xi>) \<xi> =
                     0" using cond_exp_indep[OF fortune.subalg _ integrable_toss, of p n] by force
qed

end

end