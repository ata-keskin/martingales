theory Example_Coin_Toss
imports Martingale "HOL-Probability.Stream_Space" "HOL-Probability.Probability_Mass_Function"
begin

definition bernoulli_stream :: "real \<Rightarrow> (bool stream) measure" where
  "bernoulli_stream p = stream_space (measure_pmf (bernoulli_pmf p))"

definition fortune :: "nat \<Rightarrow> bool stream \<Rightarrow> real" where
  "fortune n s = (\<Sum>b \<leftarrow> stake n s. if b then 1 else 0)"

interpretation fortune: nat_stochastic_process "bernoulli_stream p" fortune sorry

lemma "integrable (bernoulli_stream p) (fortune i)" sorry

context
  assumes p_eq_half: "p = 1/2"
begin

interpretation finite_measure "bernoulli_stream p" sorry

interpretation fortune: nat_finite_adapted_process "bernoulli_stream p" "nat_natural_filtration (bernoulli_stream p) fortune" fortune ..

interpretation nat_martingale "bernoulli_stream p" "nat_natural_filtration (bernoulli_stream p) fortune" fortune
  apply (intro fortune.martingale_of_cond_exp_diff_Suc_eq_zero) sorry

end

end