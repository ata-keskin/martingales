theory Example_Coin_Toss
imports Martingale "HOL-Probability.Stream_Space" "HOL-Probability.Probability_Mass_Function"
begin

definition bernoulli_stream :: "real \<Rightarrow> (bool stream) measure" where
  "bernoulli_stream p = stream_space (measure_pmf (bernoulli_pmf p))"
(*
definition fortune :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real measure" where
  "fortune p c n = do {s \<leftarrow> bernoulli_stream p; (\<Sum>b\<leftarrow>stake n s. if b then c else 0)}"
*)
end