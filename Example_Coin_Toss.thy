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

lemma range_toss: "range (toss n) = {-1, 1}"
proof -
  have "sconst True !! n" by simp
  moreover have "\<not>sconst False !! n" by simp
  ultimately have "\<exists>x. x !! n" "\<exists>x. \<not>x !! n" by blast+
  thus ?thesis unfolding toss_def image_def by auto
qed

lemma vimage_toss: "toss n -` A = (if 1 \<in> A then {s. s !! n} else {}) \<union> (if -1 \<in> A then {s. \<not>s !! n} else {})"
  unfolding vimage_def toss_def by auto

lemma fortune_Suc: "fortune (Suc n) s = fortune n s + toss (Suc n) s"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def)+

lemma fortune_toss_sum: "fortune n s = (\<Sum>i \<in> {..n}. toss i s)"
  by (induction n arbitrary: s) (simp add: fortune_def toss_def, simp add: fortune_Suc)

lemma fortune_bound: "norm (fortune n s) \<le> Suc n" by (induction n) (force simp add: fortune_toss_sum toss_def)+

interpretation prob_space "bernoulli_stream p" unfolding bernoulli_stream_def by (simp add: measure_pmf.prob_space_axioms prob_space.prob_space_stream_space)

abbreviation "toss_filtration p \<equiv> nat_natural_filtration (bernoulli_stream p) toss"

interpretation toss: nat_stochastic_process "bernoulli_stream p" toss unfolding toss_def by (unfold_locales, auto simp add: bernoulli_stream_def)

interpretation fortune: nat_finite_adapted_process_linorder "bernoulli_stream p" "toss_filtration p" fortune 
  unfolding fortune_toss_sum   
  by (intro nat_finite_adapted_process_linorder.intro 
            finite_adapted_process_linorder.intro 
            finite_adapted_process_order.intro 
            finite_adapted_process.intro
            toss.adapted_natural.partial_sum_adapted[folded atMost_atLeast0]) intro_locales

lemma integrable_toss: "integrable (bernoulli_stream p) (toss n)" 
  using toss.random_variable
  by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ "1 :: real"]]) (auto simp add: toss_def)

lemma integrable_fortune: "integrable (bernoulli_stream p) (fortune n)" using fortune_bound 
  by (intro Bochner_Integration.integrable_bound[OF integrable_const[of _ "Suc n"] fortune.random_variable]) auto

lemma measure_bernoulli_stream_snth_pred:
  assumes "0 \<le> p" and "p \<le> 1" and "finite J" 
  shows "prob p {w \<in> space (bernoulli_stream p). \<forall>i\<in>J. P i = w !! i} = p ^ card (J \<inter> Collect P) * (1 - p) ^ (card (J - Collect P))"
proof -
  let ?PiE = "(\<Pi>\<^sub>E i\<in>J. if P i then {True} else {False})"
  have "product_prob_space (\<lambda>_. measure_pmf (bernoulli_pmf p))" by unfold_locales

  hence *: "to_stream -` {s. \<forall>i\<in>J. P i = s !! i} = {s. \<forall>i\<in>J. P i = s i}" using assms by (simp add: to_stream_def)
  also have "... = prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE"
  proof (clarsimp intro!: set_eqI, cases)
    {
      fix s assume "(\<forall>i\<in>J. P i = s i)"
      thus "(\<forall>i\<in>J. P i = s i) = (s \<in> prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE)" 
        by (subst prod_emb_iff[of s]) (smt (verit, best) not_def assms(3) id_def PiE_eq_singleton UNIV_I extensional_UNIV insert_iff singletonD space_measure_pmf)
    }
    {
      fix s assume "\<not>(\<forall>i\<in>J. P i = s i)"
      then obtain i where "i \<in> J" "P i \<noteq> s i" by blast
      thus "(\<forall>i\<in>J. P i = s i) = (s \<in> prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE)"
        by (simp add: restrict_def prod_emb_iff[of s]) (smt (verit, ccfv_SIG) PiE_mem assms(3) id_def insert_iff singleton_iff)
    }
  qed
  finally have inteq: "(to_stream -` {s. \<forall>i\<in>J. P i = s !! i}) =  prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE" .
  let ?M = "(Pi\<^sub>M UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)))"
  have "emeasure (bernoulli_stream p) {s \<in> space (bernoulli_stream p). \<forall>i\<in>J. P i = s !! i} = emeasure ?M (to_stream -` {s. \<forall>i\<in>J. P i  = s !! i})"
    using assms emeasure_distr[of "to_stream" ?M "(vimage_algebra (streams (space (measure_pmf (bernoulli_pmf p)))) (!!) ?M)" "{s. \<forall>i\<in>J. P i = s !! i}", symmetric] measurable_to_stream[of "(measure_pmf (bernoulli_pmf p))"]
    by (simp only: bernoulli_stream_def stream_space_def *, simp add: space_PiM ) (smt (verit, best) emeasure_notin_sets in_vimage_algebra inf_top.right_neutral sets_distr vimage_Collect)
  also have "... = emeasure ?M (prod_emb UNIV (\<lambda>_. measure_pmf (bernoulli_pmf p)) J ?PiE)" using inteq by (simp add: space_PiM)
  also have "... = (\<Prod>i\<in>J. emeasure (measure_pmf (bernoulli_pmf p)) (if P i then {True} else {False}))" 
    by (subst emeasure_PiM_emb) (auto simp add: prob_space_measure_pmf assms(3))
  also have "... = (\<Prod>i\<in>J \<inter> Collect P. ennreal p) * (\<Prod>i\<in>J - Collect P. ennreal (1 - p))"
    unfolding emeasure_pmf_single[of "bernoulli_pmf p" True, unfolded pmf_bernoulli_True[OF assms(1,2)], symmetric]
              emeasure_pmf_single[of "bernoulli_pmf p" False, unfolded pmf_bernoulli_False[OF assms(1,2)], symmetric]
    by (simp add: prod.Int_Diff[OF assms(3), of _ "Collect P"])
  also have "... = p ^ card (J \<inter> Collect P) * (1 - p) ^ card (J - Collect P)" using assms by (simp add: prod_ennreal ennreal_mult' ennreal_power)
  finally show ?thesis using assms by (intro measure_eq_emeasure_eq_ennreal) auto
qed

lemma 
  assumes "0 \<le> p" and "p \<le> 1"
  shows measure_bernoulli_stream_snth: "prob p {w \<in> space (bernoulli_stream p). w !! i} = p"
    and measure_bernoulli_stream_neg_snth: "prob p {w \<in> space (bernoulli_stream p). \<not>w !! i} = 1 - p"
  using measure_bernoulli_stream_snth_pred[OF assms, of "{i}" "\<lambda>x. True"]
        measure_bernoulli_stream_snth_pred[OF assms, of "{i}" "\<lambda>x. False"] by auto

lemma integral_toss:
  assumes "0 \<le> p" "p \<le> 1"
  shows "expectation p (toss n) = 2 * p - 1"
proof -
  have [simp]:"{s. s !! n} \<in> events p" using measurable_snth[THEN measurable_sets, of "{True}" "measure_pmf (bernoulli_pmf p)" n, folded bernoulli_stream_def]
    by (simp add: vimage_def)
  have "expectation p (toss n) = Bochner_Integration.simple_bochner_integral (bernoulli_stream p) (toss n)"
    using toss.random_variable[of n, THEN measurable_sets]
    by (intro simple_bochner_integrable_eq_integral[symmetric] simple_bochner_integrable.intros) (auto simp add: toss_def simple_function_def image_def)
  also have "... = p - prob p {s. \<not> s !! n}" unfolding simple_bochner_integral_def using measure_bernoulli_stream_snth[OF assms]
    by (simp add: range_toss, simp add: toss_def)
  also have "... = p - (1 - prob p {s. s !! n})" by (subst prob_compl[symmetric], auto simp add: Collect_neg_eq Compl_eq_Diff_UNIV)
  finally show ?thesis using measure_bernoulli_stream_snth[OF assms] by simp
qed

lemma indep_set_filtration: 
  assumes "0 \<le> p" "p \<le> 1"
  shows "indep_set p (toss_filtration p n) (vimage_algebra (space (bernoulli_stream p)) (toss (Suc n)) borel)"
proof-
  have *: "case_bool (sigma_sets S a) (sigma_sets S b) = (\<lambda>q :: bool. sigma_sets S (case_bool a b q))" for a b S by (simp add: bool.case_distrib)
  { 
    fix J :: "bool set" assume not_empty: "J \<noteq> {}"
    fix A assume asm: "A \<in> Pi J (case_bool (\<Union>i\<le>n. {toss i -` A \<inter> space (bernoulli_stream p) | A. A \<in> borel}) {toss (Suc n) -` A \<inter> space (bernoulli_stream p) | A. A \<in> borel})"
    have "prob p (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob p (A j))"
    proof cases
      assume [simp]:"J = UNIV"
      have [simp]: "{s. s !! i} \<union> {s. \<not> s !! i} = UNIV" for i by blast
      have [simp]:"{s. stl s !! n} \<union> {s. \<not> stl s !! n} = UNIV" for n by blast
      hence "A True \<in> (\<Union>i\<le>n. {toss i -` A \<inter> space (bernoulli_stream p) | A. A \<in> borel})" 
            "A False \<in> {toss (Suc n) -` A \<inter> space (bernoulli_stream p) | A. A \<in> borel}" using asm by (auto simp add: UNIV_bool)
      then obtain A_T A_F i where *: "i \<le> n" "A True = toss i -` A_T" "A_T \<in> borel" "A False = toss (Suc n) -` A_F" "A_F \<in> borel" by auto
      have "A ` J = {toss i -` A_T, toss (Suc n) -` A_F}" using * by (auto simp add: UNIV_bool)
      moreover have "prob p (toss i -` A_T \<inter> toss (Suc n) -` A_F) = prob p (toss i -` A_T) * prob p (toss (Suc n) -` A_F)" 
        using prob_space assms 
              measure_bernoulli_stream_snth_pred[of p "{i, Suc n}" "\<lambda>j. j = i"]
              measure_bernoulli_stream_snth_pred[of p "{i, Suc n}" "\<lambda>j. j = Suc n"]
              measure_bernoulli_stream_snth_pred[of p "{i, Suc n}" "\<lambda>i. False"]
              measure_bernoulli_stream_snth_pred[of p "{i, Suc n}" "\<lambda>i. True"]
              measure_bernoulli_stream_snth 
              measure_bernoulli_stream_neg_snth *
        by (auto simp add: vimage_toss Collect_conj_eq[symmetric] simp del: snth.simps)
      ultimately show "prob p (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob p (A j))" using * by (auto simp add: UNIV_bool)
    next
      assume "J \<noteq> UNIV"
      hence "\<exists>b. J = {b}" by (smt (verit, best) not_empty UNIV_eq_I insertI1 subsetI subset_singleton_iff)
      thus "prob p (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob p (A j))" by force
    qed
  }
  hence "indep_set p (\<Union>i\<le>n. {toss i -` A \<inter> space (bernoulli_stream p) | A. A \<in> borel}) {toss (Suc n) -` A \<inter> space (bernoulli_stream p) | A. A \<in> borel}"
      using toss.random_variable[THEN measurable_sets] by (fastforce simp add: indep_set_def indep_sets_def split!: bool.splits)
    moreover have "Int_stable (\<Union>i\<in>{0..n}. {toss i -` A \<inter> space (bernoulli_stream p) |A. A \<in> sets borel})" 
apply (intro Int_stableI) using sets.Int[of _ borel] apply auto sorry
  moreover have "Int_stable ({toss (Suc n) -` A \<inter> space (bernoulli_stream p) |A. A \<in> sets borel})" sorry
  ultimately show ?thesis
    unfolding indep_set_def sets_natural_filtration sets_vimage_algebra * 
    using atLeast0AtMost by (intro indep_sets_sigma, presburger) (auto split: bool.split)
qed

theorem fortune_martingale:
  assumes "p = 1/2"
  shows "nat_martingale (bernoulli_stream p) (toss_filtration p) fortune"
    using cond_exp_indep[OF fortune.subalg indep_set_filtration integrable_toss, of p] integral_toss assms
    by (intro fortune.martingale_of_cond_exp_diff_Suc_eq_zero integrable_fortune) (force simp add: fortune_toss_sum)

theorem fortune_submartingale:
  assumes "1/2 \<le> p" "p \<le> 1"
  shows "nat_submartingale (bernoulli_stream p) (toss_filtration p) fortune"
proof (intro fortune.submartingale_of_cond_exp_diff_Suc_nonneg integrable_fortune)
  fix n
  show "AE \<xi> in bernoulli_stream p. 0 \<le> cond_exp (bernoulli_stream p) (toss_filtration p n) (\<lambda>\<xi>. fortune (Suc n) \<xi> - fortune n \<xi>) \<xi>"
    using cond_exp_indep[OF fortune.subalg indep_set_filtration integrable_toss, of p n] 
          integral_toss[of p "Suc n"] assms
    by (force simp add: fortune_toss_sum)
qed

theorem fortune_supermartingale:
  assumes "0 \<le> p" "p \<le> 1/2" 
  shows "nat_supermartingale (bernoulli_stream p) (toss_filtration p) fortune"
proof (intro fortune.supermartingale_of_cond_exp_diff_Suc_le_zero integrable_fortune)
  fix n
  show "AE \<xi> in bernoulli_stream p. 0 \<ge> cond_exp (bernoulli_stream p) (toss_filtration p n) (\<lambda>\<xi>. fortune (Suc n) \<xi> - fortune n \<xi>) \<xi>"
    using cond_exp_indep[OF fortune.subalg indep_set_filtration integrable_toss, of p n] 
          integral_toss[of p "Suc n"] assms
    by (force simp add: fortune_toss_sum)
qed

end

end