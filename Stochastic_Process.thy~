theory Stochastic_Process
imports Filtration
begin

subsection "Stochastic Process"

locale stochastic_process = sigma_finite_measure M for M +
  fixes X :: "'t :: {second_countable_topology,linorder_topology} \<Rightarrow> 'a \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}"
  assumes random_variable[measurable]: "\<And>i. X i \<in> borel_measurable M"
begin

definition left_continuous where "left_continuous = (AE \<xi> in M. \<forall>i. continuous (at_left i) (\<lambda>i. X i \<xi>))"
definition right_continuous where "right_continuous = (AE \<xi> in M. \<forall>i. continuous (at_right i) (\<lambda>i. X i \<xi>))"

end

subsection "Adapted Process"

locale adapted_process = filtered_sigma_finite_measure M F + stochastic_process M X for M and F :: "'t :: {second_countable_topology, linorder_topology, order_bot} \<Rightarrow> _" and X :: "'t \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, banach}" +
  assumes adapted[measurable]: "\<And>i. X i \<in> borel_measurable (F i)"

locale adapted_process_order = adapted_process M F X for M F and X :: "'t :: {second_countable_topology, linorder_topology, order_bot} \<Rightarrow> _ \<Rightarrow> _ :: ordered_euclidean_space"

subsection "Discrete-Time Processes"

locale discrete_time_stochastic_process = stochastic_process M X for M and X :: "nat \<Rightarrow> _ \<Rightarrow> _"
locale discrete_time_adapted_process = adapted_process M F X for M F and X :: "nat \<Rightarrow> _ \<Rightarrow> _"

sublocale discrete_time_adapted_process \<subseteq> discrete_time_stochastic_process by (unfold_locales)
sublocale discrete_time_adapted_process \<subseteq> nat_filtered_sigma_finite_measure by (unfold_locales)

context filtered_sigma_finite_measure
begin

definition predictable_sigma :: "('t \<times> 'a) measure" where
  "predictable_sigma = sigma (UNIV \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> s < t} \<union> {{\<bottom>} \<times> A | A. A \<in> F \<bottom>})"

lemma space_predictable_sigma[simp]: "space predictable_sigma = (UNIV \<times> space M)" unfolding predictable_sigma_def space_measure_of_conv by blast

lemma sets_predictable_sigma[simp]: "sets predictable_sigma = sigma_sets (UNIV \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> s < t} \<union> {{\<bottom>} \<times> A | A. A \<in> F \<bottom>})" 
  unfolding predictable_sigma_def sets_measure_of_conv 
  using space_F sets.sets_into_space
  by (fastforce intro!: if_P)

lemma in_predictable_sigmaI:
  assumes "I = {\<bottom>} \<Longrightarrow> S \<in> sets (F \<bottom>)" "I \<noteq> {\<bottom>} \<Longrightarrow> I = (\<Union>i :: nat. \<Inter> j :: nat. {(ss i j)<..(ts i j)}) \<and> (\<forall>i j. S \<in> sets (F (ss i j :: 't)) \<and> ss i j < ts i j)"
  shows "I \<times> S \<in> predictable_sigma"
proof -
  have *: "{{s<..t} \<times> A |A s t. A \<in> sets (F s) \<and> s < t} \<union> {{\<bottom>} \<times> A |A. A \<in> sets (F \<bottom>)} \<subseteq> Pow (UNIV \<times> space M)" 
    using filtration.space_F filtration_axioms sets.sets_into_space by blast
  show ?thesis
  proof (cases "I = {\<bottom>}")
    case True
    have "I \<times> S \<in> {{\<bottom>} \<times> A |A. A \<in> sets (F \<bottom>)}" using assms True by blast
    then show ?thesis using * by simp
  next
    case False
    define \<SS> where "\<SS> = {(\<Union>i :: nat. \<Inter> j :: nat. {ss i j<..ts i j :: 't}) \<times> A |A ss ts. \<forall>i j. A \<in> sets (F (ss i j)) \<and> ss i j < ts i j}"
    have S_in_sets_F: "S \<in> sets (F (ss i j))" and ss_less: "ss i j < ts i j" and I_eq: "I = (\<Union>i :: nat. \<Inter> j :: nat. {ss i j<..ts i j})" for i j using assms(2)[OF False] by auto
    have **: "I \<times> S \<in> \<SS>" unfolding \<SS>_def by (simp add: I_eq, metis S_in_sets_F ss_less)
    have "I \<times> S \<in> sigma_sets (UNIV \<times> space M) ({{s<..t} \<times> A |A s t. A \<in> sets (F s) \<and> s < t})"
    proof (intro subsetD[OF _ **] sigma_sets_mono, clarsimp simp add: \<SS>_def, goal_cases)
      case (1 A ss ts)
      hence *: "(\<Union>i. \<Inter>j. {ss i j<..ts i j}) \<times> A = (\<Union>i. \<Inter>j. {ss i j<..ts i j} \<times> A)" by auto
      thus ?case using space_F sets.sets_into_space 1 by (fastforce simp add: * intro!: sigma_sets.Union sigma_sets_Inter)
    qed
    thus ?thesis using * by (simp, meson sigma_sets_mono'' sigma_sets_top subsetD sup_ge1)
  qed
qed

(* TODO *)
lemma (in ennreal_filtered_sigma_finite_measure) predictable_sigma_ennreal_def:
  shows "predictable_sigma = sigma_gen (UNIV \<times> space M) borel {case_prod X | X :: ereal \<Rightarrow> _ \<Rightarrow> _. adapted_process M F X \<and> stochastic_process.left_continuous M X}"
  sorry

definition predictable :: "('t \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,banach}) \<Rightarrow> bool" where
  "predictable X = (case_prod X \<in> borel_measurable (predictable_sigma))"

lemmas predictableD = measurable_sets[OF predictable_def[THEN iffD1], unfolded space_predictable_sigma]

lemma (in nat_filtered_sigma_finite_measure) predictable_discrete_time_process:
  assumes "predictable X"
  shows "X i \<in> borel_measurable (F (i - 1))"
proof (cases i)
  case 0
  {
    fix S :: "'b set" assume open_S: "open S"
    hence "{\<bottom>} \<times> space M \<in> predictable_sigma" by (intro in_predictable_sigmaI[of "{\<bottom>}"]) (auto simp add: space_F[symmetric, of \<bottom>])
    moreover have "case_prod X -` S \<inter> (UNIV \<times> space M) \<in> predictable_sigma" using open_S by (intro predictableD[OF assms], simp add: borel_open)  
    ultimately have "case_prod X -` S \<inter> ({\<bottom>} \<times> space M) \<in> predictable_sigma" unfolding sets_predictable_sigma using space_F sets.sets_into_space
      by (subst Times_Int_distrib1[of "{\<bottom>}" UNIV "space M", simplified], subst inf.commute[of "_ \<times> _"], subst Int_assoc[symmetric], subst Int_range_binary) 
         (intro sigma_sets_Inter binary_in_sigma_sets, fast)+
    moreover have "case_prod X -` S \<inter> ({\<bottom>} \<times> space M) = {\<bottom>} \<times> (X \<bottom> -` S \<inter> space M)" by (auto simp add: le_Suc_eq)
    ultimately have "{\<bottom>} \<times> (X \<bottom> -` S \<inter> space M) \<in> predictable_sigma" by argo
    then have "X \<bottom> -` S \<inter> space M \<in> sets (F \<bottom>)" sorry
  }
  hence "X 0 \<in> borel_measurable (F 0)" by (fastforce simp add: bot_nat_def space_F intro!: borel_measurableI)
  thus ?thesis using 0 by force
next
  case (Suc i)
  {
    fix S :: "'b set" assume open_S: "open S"
    hence "{Suc i} \<times> space M \<in> predictable_sigma" by (intro in_predictable_sigmaI[of "{Suc i}" _ "\<lambda>_ _. i" "\<lambda>_ _. Suc i"]) (force simp add: space_F[symmetric, of \<bottom>], fastforce simp add: space_F[symmetric, of i])
    moreover have "case_prod X -` S \<inter> (UNIV \<times> space M) \<in> predictable_sigma" using open_S by (intro predictableD[OF assms], simp add: borel_open)
    ultimately have "case_prod X -` S \<inter> ({Suc i} \<times> space M) \<in> predictable_sigma" unfolding sets_predictable_sigma using space_F sets.sets_into_space
      by (subst Times_Int_distrib1[of "{Suc i}" UNIV "space M", simplified], subst inf.commute[of "_ \<times> _"], subst Int_assoc[symmetric], subst Int_range_binary) 
         (intro sigma_sets_Inter binary_in_sigma_sets, fast)+
    moreover have "case_prod X -` S \<inter> ({Suc i} \<times> space M) = {i<..Suc i} \<times> (X (Suc i) -` S \<inter> space M)" by (auto simp add: le_Suc_eq)
    ultimately have "{i<..Suc i} \<times> (X (Suc i) -` S \<inter> space M) \<in> predictable_sigma" by argo
    then have "X (Suc i) -` S \<inter> space M \<in> sets (F i)" sorry
  }
  hence "X (Suc i) \<in> borel_measurable (F i)" by (fastforce simp add: space_F intro!: borel_measurableI)
  then show ?thesis using Suc by force
qed

end



end