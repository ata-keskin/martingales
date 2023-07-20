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

lemma compose:
  assumes "\<And>i. f i \<in> borel_measurable borel"
  shows "stochastic_process M (\<lambda>i \<xi>. (f i) (X i \<xi>))"
  by (unfold_locales, intro measurable_compose[OF random_variable assms]) 

lemma norm: "stochastic_process M (\<lambda>i \<xi>. norm (X i \<xi>))" by (auto intro: compose borel_measurable_norm)

lemma scaleR:
  assumes "stochastic_process M R"
  shows "stochastic_process M (\<lambda>i \<xi>. (R i \<xi>) *\<^sub>R (X i \<xi>))"
  by (unfold_locales) (simp add: borel_measurable_scaleR random_variable assms stochastic_process.random_variable)

lemma scaleR_const_fun: 
  assumes "f \<in> borel_measurable M" 
  shows "stochastic_process M (\<lambda>i \<xi>. f \<xi> *\<^sub>R (X i \<xi>))"
  by (unfold_locales, intro borel_measurable_scaleR assms random_variable)

lemma scaleR_const: "stochastic_process M (\<lambda>i \<xi>. c *\<^sub>R (X i \<xi>))" by (auto intro: scaleR_const_fun borel_measurable_const)

lemma add:
  assumes "stochastic_process M Y"
  shows "stochastic_process M (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
  by (unfold_locales) (simp add: borel_measurable_add random_variable assms stochastic_process.random_variable)

lemma diff:
  assumes "stochastic_process M Y"
  shows "stochastic_process M (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
  by (unfold_locales) (simp add: borel_measurable_diff random_variable assms stochastic_process.random_variable)

lemma uminus: "stochastic_process M (-X)" using scaleR_const[of "-1"] by (simp add: fun_Compl_def)

end

subsection "Adapted Process"

locale adapted_process = filtered_sigma_finite_measure M F + stochastic_process M X for M and F :: "'t :: {second_countable_topology, linorder_topology, order_bot} \<Rightarrow> _" and X :: "'t \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, banach}" +
  assumes adapted[measurable]: "\<And>i. X i \<in> borel_measurable (F i)"
begin

lemma const_fun:
  assumes "f \<in> borel_measurable (F bot)"
  shows "adapted_process M F (\<lambda>_. f)"
  using assms by (unfold_locales) (blast intro: measurable_from_subalg subalgebra, metis borel_measurable_subalgebra bot.extremum sets_F_mono space_F)

lemma compose:
  assumes "\<And>i. f i \<in> borel_measurable borel"
  shows "adapted_process M F (\<lambda>i \<xi>. (f i) (X i \<xi>))"
  by (unfold_locales, intro measurable_compose[OF random_variable assms], intro measurable_compose[OF adapted assms])

lemma norm: "adapted_process M F (\<lambda>i \<xi>. norm (X i \<xi>))" by (auto intro: compose borel_measurable_norm)

lemma scaleR:
  assumes "adapted_process M F R"
  shows "adapted_process M F (\<lambda>i \<xi>. (R i \<xi>) *\<^sub>R (X i \<xi>))"
proof -
  interpret R: adapted_process M F R by (rule assms)
  show ?thesis by (unfold_locales) (auto simp add: borel_measurable_scaleR adapted random_variable assms R.random_variable R.adapted)
qed
  
lemma scaleR_const_fun: 
  assumes "f \<in> borel_measurable (F bot)" 
  shows "adapted_process M F (\<lambda>i \<xi>. f \<xi> *\<^sub>R (X i \<xi>))"
  using assms by (fast intro: scaleR const_fun)

lemma scaleR_const: "adapted_process M F (\<lambda>i \<xi>. c *\<^sub>R (X i \<xi>))" by (auto intro: scaleR_const_fun borel_measurable_const)

lemma add:
  assumes "adapted_process M F Y"
  shows "adapted_process M F (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: adapted_process M F Y by (rule assms)
  show ?thesis by (unfold_locales) (auto simp add: borel_measurable_add adapted random_variable Y.random_variable Y.adapted)
qed

lemma diff:
  assumes "adapted_process M F Y"
  shows "adapted_process M F (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
proof -
  interpret Y: adapted_process M F Y by (rule assms)
  show ?thesis by (unfold_locales) (auto simp add: borel_measurable_diff adapted random_variable Y.random_variable Y.adapted)
qed

lemma uminus: "adapted_process M F (-X)" using scaleR_const[of "-1"] by (simp add: fun_Compl_def)

end

locale adapted_process_order = adapted_process M F X for M F and X :: "'t :: {second_countable_topology, linorder_topology, order_bot} \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"

subsection "Discrete-Time Processes"

locale discrete_time_stochastic_process = stochastic_process M X for M and X :: "nat \<Rightarrow> _ \<Rightarrow> _"
locale discrete_time_adapted_process = adapted_process M F X for M F and X :: "nat \<Rightarrow> _ \<Rightarrow> _"
locale discrete_time_adapted_process_order = adapted_process_order M F X for M F and X :: "nat \<Rightarrow> _ \<Rightarrow> _"

sublocale discrete_time_adapted_process_order \<subseteq> discrete_time_adapted_process by (unfold_locales)
sublocale discrete_time_adapted_process \<subseteq> discrete_time_stochastic_process by (unfold_locales)
sublocale discrete_time_adapted_process \<subseteq> nat_filtered_sigma_finite_measure by (unfold_locales)

subsection "Predictable Processes"

context filtered_sigma_finite_measure
begin

definition predictable_sigma :: "('t \<times> 'a) measure" where
  "predictable_sigma = sigma (UNIV \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> s < t} \<union> {{bot} \<times> A | A. A \<in> F bot})"

lemma space_predictable_sigma[simp]: "space predictable_sigma = (UNIV \<times> space M)" unfolding predictable_sigma_def space_measure_of_conv by blast

lemma sets_predictable_sigma[simp]: "sets predictable_sigma = sigma_sets (UNIV \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> s < t} \<union> {{bot} \<times> A | A. A \<in> F bot})" 
  unfolding predictable_sigma_def sets_measure_of_conv 
  using space_F sets.sets_into_space
  by (fastforce intro!: if_P)

definition predictable :: "('t \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,banach}) \<Rightarrow> bool" where
  "predictable X = (case_prod X \<in> borel_measurable (predictable_sigma))"

lemmas predictableD = measurable_sets[OF predictable_def[THEN iffD1], unfolded space_predictable_sigma]

lemma (in nat_filtered_sigma_finite_measure) predictable_sets_in_F:
  assumes "(\<Union>i. {i} \<times> A i) \<in> predictable_sigma"
  shows "A (Suc i) \<in> F i" 
        "A 0 \<in> F 0"
  using assms unfolding sets_predictable_sigma
proof (induction "(\<Union>i. {i} \<times> A i)" arbitrary: A)
  case Basic
  {
    assume "\<exists>S. (\<Union>i. {i} \<times> A i) = {bot} \<times> S"
    then obtain S where S: "(\<Union>i. {i} \<times> A i) = {bot} \<times> S" by blast
    hence "S \<in> F 0" using Basic by (fastforce simp add: times_eq_iff bot_nat_def)
    moreover have "A i = {}" if "i \<noteq> bot" for i using that S by blast
    moreover have "A bot = S" using S by blast
    ultimately have "A (Suc i) \<in> F i" "A 0 \<in> F 0" for i unfolding bot_nat_def by (auto simp add: bot_nat_def)
  }
  note * = this
  {
    assume "\<nexists>S. (\<Union>i. {i} \<times> A i) = {bot} \<times> S"
    then obtain s t B where B: "(\<Union>i. {i} \<times> A i) = {s<..t} \<times> B" "B \<in> sets (F s)" "s < t" using Basic by auto
    hence "A i = B" if "i \<in> {s<..t}" for i using that by fast
    moreover have "A i = {}" if "i \<notin> {s<..t}" for i using B that by fastforce
    ultimately have "A (Suc i) \<in> F i" "A 0 \<in> F 0" for i unfolding bot_nat_def using B sets_F_mono by (auto simp add: bot_nat_def) (metis less_Suc_eq_le sets.empty_sets subset_eq)
  }
  note ** = this
  show "A (Suc i) \<in> sets (F i)" "A 0 \<in> sets (F 0)" using *(1)[of i] *(2) **(1)[of i] **(2) by auto blast+ 
next
  case Empty
  {
    case 1
    then show ?case using Empty by simp
  next
    case 2
    then show ?case using Empty by simp
  }
next
  case (Compl a)
  have a_in: "a \<subseteq> UNIV \<times> space M" using Compl(1) sets.sets_into_space sets_predictable_sigma space_predictable_sigma by metis
  hence A_in: "A i \<subseteq> space M" for i using Compl(4) by blast
  have a: "a = UNIV \<times> space M - (\<Union>i. {i} \<times> A i)" using a_in Compl(4) by blast
  also have "... = (\<Union>j. {j} \<times> (space M - A j))" by blast
  finally have *: "(space M - A (Suc i)) \<in> F i" "(space M - A 0) \<in> F 0" using Compl(2,3) by auto
  {
    case 1
    then show ?case using * A_in by (metis double_diff sets.compl_sets space_F subset_refl)
  next
    case 2
    then show ?case using * A_in by (metis double_diff sets.compl_sets space_F subset_refl)
  }
next
  case (Union a)
  have a_in: "a i \<subseteq> UNIV \<times> space M" for i using Union(1) sets.sets_into_space sets_predictable_sigma space_predictable_sigma by metis
  hence A_in: "A i \<subseteq> space M" for i using Union(4) by blast
  have "snd x \<in> snd ` (a i \<inter> ({fst x} \<times> space M))" if "x \<in> a i" for i x using that a_in by fastforce
  hence a_i: "a i = (\<Union>j. {j} \<times> (snd ` (a i \<inter> ({j} \<times> space M))))" for i by force
  have A_i: "A i = snd ` (\<Union> (range a) \<inter> ({i} \<times> space M))" for i unfolding Union(4) using A_in by force 
  have *: "snd ` (a j \<inter> ({Suc i} \<times> space M)) \<in> F i" "snd ` (a j \<inter> ({0} \<times> space M)) \<in> F 0" for j using Union(2,3)[OF a_i] by auto
  {
    case 1
    have "(\<Union>j. snd ` (a j \<inter> ({Suc i} \<times> space M))) \<in> F i" using * by fast
    moreover have "(\<Union>j. snd ` (a j \<inter> ({Suc i} \<times> space M))) = snd ` (\<Union> (range a) \<inter> ({Suc i} \<times> space M))" by fast
    ultimately show ?case using A_i by metis
  next
    case 2
    have "(\<Union>j. snd ` (a j \<inter> ({0} \<times> space M))) \<in> F 0" using * by fast
    moreover have "(\<Union>j. snd ` (a j \<inter> ({0} \<times> space M))) = snd ` (\<Union> (range a) \<inter> ({0} \<times> space M))" by fast
    ultimately show ?case using A_i by metis
  }
qed

lemma (in nat_filtered_sigma_finite_measure) predictable_discrete_time_process_measurable:
  assumes "predictable X"
  shows "X i \<in> borel_measurable (F (i - 1))"
proof (cases i)
  case 0
  {
    fix S :: "'b set" assume open_S: "open S"
    hence "{0} \<times> space M \<in> predictable_sigma" by (auto simp add: bot_nat_def space_F[symmetric, of bot])
    moreover have "case_prod X -` S \<inter> (UNIV \<times> space M) \<in> predictable_sigma" using open_S by (intro predictableD[OF assms], simp add: borel_open)  
    ultimately have "case_prod X -` S \<inter> ({0} \<times> space M) \<in> predictable_sigma" unfolding sets_predictable_sigma using space_F sets.sets_into_space
      by (subst Times_Int_distrib1[of "{0}" UNIV "space M", simplified], subst inf.commute[of "_ \<times> _"], subst Int_assoc[symmetric], subst Int_range_binary) 
         (intro sigma_sets_Inter binary_in_sigma_sets, fast)+
    moreover have "case_prod X -` S \<inter> ({0} \<times> space M) = {0} \<times> (X 0 -` S \<inter> space M)" by (auto simp add: le_Suc_eq)
    moreover have "... = (\<Union>i. {i} \<times> (if i = 0 then X 0 -` S \<inter> space M else {}))" by (auto split: if_splits)
    ultimately have "(\<Union>i. {i} \<times> (if i = 0 then X 0 -` S \<inter> space M else {})) \<in> predictable_sigma" by argo
    then have "X 0 -` S \<inter> space M \<in> sets (F 0)" using predictable_sets_in_F[of "\<lambda>i. if i = 0 then X 0 -` S \<inter> space M else {}"] by presburger
  }
  hence "X 0 \<in> borel_measurable (F 0)" by (fastforce simp add: bot_nat_def space_F intro!: borel_measurableI)
  thus ?thesis using 0 by force
next
  case (Suc i)
  {
    fix S :: "'b set" assume open_S: "open S"
    have "{Suc i} = {i<..Suc i}" by fastforce
    hence "{Suc i} \<times> space M \<in> predictable_sigma" unfolding space_F[symmetric, of i] by (auto intro!: sigma_sets.Basic)
    moreover have "case_prod X -` S \<inter> (UNIV \<times> space M) \<in> predictable_sigma" using open_S by (intro predictableD[OF assms], simp add: borel_open)
    ultimately have "case_prod X -` S \<inter> ({Suc i} \<times> space M) \<in> predictable_sigma" unfolding sets_predictable_sigma using space_F sets.sets_into_space
      by (subst Times_Int_distrib1[of "{Suc i}" UNIV "space M", simplified], subst inf.commute[of "_ \<times> _"], subst Int_assoc[symmetric], subst Int_range_binary) 
         (intro sigma_sets_Inter binary_in_sigma_sets, fast)+
    moreover have "case_prod X -` S \<inter> ({Suc i} \<times> space M) = {Suc i} \<times> (X (Suc i) -` S \<inter> space M)" by (auto simp add: le_Suc_eq)
    moreover have "... = (\<Union>j. {j} \<times> (if j = Suc i then (X (Suc i) -` S \<inter> space M) else {}))" by (auto split: if_splits)
    ultimately have "(\<Union>j. {j} \<times> (if j = Suc i then (X (Suc i) -` S \<inter> space M) else {})) \<in> predictable_sigma" by argo
    then have "X (Suc i) -` S \<inter> space M \<in> sets (F i)" using predictable_sets_in_F[of "\<lambda>j. if j = Suc i then (X (Suc i) -` S \<inter> space M) else {}"] by presburger
  }
  hence "X (Suc i) \<in> borel_measurable (F i)" by (fastforce simp add: space_F intro!: borel_measurableI)
  then show ?thesis using Suc by force
qed

end

end