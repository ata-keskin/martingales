theory Stochastic_Process
imports Filtered_Measure
begin      

subsection "Stochastic Process"

text \<open>A stochastic process is a collection of random variables, indexed by a type \<^typ>\<open>'b\<close>.\<close>

locale stochastic_process =
  fixes M t\<^sub>0 and X :: "'b :: {second_countable_topology, linorder_topology} \<Rightarrow> 'a \<Rightarrow> 'c :: {second_countable_topology, banach}"
  assumes random_variable[measurable]: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> X i \<in> borel_measurable M"
begin

definition left_continuous where "left_continuous = (AE \<xi> in M. \<forall>i. continuous (at_left i) (\<lambda>i. X i \<xi>))"
definition right_continuous where "right_continuous = (AE \<xi> in M. \<forall>i. continuous (at_right i) (\<lambda>i. X i \<xi>))"

end

locale nat_stochastic_process = stochastic_process M "0 :: nat" X for M X
locale real_stochastic_process = stochastic_process M "0 :: real" X for M X

context stochastic_process
begin

lemma compose:
  assumes "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> f i \<in> borel_measurable borel"
  shows "stochastic_process M t\<^sub>0 (\<lambda>i \<xi>. (f i) (X i \<xi>))"
  by (unfold_locales) (intro measurable_compose[OF random_variable assms]) 

lemma norm: "stochastic_process M t\<^sub>0 (\<lambda>i \<xi>. norm (X i \<xi>))" by (fastforce intro: compose)

lemma scaleR_right:
  assumes "stochastic_process M t\<^sub>0 Y"
  shows "stochastic_process M t\<^sub>0 (\<lambda>i \<xi>. (Y i \<xi>) *\<^sub>R (X i \<xi>))"
  using stochastic_process.random_variable[OF assms] random_variable by (unfold_locales) simp

lemma scaleR_right_const_fun: 
  assumes "f \<in> borel_measurable M" 
  shows "stochastic_process M t\<^sub>0 (\<lambda>i \<xi>. f \<xi> *\<^sub>R (X i \<xi>))" 
  by (unfold_locales) (intro borel_measurable_scaleR assms random_variable)

lemma scaleR_right_const: "stochastic_process M t\<^sub>0 (\<lambda>i \<xi>. c i *\<^sub>R (X i \<xi>))"
  by (unfold_locales) simp

lemma add:
  assumes "stochastic_process M t\<^sub>0 Y"
  shows "stochastic_process M t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
  using stochastic_process.random_variable[OF assms] random_variable by (unfold_locales) simp

lemma diff:
  assumes "stochastic_process M t\<^sub>0 Y"
  shows "stochastic_process M t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
  using stochastic_process.random_variable[OF assms] random_variable by (unfold_locales) simp


lemma uminus: "stochastic_process M t\<^sub>0 (-X)" using scaleR_right_const[of "\<lambda>_. -1"] by (simp add: fun_Compl_def)

lemma partial_sum: "stochastic_process M t\<^sub>0 (\<lambda>n \<xi>. \<Sum>i\<in>{t\<^sub>0..<n}. X i \<xi>)" by (unfold_locales) simp

lemma partial_sum': "stochastic_process M t\<^sub>0 (\<lambda>n \<xi>. \<Sum>i\<in>{t\<^sub>0..n}. X i \<xi>)" by (unfold_locales) simp

end

lemma stochastic_process_const_fun:
  assumes "f \<in> borel_measurable M"
  shows "stochastic_process M t\<^sub>0 (\<lambda>_. f)" using assms by (unfold_locales)

lemma stochastic_process_const:
  shows "stochastic_process M t\<^sub>0 (\<lambda>i _. c i)" by (unfold_locales) simp

lemma stochastic_process_sum:
  assumes "\<And>i. i \<in> I \<Longrightarrow> stochastic_process M t\<^sub>0 (X i)"
  shows "stochastic_process M t\<^sub>0 (\<lambda>k \<xi>. \<Sum>i \<in> I. X i k \<xi>)" using assms[THEN stochastic_process.random_variable] by (unfold_locales, auto)

subsection "Adapted Process"

text \<open>We call a stochastic process \<^term>\<open>X\<close> adapted if \<^term>\<open>X i\<close> is \<^term>\<open>F i\<close>-borel-measurable for all indices \<^term>\<open>i :: 't\<close>.\<close>

locale adapted_process = filtered_measure M F t\<^sub>0 for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, banach}" +
  assumes adapted[measurable]: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> X i \<in> borel_measurable (F i)"
begin

lemma adaptedE[elim]:
  assumes "\<lbrakk>\<And>j i. t\<^sub>0 \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> X j \<in> borel_measurable (F i)\<rbrakk> \<Longrightarrow> P"
  shows P
  using assms using adapted by (metis dual_order.trans borel_measurable_subalgebra sets_F_mono space_F)

lemma adaptedD:
  assumes "t\<^sub>0 \<le> j" "j \<le> i" 
  shows "X j \<in> borel_measurable (F i)" using assms adaptedE by meson

end

locale nat_adapted_process = adapted_process M F "0 :: nat" X for M F X
sublocale nat_adapted_process \<subseteq> nat_filtered_measure ..

locale real_adapted_process = adapted_process M F "0 :: real" X for M F X
sublocale real_adapted_process \<subseteq> real_filtered_measure ..

lemma (in filtered_measure) adapted_process_const_fun:
  assumes "f \<in> borel_measurable (F t\<^sub>0)"
  shows "adapted_process M F t\<^sub>0 (\<lambda>_. f)"
  using measurable_from_subalg subalgebra_F assms by (unfold_locales) blast

lemma (in filtered_measure) adapted_process_const:
  shows "adapted_process M F t\<^sub>0 (\<lambda>i _. c i)" by (unfold_locales) simp

context adapted_process
begin

lemma compose:
  assumes "\<And>i. f i \<in> borel_measurable borel"
  shows "adapted_process M F t\<^sub>0 (\<lambda>i \<xi>. (f i) (X i \<xi>))"
  by (unfold_locales) (intro measurable_compose[OF adapted assms])

lemma norm: "adapted_process M F t\<^sub>0 (\<lambda>i \<xi>. norm (X i \<xi>))" by (fastforce intro: compose)

lemma scaleR_right:
  assumes "adapted_process M F t\<^sub>0 R"
  shows "adapted_process M F t\<^sub>0 (\<lambda>i \<xi>. (R i \<xi>) *\<^sub>R (X i \<xi>))"
  using adapted_process.adapted[OF assms] adapted by (unfold_locales) simp
  
lemma scaleR_right_const_fun:
  assumes "f \<in> borel_measurable (F t\<^sub>0)" 
  shows "adapted_process M F t\<^sub>0 (\<lambda>i \<xi>. f \<xi> *\<^sub>R (X i \<xi>))"
  using assms by (fast intro: scaleR_right adapted_process_const_fun)

lemma scaleR_right_const: "adapted_process M F t\<^sub>0 (\<lambda>i \<xi>. c i *\<^sub>R (X i \<xi>))" by (unfold_locales) simp

lemma add:
  assumes "adapted_process M F t\<^sub>0 Y"
  shows "adapted_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
  using adapted_process.adapted[OF assms] adapted by (unfold_locales) simp

lemma diff:
  assumes "adapted_process M F t\<^sub>0 Y"
  shows "adapted_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
  using adapted_process.adapted[OF assms] adapted by (unfold_locales) simp

lemma uminus: "adapted_process M F t\<^sub>0 (-X)" using scaleR_right_const[of "\<lambda>_. -1"] by (simp add: fun_Compl_def)

lemma partial_sum: "adapted_process M F t\<^sub>0 (\<lambda>n \<xi>. \<Sum>i\<in>{t\<^sub>0..<n}. X i \<xi>)" 
proof (unfold_locales)
  fix i :: 'b
  have "X j \<in> borel_measurable (F i)" if "t\<^sub>0 \<le> j" "j < i" for j using that adaptedE by fastforce
  thus "(\<lambda>\<xi>. \<Sum>i\<in>{t\<^sub>0..<i}. X i \<xi>) \<in> borel_measurable (F i)" by simp
qed

lemma partial_sum': "adapted_process M F t\<^sub>0 (\<lambda>n \<xi>. \<Sum>i\<in>{t\<^sub>0..n}. X i \<xi>)" 
proof (unfold_locales)
  fix i :: 'b
  have "X j \<in> borel_measurable (F i)" if "t\<^sub>0 \<le> j" "j \<le> i" for j using that adaptedE by meson
  thus "(\<lambda>\<xi>. \<Sum>i\<in>{t\<^sub>0..i}. X i \<xi>) \<in> borel_measurable (F i)" by simp
qed

end

lemma (in filtered_measure) adapted_process_sum:
  assumes "\<And>i. i \<in> I \<Longrightarrow> adapted_process M F t\<^sub>0 (X i)"
  shows "adapted_process M F t\<^sub>0 (\<lambda>k \<xi>. \<Sum>i \<in> I. X i k \<xi>)" 
proof -
  {
    fix i k assume "i \<in> I" and asm: "t\<^sub>0 \<le> k"
    then interpret adapted_process M F t\<^sub>0 "X i" using assms by simp
    have "X i k \<in> borel_measurable M" "X i k \<in> borel_measurable (F k)" using measurable_from_subalg subalgebra adapted asm by (blast, simp)
  }
  thus ?thesis by (unfold_locales) simp
qed

text \<open>An adapted process is necessarily a stochastic process.\<close>

sublocale adapted_process \<subseteq> stochastic_process using measurable_from_subalg subalgebra adapted by (unfold_locales) blast

sublocale nat_adapted_process \<subseteq> nat_stochastic_process ..
sublocale real_adapted_process \<subseteq> real_stochastic_process ..

text \<open>A stochastic process is always adapted to the natural filtration it generates.\<close>

sublocale stochastic_process \<subseteq> adapted_natural: adapted_process M "natural_filtration M t\<^sub>0 X" t\<^sub>0 X by (unfold_locales) (auto simp add: natural_filtration_def intro: random_variable measurable_sigma_gen) 

subsection "Progressively Measurable Process"

locale progressive_process = filtered_measure M F t\<^sub>0 for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, banach}" +
  assumes progressive[measurable]: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> case_prod (\<lambda>j. X (min i j)) \<in> borel_measurable (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i)"
begin

lemma progressiveD:
  assumes "S \<in> borel"
  shows "(\<lambda>(j, \<xi>). X (min i j) \<xi>) -` S \<inter> ({t\<^sub>0..i} \<times> space M) \<in> (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i)" 
  using measurable_sets[OF progressive, OF _ assms, of i]
  by (cases "t\<^sub>0 \<le> i") (auto simp add: space_F space_restrict_space sets_pair_measure space_pair_measure)

end

locale nat_progressive_process = progressive_process M F "0 :: nat" X for M F X
locale real_progressive_process = progressive_process M F "0 :: real" X for M F X

lemma (in filtered_measure) prog_measurable_process_const_fun:
  assumes "f \<in> borel_measurable (F t\<^sub>0)"
  shows "progressive_process M F t\<^sub>0 (\<lambda>_. f)"
proof (unfold_locales)
  fix i assume asm: "t\<^sub>0 \<le> i"
  have "f \<in> borel_measurable (F i)" using borel_measurable_mono[OF order.refl asm] assms by blast
  thus "case_prod (\<lambda>_. f) \<in> borel_measurable (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i)" using measurable_compose[OF measurable_snd] by simp
qed

lemma (in filtered_measure) prog_measurable_process_const:
  assumes "c \<in> borel_measurable borel"
  shows "progressive_process M F t\<^sub>0 (\<lambda>i _. c i)"
  using assms by (unfold_locales) (auto simp add: measurable_split_conv intro!: measurable_compose[OF measurable_fst] measurable_restrict_space1)

context progressive_process
begin

lemma compose:
  assumes "case_prod f \<in> borel_measurable borel"
  shows "progressive_process M F t\<^sub>0 (\<lambda>i \<xi>. (f i) (X i \<xi>))"
proof
  fix i assume asm: "t\<^sub>0 \<le> i"
  have "(\<lambda>(j :: 'b, \<xi> :: 'a). (j, X (min i j) \<xi>)) \<in> (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i) \<rightarrow>\<^sub>M borel \<Otimes>\<^sub>M borel" using progressive[OF asm] measurable_fst''[OF measurable_restrict_space1, OF measurable_id] by (auto simp add: measurable_pair_iff space_pair_measure sets_pair_measure sets_restrict_space measurable_split_conv)
  moreover have "(\<lambda>(j :: 'b, y :: 'c). ((min i j), y)) \<in> borel \<Otimes>\<^sub>M borel \<rightarrow>\<^sub>M borel \<Otimes>\<^sub>M borel" by simp
  moreover have "(\<lambda>(j, \<xi>). f (min i j) (X (min i j) \<xi>)) = case_prod f o ((\<lambda>(j, y). ((min i j), y)) o (\<lambda>(j, \<xi>). (j, X (min i j) \<xi>)))" by fastforce
  ultimately show "(\<lambda>(j :: 'b, \<xi> :: 'a). f (min i j) (X (min i j) \<xi>)) \<in> borel_measurable (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i)" unfolding borel_prod using assms measurable_comp[OF measurable_comp] by simp
qed

lemma norm: "progressive_process M F t\<^sub>0 (\<lambda>i \<xi>. norm (X i \<xi>))" using measurable_compose[OF progressive borel_measurable_norm] by (unfold_locales) simp

lemma scaleR_right:
  assumes "progressive_process M F t\<^sub>0 R"
  shows "progressive_process M F t\<^sub>0 (\<lambda>i \<xi>. (R i \<xi>) *\<^sub>R (X i \<xi>))"
  using progressive_process.progressive[OF assms] by (unfold_locales) (simp add: progressive assms)
  
lemma scaleR_right_const_fun: 
  assumes "f \<in> borel_measurable (F t\<^sub>0)" 
  shows "progressive_process M F t\<^sub>0 (\<lambda>i \<xi>. f \<xi> *\<^sub>R (X i \<xi>))"
  using assms by (fast intro: scaleR_right prog_measurable_process_const_fun)

lemma scaleR_right_const: 
  assumes "c \<in> borel_measurable borel"
  shows "progressive_process M F t\<^sub>0 (\<lambda>i \<xi>. c i *\<^sub>R (X i \<xi>))" 
  using assms by (fastforce intro: scaleR_right prog_measurable_process_const)

lemma add:
  assumes "progressive_process M F t\<^sub>0 Y"
  shows "progressive_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
  using progressive_process.progressive[OF assms] by (unfold_locales) (simp add: progressive assms)

lemma diff:
  assumes "progressive_process M F t\<^sub>0 Y"
  shows "progressive_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
  using progressive_process.progressive[OF assms] by (unfold_locales) (simp add: progressive assms)

lemma uminus: "progressive_process M F t\<^sub>0 (-X)" using scaleR_right_const[of "\<lambda>_. -1"] by (simp add: fun_Compl_def)

end

text \<open>A progressively measurable process is also adapted.\<close>

sublocale progressive_process \<subseteq> adapted_process using measurable_compose_rev[OF progressive measurable_Pair1'] unfolding prod.case by (unfold_locales) simp

sublocale nat_progressive_process \<subseteq> nat_adapted_process ..
sublocale real_progressive_process \<subseteq> real_adapted_process ..

subsection "Predictable Process"

text \<open>We introduce the constant \<^term>\<open>\<Sigma>\<^sub>P\<close> to denote the predictable sigma algebra.\<close>

context filtered_measure
begin

definition \<Sigma>\<^sub>P :: "('b \<times> 'a) measure" where predictable_sigma: "\<Sigma>\<^sub>P \<equiv> sigma ({t\<^sub>0..} \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0})"

lemma space_predictable_sigma[simp]: "space \<Sigma>\<^sub>P = ({t\<^sub>0..} \<times> space M)" unfolding predictable_sigma space_measure_of_conv by blast

lemma sets_predictable_sigma[simp]: "sets \<Sigma>\<^sub>P = sigma_sets ({t\<^sub>0..} \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0})" 
  unfolding predictable_sigma using space_F sets.sets_into_space by (subst sets_measure_of) fastforce+

lemma measurable_predictable_sigma_snd:
  assumes "countable \<I>" "\<I> \<subseteq> {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}" "{t\<^sub>0<..} \<subseteq> (\<Union>\<I>)"
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F t\<^sub>0"
proof (intro measurableI, force simp add: space_F)
  fix S :: "'a set" assume asm: "S \<in> F t\<^sub>0"
  have countable: "countable ((\<lambda>I. I \<times> S) ` \<I>)" using assms(1) by blast
  have "(\<lambda>I. I \<times> S) ` \<I> \<subseteq> {{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and>  s < t}" using sets_F_mono[OF order_refl, THEN subsetD, OF _ asm] assms(2) by blast
  hence "(\<Union>I\<in>\<I>. I \<times> S) \<union> {t\<^sub>0} \<times> S \<in> \<Sigma>\<^sub>P" unfolding sets_predictable_sigma using asm by (intro sigma_sets_Un[OF sigma_sets_UNION[OF countable] sigma_sets.Basic] sigma_sets.Basic) blast+
  moreover have "snd -` S \<inter> space \<Sigma>\<^sub>P = {t\<^sub>0..} \<times> S" using sets.sets_into_space[OF asm] by (fastforce simp add: space_F)
  moreover have "(\<Union>I\<in>\<I>. I \<times> S) \<union> {t\<^sub>0} \<times> S = {t\<^sub>0..} \<times> S" using assms(2,3) using ivl_disj_un(1) by fastforce
  ultimately show "snd -` S \<inter> space \<Sigma>\<^sub>P \<in> \<Sigma>\<^sub>P" by argo
qed

lemma measurable_predictable_sigma_fst:
  assumes "countable \<I>" "\<I> \<subseteq> {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}" "{t\<^sub>0<..} \<subseteq> (\<Union>\<I>)"
  shows "fst \<in> borel_measurable \<Sigma>\<^sub>P"
proof -
  have "A \<times> space M \<in> sets \<Sigma>\<^sub>P" if "A \<in> sigma_sets {t\<^sub>0..} {{s<..t} |s t. t\<^sub>0 \<le> s \<and> s < t}" for A unfolding sets_predictable_sigma using that 
  proof (induction rule: sigma_sets.induct)
    case (Basic a)
    then show ?case using space_F by (intro sigma_sets.Basic) blast
  next
    case (Compl a)
    have "({t\<^sub>0..} - a) \<times> space M = {t\<^sub>0..} \<times> space M - a \<times> space M" by blast
    then show ?case using Compl by (fastforce intro: sigma_sets.Compl)
  next
    case (Union a)
    have "\<Union> (range a) \<times> space M = \<Union> (range (\<lambda>i. a i \<times> space M))" by blast
    then show ?case using Union by (fastforce intro: sigma_sets.Union)
  qed (auto)

  moreover have "restrict_space borel {t\<^sub>0..} = sigma {t\<^sub>0..} {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}"
    sorry
  ultimately have "restrict_space borel {t\<^sub>0..} \<Otimes>\<^sub>M sigma (space M) {} \<subseteq> sets \<Sigma>\<^sub>P" sorry
    
  moreover have "space (restrict_space borel {t\<^sub>0..} \<Otimes>\<^sub>M sigma (space M) {}) = space \<Sigma>\<^sub>P" by (simp add: space_pair_measure)
  moreover have "fst \<in> restrict_space borel {t\<^sub>0..} \<Otimes>\<^sub>M sigma (space M) {} \<rightarrow>\<^sub>M borel" by (fastforce intro: measurable_fst''[OF measurable_restrict_space1, of "\<lambda>x. x"]) 
  ultimately show ?thesis sorry
qed

end

locale predictable_process = filtered_measure M F t\<^sub>0 for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, banach}" +
  assumes predictable: "case_prod X \<in> borel_measurable \<Sigma>\<^sub>P"
begin

lemmas predictableD = measurable_sets[OF predictable, unfolded space_predictable_sigma]

end

(* * *)

locale nat_predictable_process = predictable_process M F "0 :: nat" X for M F X
locale real_predictable_process = predictable_process M F "0 :: real" X for M F X

lemma (in nat_filtered_measure) measurable_predictable_sigma_snd:
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F 0"
  by (intro measurable_predictable_sigma_snd[of "range (\<lambda>x. {Suc x})"]) (force | simp add: greaterThan_0)+

lemma (in real_filtered_measure) measurable_predictable_sigma_snd:
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F 0"
  using real_arch_simple by (intro measurable_predictable_sigma_snd[of "range (\<lambda>x::nat. {0<..real (Suc x)})"]) (fastforce intro: add_increasing)+

lemma (in nat_filtered_measure) measurable_predictable_sigma_fst:
  shows "fst \<in> borel_measurable \<Sigma>\<^sub>P"
  by (intro measurable_predictable_sigma_fst[of "range (\<lambda>x. {Suc x})"]) (force | simp add: greaterThan_0)+

lemma (in real_filtered_measure) measurable_predictable_sigma_fst:
  shows "fst \<in> borel_measurable \<Sigma>\<^sub>P"
  using real_arch_simple by (intro measurable_predictable_sigma_fst[of "range (\<lambda>x::nat. {0<..real (Suc x)})"]) (fastforce intro: add_increasing)+

(* * *)

lemma (in filtered_measure) predictable_process_const_fun:
  assumes "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F t\<^sub>0" "f \<in> borel_measurable (F t\<^sub>0)"
    shows "predictable_process M F t\<^sub>0 (\<lambda>_. f)"
  using measurable_compose_rev[OF assms(2)] assms(1) by (unfold_locales) (auto simp add: measurable_split_conv)

lemma (in nat_filtered_measure) predictable_process_const_fun:
  assumes "f \<in> borel_measurable (F 0)"
  shows "nat_predictable_process M F (\<lambda>_. f)"
  using assms by (intro predictable_process_const_fun[OF measurable_predictable_sigma_snd, THEN nat_predictable_process.intro])

lemma (in real_filtered_measure) predictable_process_const_fun:
  assumes "f \<in> borel_measurable (F 0)"
  shows "real_predictable_process M F (\<lambda>_. f)"
  using assms by (intro predictable_process_const_fun[OF measurable_predictable_sigma_snd, THEN real_predictable_process.intro])

lemma (in filtered_measure) predictable_process_const:
  assumes "fst \<in> borel_measurable \<Sigma>\<^sub>P" "c \<in> borel_measurable borel"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i _. c i)"
  using assms by (unfold_locales) (simp add: measurable_split_conv)

lemma (in filtered_measure) predictable_process_const':
  shows "predictable_process M F t\<^sub>0 (\<lambda>_ _. c)"
  by (unfold_locales) simp

lemma (in nat_filtered_measure) predictable_process_const:
  assumes "c \<in> borel_measurable borel"
  shows "nat_predictable_process M F (\<lambda>i _. c i)"
  using assms by (intro predictable_process_const[OF measurable_predictable_sigma_fst, THEN nat_predictable_process.intro])

lemma (in real_filtered_measure) predictable_process_const:
  assumes "c \<in> borel_measurable borel"
  shows "real_predictable_process M F (\<lambda>i _. c i)"
  using assms by (intro predictable_process_const[OF measurable_predictable_sigma_fst, THEN real_predictable_process.intro])

context predictable_process
begin

lemma compose:
  assumes "fst \<in> borel_measurable \<Sigma>\<^sub>P" "case_prod f \<in> borel_measurable borel"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. (f i) (X i \<xi>))"
proof
  have "(\<lambda>(i, \<xi>). (i, X i \<xi>)) \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M borel \<Otimes>\<^sub>M borel" using predictable assms(1) by (auto simp add: measurable_pair_iff measurable_split_conv)
  moreover have "(\<lambda>(i, \<xi>). f i (X i \<xi>)) = case_prod f o (\<lambda>(i, \<xi>). (i, X i \<xi>))" by fastforce
  ultimately show "(\<lambda>(i, \<xi>). f i (X i \<xi>)) \<in> borel_measurable \<Sigma>\<^sub>P" unfolding borel_prod using assms by simp
qed

lemma norm: "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. norm (X i \<xi>))" using measurable_compose[OF predictable borel_measurable_norm] 
  by (unfold_locales) (simp add: prod.case_distrib)

lemma scaleR_right:
  assumes "predictable_process M F t\<^sub>0 R"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. (R i \<xi>) *\<^sub>R (X i \<xi>))"
  using predictable predictable_process.predictable[OF assms] by (unfold_locales) (auto simp add: measurable_split_conv)

lemma scaleR_right_const_fun: 
  assumes "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F t\<^sub>0" "f \<in> borel_measurable (F t\<^sub>0)" 
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. f \<xi> *\<^sub>R (X i \<xi>))"
  using assms by (fast intro: scaleR_right predictable_process_const_fun)

lemma scaleR_right_const: 
  assumes "fst \<in> borel_measurable \<Sigma>\<^sub>P" "c \<in> borel_measurable borel"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. c i *\<^sub>R (X i \<xi>))" 
  using assms by (fastforce intro: scaleR_right predictable_process_const)

lemma scaleR_right_const': "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R (X i \<xi>))" 
  by (fastforce intro: scaleR_right predictable_process_const')

lemma add:
  assumes "predictable_process M F t\<^sub>0 Y"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
  using predictable predictable_process.predictable[OF assms] by (unfold_locales) (auto simp add: measurable_split_conv)

lemma diff:
  assumes "predictable_process M F t\<^sub>0 Y"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
  using predictable predictable_process.predictable[OF assms] by (unfold_locales) (auto simp add: measurable_split_conv)

lemma uminus: "predictable_process M F t\<^sub>0 (-X)" using scaleR_right_const'[of "-1"] by (simp add: fun_Compl_def)

end

text \<open>Every predictable process is also progressively measurable.\<close>

sublocale predictable_process \<subseteq> progressive_process
proof (unfold_locales)
  fix i :: 'b assume asm: "t\<^sub>0 \<le> i"
  let ?min = "(\<lambda>(j, x). (min i j, x))"
  {
    fix S :: "('b \<times> 'a) set" assume "S \<in> {{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0}"
    hence "?min -` S \<inter> ({t\<^sub>0..i} \<times> space M) \<in> restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i"
    proof
      assume "S \<in> {{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t}"
      then obtain s t A where S_is: "S = {s<..t} \<times> A" "t\<^sub>0 \<le> s" "s < t" "A \<in> F s" by blast
      hence "?min -` S \<inter> ({t\<^sub>0..i} \<times> space M) = {s<..min i t} \<times> A" using sets.sets_into_space[OF S_is(4)] by (auto simp add: space_F)
      then show ?thesis using S_is sets_F_mono[of s i] by (cases "s \<le> i") (fastforce simp add: sets_restrict_space_iff)+
    next
      assume "S \<in> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0}"
      then obtain A where S_is: "S = {t\<^sub>0} \<times> A" "A \<in> F t\<^sub>0" by blast
      hence "?min -` S \<inter> ({t\<^sub>0..i} \<times> space M) = {t\<^sub>0} \<times> A" using asm sets.sets_into_space[OF S_is(2)] by (auto simp add: space_F)
      thus ?thesis using S_is sets_F_mono[OF order_refl asm] asm by (fastforce simp add: sets_restrict_space_iff)
    qed
    hence "?min -` S \<inter> space (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i) \<in> restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i" by (simp add: space_pair_measure space_F[OF asm])
  }
  moreover have "{{s<..t} \<times> A |A s t. A \<in> sets (F s) \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A |A. A \<in> sets (F t\<^sub>0)} \<subseteq> Pow ({t\<^sub>0..} \<times> space M)" using sets.sets_into_space by (fastforce simp add: space_F)
  ultimately have "?min \<in> restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i \<rightarrow>\<^sub>M \<Sigma>\<^sub>P" using space_F[OF asm] by (intro measurable_sigma_sets[OF sets_predictable_sigma]) (fast, force simp add: space_pair_measure)
  moreover have "case_prod X o ?min = (\<lambda>(j, x). X (min i j) x)" by fastforce
  ultimately show "case_prod (\<lambda>j. X (min i j)) \<in> borel_measurable (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i)" by (metis measurable_comp predictable)
qed

sublocale nat_predictable_process \<subseteq> nat_progressive_process ..
sublocale real_predictable_process \<subseteq> real_progressive_process ..

subsection "Additional Lemmas for Discrete Time Processes"

lemma (in nat_adapted_process) partial_sum_Suc: "nat_adapted_process M F (\<lambda>n \<xi>. \<Sum>i<n. X (Suc i) \<xi>)" 
proof (unfold_locales)
  fix i
  have "X j \<in> borel_measurable (F i)" if "j \<le> i" for j using that adaptedD by blast
  thus "(\<lambda>\<xi>. \<Sum>i<i. X (Suc i) \<xi>) \<in> borel_measurable (F i)" by auto
qed

text \<open>The following lemma characterizes predictability in a discrete-time setting.\<close>

lemma (in nat_filtered_measure) sets_in_filtration:
  assumes "(\<Union>i. {i} \<times> A i) \<in> \<Sigma>\<^sub>P"
  shows "A (Suc i) \<in> F i" "A 0 \<in> F 0"
  using assms unfolding sets_predictable_sigma
proof (induction "(\<Union>i. {i} \<times> A i)" arbitrary: A)
  case Basic
  {
    assume "\<exists>S. (\<Union>i. {i} \<times> A i) = {0} \<times> S"
    then obtain S where S: "(\<Union>i. {i} \<times> A i) = {bot} \<times> S" unfolding bot_nat_def by blast
    hence "S \<in> F bot" using Basic by (fastforce simp add: times_eq_iff bot_nat_def)
    moreover have "A i = {}" if "i \<noteq> bot" for i using that S by blast
    moreover have "A bot = S" using S by blast
    ultimately have "A (Suc i) \<in> F i" "A 0 \<in> F 0" for i unfolding bot_nat_def by (auto simp add: bot_nat_def)
  }
  note * = this
  {
    assume "\<nexists>S. (\<Union>i. {i} \<times> A i) = {0} \<times> S"
    then obtain s t B where B: "(\<Union>i. {i} \<times> A i) = {s<..t} \<times> B" "B \<in> sets (F s)" "s < t" using Basic by auto
    hence "A i = B" if "i \<in> {s<..t}" for i using that by fast
    moreover have "A i = {}" if "i \<notin> {s<..t}" for i using B that by fastforce
    ultimately have "A (Suc i) \<in> F i" "A 0 \<in> F 0" for i unfolding bot_nat_def using B sets_F_mono by (auto simp add: bot_nat_def) (metis less_Suc_eq_le sets.empty_sets subset_eq)
  }
  note ** = this
  show "A (Suc i) \<in> sets (F i)" "A 0 \<in> sets (F 0)" using *(1)[of i] *(2) **(1)[of i] **(2) by blast+
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
  have a_in: "a \<subseteq> {0..} \<times> space M" using Compl(1) sets.sets_into_space sets_predictable_sigma space_predictable_sigma by metis
  hence A_in: "A i \<subseteq> space M" for i using Compl(4) by blast
  have a: "a = {0..} \<times> space M - (\<Union>i. {i} \<times> A i)" using a_in Compl(4) by blast
  also have "... = (\<Union>j. {j} \<times> (space M - A j))" by blast
  finally have *: "(space M - A (Suc i)) \<in> F i" "(space M - A 0) \<in> F 0" using Compl(2,3) by auto
  {
    case 1
    then show ?case using * A_in by (metis bot_nat_0.extremum double_diff sets.Diff sets.top sets_F_mono sets_le_imp_space_le space_F)
 next
    case 2
    then show ?case using * A_in by (metis bot_nat_0.extremum double_diff sets.Diff sets.top sets_F_mono sets_le_imp_space_le space_F)
  }
next
  case (Union a)
  have a_in: "a i \<subseteq> {0..} \<times> space M" for i using Union(1) sets.sets_into_space sets_predictable_sigma space_predictable_sigma by metis
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

text \<open>This leads to the following useful fact.\<close>

theorem (in nat_predictable_process) adapted_Suc: "nat_adapted_process M F (\<lambda>i. X (Suc i))"
proof (unfold_locales, intro borel_measurableI)
  fix S :: "'b set" and i assume open_S: "open S"
  have "{Suc i} = {i<..Suc i}" by fastforce
  hence "{Suc i} \<times> space M \<in> \<Sigma>\<^sub>P" unfolding space_F[symmetric, of i] sets_predictable_sigma by (intro sigma_sets.Basic) blast
  moreover have "case_prod X -` S \<inter> (UNIV \<times> space M) \<in> \<Sigma>\<^sub>P" unfolding atLeast_0[symmetric] using open_S by (intro predictableD, simp add: borel_open)
  ultimately have "case_prod X -` S \<inter> ({Suc i} \<times> space M) \<in> \<Sigma>\<^sub>P" unfolding sets_predictable_sigma using space_F sets.sets_into_space
    by (subst Times_Int_distrib1[of "{Suc i}" UNIV "space M", simplified], subst inf.commute, subst Int_assoc[symmetric], subst Int_range_binary) 
       (intro sigma_sets_Inter binary_in_sigma_sets, fast)+
  moreover have "case_prod X -` S \<inter> ({Suc i} \<times> space M) = {Suc i} \<times> (X (Suc i) -` S \<inter> space M)" by (auto simp add: le_Suc_eq)
  moreover have "... = (\<Union>j. {j} \<times> (if j = Suc i then (X (Suc i) -` S \<inter> space M) else {}))" by (auto split: if_splits)
  ultimately have "(\<Union>j. {j} \<times> (if j = Suc i then (X (Suc i) -` S \<inter> space M) else {})) \<in> \<Sigma>\<^sub>P" by argo
  thus "X (Suc i) -` S \<inter> space (F i) \<in> sets (F i)" using sets_in_filtration[of "\<lambda>j. if j = Suc i then (X (Suc i) -` S \<inter> space M) else {}"] space_F by presburger
qed

subsection "Processes with an Ordering"

text \<open>These locales are useful in the definition of sub- and supermartingales.\<close>

locale stochastic_process_order = stochastic_process M t\<^sub>0 X for M t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"
locale adapted_process_order = adapted_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_  \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"
locale progressive_process_order = progressive_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"
locale predictable_process_order = predictable_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"

(* Discrete Time *)

locale nat_stochastic_process_order = stochastic_process_order M "0 :: nat" X for M X
locale nat_adapted_process_order = adapted_process_order M F "0 :: nat" X for M F X
locale nat_progressive_process_order = progressive_process_order M F "0 :: nat" X for M F X
locale nat_predictable_process_order = predictable_process_order M F "0 :: nat" X for M F X

(* Continuous Time *)

locale real_stochastic_process_order = stochastic_process_order M "0 :: real" X for M X
locale real_adapted_process_order = adapted_process_order M F "0 :: real" X for M F X
locale real_progressive_process_order = progressive_process_order M F "0 :: real" X for M F X
locale real_predictable_process_order = predictable_process_order M F "0 :: real" X for M F X

(* Hierarchies *)

sublocale predictable_process_order \<subseteq> progressive_process_order ..
sublocale progressive_process_order \<subseteq> adapted_process_order ..
sublocale adapted_process_order \<subseteq> stochastic_process_order ..

sublocale nat_predictable_process_order \<subseteq> nat_progressive_process_order ..
sublocale nat_progressive_process_order \<subseteq> nat_adapted_process_order ..
sublocale nat_adapted_process_order \<subseteq> nat_stochastic_process_order ..

sublocale real_predictable_process_order \<subseteq> real_progressive_process_order ..
sublocale real_progressive_process_order \<subseteq> real_adapted_process_order ..
sublocale real_adapted_process_order \<subseteq> real_stochastic_process_order ..

subsection "Processes with a Sigma Finite Filtration"

locale sigma_finite_adapted_process = adapted_process + filtered_sigma_finite_measure
locale sigma_finite_progressive_process = progressive_process + filtered_sigma_finite_measure
locale sigma_finite_predictable_process = predictable_process + filtered_sigma_finite_measure

locale sigma_finite_adapted_process_order = adapted_process_order + filtered_sigma_finite_measure
locale sigma_finite_progressive_process_order = progressive_process_order + filtered_sigma_finite_measure
locale sigma_finite_predictable_process_order = predictable_process_order + filtered_sigma_finite_measure

(* Discrete Time *)

locale nat_sigma_finite_adapted_process = sigma_finite_adapted_process M F "0 :: nat" X for M F X
locale nat_sigma_finite_progressive_process = sigma_finite_progressive_process M F "0 :: nat" X for M F X
locale nat_sigma_finite_predictable_process = sigma_finite_predictable_process M F "0 :: nat" X for M F X

locale nat_sigma_finite_adapted_process_order = sigma_finite_adapted_process_order M F "0 :: nat" X for M F X
locale nat_sigma_finite_progressive_process_order = sigma_finite_progressive_process_order M F "0 :: nat" X for M F X
locale nat_sigma_finite_predictable_process_order = sigma_finite_predictable_process_order M F "0 :: nat" X for M F X

(* Continuous Time *)

locale real_sigma_finite_adapted_process = sigma_finite_adapted_process M F "0 :: real" X for M F X
locale real_sigma_finite_progressive_process = sigma_finite_progressive_process M F "0 :: real" X for M F X
locale real_sigma_finite_predictable_process = sigma_finite_predictable_process M F "0 :: real" X for M F X

locale real_sigma_finite_adapted_process_order = sigma_finite_adapted_process_order M F "0 :: real" X for M F X
locale real_sigma_finite_progressive_process_order = sigma_finite_progressive_process_order M F "0 :: real" X for M F X
locale real_sigma_finite_predictable_process_order = sigma_finite_predictable_process_order M F "0 :: real" X for M F X

(* Hierarchies (1/2) *)

sublocale sigma_finite_predictable_process \<subseteq> sigma_finite_progressive_process ..
sublocale sigma_finite_progressive_process \<subseteq> sigma_finite_adapted_process .. 

sublocale nat_sigma_finite_predictable_process \<subseteq> nat_sigma_finite_progressive_process ..
sublocale nat_sigma_finite_progressive_process \<subseteq> nat_sigma_finite_adapted_process .. 

sublocale real_sigma_finite_predictable_process \<subseteq> real_sigma_finite_progressive_process ..
sublocale real_sigma_finite_progressive_process \<subseteq> real_sigma_finite_adapted_process ..

sublocale nat_sigma_finite_adapted_process \<subseteq> nat_filtered_sigma_finite_measure ..
sublocale real_sigma_finite_adapted_process \<subseteq> real_filtered_sigma_finite_measure ..

(* Hierarchies (2/2) *)

sublocale sigma_finite_predictable_process_order \<subseteq> sigma_finite_progressive_process_order ..
sublocale sigma_finite_progressive_process_order \<subseteq> sigma_finite_adapted_process_order .. 

sublocale nat_sigma_finite_predictable_process_order \<subseteq> nat_sigma_finite_progressive_process_order ..
sublocale nat_sigma_finite_progressive_process_order \<subseteq> nat_sigma_finite_adapted_process_order .. 

sublocale real_sigma_finite_predictable_process_order \<subseteq> real_sigma_finite_progressive_process_order ..
sublocale real_sigma_finite_progressive_process_order \<subseteq> real_sigma_finite_adapted_process_order ..

sublocale nat_sigma_finite_adapted_process_order \<subseteq> nat_filtered_sigma_finite_measure ..
sublocale real_sigma_finite_adapted_process_order \<subseteq> real_filtered_sigma_finite_measure ..

text \<open>Thus, right from the outset, we have pretty much every locale we may need.\<close>

end