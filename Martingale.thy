theory Martingale                 
  imports Stochastic_Process Conditional_Expectation_Banach
begin                

subsection \<open>Martingale\<close>

locale martingale = sigma_finite_adapted_process +
  assumes integrable: "\<And>i. integrable M (X i)"
      and martingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>"

locale martingale_order = martingale M F X for M F and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"

lemma (in filtered_sigma_finite_measure) martingale_const[intro]:  
  assumes "integrable M f" "f \<in> borel_measurable (F \<bottom>)"
  shows "martingale M F (\<lambda>_. f)"
  using assms cond_exp_F_meas[OF assms(1), THEN AE_symmetric]
  by (unfold_locales)
     (metis bot.extremum measurable_from_subalg sets_F_mono space_F subalgebra_def, blast,
      metis (mono_tags, lifting) borel_measurable_subalgebra bot_least filtration.sets_F_mono filtration_axioms space_F) 

lemma (in filtered_sigma_finite_measure) martingale_cond_exp[intro]:  
  assumes "integrable M f"
  shows "martingale M F (\<lambda>i. cond_exp M (F i) f)"
  by (unfold_locales,
      auto simp add: subalgebra borel_measurable_cond_exp borel_measurable_cond_exp' intro!: cond_exp_nested_subalg[OF assms],
      simp add: sets_F_mono space_F subalgebra_def)

subsection \<open>Submartingale\<close>

locale submartingale = sigma_finite_adapted_process_order +
  assumes integrable: "\<And>i. integrable M (X i)"
      and submartingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>"

sublocale martingale_order \<subseteq> submartingale  using martingale_property by (unfold_locales) (force simp add: integrable)+

subsection \<open>Supermartingale\<close>

locale supermartingale = sigma_finite_adapted_process_order +
  assumes integrable: "\<And>i. integrable M (X i)"
      and supermartingale_property: "\<And>i j. i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>"

sublocale martingale_order \<subseteq> supermartingale using martingale_property by (unfold_locales) (force simp add: integrable)+

lemma martingale_iff: "martingale M F X \<longleftrightarrow> submartingale M F X \<and> supermartingale M F X"
proof (rule iffI)
  assume asm: "martingale M F X"
  interpret martingale_order M F X by (intro martingale_order.intro asm)
  show "submartingale M F X \<and> supermartingale M F X" using submartingale_axioms supermartingale_axioms by blast
next
  assume asm: "submartingale M F X \<and> supermartingale M F X"
  interpret submartingale M F X by (simp add: asm)
  interpret supermartingale M F X by (simp add: asm)
  show "martingale M F X" using submartingale_property supermartingale_property by (unfold_locales, intro integrable, force)
qed

subsection \<open>Martingale Lemmas\<close>

context martingale
begin

lemma set_integral_eq:
  assumes "A \<in> F i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)"
proof -
  have "\<integral>x \<in> A. X i x \<partial>M = \<integral>x \<in> A. cond_exp M (F i) (X j) x \<partial>M" using martingale_property[OF assms(2)] borel_measurable_cond_exp' assms(1) subalgebra subalgebra_def by (intro set_lebesgue_integral_cong_AE[OF _ random_variable]) fastforce+
  also have "... = \<integral>x \<in> A. X j x \<partial>M" using assms(1) by (auto simp: integrable intro: cond_exp_set_integral[symmetric])
  finally show ?thesis .
qed

lemma scaleR_const[intro]:
  shows "martingale M F (\<lambda>i x. c *\<^sub>R X i x)"
proof -
  {
    fix i j :: 'b assume "i \<le> j"
    hence "AE x in M. c *\<^sub>R X i x = cond_exp M (F i) (\<lambda>x. c *\<^sub>R X j x) x" 
      using cond_exp_scaleR_right[OF integrable, of i c, THEN AE_symmetric] martingale_property by force
  }
  thus ?thesis by (unfold_locales) (auto simp add: borel_measurable_const_scaleR adapted random_variable integrable)
qed

lemma uminus[intro]:
  shows "martingale M F (- X)" 
  using scaleR_const[of "-1"] by (force intro: back_subst[of "martingale M F"])

lemma add[intro]:
  assumes "martingale M F Y"
  shows "martingale M F (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: martingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. X i \<xi> + Y i \<xi> = cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using cond_exp_add[OF integrable martingale.integrable[OF assms], of i j j, THEN AE_symmetric] 
            martingale_property[OF asm] martingale.martingale_property[OF assms asm] by force
  }
  thus ?thesis using assms
  by (unfold_locales) (auto simp add: borel_measurable_add random_variable adapted integrable Y.adapted Y.random_variable martingale.integrable)
qed

lemma diff[intro]:
  assumes "martingale M F Y"
  shows "martingale M F (\<lambda>i x. X i x - Y i x)"
proof -
  interpret Y: martingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. X i \<xi> - Y i \<xi> = cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using cond_exp_diff[OF integrable martingale.integrable[OF assms], of i j j, THEN AE_symmetric, unfolded fun_diff_def] 
            martingale_property[OF asm] martingale.martingale_property[OF assms asm] by fastforce
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_diff random_variable adapted integrable Y.random_variable Y.adapted martingale.integrable)  
qed

end

lemma (in sigma_finite_adapted_process) martingale_of_set_integral_eq:
  assumes integrable: "\<And>i. integrable M (X i)"
      and "\<And>A i j. i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" 
    shows "martingale M F X"
proof (unfold_locales)
  fix i j :: 'b assume asm: "i \<le> j"
  interpret r: sigma_finite_measure "restr_to_subalg M (F i)" by (simp add: sigma_fin_subalg)
  {
    fix A assume "A \<in> restr_to_subalg M (F i)"
    hence *: "A \<in> F i" using sets_restr_to_subalg subalgebra by blast
    have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * subalg by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
    also have "... = set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(2)[OF asm] cond_exp_set_integral[OF integrable] by auto
    finally have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * subalg by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
  }
  hence "AE \<xi> in restr_to_subalg M (F i). X i \<xi> = cond_exp M (F i) (X j) \<xi>" by (intro r.density_unique, auto intro: integrable_in_subalg subalg borel_measurable_cond_exp integrable)
  thus "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalg] by blast
qed (simp add: integrable)

subsection \<open>Submartingale Lemmas\<close>

context submartingale
begin

lemma set_integral_le:
  assumes "A \<in> F i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)" 
  unfolding cond_exp_set_integral[OF integrable assms(1), of j]  
  using submartingale_property[OF assms(2)]
  by (simp only: set_lebesgue_integral_def, intro integral_mono_AE_banach, metis assms(1) in_mono integrable integrable_mult_indicator subalgebra subalgebra_def, metis assms(1) in_mono integrable_mult_indicator subalgebra subalgebra_def integrable_cond_exp) 
     (auto intro: scaleR_left_mono)

lemma cond_exp_diff_nonneg: 
  assumes "i \<le> j"
  shows "AE x in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x"
  using submartingale_property[OF assms] cond_exp_diff[OF integrable(1,1), of i j i] cond_exp_F_meas[OF integrable adapted, of i] by fastforce

lemma add[intro]:
  assumes "submartingale M F Y"
  shows "submartingale M F (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: submartingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. X i \<xi> + Y i \<xi> \<le> cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using cond_exp_add[OF integrable submartingale.integrable[OF assms], of i j j] 
            submartingale_property[OF asm] submartingale.submartingale_property[OF assms asm] add_mono[of "X i _" _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_add random_variable adapted integrable Y.random_variable Y.adapted submartingale.integrable)  
qed

lemma diff[intro]:
  assumes "supermartingale M F Y"
  shows "submartingale M F (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
proof -
  interpret Y: supermartingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. X i \<xi> - Y i \<xi> \<le> cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using cond_exp_diff[OF integrable supermartingale.integrable[OF assms], of i j j, unfolded fun_diff_def] 
            submartingale_property[OF asm] supermartingale.supermartingale_property[OF assms asm] diff_mono[of "X i _" _ _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_diff random_variable adapted integrable Y.random_variable Y.adapted supermartingale.integrable)  
qed

lemma scaleR_nonneg: 
  assumes "c \<ge> 0"
  shows "submartingale M F (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "i \<le> j"
    show "AE \<xi> in M. c *\<^sub>R X i \<xi> \<le> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>"  
      using cond_exp_scaleR_right[OF integrable, of i "c" j] submartingale_property[OF asm] by (auto intro!: scaleR_left_mono[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma scaleR_nonpos: 
  assumes "c \<le> 0"
  shows "supermartingale M F (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "i \<le> j"
    show "AE \<xi> in M. c *\<^sub>R X i \<xi> \<ge> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>" 
      using cond_exp_scaleR_right[OF integrable, of i "c" j] submartingale_property[OF asm] by (auto intro!: scaleR_left_mono_neg[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma uminus[intro]:
  shows "supermartingale M F (- X)"
  unfolding fun_Compl_def using scaleR_nonpos[of "-1"] by simp

lemma max:
  assumes "submartingale M F Y"
  shows "submartingale M F (\<lambda>i \<xi>. max (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: submartingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> max (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)" using submartingale_property Y.submartingale_property asm unfolding max_def by fastforce
    thus "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> cond_exp M (F i) (\<lambda>\<xi>. max (X j \<xi>) (Y j \<xi>)) \<xi>" using cond_exp_max[OF integrable Y.integrable, of i j j] order.trans by fast
  }
  show "\<And>i. (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. integrable M (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma max_0:
  shows "submartingale M F (\<lambda>i \<xi>. max 0 (X i \<xi>))"
proof -
  interpret zero: martingale_order M F "\<lambda>_ _. 0" by (unfold_locales, auto)
  show ?thesis by (intro zero.max submartingale_axioms)
qed

end

lemma (in sigma_finite_adapted_process_order) submartingale_of_cond_exp_diff_nonneg:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and diff_nonneg: "\<And>i j. i \<le> j \<Longrightarrow> AE x in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x"
    shows "submartingale M F X"
proof (unfold_locales)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    show "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" 
      using diff_nonneg[OF asm] cond_exp_diff[OF integrable(1,1), of i j i] cond_exp_F_meas[OF integrable adapted, of i] by fastforce
  }
qed (intro integrable)

lemma (in sigma_finite_adapted_process_order) submartingale_of_set_integral_le:
  assumes integrable: "\<And>i. integrable M (X i)"
      and "\<And>A i j. i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)"
    shows "submartingale M F X"
proof (unfold_locales)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    interpret r: sigma_finite_measure "restr_to_subalg M (F i)" by (simp add: sigma_fin_subalg)
    {
      fix A assume "A \<in> restr_to_subalg M (F i)"
      hence *: "A \<in> F i" using sets_restr_to_subalg subalgebra by blast
      have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * subalg by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
      also have "... \<le> set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(2)[OF asm] cond_exp_set_integral[OF integrable] by auto
      also have "... = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * subalg by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
      finally have "0 \<le> set_lebesgue_integral (restr_to_subalg M (F i)) A (\<lambda>\<xi>. cond_exp M (F i) (X j) \<xi> - X i \<xi>)" using * subalg by (subst set_integral_diff, auto simp add: set_integrable_def sets_restr_to_subalg intro!: integrable adapted integrable_in_subalg borel_measurable_scaleR borel_measurable_indicator borel_measurable_cond_exp integrable_mult_indicator)
    }
    hence "AE \<xi> in restr_to_subalg M (F i). 0 \<le> cond_exp M (F i) (X j) \<xi> - X i \<xi>" by (intro r.density_nonneg integrable_in_subalg subalg borel_measurable_diff borel_measurable_cond_exp adapted Bochner_Integration.integrable_diff integrable_cond_exp integrable)
    thus "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalg] by simp
    }
qed (intro integrable)

subsection \<open>Supermartingale Lemmas\<close>

text \<open>The following lemmas are exact duals of submartingale lemmas.\<close>

context supermartingale
begin

lemma set_integral_ge:
  assumes "A \<in> F i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) \<ge> set_lebesgue_integral M A (X j)"
  unfolding cond_exp_set_integral[OF integrable assms(1), of j]
  using supermartingale_property[OF assms(2)] 
  by (simp only: set_lebesgue_integral_def, intro integral_mono_AE_banach, metis assms(1) in_mono integrable_mult_indicator subalgebra subalgebra_def integrable_cond_exp, metis assms(1) in_mono integrable integrable_mult_indicator subalgebra subalgebra_def)
     (auto intro: scaleR_left_mono)

lemma cond_exp_diff_nonneg:
  assumes "i \<le> j"
  shows "AE x in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. X i \<xi> - X j \<xi>) x"
  using supermartingale_property[OF assms] cond_exp_diff[OF integrable(1,1), of i i j] cond_exp_F_meas[OF integrable adapted, of i] by fastforce

lemma add[intro]:
  assumes "supermartingale M F Y"
  shows "supermartingale M F (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: supermartingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. X i \<xi> + Y i \<xi> \<ge> cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using cond_exp_add[OF integrable supermartingale.integrable[OF assms], of i j j] 
            supermartingale_property[OF asm] supermartingale.supermartingale_property[OF assms asm] add_mono[of _ "X i _" _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_add random_variable adapted integrable Y.random_variable Y.adapted supermartingale.integrable)  
qed

lemma diff[intro]:
  assumes "submartingale M F Y"
  shows "supermartingale M F (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
proof -
  interpret Y: submartingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. X i \<xi> - Y i \<xi> \<ge> cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using cond_exp_diff[OF integrable submartingale.integrable[OF assms], of i j j, unfolded fun_diff_def] 
            supermartingale_property[OF asm] submartingale.submartingale_property[OF assms asm] diff_mono[of _ "X i _" "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_diff random_variable adapted integrable Y.random_variable Y.adapted submartingale.integrable)  
qed

lemma scaleR_nonneg: 
  assumes "c \<ge> 0"
  shows "supermartingale M F (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "i \<le> j"
    show "AE \<xi> in M. c *\<^sub>R X i \<xi> \<ge> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>" 
      using cond_exp_scaleR_right[OF integrable, of i "c" j] supermartingale_property[OF asm] 
      by (auto intro!: scaleR_left_mono[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma scaleR_nonpos: 
  assumes "c \<le> 0"
  shows "submartingale M F (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "i \<le> j"
    show "AE \<xi> in M. c *\<^sub>R X i \<xi> \<le> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>" 
      using cond_exp_scaleR_right[OF integrable, of i "c" j] supermartingale_property[OF asm] 
      by (auto intro!: scaleR_left_mono_neg[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma uminus[intro]:
  shows "submartingale M F (- X)"
  unfolding fun_Compl_def using scaleR_nonpos[of "-1"] by simp

lemma min:
  assumes "supermartingale M F Y"
  shows "supermartingale M F (\<lambda>i \<xi>. min (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: supermartingale M F Y by (rule assms)
  {
    fix i j :: 'b assume asm: "i \<le> j"
    have "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> min (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)" using supermartingale_property Y.supermartingale_property asm unfolding min_def by fastforce
    thus "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> cond_exp M (F i) (\<lambda>\<xi>. min (X j \<xi>) (Y j \<xi>)) \<xi>" using cond_exp_min[OF integrable Y.integrable, of i j j] order.trans by fast
  }
  show "\<And>i. (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. integrable M (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma min_0:
  shows "supermartingale M F (\<lambda>i \<xi>. min 0 (X i \<xi>))"
proof -
  interpret zero: martingale_order M F "\<lambda>_ _. 0" by (unfold_locales, auto)
  show ?thesis by (intro zero.min supermartingale_axioms)
qed

end

lemma (in sigma_finite_adapted_process_order) supermartingale_of_cond_exp_diff_nonneg: 
  assumes integrable: "\<And>i. integrable M (X i)" 
      and diff_nonneg: "\<And>i j. i \<le> j \<Longrightarrow> AE x in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. X i \<xi> - X j \<xi>) x"
    shows "supermartingale M F X"
proof 
  {
    fix i j :: 'b assume asm: "i \<le> j"
    show "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>" 
      using diff_nonneg[OF asm] cond_exp_diff[OF integrable(1,1), of i i j] cond_exp_F_meas[OF integrable adapted, of i] by fastforce
  }
qed (intro integrable)

lemma (in sigma_finite_adapted_process_order) supermartingale_of_set_integral_ge:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i j. i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X j) \<le> set_lebesgue_integral M A (X i)" 
    shows "supermartingale M F X"
proof -
  interpret uminus_X: sigma_finite_adapted_process_order M F "-X" using uminus[THEN adapted_process.adapted] by (unfold_locales) blast
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "supermartingale M F (-(- X))" using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(2)] *[symmetric]]] subalg
    by (intro submartingale.uminus uminus_X.submartingale_of_set_integral_le) (auto simp add: subalgebra_def integrable fun_Compl_def, blast)
  thus ?thesis unfolding fun_Compl_def by simp
qed

subsection \<open>Discrete Time Martingales\<close>

locale nat_martingale = martingale M F X for M F and X :: "nat \<Rightarrow> _ \<Rightarrow> _"
locale nat_submartingale = submartingale M F X for M F and X :: "nat \<Rightarrow> _ \<Rightarrow> _"
locale nat_supermartingale = supermartingale M F X for M F and X :: "nat \<Rightarrow> _ \<Rightarrow> _"

sublocale nat_martingale \<subseteq> nat_adapted_process by (unfold_locales)
sublocale nat_submartingale \<subseteq> nat_adapted_process_order by (unfold_locales)
sublocale nat_supermartingale \<subseteq> nat_adapted_process_order by (unfold_locales)

subsection "Discrete Time Martingales"

lemma (in nat_martingale) predictable_eq_zero:
  assumes "nat_predictable_process M F X"
  shows "AE \<xi> in M. X i \<xi> = X 0 \<xi>"
proof (induction i)
  case 0
  then show ?case by (simp add: bot_nat_def)
next
  case (Suc i)
  interpret S: nat_adapted_process M F "\<lambda>i. X (Suc i)" by (intro nat_predictable_process.adapted_Suc assms)
  show ?case using Suc S.adapted[of i] martingale_property[OF le_SucI, of i] cond_exp_F_meas[OF integrable, of "Suc i" i] Suc by fastforce
qed

lemma (in nat_sigma_finite_adapted_process) martingale_of_set_integral_eq_Suc:
  assumes integrable: "\<And>i. integrable M (X i)"
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X (Suc i))" 
    shows "nat_martingale M F X"
proof (intro nat_martingale.intro martingale_of_set_integral_eq)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(2)[THEN trans])
  qed
qed (simp add: integrable)

lemma (in nat_sigma_finite_adapted_process) martingale_nat:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "nat_martingale M F X"
proof (unfold_locales)
  fix i j :: nat assume asm: "i \<le> j"
  show "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    hence "j = i" by simp
    thus ?case using cond_exp_F_meas[OF integrable adapted, THEN AE_symmetric] by presburger
  next
    case (Suc n)
    have j: "j = Suc (n + i)" using Suc by linarith
    have n: "n = n + i - i" using Suc by linarith
    have *: "AE \<xi> in M. cond_exp M (F (n + i)) (X j) \<xi> = X (n + i) \<xi>" unfolding j using assms(2)[THEN AE_symmetric] by blast
    have "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (cond_exp M (F (n + i)) (X j)) \<xi>" by (intro cond_exp_nested_subalg integrable subalg, simp add: subalgebra_def space_F sets_F_mono)
    hence "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (X (n + i)) \<xi>" using cond_exp_cong_AE[OF integrable_cond_exp integrable *] by force
    thus ?case using Suc(1)[OF n] by fastforce
  qed
qed (simp add: integrable)

lemma (in nat_sigma_finite_adapted_process) martingale_of_cond_exp_diff_Suc_eq_zero:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. 0 = cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi>" 
    shows "nat_martingale M F X"
proof (intro martingale_nat integrable) 
  fix i 
  show "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(2)[of i] by fastforce
qed

subsection "Discrete Time Submartingales"

lemma (in nat_submartingale) predictable_ge_zero:
  assumes "nat_predictable_process M F X"
  shows "AE \<xi> in M. X i \<xi> \<ge> X 0 \<xi>"
proof (induction i)
  case 0
  then show ?case by (simp add: bot_nat_def)
next
  case (Suc i)
  interpret S: nat_adapted_process M F "\<lambda>i. X (Suc i)" by (intro nat_predictable_process.adapted_Suc assms)
  show ?case using Suc S.adapted[of i] submartingale_property[OF le_SucI, of i] cond_exp_F_meas[OF integrable, of "Suc i" i] Suc by fastforce
qed

lemma (in nat_sigma_finite_adapted_process_order) submartingale_of_set_integral_le_Suc:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X (Suc i))" 
    shows "nat_submartingale M F X"
proof (intro nat_submartingale.intro submartingale_of_set_integral_le)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(2)[THEN order_trans])
  qed
qed (simp add: integrable)

lemma (in nat_sigma_finite_adapted_process_order) submartingale_nat:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "nat_submartingale M F X"
  using subalg integrable assms(2)
  by (intro submartingale_of_set_integral_le_Suc ord_le_eq_trans[OF set_integral_mono_AE_banach cond_exp_set_integral[symmetric]], simp)
     (meson in_mono integrable_mult_indicator set_integrable_def subalgebra_def, meson integrable_cond_exp in_mono integrable_mult_indicator set_integrable_def subalgebra_def, fast+)

lemma (in nat_sigma_finite_adapted_process_order) submartingale_of_cond_exp_diff_Suc_nonneg:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi>" 
    shows "nat_submartingale M F X"
proof (intro submartingale_nat integrable) 
  fix i 
  show "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(2)[of i] by fastforce
qed

lemma (in nat_submartingale) partial_sum_scaleR:
  assumes "nat_sigma_finite_adapted_process M F C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "nat_submartingale M F (\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
proof-
  interpret C: nat_sigma_finite_adapted_process M F C by (rule assms)
  interpret S: nat_sigma_finite_adapted_process_order M F "(\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))" 
    using C.adaptedE adaptedE
  
               nat_adapted_process.partial_sum_Suc[of M F "\<lambda>i \<xi>. C (i - 1) \<xi> *\<^sub>R (X i \<xi> - X (i - 1) \<xi>)", unfolded diff_Suc_1]
    apply (unfold_locales) sorry
  have "integrable M (\<lambda>x. C i x *\<^sub>R (X (Suc i) x - X i x))" for i using assms(2,3)[of i] by (intro Bochner_Integration.integrable_bound[OF integrable_scaleR_right, OF Bochner_Integration.integrable_diff, OF integrable(1,1), of _ R "Suc i" i], auto simp add: mult_mono)
  moreover have "AE \<xi> in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. (\<Sum>i<Suc i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>)) - (\<Sum>i<i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))) \<xi>" for i using cond_exp_measurable_scaleR[OF calculation _ C.adapted, of i] cond_exp_diff_nonneg[OF le_SucI, OF order.refl, of i] assms(2,3)[of i] by (auto simp add: scaleR_nonneg_nonneg integrable)
  ultimately show ?thesis by (intro S.submartingale_of_cond_exp_diff_Suc_nonneg Bochner_Integration.integrable_sum, blast+)
qed

lemma (in nat_submartingale) partial_sum_scaleR':
  assumes "nat_sigma_finite_predictable_process M F C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "nat_submartingale M F (\<lambda>n \<xi>. \<Sum>i<n. C (Suc i) \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
  apply (intro partial_sum_scaleR[of _ R] assms)
  using nat_predictable_process.adapted_Suc

subsection "Discrete Time Supermartingales"

lemma (in nat_supermartingale) predictable_le_zero:
  assumes "nat_predictable_process M F X"
  shows "AE \<xi> in M. X i \<xi> \<le> X 0 \<xi>"
proof (induction i)
  case 0
  then show ?case by (simp add: bot_nat_def)
next
  case (Suc i)
  interpret S: nat_adapted_process M F "\<lambda>i. X (Suc i)" by (intro nat_predictable_process.adapted_Suc assms)
  show ?case using Suc S.adapted[of i] supermartingale_property[OF le_SucI, of i] cond_exp_F_meas[OF integrable, of "Suc i" i] Suc by fastforce
qed

lemma (in nat_adapted_process_order) supermartingale_of_set_integral_ge_Suc:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X (Suc i)) \<le> set_lebesgue_integral M A (X i)" 
    shows "nat_supermartingale M F X"
proof -
  interpret uminus_X: nat_adapted_process_order M F "-X" by (intro nat_adapted_process_order.intro nat_adapted_process.intro uminus)
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "nat_supermartingale M F (-(- X))" using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(2)] *[symmetric]]] subalg
    by (intro nat_supermartingale.intro submartingale.uminus nat_submartingale.axioms uminus_X.submartingale_of_set_integral_le_Suc) (auto simp add: subalgebra_def integrable fun_Compl_def, blast)
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma (in nat_adapted_process_order) supermartingale_nat:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "nat_supermartingale M F X"
proof -
  interpret uminus_X: nat_adapted_process_order M F "-X" by (intro nat_adapted_process_order.intro nat_adapted_process.intro uminus)
  have "AE \<xi> in M. - X i \<xi> \<le> cond_exp M (F i) (\<lambda>x. - X (Suc i) x) \<xi>" for i using assms(2) cond_exp_uminus[OF integrable, of i "Suc i"] by force
  hence "nat_supermartingale M F (-(- X))" by (intro nat_supermartingale.intro submartingale.uminus nat_submartingale.axioms uminus_X.submartingale_nat) (simp only: fun_Compl_def, intro integrable_minus integrable, auto simp add: fun_Compl_def)
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma (in nat_adapted_process_order) supermartingale_of_cond_exp_diff_Suc_nonneg:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. X i \<xi> - X (Suc i) \<xi>) \<xi>" 
    shows "nat_supermartingale M F X"
proof (intro supermartingale_nat integrable) 
  fix i 
  show "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i i "Suc i"] cond_exp_F_meas[OF integrable adapted, of i] assms(2)[of i] by fastforce
qed

end