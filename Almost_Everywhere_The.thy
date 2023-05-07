theory Misc
  imports "HOL-Analysis.Measure_Space" "HOL-Analysis.Bochner_Integration"
begin

lemma banach_simple_function_indicator_representation:
  fixes f ::"'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "simple_function M f" and x: "x \<in> space M"
  shows "f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"
  (is "?l = ?r")
proof -
  have "?r = (\<Sum>y \<in> f ` space M.
    (if y = f x then indicator (f -` {y} \<inter> space M) x *\<^sub>R y else 0))" by (auto intro!: sum.cong)
  also have "... =  indicator (f -` {f x} \<inter> space M) x *\<^sub>R f x" using assms by (auto dest: simple_functionD)
  also have "... = f x" using x by (auto simp: indicator_def)
  finally show ?thesis by auto
qed

lemma bochner_integrable_induct[consumes 1, case_names set add seq]:
  fixes P :: "('a \<Rightarrow> 'b :: {second_countable_topology, banach}) \<Rightarrow> bool"
  assumes u: "integrable M u"
  assumes cong: "\<And>f g. integrable M f \<Longrightarrow> integrable M g \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P g \<Longrightarrow> P f"
  assumes set: "\<And>A y. A \<in> sets M \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>u v. P u \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  assumes seq: "\<And>u s. (\<And>i. Bochner_Integration.simple_bochner_integrable M (s i)) \<Longrightarrow> (\<And>i. P (s i)) \<Longrightarrow> ((\<lambda>i. \<integral>\<^sup>+x. norm (u x - s i x) \<partial>M) \<longlonglongrightarrow> 0) \<Longrightarrow> P u"
  shows "P u"
proof-
  obtain I where "has_bochner_integral M u I" using u integrable.cases by auto
  then obtain s where s_is: "Bochner_Integration.simple_bochner_integrable M (s i)" "((\<lambda>i. \<integral>\<^sup>+x. norm (u x - s i x) \<partial>M) \<longlonglongrightarrow> 0)" for i using has_bochner_integral.cases by force

  have s_simple: "simple_function M (s i)" for i using s_is using simple_bochner_integrable.simps by blast

  have P_set: "P (\<lambda>x. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" for i y using set s_simple simple_functionD(2) by blast
  have P_add: "P (\<lambda>x. \<Sum>y \<in> s i ` space M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" for i using simple_functionD(1)[OF s_simple]
  proof (induction rule: finite_induct)
    case empty
    then show ?case using set[of "{}"] by simp
  next
    case (insert x F)
    have "(\<Sum>y\<in>insert x F. indicat_real (s i -` {y} \<inter> space M) z *\<^sub>R y) = indicat_real (s i -` {x} \<inter> space M) z *\<^sub>R x + (\<Sum>y\<in>F. indicat_real (s i -` {y} \<inter> space M) z *\<^sub>R y)" for z using insert(2) by (subst sum.insert_remove[OF insert(1)], auto)
    then show ?case using P_set insert(3) add by presburger
  qed

  have s_i_integrable: "integrable M (s i)" for i by (simp add: integrableI_simple_bochner_integrable s_is(1))
  moreover have s_i_rep: "s i x = (\<Sum>y \<in> s i ` space M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" if "x \<in> space M" for x i using banach_simple_function_indicator_representation[OF s_simple that] by blast
  moreover have "integrable M (\<lambda>x. \<Sum>y \<in> s i ` space M. indicator (s i -` {y} \<inter> space M) x *\<^sub>R y)" for i using s_i_rep s_i_integrable by (rule integrable_cong[OF refl, of M "s i", THEN iffD1], blast)
  ultimately have "P (s i)" for i using cong P_add by meson
  thus ?thesis using seq s_is by blast
qed
  

end