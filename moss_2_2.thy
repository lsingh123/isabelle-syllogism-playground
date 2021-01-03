theory moss_2_2

imports Main "HOL.Order_Relation"

begin

subsection "Syntax and Semantics"

typedecl atomic 

datatype wff = All atomic atomic ("All _ are _")
print_theorems

type_synonym 'a model = "(atomic \<Rightarrow> 'a set)"

fun satisfies :: "'a model \<Rightarrow> wff \<Rightarrow> bool" ("_ \<Turnstile> _")
  where "satisfies M (All x are y) = (M x \<subseteq> M y)"

datatype example2_1 = e1 | e2 | e3 | e4 | e5

lemma example2_1: 
  assumes "(UNIV :: atomic set) = {n, p, q} \<and> n \<noteq> p \<and> p \<noteq> q \<and> n \<noteq> q"
  assumes "M n = {} \<and> M p = {e1, e3, e4} \<and> M q = {e1,e3}"
  shows "M \<Turnstile> (All n are n)"
    and  "M \<Turnstile> (All n are p)"
    and  "M \<Turnstile> (All n are q)"
    and  "M \<Turnstile> (All p are p)"
    and  "M \<Turnstile> (All q are p)"
    and  "M \<Turnstile> (All q are q)"
    and  "\<not>( M \<Turnstile> (All p are n))"
    and  "\<not> (M \<Turnstile> (All p are q))"
    and  "\<not>( M \<Turnstile> (All q are n))"
          apply simp
         apply (simp add: assms(2))
        apply (simp add: assms(2))
       apply simp
      apply (simp add: assms(2))
     apply simp
  apply (simp add: assms(2))
   apply (simp add: assms(2))
  by (simp add: assms(2))

definition M_satisfies_G :: "'a model \<Rightarrow> wff set \<Rightarrow> bool" ("_ \<Turnstile>M _")
  where "M_satisfies_G M G \<equiv> \<forall> f. f \<in> G \<longrightarrow> (M \<Turnstile> f)"

definition entails :: "wff set \<Rightarrow> wff \<Rightarrow> 'a itself \<Rightarrow> bool" ("_ \<Turnstile>G _")
  where "entails G phi (ty:: 'a itself) \<equiv> \<forall> (M :: 'a model). (M_satisfies_G M G) \<longrightarrow> (M \<Turnstile> phi)"

subsection "Proof Theory"

inductive derivable :: "wff \<Rightarrow> bool" ("0\<Turnstile>")
  where A_axiom: "derivable (All X are X)"
  | A_barbara: "\<lbrakk> derivable (All X are Y); derivable (All Y are Z) \<rbrakk> \<Longrightarrow> derivable (All X are Z)"

lemma example_2_5: 
  assumes "derivable All l are m"
and "derivable All q are l"
and "derivable All m are p"
and "derivable All n are p"
and "derivable All l are q"
shows "derivable All q are p"
  apply (rule_tac Y=l in A_barbara)
   apply (rule assms(2))
  apply (rule_tac Y=m in A_barbara)
   apply (rule_tac Y=m in A_barbara)
    apply (rule assms(1))
   apply (rule A_axiom)
  apply (rule assms(3))
  done

inductive derives:: "wff set \<Rightarrow> wff \<Rightarrow> bool" ("_ \<turnstile> _")
  where A_assumption: "f \<in> hs \<Longrightarrow> hs \<turnstile> f"
  | A_axiom: "hs \<turnstile> All x are x"
  | A_barbara: "\<lbrakk> hs \<turnstile> (All X are Y);  hs \<turnstile> (All Y are Z) \<rbrakk> \<Longrightarrow>  hs \<turnstile> (All X are Z)"

lemma example_2_5_b: 
  fixes l m n p q
  defines "G_2_5 \<equiv> {All l are m, All q are l, All m are p, All n are p, All l are q}"
  shows "G_2_5 \<turnstile> All q are p"
  apply (rule_tac Y=l in A_barbara)
   apply (rule A_assumption) apply (simp add: G_2_5_def)
  apply (rule_tac Y=m in A_barbara)
   apply (rule A_assumption) apply (simp add: G_2_5_def)
  apply (rule A_assumption) apply (simp add: G_2_5_def)
  done

lemma soundness: 
  fixes G g
  assumes "G \<turnstile> g"
  shows "entails G g (TYPE(atomic))"
  using assms
proof (induct rule: derives.induct)
  case (A_assumption)
  show ?case
    by (simp add: A_assumption.hyps M_satisfies_G_def entails_def)
next 
  case (A_axiom) 
  show ?case
    by (simp add: entails_def)
next 
  case (A_barbara) 
  show ?case
    by (meson A_barbara.hyps(2) A_barbara.hyps(4) entails_def satisfies.simps subset_trans)
qed

lemma soundness2: 
  fixes G g
  assumes "G \<turnstile> g"
  shows "entails G g (TYPE(atomic))"
  apply (rule derives.induct)
     apply (rule assms)
    apply (simp add: M_satisfies_G_def entails_def)
  apply (simp add: entails_def)
  using derives.A_barbara soundness by blast

definition less_equal_atomic :: "atomic \<Rightarrow> wff set \<Rightarrow> atomic \<Rightarrow> bool" ("_ \<lesssim> _ _")
  where "less_equal_atomic u G v\<equiv> G \<turnstile> All u are v"

find_theorems name:preorder

lemma prop_2_4_1:
  fixes G 
  shows "preorder_on UNIV {(x,y). x \<lesssim>G y}" 
proof (auto simp add: preorder_on_def)
  show "refl {(x, y). x \<lesssim> G y}"
    by (simp add: derives.A_axiom less_equal_atomic_def refl_on_def)
  show "trans {(x, y). x \<lesssim> G y}"
    by (metis (mono_tags, lifting) CollectD CollectI case_prodD case_prodI derives.A_barbara less_equal_atomic_def transI)
qed

definition "canonical_model G u \<equiv> {v. v\<lesssim>G u}"

lemma lemma_2_4_2: 
  fixes G
  assumes "M = canonical_model G"
  shows "M \<Turnstile>M G"
proof (auto simp add: M_satisfies_G_def)
  fix f assume "f \<in> G"
  show "M \<Turnstile> f"
    by (metis A_assumption \<open>f \<in> G\<close> assms canonical_model_def derives.A_barbara less_equal_atomic_def mem_Collect_eq satisfies.elims(3) subsetI)
qed


lemma lemma_2_4_2_b: 
  fixes G
  assumes "M = canonical_model G"
  shows "M \<Turnstile>M G"
proof (auto simp add: M_satisfies_G_def)
  fix g assume "g \<in> G"
  then obtain p q where "(All p are q) = g"
    by (metis wff.exhaust)
  then have "p \<lesssim> G q" using A_assumption
    by (simp add: \<open>g \<in> G\<close> less_equal_atomic_def)
  then have "M p \<subseteq> M q" using A_barbara
    using assms canonical_model_def less_equal_atomic_def by blast
  thus "M \<Turnstile> g"
    using \<open>(All p are q) = g\<close> by auto
qed

lemma completeness:
  assumes "entails G (All p are q) (TYPE(atomic))"
  shows "G \<turnstile> (All p are q)"
proof -
  define M where "M \<equiv> canonical_model G"
  have "M \<Turnstile> All p are q" using lemma_2_4_2
    using M_def assms entails_def by blast
  then have "M p \<subseteq> M q"
    by simp
  have "p \<lesssim> G p"
    by (simp add: derives.A_axiom less_equal_atomic_def)
  then have "p \<in> M p"
    by (simp add: M_def canonical_model_def)
  have "p \<in> M q"
    using \<open>M p \<subseteq> M q\<close> \<open>p \<in> M p\<close> by blast
  then have "p \<lesssim> G q"
    using M_def canonical_model_def by blast
  thus ?thesis
    using less_equal_atomic_def by blast
qed

lemma example_2_1_aa:
  assumes "(UNIV :: atomic set) = {n}"
  shows "card (UNIV :: atomic set) = 1"
proof - 
  obtain A where "A \<equiv> (UNIV :: wff set)"
    by simp
  then have "A = {All n are n}"
    by (metis UNIV_I UNIV_eq_I assms insertI1 singletonD wff.exhaust)
  then have "card (A) = 1"
    by (simp add: \<open>A = {All n are n}\<close>)
  thus ?thesis
    by (simp add: assms)
qed

lemma example_2_1_ab_1:
  assumes "(UNIV::atomic set) = {n, p, q}"
  assumes "X = {All n are n, All p are p, All q are q, All n are p, All n are q, All p are n, All p are q, All q are n, All q are p}"
  assumes "not_equal n p"
  assumes "not_equal n q"
  assumes "not_equal q p"
  shows "X = (UNIV::wff set)"
proof - 
  obtain A where "A \<equiv> (UNIV :: wff set)"
    by simp
  have "\<forall> x. x \<in> A \<longrightarrow> (\<exists> c . \<exists>b . x = (All c are b) \<and> (c \<in> (UNIV:: atomic set))\<and> (b \<in> (UNIV:: atomic set)))"
    by (meson UNIV_I wff.exhaust) 
  then have "\<forall> x. x \<in> A \<longrightarrow> x \<in> X"
    by (smt assms(1) assms(2) insertE insert_subset singletonD subset_insertI)
  then have "A \<subseteq> X"
    by blast
  have "X \<subseteq> A"
    by (simp add: \<open>A \<equiv> UNIV\<close>)
  then have "X = A"
    using \<open>A \<subseteq> X\<close> by blast
  thus ?thesis
    by (simp add: \<open>A \<equiv> UNIV\<close>)
qed

lemma example_2_1_ab_2:
  assumes "(UNIV::atomic set) = {n, p, q}"
  assumes "not_equal n p"
  assumes "not_equal n q"
  assumes "not_equal q p"
  shows "card(UNIV::wff set) = 9"
proof - 
  define X where "X = {All n are n, All p are p, All q are q, All n are p, All n are q, All p are n, All p are q, All q are n, All q are p}"
  obtain A where "A \<equiv> (UNIV :: wff set)"
    by simp
  have "card(X) = 9" using X_def and assms by fastforce
  have "A = X" using example_2_1_ab_1
    using X_def \<open>A \<equiv> UNIV\<close> assms(1) assms(2) assms(3) assms(4) by presburger
  thus ?thesis
    using \<open>A \<equiv> UNIV\<close> \<open>card X = 9\<close> by blast
qed


lemma example_2_2:
  shows "entails {(All p are q), (All n are p)} (All n are q) TYPE(atomic)"
proof -
  have "\<forall> M. (M \<Turnstile>M {All p are q, All n are p}) \<longrightarrow> (M \<Turnstile>M {All n are q})"
    by (metis M_satisfies_G_def insertI1 insert_commute order.trans satisfies.simps singletonD)
  have "\<forall> M. (M \<Turnstile>M {All n are q}) \<longrightarrow> (M \<Turnstile> All n are q)"
    by (simp add: M_satisfies_G_def)
  then have "\<forall> M. (M \<Turnstile>M {All p are q, All n are p}) \<longrightarrow> (M \<Turnstile> All n are q)"
    using \<open>\<forall>M. (M \<Turnstile>M {All p are q, All n are p}) \<longrightarrow> (M \<Turnstile>M {All n are q})\<close> by blast
  thus ?thesis
    using entails_def by blast
qed

lemma example_2_2_b:
  shows "entails {(All p are q), (All n are p)} (All n are q) TYPE(atomic)"
  unfolding entails_def
proof (rule+)
  fix M assume "M \<Turnstile>M {All p are q, All n are p}"
  then have "M \<Turnstile>M {All n are q}"
    by (metis M_satisfies_G_def insertI1 insert_commute order.trans satisfies.simps singletonD)
  thus "M \<Turnstile> All n are q"
    using M_satisfies_G_def by blast
qed

lemma example_2_4_1:
  fixes G
  assumes "M = canonical_model G"
  assumes "entails G g (TYPE(atomic))"
  shows "G \<turnstile> g"
  by (metis assms(2) completeness entails_def lemma_2_4_2 satisfies.elims(2))


lemma example_2_4_2:
  fixes G g M
  assumes "M = canonical_model G"
  assumes "M \<Turnstile> g"
  shows "G \<turnstile> g"
proof -
  have "entails G g (TYPE(atomic))"
    by (metis assms(1) assms(2) canonical_model_def derives.A_axiom insert_subset less_equal_atomic_def mem_Collect_eq satisfies.simps soundness subsetI subset_trans wff.exhaust)
  thus ?thesis
    using example_2_4_1 by blast
qed













  









    






   
  

  


  

  





























