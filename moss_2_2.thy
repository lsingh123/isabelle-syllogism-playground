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

















