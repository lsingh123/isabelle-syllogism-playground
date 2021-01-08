theory ARC

imports Main "HOL.Order_Relation" "HOL.Set"

begin

typedecl noun

typedecl verb

datatype Term = Noun noun | All verb Term ("_ all _")
print_theorems

datatype sentence = All Term Term ("All _ _") 

(*This definition is a little wonky because a model needs to interpret both terms and verbs*)
type_synonym 'a pre_model = "'a set \<times> (noun \<Rightarrow> 'a set) \<times> (verb => (('a \<times> 'a) set))"

(*I am doing the clunky thing and defining a premodel and a well defined model because models are more complex for ARC.
there may be a better way to do this.*)
definition wf_model :: "'a pre_model \<Rightarrow> bool"
  where "wf_model M \<equiv> let (U, f, g) = M in (\<forall> v :: verb. g v \<subseteq> U \<times> U) \<and>
 (\<forall> n :: noun. f n \<subseteq> U)"

(*The interpretation of a term in a model is a little more complex because we have 
to handle nouns, verbs, and complex terms differently*)

(*hacky workaround for now - ideally some kind of polymorphism would be best here*)
(*I think it might be better to have this function also handle verbs
That would require some shenanigans with types because the interpretation 
of a verb has type 'a x'a set.*)
fun interp_verb :: "'a pre_model \<Rightarrow> verb \<Rightarrow> ('a \<times> 'a) set" 
  where "interp_verb M v = (let (U, f, g) = M in (g v))"

fun interp :: "'a pre_model \<Rightarrow> Term \<Rightarrow> 'a set" ("_ interpreting _")
  where 
"interp M (Noun n) = (let (U, f, g) = M in f n)"
| "interp M (r all t) = (let (U, f, g) = M in
 {m \<in> U. \<forall> n. (n \<in> (interp M t)) \<longrightarrow> ((m, n) \<in> (interp_verb M r))})"

print_theorems

fun satisfies :: "'a pre_model \<Rightarrow> sentence \<Rightarrow> bool" ("_ \<Turnstile> _")
  where "satisfies M (All x m) = ((interp M x) \<subseteq> (interp M m))"
print_theorems

datatype example_universe = e1 | e2 | e3

find_theorems name:satisfies

(*assms(3) was the key to this example. I wasn't able to 
complete the proof without specifying the universe.*)
lemma example_model:
  fixes M
  assumes "(UNIV::noun set) = {dog, cat}"
  assumes "(UNIV::verb set) = {see}"
  assumes "let (U, f, g) = M in (U = (UNIV:: example_universe set))"
  assumes "interp M (Noun dog) = {e2}"
  assumes "interp M (Noun cat) = {e1, e3}"
  assumes "interp_verb M see = {(e2, e1), (e2, e2), (e2, e3)}"
  assumes "wf_model M"
  shows "M \<Turnstile> (All (Noun dog) (see all (Noun dog)))"
and "M \<Turnstile> All (see all (Noun cat)) (see all (Noun dog))"
proof - 
  have "{e2} \<subseteq> interp M (see all (Noun dog))" 
    using assms by force
  thus "M \<Turnstile> (All (Noun dog) (see all (Noun dog)))"
    using assms(4) by auto
  have "interp M (see all (Noun cat)) = {e2}" 
    using assms by force
  thus "M \<Turnstile> All (see all (Noun cat)) (see all (Noun dog))"
    using \<open>{e2} \<subseteq> interp M (see all( Noun dog))\<close> by auto
qed

definition M_satisfies_G :: "'a pre_model \<Rightarrow> sentence set \<Rightarrow> bool"
  where "M_satisfies_G M G \<equiv> \<forall> g. g \<in> G \<longrightarrow> satisfies M g"

definition entails :: "sentence set \<Rightarrow> sentence \<Rightarrow> 'a itself \<Rightarrow> bool"
  where "entails G phi (ty:: 'a itself) \<equiv> \<forall> (M :: 'a pre_model). M_satisfies_G M G \<and> (wf_model M) \<longrightarrow> satisfies M phi"

find_theorems name:subset_
lemma example_2_6:
  shows "entails {All d (chase all a), All c a} (All d (chase all c)) (TYPE(sentence))"
  unfolding entails_def
proof (rule+)
  fix M assume "M_satisfies_G M {All d (chase all a), All c a}"
  have "M \<Turnstile> All d (chase all a)"
    by (meson M_satisfies_G_def \<open>M_satisfies_G M {All d (chase all a), All c a}\<close> insertI1)
  have "M \<Turnstile> All c a"
    by (meson M_satisfies_G_def \<open>M_satisfies_G M {All d (chase all a), All c a}\<close> insert_subset subset_insertI) 
  (*have "M \<Turnstile> All d (chase all c)"*)
  have "M \<Turnstile> All d (chase all c)"
    unfolding satisfies.simps 
  proof - 
    fix x assume "x = interp M d"
    fix y assume "y = interp M (chase all c)"
    have "interp M c \<subseteq> interp M a"
      using \<open>M \<Turnstile> All c a\<close> by auto 
    then have  "interp M (chase all c) \<subseteq> interp M (chase all a)"
      unfolding interp.simps using subset_eq  
  