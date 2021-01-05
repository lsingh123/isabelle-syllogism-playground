theory ARC

imports Main "HOL.Order_Relation"

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
to handle nouns and complex terms differently*)
fun interp :: "'a pre_model \<Rightarrow> Term \<Rightarrow> 'a set" ("_ interpreting _")
  where 
"interp M (Noun n) = (let (U, f, g) = M in f n)"
| "interp M (r all t) = (let (U, f, g) = M in
 {m \<in> U. \<forall> n. (n \<in> (interp M t)) \<longrightarrow> ((m, n) \<in> (g r))})"

print_theorems
(*I think it might be better to have this function also handle verbs
That would require some shenanigans with types because the interpretation 
of a verb has type 'a x'a set.*)

(*hacky workaround for now - ideally some kind of polymorphism would be best here*)
fun interp_verb :: "'a pre_model \<Rightarrow> verb \<Rightarrow> ('a \<times> 'a) set" 
  where "interp_verb M v = (let (U, f, g) = M in (g v))"

fun satisfies :: "'a pre_model \<Rightarrow> sentence \<Rightarrow> bool" ("_ \<Turnstile> _")
  where "satisfies M (All x m) = ((interp M x) \<subseteq> (interp M m))"
print_theorems

datatype example_universe = e1 | e2 | e3

lemma example_model:
  fixes M
  assumes "(UNIV::noun set) = {dog, cat}"
  assumes "(UNIV::verb set) = {see}"
  assumes "interp M (Noun dog) = {e2}"
  assumes "interp M (Noun cat) = {e1, e3}"
  assumes "interp_verb M sees = {(e1, e1), (e1, e2), (e1, e3)}"
  shows "M \<Turnstile> (All (see all (Noun cat)) (see all (Noun dog)))"











