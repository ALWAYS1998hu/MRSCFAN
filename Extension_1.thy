theory Extension_1
  imports Main SGraph HOL.Real core
begin

primrec unblock_addswap :: "('a\<times>'a) option list \<Rightarrow> ('a\<times>'a) list"
  where "unblock_addswap [] = []"|
        "unblock_addswap (a#as) = (if (a=None) then (unblock_addswap as) else (the a)#(prod.swap(the a))#(unblock_addswap as))"

definition MapReduce_E1 :: 
  "(node\<times>iscore) list \<Rightarrow>(edge\<times>real) list \<Rightarrow>
    ((node\<times>iscore) \<Rightarrow> (node\<times>iscore)) \<Rightarrow> ((edge\<times>real) \<Rightarrow> edge option) \<Rightarrow>
    ((node\<times>iscore) list \<Rightarrow> edge list \<Rightarrow>(node\<times>(iscore list)\<times>(node list)) list) \<Rightarrow>
    ((node\<times>(iscore list)\<times>(node list)) \<Rightarrow> (edge\<times>node\<times>iscore) list) \<Rightarrow>
    (edge\<times>(node\<times>iscore)) list list"
  where "MapReduce_E1 input1 input2 Map1 Map2 Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map1 input1) (unblock_addswap (map Map2 input2)))"

(***************************mapper***************************)

definition "mapper_E1_iscore \<equiv> BNF_Composition.id_bnf"
fun mapper_E1_filter :: "(edge\<times>real) \<Rightarrow> edge option" 
  where "mapper_E1_filter (e,sim) =(if (sim\<ge>\<epsilon>) then Some e else None)"

(***************************shuffer***************************)

fun shuffler_E1 :: "(node\<times>iscore) list \<Rightarrow> edge list \<Rightarrow> (node\<times>(iscore list)\<times>(node list)) list"
  where "shuffler_E1 ncs es=Shuffle_multi ncs es" 

theorem shuffler_E1_theorem:"List.member (shuffler_E1 xs1 xs2) (k,v1s,v2s) \<Longrightarrow> 
        List.member v1s v1 = List.member xs1 (k,v1) \<and> List.member v2s v2 = List.member xs2 (k,v2)"
  apply (rule Shuffle_multi_theorem)
  by auto

(***************************reducer***************************)
fun reducer_E1 :: "(node\<times>(iscore list)\<times>(node list)) \<Rightarrow> (edge\<times>node\<times>iscore) list" 
  where "reducer_E1 (n,b,[]) =[]"|
        "reducer_E1 (n,b,(nn#nns)) =(form_edge n nn,(n,hd b))# (reducer_E1 (n,b,nns))"

theorem reducer_E1_size:"size nns = size (reducer_E1 (n,hd b,nns))"
  apply (induct nns)
  by auto

theorem reducer_E1_member:"List.member nns nn \<Longrightarrow> List.member (reducer_E1 (n,b,nns)) ((form_edge n nn,(n,hd b)))"
  apply (induct nns)
   apply (simp add:member_def)+
  by auto

(***************************result***************************)
definition result_E1 :: "(edge\<times>(node\<times>iscore)) list" 
  where "result_E1 \<equiv> concat (MapReduce_E1 result_Core result_Similarity 
                     mapper_E1_iscore mapper_E1_filter shuffler_E1 reducer_E1)"

end