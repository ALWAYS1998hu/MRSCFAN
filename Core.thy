theory Core
  imports Main HOL.Real Complex_Main SGraph Similarity
begin


definition MapReduce_Core :: 
  "(edge\<times>similarity) list \<Rightarrow>
    ((edge\<times>similarity) \<Rightarrow> (node\<times>node\<times>similarity) list) \<Rightarrow>
    ((node\<times>node\<times>similarity) list list \<Rightarrow> (node\<times>(node\<times>similarity) list) list) \<Rightarrow>
    ((node\<times>(node\<times>similarity) list) \<Rightarrow> (node\<times>iscore)) \<Rightarrow>
    (node\<times>iscore) list"
  where "MapReduce_Core input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

(***************************mapper***************************)
fun mapper_Core :: "(edge\<times>similarity) \<Rightarrow> (node\<times>node\<times>similarity) list" 
  where "mapper_Core ((u,v),sim) = [(u,(v,sim)),(v,(u,sim))]"

(***************************shuffer***************************)
definition shuffler_Core :: "((node\<times>node\<times>similarity) list) list \<Rightarrow>(node\<times>(node\<times>similarity) list) list"
  where "shuffler_Core xs \<equiv> Shuffle_single_inputlistlist xs"

theorem shuffler_Core_theorem : "List.member (shuffler_Core xss) (k,vs) \<Longrightarrow> 
        (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "
  by (simp add: Shuffle_single_inputlistlist_theorem shuffler_Core_def)

(***************************reducer***************************)  
primrec count :: "(node\<times>similarity) list  \<Rightarrow>nat" 
  where "count []  = 0"|
        "count (a#as)  = (if (snd a\<ge>\<epsilon>) then Suc (count as) else count as)"

fun iscore :: "(node\<times>real) list \<Rightarrow>bool" 
  where "iscore as = (if (count as  \<ge> \<mu>) then True else False)"

fun reducer_Core :: "(node\<times>(node\<times>real) list)\<Rightarrow>(node\<times>iscore) " 
  where "reducer_Core a = (fst a,iscore (snd a))"

lemma count_lemma :"size (filter (\<lambda> t::(node\<times>similarity). snd t\<ge>\<epsilon>) as) =count as "
  apply (induct as)
  by simp+
theorem reducer_Core_theorem :" size (filter (\<lambda> t::(node\<times>similarity). snd t \<ge>\<epsilon>) (snd nns)) \<ge> \<mu> 
        \<Longrightarrow> snd (reducer_Core nns) = True "
  by (simp add:count_lemma)

(***************************result***************************)
definition result_Core :: "(node \<times> iscore) list" 
  where "result_Core \<equiv> MapReduce_Core result_Similarity mapper_Core shuffler_Core reducer_Core"

end