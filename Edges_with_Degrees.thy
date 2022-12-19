theory Edges_with_Degrees
  imports Main SGraph Shuffle
begin

definition MapReduce_EwD :: 
  "(nat\<times>edge) list \<Rightarrow>
    ((nat\<times>edge) \<Rightarrow> (node\<times>edge) list) \<Rightarrow>
    ((node\<times>edge) list list \<Rightarrow> (node\<times>edge list) list) \<Rightarrow>
    ((node\<times>edge list) \<Rightarrow> (edge\<times>degree\<times>degree) list) \<Rightarrow>
    (edge\<times>degree\<times>degree) list list"
  where "MapReduce_EwD input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

fun mapper_EwD :: "(nat\<times>edge) \<Rightarrow> (node\<times>edge) list" where 
"mapper_EwD (n,e) = [(fst e,form_edge (fst e) (snd e)),(snd e,form_edge (fst e) (snd e))]"

definition shuffler_EwD :: "((node\<times>edge) list) list \<Rightarrow>(node\<times>edge list) list"
  where "shuffler_EwD nes \<equiv>  Shuffle_single_inputlistlist nes"

theorem shuffler_EwD_theorem : "List.member (shuffler_EwD xss) (k,vs) \<Longrightarrow> (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "
  by (simp add: Shuffle_single_inputlistlist_theorem shuffler_EwD_def)

fun reducer_EwD_emit :: "node\<times>edge list \<Rightarrow>degree \<Rightarrow>(edge\<times>degree\<times>degree) list"
  where "reducer_EwD_emit (n,[]) d = []" |
        "reducer_EwD_emit (n,e#es) d = (if (n=fst e) then (e,d,0) else (e,0,d))#reducer_EwD_emit (n,es) d"

fun reducer_EwD :: "node\<times>edge list \<Rightarrow>(edge\<times>degree\<times>degree) list"
  where "reducer_EwD n_es = reducer_EwD_emit n_es (size(snd n_es))" 

lemma reducer_EwD_emit_degree: "(e, d1, d2) \<in> set (reducer_EwD_emit (n, es) d) \<Longrightarrow> (if (n = fst e) then d1 = d \<and> d2 = 0 else d1 = 0 \<and> d2 = d)"
  apply (induct es)
  apply simp+
  apply (case_tac "n = fst a")
  apply simp+
  by auto

theorem reducer_EwD_theorem:"List.member (reducer_EwD (n,es)) (e,d1,d2) \<Longrightarrow> (if (fst e = n) then d1 = size es \<and> d2 = 0 else d1 = 0 \<and> d2 = size es)"
  apply (simp add:member_def)
  apply (induct es)
  apply simp+
  apply (case_tac "n = fst a")
  apply auto
  by (drule reducer_EwD_emit_degree,simp)+

definition graph_edge :: "(nat\<times>edge) list" where
"graph_edge \<equiv> [(1,(1,2)),(2,(2,5)),(3,(3,5)),(4,(3,4)),
(5,(4,5))]"

definition result_EwD :: "(edge\<times>degree\<times>degree) list" where
"result_EwD \<equiv> concat(MapReduce_EwD graph_edge mapper_EwD shuffler_EwD reducer_EwD)"

definition MapReduce_EwDs :: 
  "(edge\<times>degree\<times>degree) list \<Rightarrow>
    ((edge\<times>degree\<times>degree) \<Rightarrow> (edge\<times>degree\<times>degree)) \<Rightarrow>
    ((edge\<times>degree\<times>degree) list  \<Rightarrow> (edge\<times>(degree\<times>degree) list) list) \<Rightarrow>
    ((edge\<times>(degree\<times>degree) list) \<Rightarrow> (edge\<times>degree\<times>degree)) \<Rightarrow>
    (edge\<times>degree\<times>degree) list "
  where "MapReduce_EwDs input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

definition "mapper_EwDs \<equiv> BNF_Composition.id_bnf"

definition shuffler_EwDs :: "(edge\<times>degree\<times>degree) list \<Rightarrow>(edge\<times>(degree\<times>degree) list) list "
  where "shuffler_EwDs eds \<equiv> Shuffle_single_inputalist eds"

theorem shuffler_EwDs_theorem : "List.member (shuffler_EwDs xs) (k,vs) \<Longrightarrow> (List.member xs (k,v)) = (List.member vs v) "
  by (metis Shuffle_single_inputalist_theorem shuffler_EwDs_def)

fun reducer_EwDs :: "edge\<times>(degree\<times>degree) list \<Rightarrow> (edge\<times>degree\<times>degree)"
  where "reducer_EwDs (e,d#ds) =(let de=hd(ds) in (if (fst d=0) then (e,fst de,snd d) else (e,fst d,snd de)))" 

definition result_EwDs :: "(edge\<times>degree\<times>degree) list" where
"result_EwDs \<equiv> MapReduce_EwDs result_EwD mapper_EwDs shuffler_EwDs reducer_EwDs"
value"result_EwDs"
end