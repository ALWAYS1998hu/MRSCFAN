theory Enumerating_Triangles
  imports Main SGraph Edges_with_Degrees Shuffle
begin

(*enumerate open triads*)
definition MapReduce_EOT :: 
  "(edge\<times>degree\<times>degree) list \<Rightarrow>
    ((edge\<times>degree\<times>degree) \<Rightarrow> (node\<times>edge)) \<Rightarrow>
    ((node\<times>edge) list  \<Rightarrow> (node\<times>edge list) list) \<Rightarrow>
    ((node\<times>edge list) \<Rightarrow> (edge\<times>edge\<times>edge) list) \<Rightarrow>
    (edge\<times>edge\<times>edge) list list"
  where "MapReduce_EOT input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

fun mapper_EOT ::"(edge\<times>degree\<times>degree) \<Rightarrow> (node\<times>edge)" where
"mapper_EOT (e,d_f,d_s) = (if (d_f<d_s) then (fst e,e) 
                           else (if (d_s<d_f) then (snd e,e) 
                                 else (Node_Comparison e,e)))"

definition shuffler_EOT :: "(node\<times>edge) list \<Rightarrow>(node\<times>edge list) list"
  where "shuffler_EOT nes \<equiv>  Shuffle_single_inputalist nes"

theorem shuffler_EOT_theorem : "List.member (shuffler_EOT xs) (k,vs) \<Longrightarrow> (List.member xs (k,v)) = (List.member vs v) "
  by (metis Shuffle_single_inputalist_theorem shuffler_EOT_def)

fun Edge_for_Triad :: "edge \<Rightarrow> edge \<Rightarrow> (edge\<times>edge\<times>edge)" where
"Edge_for_Triad e1 e2 = (if (fst e1=fst e2) then (form_edge (snd e1) (snd e2),e1,e2) 
                         else if (fst e1=snd e2) then (form_edge(snd e1) (fst e2),e1,e2) 
                              else if (snd e1=snd e2) then (form_edge(fst e1) (fst e2),e1,e2) 
                                   else (form_edge(fst e1) (snd e2),e1,e2))"

primrec Get_one_Pairs :: "'a \<Rightarrow> 'a list \<Rightarrow> ('a\<times>'a) list" 
  where "Get_one_Pairs a [] = []"|
        "Get_one_Pairs a (aa#as) = (a,aa) # Get_one_Pairs a as"

fun Get_Pairs :: "'a list \<Rightarrow> ('a\<times>'a) list" 
  where "Get_Pairs [] = []"|
        "Get_Pairs [a] = []"|
        "Get_Pairs (a#as) = (Get_one_Pairs a as) @ (Get_Pairs as)"
value"Get_Pairs [1::nat,2,3,4,5,6,7]"

primrec Get_Open_Triads :: "(edge\<times>edge) list \<Rightarrow> (edge\<times>edge\<times>edge) list"
  where "Get_Open_Triads [] = []"|
        "Get_Open_Triads (ee#ees) = (Edge_for_Triad (fst ee) (snd ee)) # Get_Open_Triads ees"

fun reducer_EOT :: "(node\<times>edge list) \<Rightarrow> (edge\<times>edge\<times>edge) list" where
"reducer_EOT (n,es) = Get_Open_Triads (Get_Pairs es)"

definition result_Open_Triads :: "(edge\<times>edge\<times>edge) list" where
"result_Open_Triads \<equiv> concat(MapReduce_EOT result_EwDs mapper_EOT shuffler_EOT reducer_EOT)"

(*form triangles*)

definition MapReduce_FT :: 
  "(edge\<times>edge\<times>edge) list \<Rightarrow> (edge\<times>degree\<times>degree) list \<Rightarrow>
    ((edge\<times>edge\<times>edge) \<Rightarrow> (edge\<times>edge\<times>edge)) \<Rightarrow> ((edge\<times>degree\<times>degree) \<Rightarrow> (edge\<times>edge)) \<Rightarrow>
    ((edge\<times>edge\<times>edge) list \<Rightarrow> (edge\<times>edge) list \<Rightarrow>(edge\<times>(edge\<times>edge) list\<times>edge list) list) \<Rightarrow>
    ((edge\<times>(edge\<times>edge) list\<times>edge list) \<Rightarrow> (edge\<times>edge\<times>edge\<times>edge)) \<Rightarrow>
    (edge\<times>edge\<times>edge\<times>edge) list"
  where "MapReduce_FT input1 input2 Map1 Map2 Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map1 input1) (map Map2 input2))"

definition "mapper_needed_edge \<equiv> BNF_Composition.id_bnf"
fun mapper_edge :: "(edge\<times>degree\<times>degree) \<Rightarrow> (edge\<times>edge)" where
"mapper_edge (e,d_f,d_s) = (form_edge (fst e) (snd e),e)"

fun shuffler_FT :: "(edge\<times>edge\<times>edge) list \<Rightarrow> (edge\<times>edge) list \<Rightarrow> (edge\<times>(edge\<times>edge) list\<times>edge list) list" 
  where "shuffler_FT e_ees e_es = Shuffle_multi e_ees e_es" 

theorem shuffler_FT_theorem:"List.member (shuffler_FT xs1 xs2) (k,v1s,v2s) \<Longrightarrow> 
        List.member v1s v1 = List.member xs1 (k,v1) \<and> List.member v2s v2 = List.member xs2 (k,v2)"
  apply (rule Shuffle_multi_theorem)
  by auto

fun reducer_FT :: "(edge\<times>(edge\<times>edge) list\<times>edge list) \<Rightarrow> (edge\<times>edge\<times>edge\<times>edge)"
  where "reducer_FT (e_need,ees,es) = (e_need,fst (hd ees),snd (hd ees),(hd es))"

definition result_Form_Triangles :: "(edge\<times>edge\<times>edge\<times>edge) list" where
"result_Form_Triangles \<equiv> MapReduce_FT result_Open_Triads result_EwDs mapper_needed_edge mapper_edge shuffler_FT reducer_FT"

definition result_Triangles :: "(edge\<times>edge\<times>edge) list" where
"result_Triangles \<equiv> map snd result_Form_Triangles"

end