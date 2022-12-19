theory Edges_with_Ntriangles
  imports Main SGraph Enumerating_Triangles 
begin

(*get number of triangles*)

definition MapReduce_GetNT :: 
  "(edge\<times>edge\<times>edge) list \<Rightarrow>
    ((edge\<times>edge\<times>edge) \<Rightarrow> (edge\<times>edge\<times>edge) list) \<Rightarrow>
    ((edge\<times>edge\<times>edge) list list \<Rightarrow> (edge\<times>(edge\<times>edge) list) list) \<Rightarrow>
    ((edge\<times>(edge\<times>edge) list) \<Rightarrow> (edge\<times>Ntriangles)) \<Rightarrow>
    (edge\<times>Ntriangles) list"
  where "MapReduce_GetNT input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

fun mapper_GetNT :: "(edge\<times>edge\<times>edge) \<Rightarrow> (edge\<times>edge\<times>edge) list" where
"mapper_GetNT (e1,e2,e3) = [(e1,e2,e3),(e2,e1,e3),(e3,e1,e2)]"

definition shuffler_GetNT :: "((edge\<times>edge\<times>edge) list) list \<Rightarrow>(edge\<times>(edge\<times>edge) list) list"
  where "shuffler_GetNT e_ees \<equiv> Shuffle_single_inputlistlist e_ees"

theorem shuffler_GetNT_theorem : "List.member (shuffler_GetNT xss) (k,vs) \<Longrightarrow> 
        (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "
  by (simp add: Shuffle_single_inputlistlist_theorem shuffler_GetNT_def)

fun reducer_GetNT :: "edge\<times>(edge\<times>edge) list \<Rightarrow> edge\<times>Ntriangles" where
"reducer_GetNT (e,ees) = (e,size ees)"

definition result_GetNT :: "(edge\<times>Ntriangles) list" where
"result_GetNT \<equiv> MapReduce_GetNT result_Triangles mapper_GetNT shuffler_GetNT reducer_GetNT"

(*Edges_with_Ntriangles*)

definition MapReduce_EwNtri :: 
  "'a list \<Rightarrow> 'b list \<Rightarrow>
    ('a \<Rightarrow> ('k1 \<times>'v11)) \<Rightarrow> ('b \<Rightarrow> ('k1 \<times>'v12)) \<Rightarrow>
    (('k1 \<times>'v11) list \<Rightarrow> ('k1 \<times>'v12) list \<Rightarrow>('k2 \<times> 'v2) list) \<Rightarrow>
    (('k2 \<times> 'v2) \<Rightarrow> ('k2 \<times> 'v2 )) \<Rightarrow>
    ('k2 \<times> 'v2 ) list"
  where "MapReduce_EwNtri input1 input2 Map1 Map2 Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map1 input1) (map Map2 input2))"

fun mapper_GetEdge :: "(nat\<times>edge) \<Rightarrow> (edge\<times>nat)" where 
"mapper_GetEdge (n,e) = (form_edge (fst e) (snd e),n)"
definition "mapper_GetNtri \<equiv> BNF_Composition.id_bnf"

primrec shuffler_EwNtri :: "(edge\<times>nat) list \<Rightarrow> (edge\<times>Ntriangles) list \<Rightarrow> (edge\<times>Ntriangles) list" 
  where "shuffler_EwNtri [] e_ns = []"|
        "shuffler_EwNtri (e # es) e_ns = (if ((map_of e_ns (fst e))= None) then ((fst e),0)#shuffler_EwNtri es e_ns 
                                      else ((fst e),the (map_of e_ns (fst e)))#shuffler_EwNtri es e_ns)" 

definition "reducer_EwNtri \<equiv> BNF_Composition.id_bnf" 

definition result_EwNtri :: "(edge\<times>Ntriangles) list" where
"result_EwNtri \<equiv> MapReduce_EwNtri graph_edge result_GetNT mapper_GetEdge mapper_GetNtri shuffler_EwNtri reducer_EwNtri"
value "result_EwNtri"
end