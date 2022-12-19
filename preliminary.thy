theory preliminary
imports Main Edges_with_Degrees Enumerating_Triangles Edges_with_Ntriangles
begin

definition graph_edge :: "(nat\<times>edge) list" where
"graph_edge \<equiv> [(1,(1,2)),(2,(2,7)),(3,(3,4)),(4,(3,7)),
(5,(4,6)),(6,(4,7)),(7,(5,6)),(8,(5,7)),(9,(6,7))]"

(*Edges_with_Degrees*)
definition result_EwD :: "(edge\<times>degree\<times>degree) list" where
"result_EwD \<equiv> concat(MapReduce_EwD graph_edge mapper_EwD shuffler_EwD reducer_EwD)"
definition result_EwDs :: "(edge\<times>degree\<times>degree) list" where
"result_EwDs \<equiv> MapReduce_EwDs result_EwD mapper_EwDs shuffler_EwDs reducer_EwDs"
value "result_EwDs"

(*Edges_with_Ntriangles*)
definition result_Open_Triads :: "(edge\<times>edge\<times>edge) list" where
"result_Open_Triads \<equiv> concat(MapReduce_EOT result_EwDs mapper_EOT shuffler_EOT reducer_EOT)"
definition result_Form_Triangles :: "(edge\<times>edge\<times>edge\<times>edge) list" where
"result_Form_Triangles \<equiv> MapReduce_FT result_Open_Triads result_EwDs mapper_needed_edge mapper_edge shuffler_FT reducer_FT"
definition result_Triangles :: "(edge\<times>edge\<times>edge) list" where
"result_Triangles \<equiv> map snd result_Form_Triangles"

definition result_GetNT :: "(edge\<times>Ntriangles) list" where
"result_GetNT \<equiv> MapReduce_GetNT result_Triangles mapper_GetNT shuffler_GetNT reducer_GetNT"
definition result_EwNtri :: "(edge\<times>Ntriangles) list" where
"result_EwNtri \<equiv> MapReduce_EwNtri graph_edge result_GetNT mapper_GetEdge mapper_GetNtri shuffler_EwNtri reducer_EwNtri"
value "result_EwNtri"

(*value definition*)
definition \<epsilon> :: "real" where
"\<epsilon> \<equiv> 0.7"
definition \<mu> :: "nat" where
"\<mu> \<equiv> 3"

end