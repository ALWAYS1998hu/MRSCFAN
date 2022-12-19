theory Similarity
  imports Complex_Main HOL.Real Complex_Main SGraph HOL.NthRoot preliminary
begin

definition MapReduce_similarity :: 
  "(edge\<times>nat\<times>nat) list \<Rightarrow>(edge\<times>nat) list \<Rightarrow>
    ((edge\<times>nat\<times>nat) \<Rightarrow> (edge\<times>nat\<times>nat)) \<Rightarrow> ((edge\<times>nat) \<Rightarrow> (edge\<times>nat)) \<Rightarrow>
    ((edge\<times>nat\<times>nat) list \<Rightarrow> (edge\<times>nat) list \<Rightarrow>(edge\<times>(nat\<times>nat) list\<times>nat list) list) \<Rightarrow>
    ((edge\<times>(nat\<times>nat) list\<times>nat list) \<Rightarrow> (edge\<times>real)) \<Rightarrow>
    (edge\<times>real) list"
  where "MapReduce_similarity input1 input2 Map1 Map2 Shuffle Reduce \<equiv> 
         map Reduce (Shuffle (map Map1 input1) (map Map2 input2))"

(***************************mapper***************************)

definition "mapper_similarity_inputEwDs \<equiv> BNF_Composition.id_bnf"
definition "mapper_similarity_inputEwNtri \<equiv> BNF_Composition.id_bnf"

(***************************shuffer***************************)

fun shuffler_Similarity :: "(edge\<times>nat\<times>nat) list \<Rightarrow> (edge\<times>nat) list \<Rightarrow> (edge\<times>(nat\<times>nat) list\<times>nat list) list" 
  where "shuffler_Similarity enns ens = Shuffle_multi enns ens" 

theorem shuffler_Similarity_theorem:"List.member (shuffler_Similarity xs1 xs2) (k,v1s,v2s) \<Longrightarrow> 
        List.member v1s v1 = List.member xs1 (k,v1) \<and> List.member v2s v2 = List.member xs2 (k,v2)"
  apply (rule Shuffle_multi_theorem)
  by auto

(***************************reducer***************************)

fun reduce_Similarity :: "(edge\<times>(nat\<times>nat) list\<times>nat list)\<Rightarrow> (edge\<times>real)" 
  where "reduce_Similarity (e,Ds,triN) = (e,(hd triN)+2 / (sqrt (fst (hd Ds)+1)*(snd (hd Ds)+1)))"

theorem reduce_Similarity_theorem: "reduce_Similarity (e,Ds,triN) = (e,(hd triN)+2 / (sqrt (fst (hd Ds)+1)*(snd (hd Ds)+1)))"
  by auto

(***************************result***************************)

definition result_Similarity :: "(edge\<times>real) list" 
  where "result_Similarity\<equiv>MapReduce_similarity result_EwDs result_EwNtri mapper_similarity_inputEwDs 
                           mapper_similarity_inputEwNtri shuffler_Similarity reduce_Similarity"

end