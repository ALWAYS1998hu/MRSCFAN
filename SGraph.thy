theory SGraph
  imports Main HOL.Real 
begin

(*typedecl node *)
type_synonym node ="nat"
type_synonym similarity ="real"
type_synonym iscore ="bool"
type_synonym fnode ="node*iscore"
type_synonym edge = "(node * node)"
type_synonym graph = "edge list"
type_synonym degree = "nat"
type_synonym Ntriangles = "nat"

fun form_edge :: "node \<Rightarrow> node \<Rightarrow> edge" where
"form_edge n1 n2 = (if (n1<n2) then (n1,n2) else (n2,n1))"

fun Node_Comparison ::"edge \<Rightarrow> node" where
"Node_Comparison e = min (fst e) (snd e)"

primrec app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" 
where "app Nil ys = ys" |
"app (Cons x xs) ys =Cons x (app xs ys)"

theorem app_size: "size (app xs1 xs2) = size xs1 + size xs2"
  apply (induct xs1)
  apply auto
  done

end