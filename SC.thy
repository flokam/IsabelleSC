theory SC
  imports ModTrans
begin

datatype action = get | move | eval |put
typedecl actor
type_synonym identity = string
consts Actor :: "string => actor"
type_synonym policy = "((actor => bool) * action set)"

type_synonym data = string
  (* Inspired by Myers DLM mode: first is the owner of a data item, second is the
     set of all actors that may access the data item *)
type_synonym dlm = "identity * identity set"

(* type of functions that preserves the security labeling *)    
typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
proof (auto)
  show "\<exists>x::(identity \<times> identity set) \<times> string \<Rightarrow> (identity \<times> identity set) \<times> string.
       \<forall>(a::identity) (b::identity set) ba::string. (a, b) = fst (x ((a, b), ba))"
  by (rule_tac x = id in exI, simp)
qed

datatype location = Location nat

typedef ledger = "{ ld :: dlm \<times> data \<Rightarrow> location set. \<forall> d. (\<forall> l. ld (l, d) = {}) \<or>
(\<exists>! l. ld (l, d) \<noteq> {})}"
  by auto

(* functions in a smart contract can be such that they change the labelled data
   or not *)
datatype sc_fun = Nochange "label_fun" | Change "dlm * data \<Rightarrow> dlm * data"

type_synonym transaction_record = "sc_fun list"

datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                         "actor \<Rightarrow> (string set * string set)"  "location \<Rightarrow> string"
                         "ledger" "transaction_record"
datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph ,location] \<Rightarrow> policy set" 
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c l ld tr) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity set)"
where  "agra(Lgraph g a c l ld tr) = a"
primrec cgra :: "igraph \<Rightarrow> (actor \<Rightarrow> string set * string set)"
where  "cgra(Lgraph g a c l ld tr) = c"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string)"
  where  "lgra(Lgraph g a c l ld tr) = l"
primrec ledgra :: "igraph \<Rightarrow> ledger"
  where  "ledgra(Lgraph g a c l ld tr) = ld"
primrec trec :: "igraph \<Rightarrow> transaction_record"
  where "trec(Lgraph g a c l ld tr) = tr"

definition ledgra_upd :: "[ledger, dlm \<times> data, location set] \<Rightarrow> ledger" ("_ _ := _" 50)
  where
 "ledgra_upd ld dl L == Abs_ledger((Rep_ledger ld)(dl := L))"

definition ledgra_at :: "[ledger, dlm \<times> data] \<Rightarrow> location set" ("_ \<nabla> _" 50)
  where  "l \<nabla> dl \<equiv> (Rep_ledger l) dl"

definition nodes :: "igraph \<Rightarrow> location set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> (agra g y)}"

primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, actor ] \<Rightarrow> string set * string set"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string"
where "lspace (Infrastructure g d) = lgra g"
definition credentials :: "string set * string set \<Rightarrow> string set"
  where  "credentials lxl \<equiv> (fst lxl)"
definition has :: "[igraph, actor * string] \<Rightarrow> bool"
  where "has G ac \<equiv> snd ac \<in> credentials(cgra G (fst ac))"
definition roles :: "string set * string set \<Rightarrow> string set"
  where  "roles lxl \<equiv> (snd lxl)"
definition role :: "[igraph, actor * string] \<Rightarrow> bool"
  where "role G ac \<equiv> snd ac \<in> roles(cgra G (fst ac))"

definition isin :: "[igraph,location, string] \<Rightarrow> bool" 
  where "isin G l s \<equiv> s = (lgra G l)"

definition owner :: "dlm * data \<Rightarrow> identity" where "owner d \<equiv> fst(fst d)"
    
definition owns :: "[igraph, location, identity, dlm * data] \<Rightarrow> bool"    
  where "owns G l a d \<equiv> owner d = a"
    
definition readers :: "dlm * data \<Rightarrow> identity set"
  where "readers d \<equiv> snd (fst d)"

definition has_access :: "[igraph, location, identity, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"
  
definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))(cgra g)(lgra g)(ledgra g)(trec g)"

definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" ("_ \<Updown> _" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 

datatype inter_trans = Intra "infrastructure" "sc_fun" 
                     | Inter "infrastructure" "infrastructure" "sc_fun"

datatype ibc_protocol = Protocol "inter_trans list set"

datatype blockchainset = Infs "ibc_protocol" "infrastructure list"

primrec the_ibc :: "blockchainset \<Rightarrow> ibc_protocol"
  where
"the_ibc (Infs ibc Il) = ibc"

primrec the_prot :: "ibc_protocol \<Rightarrow> inter_trans list set"
  where 
"the_prot (Protocol evs) = evs"


primrec the_Il :: "blockchainset \<Rightarrow> infrastructure list"
  where
"the_Il (Infs ibc Il) = Il"

primrec replace :: "infrastructure \<Rightarrow> infrastructure \<Rightarrow> blockchainset \<Rightarrow> blockchainset"
  where
replace_def: "replace I' I (Infs ibc Il) = Infs ibc (I' # (remove1 I Il))"

primrec inbc :: "infrastructure \<Rightarrow> blockchainset \<Rightarrow> bool"
  where
inbc_def: "inbc I (Infs ibc Il) = (I \<in> (set Il))"

definition insertp :: "inter_trans list \<Rightarrow> blockchainset \<Rightarrow> blockchainset"
  where
"insertp l bc \<equiv> Infs (Protocol(insert l (the_prot (the_ibc bc))))(the_Il bc)" 


lemma move_graph_eq: "move_graph_a a l l g = g"  
proof (simp add: move_graph_a_def, case_tac g, force)
qed

inductive state_transition_in :: "[blockchainset, blockchainset] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move; inbc I Il;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I);
         Il' = replace I' I Il   \<rbrakk> \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'" 
| get_data : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> 
        enables I l (Actor a) get \<Longrightarrow> 
        (ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow> l' \<in> L  \<Longrightarrow>  a \<in> as \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                           ((ledgra G)((a', as), n) := (L \<union> {l}))(trec g))
                   (delta I) \<Longrightarrow> inbc I Il \<Longrightarrow> Il' = replace I' I Il
         \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'"
| process_local : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l (Actor a) eval \<Longrightarrow> 
        (ledgra G \<nabla> ((a', as), n)) = L \<Longrightarrow>
        a \<in> as  \<or> a = a'\<Longrightarrow> 
        (newtrec :: transaction_record) = ((Nochange (f :: label_fun))#(trec G)) \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                                 ((ledgra G ((a', as), n) := {}
                                    (f :: label_fun) \<Updown> ((a', as), n) := L))
                           newtrec)
                   (delta I) \<Longrightarrow> inbc I Il \<Longrightarrow> Il' = replace I' I Il
         \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'"  
| process_trans_local: "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l (Actor a) eval \<Longrightarrow> 
        (ledgra G \<nabla> ((a, as), n)) = L \<Longrightarrow>
        (newtrec :: transaction_record) = ((Change (f :: (dlm * data \<Rightarrow> dlm * data)))#(trec G)) \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                                 ((ledgra G ((a, as), n) := {}
                                    f ((a, as), n) := L))
                           newtrec)
                   (delta I) \<Longrightarrow> inbc I Il \<Longrightarrow> Il' = replace I' I Il
         \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'"  
| process_trans_global: "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        H = graphI J \<Longrightarrow> a' @\<^bsub>H\<^esub> l' \<Longrightarrow>
        enables I l (Actor a) eval \<Longrightarrow> enables J l' (Actor a') eval \<Longrightarrow> 
        (ledgra G \<nabla> ((a, as), n)) = L \<Longrightarrow>
        t \<in> (the_prot(the_ibc Il)) \<Longrightarrow> 
        (newtrec :: transaction_record) = ((Change (f :: (dlm * data \<Rightarrow> dlm * data)))#(trec G)) \<Longrightarrow> 
        (newtrec' :: transaction_record) = ((Change (f :: (dlm * data \<Rightarrow> dlm * data)))#(trec H)) \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                                 ((ledgra G ((a, as), n) := {}))
                           newtrec)
                   (delta I) \<Longrightarrow> 
        J' = Infrastructure 
                   (Lgraph (gra H)(agra H)(cgra H)(lgra H)
                                 (((ledgra H ((a, as), n) := {})
                                    ((a', as), n) := L))
                           newtrec')
                   (delta J) \<Longrightarrow> 
              inbc I Il \<Longrightarrow> Il' = replace I' I Il \<Longrightarrow> inbc J Il' \<Longrightarrow> Il'' = replace J' J Il'
              \<Longrightarrow> Il''' = insertp ((Inter I J (Change f))# t) Il'' 
         \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'''"  

(* Can't have del_data or at least not the unrestricted form *)
(* the "ledgra G \<nabla> ((a, as),n) = {}" is the decisive pre-condition *)
| put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> enables I l (Actor a) put \<Longrightarrow>
        ledgra G \<nabla> ((a, as),n) = {} \<Longrightarrow>
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                          (ledgra G ((a, as),n) := {l})(trec g))
                   (delta I) \<Longrightarrow> inbc I Il \<Longrightarrow> Il' = replace I' I Il
          \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'"


(* type_synonym infrastructure_list = "infrastructure list"  *)

instantiation blockchainset :: state
begin

definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: blockchainset))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end

definition global_consistency
  where 
 "global_consistency Il \<equiv> (\<forall> I I'. inbc I Il \<longrightarrow> inbc I' Il \<longrightarrow>
       (\<forall> d. (\<forall> l. (ledgra (graphI I) \<nabla> (l, d) = {})  \<or> 
             (\<exists>! l. (ledgra (graphI I) \<nabla> (l, d)) \<noteq> {}) \<and> 
              ((ledgra (graphI I') \<nabla> (l, d)) = (ledgra (graphI I) \<nabla> (l, d))))))"

lemma consistency_preservation: 
   "global_consistency Il \<Longrightarrow> Il \<rightarrow>\<^sub>n Il' \<Longrightarrow> global_consistency Il'" 
  oops

end