theory SC
  imports ModTrans
begin

datatype action = scan | eval |submit
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

datatype node = Node nat

(* In this efficient modeling of ledger (cf older versions), we have a unique
(dlm * node set) for each data -- if it is defined --, that is, a data has a unique label and
one set of locations where it occurs. 
There is redundancy in this representation compared to the above one:
the fact that there is no label assigned to a data item may be
recorded as lg(d) = None or lg(d) = (l,{}) for any label l.
I don't see why this should cause confusion. 
*)
type_synonym ledger = \<open>data \<Rightarrow> (dlm \<times> node set)option\<close>

lemma ledger_def_prop: "\<forall> lg:: ledger. \<forall> d:: data.
     lg d = None | (\<exists>! lL. lg d = Some(lL))"
  by force 

lemma prod_exu: \<open>\<forall> p:: ('a * 'b). \<exists>! a. \<exists>! b. p = (a,b)\<close>
  by auto

lemma ledger_def_prop'[rule_format]: "\<forall> lg:: ledger. \<forall> d:: data.
     lg d = None | (\<exists>! l. (\<exists>! L. lg d = Some(l, L)))"
  apply (rule allI)+
  apply (case_tac "lg d")
   apply (erule disjI1)
  apply(rule disjI2)
  by (auto simp: ledger_def_prop prod_exu)
  
thm dom_def inj_on_def
typedef label_fun' = \<open>{f:: data \<Rightarrow> data. inj f}\<close>
by auto

typedef label_funl = \<open>{fl:: ((data \<Rightarrow> data) \<times> ledger). (\<forall> x. (snd fl)((fst fl) x) = snd fl x)}\<close>
by auto

(*  the data function of the label preserving ledger function*)
definition dfunl :: "label_funl \<Rightarrow> (data \<Rightarrow> data)"
  where "dfunl fl = (fst (Rep_label_funl fl))"

definition lgfunl :: "label_funl \<Rightarrow> ledger"
  where "lgfunl fl = (snd (Rep_label_funl fl))"

(* apply a label preserving function to a ledger to change the ledger*)
definition label_funl_ledger_app :: "label_funl \<Rightarrow> ledger \<Rightarrow> ledger" ("_ \<lozenge> _" 50)
  where "f \<lozenge> l \<equiv> l \<circ> (dfunl f)" 

lemma funl_appl: "x \<in> dom(lgfunl fl) \<Longrightarrow> (lgfunl fl x) = lgfunl fl ((dfunl fl) x)"
  using Rep_label_funl dfunl_def lgfunl_def by auto

(* functions in a smart contract can be such that they change the labelled data
   or not *)
datatype sc_fun = Nochange "label_funl" | Change "dlm * data \<Rightarrow> dlm * data" | 
                  Send "identity * identity * dlm * data" | 
                  Receive "identity * identity * dlm * data" 

type_synonym transaction_record = "sc_fun list"

datatype igraph = Lgraph "(node * node)set" "node \<Rightarrow> identity set"
                         "actor \<Rightarrow> (string set * string set)"  "node \<Rightarrow> string"
                         "ledger" "transaction_record"
datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph ,node] \<Rightarrow> policy set" 
primrec loc :: "node \<Rightarrow> nat"
where  "loc(Node n) = n"
primrec gra :: "igraph \<Rightarrow> (node * node)set"
where  "gra(Lgraph g a c l ld tr) = g"
primrec agra :: "igraph \<Rightarrow> (node \<Rightarrow> identity set)"
where  "agra(Lgraph g a c l ld tr) = a"
primrec cgra :: "igraph \<Rightarrow> (actor \<Rightarrow> string set * string set)"
where  "cgra(Lgraph g a c l ld tr) = c"
primrec lgra :: "igraph \<Rightarrow> (node \<Rightarrow> string)"
  where  "lgra(Lgraph g a c l ld tr) = l"
primrec ledgra :: "igraph \<Rightarrow> ledger"
  where  "ledgra(Lgraph g a c l ld tr) = ld"
primrec trec :: "igraph \<Rightarrow> transaction_record"
  where "trec(Lgraph g a c l ld tr) = tr"

definition nodes :: "igraph \<Rightarrow> node set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> (agra g y)}"

primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, node] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, actor ] \<Rightarrow> string set * string set"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, node ] \<Rightarrow> string"
where "lspace (Infrastructure g d) = lgra g"
definition credentials :: "string set * string set \<Rightarrow> string set"
  where  "credentials lxl \<equiv> (fst lxl)"
definition has :: "[igraph, actor * string] \<Rightarrow> bool"
  where "has G ac \<equiv> snd ac \<in> credentials(cgra G (fst ac))"
definition roles :: "string set * string set \<Rightarrow> string set"
  where  "roles lxl \<equiv> (snd lxl)"
definition role :: "[igraph, actor * string] \<Rightarrow> bool"
  where "role G ac \<equiv> snd ac \<in> roles(cgra G (fst ac))"

definition isin :: "[igraph,node, string] \<Rightarrow> bool" 
  where "isin G l s \<equiv> s = (lgra G l)"

definition owner :: "dlm * data \<Rightarrow> identity" where "owner d \<equiv> fst(fst d)"
    
definition owns :: "[igraph, node, identity, dlm * data] \<Rightarrow> bool"    
  where "owns G l a d \<equiv> owner d = a"
    
definition readers :: "dlm * data \<Rightarrow> identity set"
  where "readers d \<equiv> snd (fst d)"

definition has_access :: "[igraph, node, identity, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"
  
definition atI :: "[identity, igraph, node] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

definition enables :: "[infrastructure, node, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

(*
datatype inter_trans = Intra "infrastructure" "sc_fun" 
                     | Inter "infrastructure" "infrastructure" "sc_fun"

datatype ibc_protocol = Protocol "inter_trans list set"
*)
datatype ibc_protocol = Protocol "sc_fun list set"

datatype blockchainset = Infs "ibc_protocol" "infrastructure list" "infrastructure"

primrec the_ibc :: "blockchainset \<Rightarrow> ibc_protocol"
  where
"the_ibc (Infs ibc Il rl) = ibc"

(* primrec the_prot :: "ibc_protocol \<Rightarrow> inter_trans list set" *)
primrec the_prot :: "ibc_protocol \<Rightarrow> sc_fun list set"
  where 
"the_prot (Protocol evs) = evs"

primrec the_Il :: "blockchainset \<Rightarrow> infrastructure list"
  where
"the_Il (Infs ibc Il rl) = Il"

definition upd_ld 
  where "upd_ld d lN I = 
(Infrastructure (Lgraph (gra (graphI I))(agra (graphI I))(cgra (graphI I))(lgra (graphI I))
                          ((ledgra (graphI I))(d := Some lN))(trec (graphI I)))
                   (delta I))"

primrec upd_Il :: "data \<Rightarrow> dlm * node set \<Rightarrow> infrastructure list \<Rightarrow> infrastructure list"
  where 
  upd_Il_start: "upd_Il d lN [] =  []" |
  upd_Il_step: "upd_Il d lN (I # Il) = (upd_ld d lN I) # (upd_Il d lN Il)"

(* definition trcs :: "blockchainset \<Rightarrow> inter_trans list set" *)
definition trcs :: "blockchainset \<Rightarrow> sc_fun list set"
  where 
"trcs bc = the_prot(the_ibc bc)" 

primrec relayer :: "blockchainset \<Rightarrow> infrastructure"
  where
"relayer (Infs ibc Il rl) = rl"

definition bc_upd 
  where \<open>bc_upd d lN bcs = Infs (the_ibc bcs)(upd_Il d lN (the_Il bcs))
                                             (upd_ld d lN (relayer bcs))\<close>

primrec replace :: "infrastructure \<Rightarrow> infrastructure \<Rightarrow> blockchainset \<Rightarrow> blockchainset"
  where
replace_def: "replace I' I (Infs ibc Il rl) = Infs ibc (I' # (remove1 I Il)) rl"

primrec inbc :: "infrastructure \<Rightarrow> blockchainset \<Rightarrow> bool"
  where
inbc_def: "inbc I (Infs ibc Il rl) = (I \<in> (set Il))"

(* definition insertp :: "inter_trans list \<Rightarrow> blockchainset \<Rightarrow> blockchainset" *)
definition insertp :: "sc_fun list \<Rightarrow> blockchainset \<Rightarrow> blockchainset"
  where
"insertp l bc \<equiv> Infs (Protocol(insert l (the_prot (the_ibc bc))))(the_Il bc)(relayer bc)"

primrec replrel :: "infrastructure \<Rightarrow> blockchainset \<Rightarrow> blockchainset"
  where
replrel_def: "replrel rl' (Infs ibc Il rl) = Infs ibc Il rl'"

definition relrole
  where "relrole I a = role (graphI I) (a, ''relayer'')"

(* abstract constant to express consensus about the successor state*)
consts Consensus :: "actor set \<Rightarrow> blockchainset"

definition global_consistency
  where 
 "global_consistency Il \<equiv> (\<forall> I I'. inbc I Il \<longrightarrow> inbc I' Il \<longrightarrow> 
       (\<forall> d. (ledgra (graphI I') d) = (ledgra (graphI I) d)))"


lemma bc_upd_inv: \<open>global_consistency Il \<Longrightarrow> global_consistency (bc_upd d lN Il)\<close>
  unfolding global_consistency_def bc_upd_def upd_Il_def
  sorry


inductive state_transition_in :: "[blockchainset, blockchainset] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
 scan : "inbc I Il \<Longrightarrow> G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> n \<Longrightarrow> n \<in> nodes G \<Longrightarrow> 
         R = graphI (relayer Il) \<Longrightarrow> r @\<^bsub>R\<^esub> n' \<Longrightarrow> n' \<in> nodes R \<Longrightarrow> 
         relrole (relayer Il) (Actor r) \<Longrightarrow> enables I n (Actor r) scan \<Longrightarrow> 
         ledgra G d = Some ((a, as), N) \<Longrightarrow> r \<in> as \<Longrightarrow> 
         R' = Infrastructure 
                   (Lgraph (gra R)(agra R)(cgra R)(lgra R)
                           ((ledgra R)(d := Some((a', as),N)))
                           ((Send(a,b,(a,as), d)) # (trec R)))
                   (delta (relayer Il)) \<Longrightarrow>  
         l \<in> trcs Il \<Longrightarrow> Consensus (actors G) = Il' \<Longrightarrow>
         Il' = insertp ((Send(a,b,(a,as), d)) # l) (replrel R' Il)
         \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'"
| submit : "G = graphI I \<Longrightarrow> inbc I Il \<Longrightarrow> a @\<^bsub>G\<^esub> n \<Longrightarrow> n \<in> nodes G \<Longrightarrow> 
            ledgra G d = Some ((a, as), N) \<Longrightarrow> 
            H = graphI J \<Longrightarrow> inbc J Il \<Longrightarrow> b @\<^bsub>H\<^esub> n' \<Longrightarrow> n' \<in> nodes H \<Longrightarrow> 
            ledgra H d = Some ((a, as), N) \<Longrightarrow> 
            R = graphI (relayer Il) \<Longrightarrow> r @\<^bsub>R\<^esub> n'' \<Longrightarrow> n'' \<in> nodes R \<Longrightarrow> 
            relrole (relayer Il) (Actor r) \<Longrightarrow> enables J n' (Actor r) submit \<Longrightarrow>
           r \<in> as \<Longrightarrow> 
            R' = Infrastructure 
                   (Lgraph (gra R)(agra R)(cgra R)(lgra R)
                           ((ledgra R)(d := Some((b, bs),N)))
                           ((Receive(a,b,(a,as), d)) # (trec R)))
                  (delta (relayer Il))  \<Longrightarrow>
            Il' = insertp (Receive(a,b,(a,as),d)# l) (replrel R' (bc_upd d ((b,bs), N) Il)) \<Longrightarrow>
            Consensus (actors H) = Il 
            \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'"

instantiation blockchainset :: state
begin

definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: blockchainset))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end


lemma cons_lemma: "global_consistency Il \<Longrightarrow>
R = graphI (relayer Il) \<Longrightarrow>
R' = Infrastructure 
                   (Lgraph (gra R)(agra R)(cgra R)(lgra R)
                           ((ledgra R)(d := Some((a', as),N)))
                           ((Send(a,b,(a,as), d)) # (trec R)))
                   (delta I) \<Longrightarrow>
Il' = insertp ((Send(a,b,(a,as), d)) # l) (replrel R' Il)
\<Longrightarrow> global_consistency Il'"
  by (metis (no_types, hide_lams) blockchainset.exhaust global_consistency_def inbc.inbc_def insertp_def replrel.replrel_def the_Il.simps)

lemma consistency_preservation: 
   "global_consistency Il \<Longrightarrow> (Il \<rightarrow>\<^sub>n Il') \<Longrightarrow> global_consistency Il'" 
proof (erule state_transition_in.cases, simp_all)
  show \<open>\<And>I Ila G a n R r n' d as N R' a' b l actors Il'a.
       global_consistency Ila \<Longrightarrow>
       Il = Ila \<Longrightarrow>
       Il' =
       insertp (Send (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
              (Send (a, b, (a, as), d) # trec (graphI (relayer Ila))))
            (delta (relayer Ila)))
          Ila) \<Longrightarrow>
       inbc I Ila \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> n \<Longrightarrow>
       n \<in> nodes (graphI I) \<Longrightarrow>
       R = graphI (relayer Ila) \<Longrightarrow>
       r @\<^bsub>graphI (relayer Ila)\<^esub> n' \<Longrightarrow>
       n' \<in> nodes (graphI (relayer Ila)) \<Longrightarrow>
       relrole (relayer Ila) (Actor r) \<Longrightarrow>
       enables I n (Actor r) scan \<Longrightarrow>
       ledgra (graphI I) d = Some ((a, as), N) \<Longrightarrow>
       r \<in> as \<Longrightarrow>
       R' =
       Infrastructure
        (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila)))
          (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
          (Send (a, b, (a, as), d) # trec (graphI (relayer Ila))))
        (delta (relayer Ila)) \<Longrightarrow>
       l \<in> trcs Ila \<Longrightarrow>
       Consensus (actors (graphI I)) =
       insertp (Send (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
              (Send (a, b, (a, as), d) # trec (graphI (relayer Ila))))
            (delta (relayer Ila)))
          Ila) \<Longrightarrow>
       Il'a =
       insertp (Send (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
              (Send (a, b, (a, as), d) # trec (graphI (relayer Ila))))
            (delta (relayer Ila)))
          Ila) \<Longrightarrow>
       global_consistency
        (insertp (Send (a, b, (a, as), d) # l)
          (replrel
            (Infrastructure
              (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
                (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
                (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
                (Send (a, b, (a, as), d) # trec (graphI (relayer Ila))))
              (delta (relayer Ila)))
            Ila))\<close>
    by (simp add: cons_lemma)
next show \<open>\<And>G I Ila a n d as N H J b n' R r n'' R' bs Il'a l actors.
       global_consistency Ila \<Longrightarrow>
       Il = Ila \<Longrightarrow>
       Il' =
       insertp (Receive (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
              (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila))))
            (delta (relayer Ila)))
          (bc_upd d ((b, bs), N) Ila)) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       inbc I Ila \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> n \<Longrightarrow>
       n \<in> nodes (graphI I) \<Longrightarrow>
       ledgra (graphI I) d = Some ((a, as), N) \<Longrightarrow>
       H = graphI J \<Longrightarrow>
       inbc J Ila \<Longrightarrow>
       b @\<^bsub>graphI J\<^esub> n' \<Longrightarrow>
       n' \<in> nodes (graphI J) \<Longrightarrow>
       ledgra (graphI J) d = Some ((a, as), N) \<Longrightarrow>
       R = graphI (relayer Ila) \<Longrightarrow>
       r @\<^bsub>graphI (relayer Ila)\<^esub> n'' \<Longrightarrow>
       n'' \<in> nodes (graphI (relayer Ila)) \<Longrightarrow>
       relrole (relayer Ila) (Actor r) \<Longrightarrow>
       enables J n' (Actor r) submit \<Longrightarrow>
       r \<in> as \<Longrightarrow>
       R' =
       Infrastructure
        (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila)))
          (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
          (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila))))
        (delta (relayer Ila)) \<Longrightarrow>
       Il'a =
       insertp (Receive (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
              (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila))))
            (delta (relayer Ila)))
          (bc_upd d ((b, bs), N) Ila)) \<Longrightarrow>
       Consensus (actors (graphI J)) = Ila \<Longrightarrow>
       global_consistency
        (insertp (Receive (a, b, (a, as), d) # l)
          (replrel
            (Infrastructure
              (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
                (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
                (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
                (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila))))
              (delta (relayer Ila)))
            (bc_upd d ((b, bs), N) Ila))) \<close>
  proof -
fix G :: igraph and I :: infrastructure and Ila :: blockchainset and a :: "char list" and n :: node and d :: "char list" and as :: "char list set" and N :: "node set" and H :: igraph and J :: infrastructure and b :: "char list" and n' :: node and R :: igraph and r :: "char list" and n'' :: node and R' :: infrastructure and bs :: "char list set" and Il'a :: blockchainset and l :: "sc_fun list" and actors :: "igraph \<Rightarrow> actor set"
  assume a1: "global_consistency Ila"
obtain ii :: "blockchainset \<Rightarrow> infrastructure" and iia :: "blockchainset \<Rightarrow> infrastructure" where
"\<forall>x0. (\<exists>v1 v2. (inbc v1 x0 \<and> inbc v2 x0) \<and> (\<exists>v3. ledgra (graphI v2) v3 \<noteq> ledgra (graphI v1) v3)) = ((inbc (ii x0) x0 \<and> inbc (iia x0) x0) \<and> (\<exists>v3. ledgra (graphI (iia x0)) v3 \<noteq> ledgra (graphI (ii x0)) v3))"
by moura
  then obtain ccs :: "blockchainset \<Rightarrow> char list" where
    f2: "\<forall>b. (\<exists>i ia. (inbc i b \<and> inbc ia b) \<and> (\<exists>cs. ledgra (graphI ia) cs \<noteq> ledgra (graphI i) cs)) = ((inbc (ii b) b \<and> inbc (iia b) b) \<and> ledgra (graphI (iia b)) (ccs b) \<noteq> ledgra (graphI (ii b)) (ccs b))"
    by moura
  have f3: "\<forall>i ia. \<not> inbc i (Infs (the_ibc Ila) (upd_Il d ((b, bs), N) (the_Il Ila)) (upd_ld d ((b, bs), N) (relayer Ila))) \<or> \<not> inbc ia (Infs (the_ibc Ila) (upd_Il d ((b, bs), N) (the_Il Ila)) (upd_ld d ((b, bs), N) (relayer Ila))) \<or> (\<forall>cs. ledgra (graphI ia) cs = ledgra (graphI i) cs)"
    using a1 by (metis (no_types) bc_upd_def bc_upd_inv global_consistency_def)
  have "upd_Il d ((b, bs), N) (the_Il Ila) = the_Il (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila))"
    by (simp add: bc_upd_def)
  then have "\<not> inbc (ii (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila)))) (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila))) \<or> \<not> inbc (iia (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila)))) (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila))) \<or> ledgra (graphI (iia (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila))))) (ccs (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila)))) = ledgra (graphI (ii (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila))))) (ccs (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila))))"
    using f3 by (metis (no_types) inbc.inbc_def insertp_def)
  then show "global_consistency (insertp (Receive (a, b, (a, as), d) # l) (replrel (Infrastructure (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila))) (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila))) (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N))) (Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)))) (delta (relayer Ila))) (bc_upd d ((b, bs), N) Ila)))"
    using f2 global_consistency_def by auto
qed
qed

  

end