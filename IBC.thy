theory IBC
  imports Refinement
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
                         "ledger" "node \<Rightarrow> transaction_record"
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
primrec trec :: "igraph \<Rightarrow> node \<Rightarrow> transaction_record"
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
consts Consensus :: "infrastructure \<Rightarrow> blockchainset \<Rightarrow> blockchainset"

definition global_consistency
  where 
 "global_consistency Il \<equiv> (\<forall> I I'. inbc I Il \<longrightarrow> inbc I' Il \<longrightarrow> 
       (\<forall> d. (ledgra (graphI I') d) = (ledgra (graphI I) d)))"

lemma glob_con_dom_eq: \<open>global_consistency Il \<Longrightarrow> inbc I Il \<Longrightarrow> inbc I' Il \<Longrightarrow>
                        dom (ledgra (graphI I)) = dom (ledgra (graphI I'))\<close>
  by (metis global_consistency_def map_le_antisym map_le_def)

lemma updIl_lem0: "d \<notin> dom (ledgra (graphI I)) \<Longrightarrow> 
        (I \<in> set(upd_Il d lN il)) \<Longrightarrow> (I \<in> set il)" unfolding upd_Il_def upd_ld_def
proof (induction il)
  case Nil
then show ?case
  by simp 
next
  case (Cons a il)
  then show ?case
    by auto 
qed

lemma updIl_lem1: "d \<notin> dom (ledgra (graphI I)) \<Longrightarrow> 
        inbc I (Infs p (upd_Il d lN (the_Il Il)) r) \<Longrightarrow> inbc I (Infs p (the_Il Il) r)"
  using inbc.inbc_def updIl_lem0 by blast
  
lemma d_dom_ledgra: "(d \<notin> dom (ledgra (graphI I))) \<Longrightarrow>
                     inbc I (Infs (the_ibc Il) (upd_Il d lN (the_Il Il)) (upd_ld d lN (relayer Il))) \<Longrightarrow>
                     inbc I Il"
  by (metis blockchainset.exhaust inbc.inbc_def the_Il.simps updIl_lem1)

lemma upd_lem3a: \<open>I \<in> set (upd_Il d lN il) 
    \<Longrightarrow> ledgra (graphI I) d = Some lN\<close>
unfolding upd_Il_def upd_ld_def
proof (induction il)
case Nil
then show ?case
  by simp 
next
  case (Cons a il)
  then show ?case
    by auto 
qed

lemma upd_lem3: \<open>inbc I (Infs (the_ibc Il) (upd_Il d lN (the_Il Il)) (upd_ld d lN (relayer Il))) 
    \<Longrightarrow> ledgra (graphI I) d = Some lN\<close>
by (rule upd_lem3a, simp add: upd_Il_def upd_ld_def)

lemma upd_lem4a:
  assumes "I \<in> set (upd_Il d lN il)"
  shows "\<exists>I0. I = upd_ld d lN I0 \<and> I0 \<in> (set il)"
  using assms
proof (induction il)
  case Nil
  then show ?case
    by simp
next
  case (Cons a il)
  then show ?case
    by auto
qed

lemma upd_lem4: "inbc I (Infs (the_ibc Il) (upd_Il d lN (the_Il Il)) (upd_ld d lN (relayer Il)))
     \<Longrightarrow> \<exists> I0. I = upd_ld d lN I0 \<and> inbc I0 Il"
  by (metis blockchainset.exhaust inbc.inbc_def the_Il.simps upd_lem4a)

lemma bc_upd_inv: 
  assumes \<open>global_consistency Il\<close>
  shows \<open>global_consistency (bc_upd d lN Il)\<close>
  unfolding global_consistency_def bc_upd_def
proof (clarify)
  fix I I' da
  assume p0 : "inbc I (Infs (the_ibc Il) (upd_Il d lN (the_Il Il)) (upd_ld d lN (relayer Il)))"
    and p1: "inbc I' (Infs (the_ibc Il) (upd_Il d lN (the_Il Il)) (upd_ld d lN (relayer Il)))"
  obtain I0 where \<open>I = upd_ld d lN I0\<close>  and "inbc I0 Il" using assms upd_lem4 p0
    by blast
  obtain I1 where \<open>I' = upd_ld d lN I1\<close>  and "inbc I1 Il" using assms upd_lem4 p1
    by blast
  have prem0: "\<forall> d. ledgra (graphI I0) d = ledgra (graphI I1) d"
    using \<open>inbc I0 Il\<close> \<open>inbc I1 Il\<close> assms global_consistency_def by blast 
  show "inbc I (Infs (the_ibc Il) (upd_Il d lN (the_Il Il)) (upd_ld d lN (relayer Il))) \<Longrightarrow>
       inbc I' (Infs (the_ibc Il) (upd_Il d lN (the_Il Il)) (upd_ld d lN (relayer Il))) \<Longrightarrow>
       ledgra (graphI I') da = ledgra (graphI I) da"
    using assms
    by (simp add: \<open>I = upd_ld d lN I0\<close> \<open>I' = upd_ld d lN I1\<close> \<open>inbc I0 Il\<close> \<open>inbc I1 Il\<close> global_consistency_def upd_ld_def)
qed

lemma trec_upd_inv: 
  fixes ibc Il rl I I'
  assumes \<open>global_consistency (Infs ibc Il rl)\<close>
   and  \<open>ledgra (graphI I) = ledgra (graphI I')\<close>
 shows  \<open>global_consistency (replace I I' (Infs ibc Il rl))\<close>
  unfolding global_consistency_def using assms
proof (induction Il)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a Il)
  then show ?case sorry
qed




inductive state_transition_in :: "[blockchainset, blockchainset] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
 scan : "inbc I Il \<Longrightarrow> G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> n \<Longrightarrow> n \<in> nodes G \<Longrightarrow> 
         R = graphI (relayer Il) \<Longrightarrow> r @\<^bsub>R\<^esub> n' \<Longrightarrow> n' \<in> nodes R \<Longrightarrow> 
         relrole (relayer Il) (Actor r) \<Longrightarrow> enables I n (Actor r) scan \<Longrightarrow> 
         ledgra G d = Some ((a, as), N) \<Longrightarrow> r \<in> as \<Longrightarrow> 
         R' = Infrastructure 
                   (Lgraph (gra R)(agra R)(cgra R)(lgra R)
                           ((ledgra R)(d := Some((a', as),N)))
                           (\<lambda> n. (Send(a,b,(a,as), d)) # (trec R n)))
                   (delta (relayer Il)) \<Longrightarrow>  
         l \<in> trcs Il \<Longrightarrow> Consensus I Il = Il' \<Longrightarrow>
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
                           (\<lambda> n. (Receive(a,b,(a,as), d)) # (trec R n)))
                  (delta (relayer Il))  \<Longrightarrow>
            Il' = insertp (Receive(a,b,(a,as),d)# l) (replrel R' (bc_upd d ((b,as), N) Il)) \<Longrightarrow>
            Consensus J Il = Il' 
            \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'" |
 internal_Send : "inbc I Il \<Longrightarrow> G = graphI I \<Longrightarrow> a \<in> actors G \<Longrightarrow> n \<in> nodes G \<Longrightarrow> 
         ledgra G d = Some ((a, as), N) \<Longrightarrow> 
         I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                           (ledgra G)
                           ((trec G)(n := (Send(a,b,(a,as), d)) # (trec G n))))
                   (delta I) \<Longrightarrow>  
         Il' = replace I' I Il
         \<Longrightarrow> Il \<rightarrow>\<^sub>n Il'"|
 internal_Receive : "inbc I Il \<Longrightarrow> G = graphI I \<Longrightarrow> a \<in> actors G \<Longrightarrow> n \<in> nodes G \<Longrightarrow> 
         ledgra G d = Some ((a, as), N) \<Longrightarrow> 
         I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)
                           (ledgra G)
                           ((trec G)(n := (Receive(a,b,(a,as), d)) # (trec G n))))
                   (delta I) \<Longrightarrow>  
         Il' = replace I' I Il
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
                           (\<lambda> n. (Send(a,b,(a,as), d)) # (trec R n)))
                   (delta I) \<Longrightarrow>
Il' = insertp ((Send(a,b,(a,as), d)) # l) (replrel R' Il)
\<Longrightarrow> global_consistency Il'"
  by (metis (no_types, hide_lams) blockchainset.exhaust global_consistency_def inbc.inbc_def insertp_def replrel.replrel_def the_Il.simps)

theorem consistency_preservation: 
   "global_consistency Il \<Longrightarrow> (Il \<rightarrow>\<^sub>n Il') \<Longrightarrow> global_consistency Il'" 
proof (erule state_transition_in.cases, simp_all)
  show \<open>\<And>I Ila G a n R r n' d as N R' a' b l Il'a.
       global_consistency Ila \<Longrightarrow>
       Il = Ila \<Longrightarrow>
       Il' =
       insertp (Send (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
              (\<lambda>n. Send (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
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
          (\<lambda>n. Send (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
        (delta (relayer Ila)) \<Longrightarrow>
       l \<in> trcs Ila \<Longrightarrow>
       Consensus I Ila =
       insertp (Send (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
              (\<lambda>n. Send (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
            (delta (relayer Ila)))
          Ila) \<Longrightarrow>
       Il'a =
       insertp (Send (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
              (\<lambda>n. Send (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
            (delta (relayer Ila)))
          Ila) \<Longrightarrow>
       global_consistency
        (insertp (Send (a, b, (a, as), d) # l)
          (replrel
            (Infrastructure
              (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
                (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
                (ledgra (graphI (relayer Ila))(d \<mapsto> ((a', as), N)))
                (\<lambda>n. Send (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
              (delta (relayer Ila)))
            Ila))\<close>
    by (simp add: cons_lemma)
next show \<open>\<And>G I Ila a n d as N H J b n' R r n'' R' bs Il'a l.
       global_consistency Ila \<Longrightarrow>
       Il = Ila \<Longrightarrow>
       Il' =
       insertp (Receive (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
              (\<lambda>n. Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
            (delta (relayer Ila)))
          (bc_upd d ((b, as), N) Ila)) \<Longrightarrow>
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
          (\<lambda>n. Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
        (delta (relayer Ila)) \<Longrightarrow>
       Il'a =
       insertp (Receive (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
              (\<lambda>n. Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
            (delta (relayer Ila)))
          (bc_upd d ((b, as), N) Ila)) \<Longrightarrow>
       Consensus J Ila =
       insertp (Receive (a, b, (a, as), d) # l)
        (replrel
          (Infrastructure
            (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
              (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
              (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
              (\<lambda>n. Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
            (delta (relayer Ila)))
          (bc_upd d ((b, as), N) Ila)) \<Longrightarrow>
       global_consistency
        (insertp (Receive (a, b, (a, as), d) # l)
          (replrel
            (Infrastructure
              (Lgraph (gra (graphI (relayer Ila))) (agra (graphI (relayer Ila)))
                (cgra (graphI (relayer Ila))) (lgra (graphI (relayer Ila)))
                (ledgra (graphI (relayer Ila))(d \<mapsto> ((b, bs), N)))
                (\<lambda>n. Receive (a, b, (a, as), d) # trec (graphI (relayer Ila)) n))
              (delta (relayer Ila)))
            (bc_upd d ((b, as), N) Ila))) \<close>
    by (smt bc_upd_def bc_upd_inv global_consistency_def inbc.inbc_def insertp_def replrel.replrel_def the_Il.simps) 
next show \<open> \<And>I Ila G a actors n d as N I' b Il'a.
       global_consistency Ila \<Longrightarrow>
       Il = Ila \<Longrightarrow>
       Il' =
       replace
        (Infrastructure
          (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))
            (ledgra (graphI I)) ((trec (graphI I))(n := Send (a, b, (a, as), d) # trec (graphI I) n)))
          (delta I))
        I Ila \<Longrightarrow>
       inbc I Ila \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a \<in> actors (graphI I) \<Longrightarrow>
       n \<in> nodes (graphI I) \<Longrightarrow>
       ledgra (graphI I) d = Some ((a, as), N) \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I)) (ledgra (graphI I))
          ((trec (graphI I))(n := Send (a, b, (a, as), d) # trec (graphI I) n)))
        (delta I) \<Longrightarrow>
       Il'a =
       replace
        (Infrastructure
          (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))
            (ledgra (graphI I)) ((trec (graphI I))(n := Send (a, b, (a, as), d) # trec (graphI I) n)))
          (delta I))
        I Ila \<Longrightarrow>
       global_consistency
        (replace
          (Infrastructure
            (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))
              (ledgra (graphI I)) ((trec (graphI I))(n := Send (a, b, (a, as), d) # trec (graphI I) n)))
            (delta I))
          I Ila)\<close>
    by (metis blockchainset.exhaust graphI.simps ledgra.simps trec_upd_inv)
next show \<open>\<And>I Ila G a actors n d as N I' b Il'a.
       global_consistency Ila \<Longrightarrow>
       Il = Ila \<Longrightarrow>
       Il' =
       replace
        (Infrastructure
          (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))
            (ledgra (graphI I)) ((trec (graphI I))(n := Receive (a, b, (a, as), d) # trec (graphI I) n)))
          (delta I))
        I Ila \<Longrightarrow>
       inbc I Ila \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a \<in> actors (graphI I) \<Longrightarrow>
       n \<in> nodes (graphI I) \<Longrightarrow>
       ledgra (graphI I) d = Some ((a, as), N) \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I)) (ledgra (graphI I))
          ((trec (graphI I))(n := Receive (a, b, (a, as), d) # trec (graphI I) n)))
        (delta I) \<Longrightarrow>
       Il'a =
       replace
        (Infrastructure
          (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))
            (ledgra (graphI I)) ((trec (graphI I))(n := Receive (a, b, (a, as), d) # trec (graphI I) n)))
          (delta I))
        I Ila \<Longrightarrow>
       global_consistency
        (replace
          (Infrastructure
            (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))
              (ledgra (graphI I)) ((trec (graphI I))(n := Receive (a, b, (a, as), d) # trec (graphI I) n)))
            (delta I))
          I Ila) \<close>
    by (metis blockchainset.exhaust graphI.simps ledgra.simps trec_upd_inv)  
  qed

locale ConsensusExample =

fixes cons_algo_aux :: \<open>infrastructure \<Rightarrow> blockchainset \<Rightarrow> sc_fun\<close>
defines cons_algo_aux_def: "cons_algo_aux I Il \<equiv> 
          (SOME x. x \<in> {x. \<exists> n. n \<in> nodes (graphI I) \<and> x = hd(trec (graphI I) n)})"

fixes cons_algo :: \<open>infrastructure \<Rightarrow> blockchainset \<Rightarrow> infrastructure\<close>
defines cons_algo_def: "cons_algo I Il \<equiv> 
           Infrastructure 
                   (Lgraph (gra (graphI I))(agra (graphI I))(cgra (graphI I))
                           (lgra (graphI I))(ledgra (graphI I))
                            ((\<lambda> n. (cons_algo_aux I Il) # (trec (graphI I) n))))
                   (delta I)"

fixes Consensus :: \<open>infrastructure \<Rightarrow> blockchainset \<Rightarrow> blockchainset\<close>
defines Consensus_def: 
  "Consensus I Il \<equiv> replace (cons_algo I Il) I Il"

begin
end

end