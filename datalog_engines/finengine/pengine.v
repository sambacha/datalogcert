(************************************************************************************)
(**                                                                                 *)
(**                             The DatalogCert Library                             *)
(**                                                                                 *)
(**             CNRS & Université Paris-Sud, Université Paris-Saclay                *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                  Stefania Dumbrava                                              *)
(**                                                                                 *)
(************************************************************************************)



From mathcomp
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp
Require Import tuple finfun bigop finset.

Add LoadPath "../lib" as lib.
From lib
Require Import bigop_aux.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Standard Datalog in Coq

We define the *syntax* and *model-theoretic semantics*, as well as a bottom-up fixpoint evaluation
engine, for standard Datalog. The syntactic primitives of the language are terms (constants or variables),
atoms, clauses and programs. Semantically, *interpretations* (ground atom sets) are the main building blocks.
The bottom-up engine iteratively extends an initial seed substitution into one that matches all clause body atoms to an
existing interpretations (candidate model) and provably grounds the corresponding clause head, i.e, instantiates all of
its variables. To ease the proof-engineering effort, we distinguish between ground and non-ground constructs.
As such, we define corresponding separate types, both for the language primitives and for substitutions (we call
grounding substitutions "groundings"). *)

Section Datalog.

(** maximal number of program variables *)
Variable n        : nat.

(** program signature: constants and symbols as finite types and arities as finitely-supported functions *)
Variable constype : finType.
Variable symtype  : finType.
Variable arity    : {ffun symtype -> nat}.

Inductive constant := C of constype.
Definition of_constant c := let: C c := c in c.

(** instances for the type of constants *)
Canonical cons_subType      := Eval hnf in [newType for of_constant].
Canonical cons_eqType       := Eval hnf in EqType _     [eqMixin of constant by <: ].
Canonical cons_choiceType   := Eval hnf in ChoiceType _ [choiceMixin of constant by <:].
Canonical cons_countType    := Eval hnf in CountType  _ [countMixin  of constant by <:].
Canonical cons_subCountType := Eval hnf in [subCountType of constant].
Canonical cons_finType      := Eval hnf in FinType    _ [finMixin    of constant by <:].
Canonical cons_subFinType   := Eval hnf in [subFinType of constant].

(** "raw" ground atoms pack a symbol and an argument list of constants *)
Inductive raw_gatom := RawGAtom of symtype & seq constant.

(** extractors for the corresponding symbols and arguments of a "raw" ground atom *)
Definition sym_gatom ga := let: RawGAtom s_ga _   := ga in s_ga.
Definition arg_gatom ga := let: RawGAtom _ arg_ga := ga in arg_ga.

Lemma gatom_eta ga : ga = RawGAtom (sym_gatom ga) (arg_gatom ga).
Proof. by case: ga. Qed.

(** *** Ground Atom Instances *)

Section RawGAtomInstances.

(** packing and unpacking of a "raw" ground atom; needed for the canonical inference of its instances *)
Definition raw_gatom_rep l := let: RawGAtom s a := l in (s, a).
Definition raw_gatom_pre l := let: (s, a) := l in RawGAtom s a.

(** cancelation lemma for "raw" ground atoms *)
Lemma raw_gatom_repK : cancel raw_gatom_rep raw_gatom_pre.
Proof. by case. Qed.

(** "raw" ground atom instances *)
Canonical raw_gatom_eqType :=
  Eval hnf in EqType raw_gatom (CanEqMixin raw_gatom_repK).

Canonical raw_gatom_choiceType :=
  Eval hnf in ChoiceType raw_gatom (CanChoiceMixin raw_gatom_repK).

Canonical raw_gatom_countType :=
  Eval hnf in CountType  raw_gatom (CanCountMixin  raw_gatom_repK).

End RawGAtomInstances.

(** ** Ground Atoms:
A ground atom [gatom] packs a "raw" ground atom and a boolean well-formedness condition *)

(** ground atom well-formedness condition: argument size and symbol arity have to match *)
Definition wf_gatom ga := size (arg_gatom ga) == arity (sym_gatom ga).

(** ground atom record *)
Structure gatom : Type := GAtom {uga :> raw_gatom; _ : wf_gatom uga}.

(** ground atom instances *)
Canonical gatom_subType      := Eval hnf in [subType for uga].
Canonical gatom_eqType       := Eval hnf in EqType _     [eqMixin     of gatom by <:].
Canonical gatom_choiceType   := Eval hnf in ChoiceType _ [choiceMixin of gatom by <:].
Canonical gatom_countType    := Eval hnf in CountType  _ [countMixin  of gatom by <:].
Canonical gatom_subCountType := Eval hnf in [subCountType of gatom].

Section GatomFinType.

(** maximal symbol arity *)
Notation max_ar := (\max_(s in symtype) arity s).

Lemma max_ar_bound y : arity y < max_ar.+1.
Proof. exact/leq_bigmax_cond. Qed.

(** corresponding finite type for ground atoms, packing a symbol type and a tuple of constants
    of length bounded by the maximal symbol arity *)
Notation gatom_enc := ({x : 'I_(max_ar.+1) & (symtype * x.-tuple constant)%type}).

(** injecting a ground atom [ga] into its corresponding finite type encoding [gatom_enc] *)
Definition gatom_fenc (ga : gatom) : gatom_enc :=
  let: GAtom ga proof := ga in

  existT _ (Ordinal (max_ar_bound (sym_gatom ga))) (sym_gatom ga, Tuple proof).

(** conversely converting a ground atom finite type encoding [gatom_enc] into a ground atom [gatom] *)
Definition fenc_gatom (e : gatom_enc): option gatom.
case: e => x [s]; case: (val x == arity s) / eqP => [-> | _] [tup proof];
[exact: (Some (@GAtom (RawGAtom s tup) proof)) | exact/None].
Defined.

(** partial cancelation lemma for ground atoms *)
Lemma fenc_gatomK : pcancel gatom_fenc fenc_gatom.
Proof. by case=> [[s args] proof] /=; case: eqP => // ?; rewrite !eq_axiomK. Qed.

End GatomFinType.

(** canonical instances for ground atoms *)
Canonical gatom_finType     := Eval hnf in FinType gatom (PcanFinMixin fenc_gatomK).
Canonical gatom_subFinType  := [subFinType of gatom].

(** ** Ground Clauses:
A ground clause [gclause] packs a ground atom head and a body list of ground atoms *)
Inductive  gclause      := GClause of gatom & seq gatom.

(** head and body extractors for ground clauses *)
Definition head_gcl gcl := let: GClause h b := gcl in h.
Definition body_gcl gcl := let: GClause h b := gcl in b.

(** interpretations are finite sets of ground atoms *)
Notation interp := {set gatom}.

Implicit Types (i m : interp) (gcl : gclause).

(** set of all symbols of a given interpretation *)
Definition sym_i i := [set sym_gatom (val ga) | ga in i].

(** satisfiability of a ground clause [gcl] w.r.t a given interpretation [i]:
    if all body atoms belong to [i], the head should also belong to [i] *)
Definition gcl_true gcl i :=
  all (mem i) (body_gcl gcl) ==> (head_gcl gcl \in i).

(** Terms are either
    - variables, i.e, integers bound by a maximal (computable) index [n]
      - to which we assign the _finite_ ordinal type ['I_n]
    - constants to which we assign the _finite_ [constype]
*)

Inductive term : Type :=
  | Var of 'I_n
  | Val of constant.

(** corresponding sigma type encoding for terms; needed for canonical instance inference *)
Notation termRep := ('I_n + constant)%type.

(** injecting a term [t] into its [termRep] encoding *)
Definition term_rep (t : term) : termRep :=
  match t with
  | Var i => inl i
  | Val c => inr c
  end.

(** converting a [termRep] encoding into the corresponding term type  *)
Definition term_con (r : termRep) : term :=
  match r with
  | inl i => Var i
  | inr c => Val c
  end.

(** cancelation lemma for terms *)
Lemma term_repK : cancel term_rep term_con.
Proof. by case. Qed.

(** canonical instances for terms *)
Canonical term_eqType := Eval hnf in EqType term (CanEqMixin term_repK).
Canonical term_choiceType := Eval hnf in ChoiceType term (CanChoiceMixin term_repK).

(** Atoms are represented as records packing:
   - a base type [raw_atom]
     - which pairs a symbol with its term list argument
   - a _boolean_ well-formedness condition [wf_atom]
     - which ensures symbol arity and argument size agree *)

Inductive raw_atom : Type := RawAtom of symtype & seq term.

Section RawAtomInstances.

(** packing and unpacking of raw atoms *)
Definition raw_atom_rep l := let: RawAtom s a := l in (s, a).
Definition raw_atom_pre l := let: (s, a)      := l in RawAtom s a.

(** cancelation lemma for raw atoms *)
Lemma raw_atom_repK : cancel raw_atom_rep raw_atom_pre.
Proof. by case. Qed.

(** canonical instances for raw atoms *)
Canonical raw_atom_eqType     := Eval hnf in EqType     raw_atom (CanEqMixin     raw_atom_repK).
Canonical raw_atom_choiceType := Eval hnf in ChoiceType raw_atom (CanChoiceMixin raw_atom_repK).

End RawAtomInstances.

(** extractors for the corresponding symbols and arguments of an atom *)
Definition sym_atom a := let: RawAtom s_a _     := a in s_a.
Definition arg_atom a := let: RawAtom _   arg_a := a in arg_a.

(** atom well-formedness condition: argument size and symbol arity must match *)
Definition wf_atom a := size (arg_atom a) == arity (sym_atom a).

(** ** Atoms are records packing a "raw" atom and a corresponding boolean well-formedness condition *)
Structure atom : Type := Atom {ua :> raw_atom; _ : wf_atom ua}.

(** atom instances *)
Canonical atom_subType    := Eval hnf in [subType for ua].
Canonical atom_eqType     := Eval hnf in EqType     _ [eqMixin of atom by <: ].
Canonical atom_choiceType := Eval hnf in ChoiceType _ [choiceMixin of atom by <:].

(** Clauses pack an atom head and an atom list body. *)
Inductive clause : Type := Clause of atom & seq atom.

Section ClauseInstances.

(** packing and unpacking of clauses *)
Definition clause_rep cl := let: Clause hd bd := cl in (hd, bd).
Definition clause_pre cl := let: (hd, bd)     := cl in Clause hd bd.

(** cancelation lemma for clauses *)
Lemma clause_repK : cancel clause_rep clause_pre.
Proof. by case. Qed.

(** clause instances *)
Canonical clause_eqType     := Eval hnf in EqType     clause (CanEqMixin     clause_repK).
Canonical clause_choiceType := Eval hnf in ChoiceType clause (CanChoiceMixin clause_repK).

End ClauseInstances.

(** ** Programs are clause lists. *)
Definition program := seq clause.

(** extractors for the corresponding head, body and atoms of a clause *)
Definition head_cl  cl := let: Clause h b := cl in h.
Definition body_cl  cl := let: Clause h b := cl in b.
Definition atoms_cl cl := [:: head_cl cl & body_cl cl].

(** clause head symbols *)
Definition hsym_cl cl := sym_atom (head_cl cl).

(** all clause symbols *)
Definition sym_cl  cl := [seq sym_atom (val a) | a <- atoms_cl cl].

(** all head symbols of a program *)
Definition hsym_prog  p := [seq hsym_cl cl | cl <- p].

(** all program symbols *)
Definition sym_prog   p := flatten [seq sym_cl cl   | cl <- p].

(** all program atoms *)
Definition atoms_prog p := flatten [seq atoms_cl cl | cl <- p].

Section Grounding.

(** *** Ground valuations and their application  *)

(** type of groundings: finitely-supported functions mapping variables to constants *)
Definition gr := {ffun 'I_n -> constant}.

Implicit Types (g : gr) (t : term) (ra : raw_atom) (a : atom)
               (cl : clause) (hd : atom) (tl : seq atom).

(** term grounding *)
Definition gr_term g t :=
  match t with
  | Var v => g v
  | Val c => c
  end.

(** raw atom grounding *)
Definition gr_raw_atom g ra :=
  RawGAtom (sym_atom ra) [seq gr_term g x | x <- arg_atom ra].

(** the grounding of a well-formed ground atom is well-formed *)
Definition gr_atom_proof g a : wf_gatom (gr_raw_atom g a).
Proof. by case: a => s arg; rewrite /wf_gatom size_map. Qed.

(** atom grounding *)
Definition gr_atom g a := GAtom (gr_atom_proof g a).

(** clause grounding *)
Definition gr_cl g cl :=
  GClause (gr_atom g (head_cl cl)) [seq gr_atom g a | a <- body_cl cl].

End Grounding.

Section Theory.

(** *** Collecting Constants *)

Section Constants.

Definition const_term t : seq constant :=
  if t is Val e then [:: e] else [::].

(** atom constants *)
Definition const_atom a : seq constant :=
  flatten [seq const_term x | x <- arg_atom a].

(** atom list constants *)
Definition const_tail (tl : seq atom) : seq constant :=
  flatten [seq const_atom (val x) | x <- tl].

(** clause constants *)
Definition const_cl cl : seq constant :=
  const_tail [:: head_cl cl & body_cl cl].

End Constants.

Section Variables.

(** *** Collecting Variables *)

(** term variables *)
Definition term_vars t : {set 'I_n} := if t is Var v then [set v] else set0.

(** "raw" atom variables *)
Definition raw_atom_vars (ra : raw_atom) : {set 'I_n} :=
  \bigcup_(t <- arg_atom ra) term_vars t.

(** atom variables *)
Definition atom_vars (a : atom) : {set 'I_n} := raw_atom_vars a.

(** atom list variables *)
Definition tail_vars tl : {set 'I_n} := \bigcup_(t <- tl) atom_vars t.

(** **** Program Safety Condition *)

(** clause safety: all head variables should appear among the body variables *)
Definition safe_cl cl :=
  atom_vars (head_cl cl) \subset tail_vars (body_cl cl).

(** program safety: all clauses should be safe *)
Definition prog_safe p := all safe_cl p.

End Variables.

(** ** Program Satisfiability *)

(** a clause [c] is satisfied by an interpretation [i], if for all groundings [g]
its corresponding instantiation is satisfied by [i] *)
Definition cl_true cl i := forall g : gr, gcl_true (gr_cl g cl) i.

Definition prog_true p i :=
  forall g : gr, all (fun cl => gcl_true (gr_cl g cl) i) p.

End Theory.

Section Substitutions.

(** *** Substitutions as finitely supported partial functions *)
Definition sub := {ffun 'I_n -> option constant}.

Implicit Types (s : sub) (t : term) (a : atom) (v : 'I_n)
         (b : 'I_n * constant).

(** empty substitution *)
Definition emptysub : sub := [ffun _ => None].

(** Variable is mapped/free by the substitution s *)
Definition mem_bound s v : bool := s v.
Definition mem_free  s v : bool := s v == None.

(** Binding b belongs to s *)
Definition mem_binding s b : bool := s b.1 == Some b.2.

(** mem_binding = \in to be used as generic predicate *)
Definition eqbind_class := sub.

(** Implementing the collective predicate interface for sub *)
Identity Coercion sub_of_eqbind : eqbind_class >-> sub.

Coercion pred_of_eq_bind (s : eqbind_class) : pred_class := [eta mem_binding s].

Canonical mem_bind_symtype := mkPredType mem_binding.

Lemma mem_bindE s b : b \in s = (s b.1 == Some b.2). Proof. by []. Qed.

Definition inE := (mem_bindE, inE).

(** substitution [s2] extends [s1] *)
Definition sub_st s1 s2 :=
  [forall v : 'I_n, if s1 v is Some b1 then (v, b1) \in s2 else true].

Notation "A \sub B" := (sub_st A B)
  (at level 70, no associativity) : bool_scope.

(** reflection lemma for substitution ordering *)
Lemma substP s1 s2 : reflect {subset s1 <= s2} (s1 \sub s2).
Proof.
apply/(iffP forallP)=> [H t|H v].
  by move/eqP=> t_s1; have:= H t.1; rewrite t_s1.
by case E: (s1 _) => [d|//]; apply/H; rewrite inE E.
Qed.

Implicit Arguments substP [s1 s2].
Prenex Implicits substP.

(** **** Substitution Extensionality Lemma *)
Lemma substE s1 s2 :
  reflect (forall d v, s1 v = Some d -> s2 v = Some d) (s1 \sub s2).
Proof.
apply/(iffP substP)=> [H d v| H [v d]].
  by move/(_ (v,d)): H; rewrite !inE => H /eqP H1; exact/eqP/H.
by rewrite !inE => /eqP H1; rewrite (H d).
Qed.

(** reflexivity of substitution ordering *)
Lemma substss s : s \sub s.
Proof. exact/substP. Qed.

(** transitivity of substitution ordering *)
Lemma subst_trans s1 s2 s3 : s2 \sub s3 -> s1 \sub s2 -> s1 \sub s3.
Proof. by move=> /substP H1 /substP H2; apply/substP=> b /H2; auto. Qed.

(** any substitution extends the empty substitution *)
Lemma subst0s s : emptysub \sub s.
Proof. by apply/substP=> ?; rewrite inE ffunE. Qed.

(** Extending a substitution [s] with a binding [(v,d)] *)
Definition add s v d :=
  [ffun u => if u == v then Some d else s u].

(** If [v] was free in [s], substitution extension respects ordering. *)
Lemma sub_add s v d : mem_free s v -> s \sub (add s v d).
Proof.
move/eqP=> H; apply/substP=> -[u e].
by rewrite !inE !ffunE; case: ifP H => // /eqP -> ->.
Qed.

Lemma addE (s : sub) (v : 'I_n) d : (add s v d) v = Some d.
Proof. by rewrite ffunE eqxx. Qed.

Lemma add_add (s : sub) v d e : (add (add s v e) v d) = add s v d.
Proof. by apply/ffunP=> u; rewrite !ffunE; case: eqP. Qed.

(** Term substitution *)
Definition sterm s t : term :=
  match t with
  | Val d => Val d
  | Var v => if s v is Some d
             then Val d
             else Var v
  end.

(** Term grounding *)
Definition term_gr s t := { gt : constant | Val gt = sterm s t }.

(** Empty term substitution application *)
Lemma emptysubE t : sterm emptysub t = t.
Proof. by case: t => //= v; rewrite ffunE. Qed.

(** Substitution extension for terms *)
Lemma sterm_sub t s1 s2 d :
  s1 \sub s2 -> sterm s1 t = Val d -> sterm s2 t = Val d.
Proof.
case: t => //= v /substE H.
by case E: (s1 v) => [a1|//]; move/H: E ->.
Qed.

(** Atom substitution: applying a substiution [s] to a "raw" atom [ra] *)
Definition sraw_atom ra s := RawAtom (sym_atom ra) [seq sterm s x | x <- arg_atom ra].

(** Given an atom [a] and a substitution [s], the atom resulting by instantiating
[a] with [s] is well-formed *)
Lemma satom_proof a s : wf_atom (sraw_atom a s).
Proof. by case: a => ra pf; rewrite /wf_atom /= size_map. Qed.

(** Instantiation function that, for a given atom [a], takes a substitution [s]
and returns the corresponding substituted atom *)
Definition satom a : sub -> atom := fun s => Atom (satom_proof a s).

(** Atom symbols are preserved by substitution instantiation *)
Lemma sym_satom a nu : sym_atom (satom a nu) = sym_atom a.
Proof. by []. Qed.

(** Lifting ground raw atoms to raw atoms *)
Definition to_raw_atom gra :=
  RawAtom (sym_gatom gra) [seq Val x | x <- arg_gatom gra].

(** The atom obtain from the lifting of a ground atom is well-formed *)
Lemma to_atom_proof (ga : gatom) : wf_atom (to_raw_atom ga).
Proof. by case: ga => ra pf; rewrite /wf_atom /= size_map. Qed.

(** Lifting of ground atoms to atoms *)
Definition to_atom ga := Atom (to_atom_proof ga).

(** Atom grounding *)
Definition atom_gr a s := { gtl : gatom | to_atom gtl = satom a s }.

(** **** Atom Substitution Extensions Lemma:
Let [s1], [s2] be two substitutions. If [s2] extends [s1] and [s1] instantiates
an atom [a] to a ground atom [ga], then [s2] also instantitates [a] to [ga]. *)
Lemma satom_sub a s1 s2 ga :
  s1 \sub s2 -> satom a s1 = to_atom ga -> satom a s2 = to_atom ga.
Proof.
case: a ga => // [[sy1 a1] pf1] [[sy2 a2] pf2] ss /= [hs harg].
apply/val_inj; congr RawAtom; rewrite //=.
elim: a1 a2 harg {pf1 pf2} => //= a1 l1 iha [|a2 l2] //= [].
by move/(sterm_sub ss)=> ->/iha<-.
Qed.

(** Tail substitution *)
Definition stail tl s : list atom := [seq satom a s | a <- tl].

(** Lifting of a ground tail to tail *)
Definition to_tail gtl : list atom := [seq to_atom ga | ga <- gtl].

(** Grounding of atom list *)
Definition tail_gr tl s := { gtl : list gatom | to_tail gtl = stail tl s}.

End Substitutions.

(** Export the notation *)
Notation "A \sub B" := (sub_st A B)
  (at level 70, no associativity) : bool_scope.

Hint Resolve substss subst0s.

Section NoDepGrounding.

(** Non-dependent grounding using default element *)
Implicit Types (s : sub) (t : term) (a : atom) (v : 'I_n)
               (b : 'I_n * constant).

(** default element *)
Variable def : constant.

(** grounding a term [t] with a substitution [s] and the default element [def] *)
Definition gr_term_def s t : constant :=
  match t with
  | Val c => c
  | Var i => odflt def (s i)
  end.

(** If, when instantiating a term [t] with a substitution [s], we obtain a constant [c],
then we obtain [c] also when grounding [t] with [s] using the default element [def]. *)
Lemma gr_term_defP c t s :
  sterm s t = Val c -> gr_term_def s t = c.
Proof. by case: t => /= [v|e [//]]; case: (s _) => // e []. Qed.

Lemma gr_term_sub t1 t2 s d (t_sub : term_vars t1 \subset term_vars t2) :
  sterm s t2 = Val d -> exists e, sterm s t1 = Val e.
Proof.
case: t2 t1 t_sub => [v2|d2] [v1|d1] /subsetP /=.
+ move/(_ v1)=> /implyP; rewrite !inE eqxx /= => /eqP->.
  by case E: (s v2) => [a|] //= _; exists a.
+ by move=> _ _; exists d1.
+ by move/(_ v1)=> /implyP; rewrite !inE eqxx.
+ by move=> _ _; exists d1.
Qed.

(** grounding a raw atom [ra] with a substitution [s] and the default element [def] *)
Definition gr_raw_atom_def s ra : raw_gatom :=
  RawGAtom (sym_atom ra) (map (gr_term_def s) (arg_atom ra)).

(** well-formedness is preserved by non-dependent grounding *)
Lemma gr_atom_def_proof s a : wf_gatom (gr_raw_atom_def s a).
Proof. by case: a => ra pf; rewrite /wf_gatom size_map. Qed.

(** grounding an atom [a] with a substitution [s] *)
Definition gr_atom_def s a : gatom := GAtom (gr_atom_def_proof s a).

(** Let [a] be an atom and [s] a substitution. If, when instantiating [a] with [s], we obtain
the ground atom [ga], then, when grounding [a] with [s] and the default element [def], we also
obtain [ga]. *)
Lemma gr_atom_defP a s ga :
  satom a s = to_atom ga -> gr_atom_def s a = ga.
Proof.
case: a ga => [[sym1 t1] pf1] [[sym2 t2] pf2] /= [hs harg].
apply/val_inj; congr RawGAtom; rewrite //=.
by elim: t1 t2 harg {pf1 pf2} => [|x1 t1 iht1] [|x2 t2] //= [] /gr_term_defP <- /iht1<-.
Qed.

(** Let [ga] be a ground atom. If we lift it to an atom and ground it with a substitution
[s] and a default element [def], [ga] is preserved. *)
Lemma gr_atom_defK ga s : gr_atom_def s (to_atom ga) = ga.
Proof.
case: ga => //= [[sym t] pf]; apply/val_inj => /=; congr RawGAtom.
by elim: t {pf} => //= a ga ->.
Qed.

(** Using default value to lift a subst to a grounding *)
Definition to_gr s : gr := [ffun v => if s v is Some c then c else def].

Definition to_sub (g : gr) : sub := [ffun v => Some (g v)].

Lemma to_subE t g : sterm (to_sub g) t = Val (gr_term g t).
Proof. by case: t => [i|d] //=; rewrite ffunE. Qed.

Lemma to_grP t s c : sterm s t = Val c -> gr_term (to_gr s) t = c.
Proof.
move/gr_term_defP; case: t => [v|e] //=.
by case E: (s v) => [a|] <-; rewrite ffunE E.
Qed.

End NoDepGrounding.

Section Match.
(** Matching functions *)

Implicit Types (s : sub) (t : term) (a : atom) (v : 'I_n)
         (b : 'I_n * constant).

(** matching a term [t] against a constant [d], starting from an initial substitution [s]. *)
Definition match_term d t s : option sub :=
  match t with
  | Val e => if d == e then Some s else None
  | Var v => if s v is Some e then
             (if d == e then Some s else None)
             else Some (add s v d)
  end.

(** Let [s1], [s2] be two substitutions. If [s2] is the result of matching a term [t]
against a constant [d], starting from an initial substitution [s1], then [s2] extends [s1]. *)
Lemma match_term_sub s1 s2 t d : match_term d t s1 = Some s2 -> sub_st s1 s2.
Proof.
case: t => //= [v|e]; last first.
  by case: eqP => _ // [->].
case E: (s1 _) => /= [a|].
  by case: eqP => _ // [->].
by case=> <-; have/eqP/sub_add := E.
Qed.

(** matching a raw atom [ra] against a ground raw atom [rga], starting from an initial substitution [s]. *)
Definition match_raw_atom s ra rga : option sub :=
  match ra, rga with
    | RawAtom s1 arg1, RawGAtom s2 arg2 =>
      if (s1 == s2) && (size arg1 == size arg2)
      then foldl (fun acc p => obind (match_term p.1 p.2) acc)
                 (Some s) (zip arg2 arg1)
      else None
  end.

(** matching an [a] against a ground atom [ga], starting from an initial substitution [s]. *)
Definition match_atom s a (ga : gatom) := match_raw_atom s a ga.

(** matching an atom [a] against all the ground atoms of an interpretation [i], starting from an
initial substitution [s] *)
Definition match_atom_all i a s :=
  [set x | Some x \in [set match_atom s a ga | ga in i]].

(** reflection lemma for atom matching *)
Lemma match_atomsP a i r s :
  reflect (exists2 ga, ga \in i & Some r = match_atom s a ga)
          (r \in match_atom_all i a s).
Proof. by rewrite inE; exact: (iffP imsetP). Qed.

(** join for the set monad *) 
Definition bindS {A B : finType} (i : {set A}) (f : A -> {set B}) : {set B} :=
  cover [set f x | x in i].

(** reflection lemma for binding *)
Lemma bindP (A B : finType) (i : {set A}) (f : A -> {set B}) (r : B) :
  reflect (exists2 s, s \in i & r \in f s) (r \in bindS i f).
Proof.
by rewrite /bindS cover_imset; exact: (iffP bigcupP); case=> s xin rin; exists s.
Qed.

(** monadic fold for the set monad: iteratively composing the result of applying a function [f],
seeded with an initial value [s0], to all elements of a list [l] *)
Fixpoint foldS {A : Type} {B : finType}
         (f : A -> B -> {set B}) (s0 : {set B}) (l : seq A) :=
  if l is [:: x & l] then bindS s0 (fun y => foldS f (f x y) l)
  else s0.

(** If functions [f] and [g] are extensionally equal, then we get the same output when binding
a set [s] with them. *)
Lemma eq_bindS (A B : finType) (f g : A -> {set B}) (s : {set A}) :
  f =1 g -> bindS s f = bindS s g.
Proof.
move=> h_f; apply/setP=> x; rewrite /bindS !cover_imset.
by apply/bigcupP/bigcupP; case=> y y_in x_in; exists y; rewrite // ?h_f // -h_f.
Qed.

(** The result of binding the union of two sets [s1] and [s2] with a function [f]
equals the result of taking the union between the binding of [s1] with [f] and
the binding of [s2] with [f] *)
Lemma bindSU (A B : finType) (f : A -> {set B}) (s1 s2 : {set A})  :
  bindS (s1 :|: s2) f = bindS s1 f :|: bindS s2 f.
Proof. by rewrite /bindS !cover_imset bigcup_setU. Qed.

(** Let [s] be a set and [f], [g] two functions. The result of taking the union
between the binding of [s] with [f] and the binding of [s] with [g] equals the 
binding of [s] with the function that returns the point-wise union of [f] and [g] application *)
Lemma bindUS (A B : finType) (f g : A -> {set B}) (s : {set A})  :
  bindS s f :|: bindS s g = bindS s (fun x => f x :|: g x ).
Proof.
rewrite /bindS !cover_imset; apply/setP=> x; rewrite !inE; apply/orP/bigcupP.
  by case=> /bigcupP[y hy hfy]; exists y; rewrite // inE hfy ?orbT.
by case=> [y hy]; rewrite inE; case/orP=> hf; [left | right]; apply/bigcupP; exists y.
Qed.

(** If [f] and [g] are extensionally equal, then the results of taking their fold over a list [l],
seeded with an initial set [s], are equal *)
Lemma eq_foldS (A : eqType) (T : finType) f g (s : {set T}) (l : seq A) :
  {in l, f =2 g} -> foldS f s l = foldS g s l.
Proof.
move=> h_f; elim: l s h_f => //= x l ihl s h_f.
have heq: (fun y : T => foldS f (f x y) l) =1
          (fun y : T => foldS g (g x y) l).
  move=> y; rewrite h_f ?inE ?eqxx ?ihl //.
  by move=> u hu k; rewrite h_f // inE hu orbT.
by rewrite (eq_bindS _ heq).
Qed.

(** The result of folding a function [f] over a list [l], starting from the union 
of sets [s1] and [s2] equals the union of folding [f] over [l] starting from [s1]
and of folding [f] over [l] starting from [s2] *)
Lemma foldSU A (T : finType) f (s1 s2 : {set T}) (l : seq A) :
  foldS f (s1 :|: s2) l = foldS f s1 l :|: foldS f s2 l.
Proof. by elim: l => //= x l ihl; rewrite bindSU. Qed.

(** matching a list of atoms [tl] agains ground atoms of an interpretation [i] *)
Definition match_body i tl : {set sub} :=
  foldS (match_atom_all i) [set emptysub] tl.

(** one iteration of fwd_chain for a one-clause program *)
Definition cons_clause (def : constant) (cl : clause) i : {set gatom} :=
  [set gr_atom_def def s (head_cl cl) | s in match_body i (body_cl cl)].

(** one iteration of fwd_chain for a program *)
Definition fwd_chain def p i : {set gatom} :=
  i :|: \bigcup_(cl <- p) cons_clause def cl i.

End Match.

(** Monotonicity lemmas for fwd_chain functions *)
Section Monotonicity.

Lemma bindS_mon {A B : finType} (i1 i2 : {set A}) (f1 f2 : A -> {set B}) :
  i1 \subset i2 -> (forall x, f1 x \subset f2 x) ->
  bindS i1 f1 \subset bindS i2 f2.
Proof.
move=> H1 H2; apply/subsetP => r; case/bindP=> u ui1 ri1.
apply/bindP; exists u; move/subsetP: H1. by apply.
by move/subsetP: (H2 u) => H _; apply: H.
Qed.

Lemma foldS_mon {A : eqType} {B : finType} (f1 f2 : A -> B -> {set B}) (l : seq A)
  (f_mon : forall x y, f1 x y \subset f2 x y) :
  (forall (s1 s2 : {set B}), (s1 \subset s2) -> foldS f1 s1 l \subset foldS f2 s2 l).
Proof. by elim: l => //= x l ihl s1 s2 hs12; apply/bindS_mon=> // y; exact/ihl. Qed.

Lemma match_atom_all_mon i1 i2 s a :
 i1 \subset i2 -> match_atom_all i1 a s \subset match_atom_all i2 a s.
Proof. by move=> s12; apply/preimsetS/imsetS. Qed.

Lemma match_body_mon i1 i2 cl :
  i1 \subset i2 -> match_body i1 (body_cl cl) \subset match_body i2 (body_cl cl).
Proof.
by move=> H; apply/foldS_mon => //; move=> u s'; apply: match_atom_all_mon.
Qed.

Lemma cons_cl_mon i1 i2 cl def :
  i1 \subset i2 -> cons_clause def cl i1 \subset cons_clause def cl i2.
Proof. by move=> Hs; rewrite //; apply/imsetS/match_body_mon. Qed.

Lemma fwd_chain_mon i1 i2 p def :
  i1 \subset i2 ->
  fwd_chain def p i1 \subset fwd_chain def p i2.
Proof.
move=> Hs; apply/setUSS/subsetP; move=> // ga /bigcup_seqP[cl cl_in /andP[ga_in _]].
apply/bigcup_seqP; exists cl => //; apply/andP; split; auto.
by move/subsetP: (cons_cl_mon cl def Hs); apply.
Qed.

End Monotonicity.

Section Increasing.

(** Forward Chain is increasing. *)
Lemma fwd_chain_inc i p def : i \subset fwd_chain def p i.
Proof. exact: subsetUl. Qed.

End Increasing.

Section Soundness.

Implicit Types (s r : sub) (d def : constant) (t : term) (a : atom)
               (ga : gatom) (tl : list atom) (cl : clause).

(** **** Term Matching Soundness: 
Let [t] be a term, [d] a constant and [s] an arbitrary substitution.
If term matching outputs a substitution [r], extending [s] with the matching of [t] against [d], then
[r] is indeed a solution, i.e, the instantiation of [t] with [r] equals [d].*)
Lemma match_term_sound d t s r : match_term d t s = Some r -> sterm r t = Val d.
Proof.
case: t => /= [v|c]; last by case: eqP => [->|].
case E: (s _) => [e|]; last by case => <-; rewrite ffunE eqxx.
by case: eqP => //->[<-]; rewrite E.
Qed.

(** List Fold Soundness *)
Lemma foldl_0_gen {A} u l r
     (f : A -> sub -> option sub)
     (f_pmon : forall x s r, f x s = Some r -> s \sub r)
 : foldl (fun acc p => obind (f p) acc) u l = Some r ->
   exists2 s, u = Some s & s \sub r.
Proof.
elim: l u => [|hd tl IHl] //= => [Hu | u Hfold].
  by exists r; [done | apply/substss].
case: (IHl (obind (f hd) u) Hfold) => [s Hbind Hsub].
case E : u => [s'|]; rewrite E //= in Hbind.
by exists s'; [done | apply/(subst_trans Hsub (@f_pmon hd s' s Hbind))].
Qed.

Lemma foldl_0 gar ar u r :
 foldl (fun acc p => obind [eta match_term p.1 p.2] acc) u (zip gar ar) = Some r ->
 exists2 s, u = Some s & s \sub r.
Proof. by apply: foldl_0_gen => x s r0; apply: match_term_sub. Qed.

(** **** Atom Matching Soundness: 
Let [a] be an atom, [ga] a ground atom and [s], an arbitrary substitution.
If atom matching outputs a substitution [r], extending [s] with the matching of [a] against [ga], then 
[r] is indeed a solution, i.e, the instantiation of [a] with [r] equals [ga]. *)
Lemma match_atom_sound a ga s r :
  match_atom s a ga = Some r -> satom a r = to_atom ga.
Proof.
case: a ga => /= [[s_a arg_a] pf_a] [[s_g arg_g] pf_g] // hma.
apply/val_inj; move: hma; rewrite /match_atom /= {pf_a pf_g}.
case: eqP => Hs //; rewrite Hs; case: eqP => Harg //=.
elim: arg_a arg_g s Harg => [| a ar iha] [| g gar] //= s [Hsize] Hf.
congr RawAtom => /=.
have [s' Hs' Hsub] := foldl_0 Hf; rewrite Hs' in Hf.
have [->] := iha _ _ Hsize Hf.
by have/sterm_sub-> := (match_term_sound Hs').
Qed.

(** **** Atom Matching Substitution Lemma: 
If [s2] is the result of matching an atom [a] against 
a ground atom [ga], starting from an initial substitution [s1], then [s2] is the extension of [s1]. *)
Lemma match_atom_sub s1 s2 a ga :
  match_atom s1 a ga  = Some s2 -> sub_st s1 s2.
Proof.
rewrite/match_atom.
case: a ga => [[s_a arg_a] pf_a] [[s_g arg_g] pf_g].
rewrite /match_raw_atom /=.
case: eqP => // Hs //=.
case: eqP => // Harg //=.
move/foldl_0=> [s' Hs' Hsub].
by injection Hs' => H; rewrite H; apply/Hsub.
Qed.

(** substitution domain: set of all variables it binds *)
Definition dom s := [set v : 'I_n | s v].

Lemma to_sub_grt def t nu :
  gr_term_def def (to_sub nu) t = gr_term nu t.
Proof. by case: t=> [var | val] //=; rewrite ffunE. Qed.

Lemma to_sub_gra def a nu :
  gr_atom_def def (to_sub nu) a = gr_atom nu a.
Proof.
case: a=> [[sym args] pf_a]; apply/val_inj; congr RawGAtom.
by apply/eq_map=> x; apply/to_sub_grt.
Qed.

Lemma sub_dom_grt t s :
  term_vars t \subset dom s <-> exists c, sterm s t = Val c.
Proof.
case: t=> [var|val]; split; rewrite ?(sub0set, sub1set, inE) //=.
+ by case: (s var) => [c|]=> c'//=; exists c.
+ by case: (s var) => [c|] //; case=> //.
+ by exists val.
Qed.

Lemma sub_dom_gra (ra : raw_atom) s :
  reflect (exists gra, sraw_atom ra s = to_raw_atom gra)
          (raw_atom_vars ra \subset dom s).
Proof.
case: ra => [sym args]; apply: (iffP idP).
  elim: args => [|t arg iha]; first by exists (RawGAtom sym [::]).
  rewrite /raw_atom_vars big_cons subUset => /andP[/sub_dom_grt [c Hc] /iha] [[sy l] [->]] H.
  by exists (RawGAtom sy (c :: l)); congr RawAtom; rewrite /= Hc H.
elim: args => [| a arg iha]; first by rewrite /raw_atom_vars big_nil sub0set.
case=> [[sga [|ga gal]] // [hs hga hgal]].
rewrite /raw_atom_vars big_cons subUset iha ?andbT; first by apply/sub_dom_grt; exists ga.
by exists (RawGAtom sym gal); congr RawAtom; rewrite /= hgal.
Qed.

Lemma sub_dom_raw a s :
  (exists gra : raw_gatom, sraw_atom a s = to_raw_atom gra) ->
   exists ga : gatom, satom a s = to_atom ga.
Proof.
case=> ga sha.
have pf_ga: wf_gatom ga.
  case: ga a sha => [s' arg'] [[sa aa] pfa] [h1 h2].
  rewrite /wf_gatom /= -h1.
  have -> // : size arg' = size aa.
  by move/(congr1 size): h2; rewrite !size_map.
by exists (GAtom pf_ga); apply/val_inj.
Qed.

Lemma sub_dom_ga (a : atom) s :
  reflect (exists ga, satom a s = to_atom ga)
          (atom_vars a \subset dom s).
Proof.
have [h|h]:= (sub_dom_gra a s).
  by left; apply: sub_dom_raw.
right; case=> [ga hga]; apply: h.
by exists ga; case: a hga => a /= pf /(congr1 val).
Qed.

Implicit Types (ss : {set sub}).

Definition match_pbody tl i ss0 := foldS (match_atom_all i) ss0 tl.

Lemma match_pbody_cons a l i r ss0 :
  reflect (exists2 s, s \in ss0 & r \in match_pbody l i (match_atom_all i a s))
          (r \in match_pbody (a :: l) i ss0).
Proof. exact: bindP. Qed.

Lemma match_body_pbody tl i r :
  match_body i tl = match_pbody tl i [set emptysub].
Proof. by rewrite /match_pbody /match_body. Qed.

Lemma sub_st_add v d s' s :
  s' \sub s -> s v = Some d -> s' v = None -> add s' v d \sub s.
Proof.
move=> Hsub Hs Hs'; apply/forallP=> v'; rewrite /add ffunE.
case: eqP => [->| Hv]; first exact/eqP.
by move/forallP in Hsub; apply/Hsub.
Qed.

(** **** Term Matching Completeness: 
Given a solution [s] to term-matching [t] w.r.t [d],
for any sub-substitution [s'], there exists an [r] that is a solution
 and also better/minimal w.r.t [s] *)
Lemma match_term_complete d t s s' :
 sub_st s' s -> sterm s t = Val d ->
 exists r, match_term d t s' = Some r /\ sub_st r s.
Proof.
case: t=> /= [v|c] // => Hsub //; last first.
  by case=> [->] //; exists s'; split; [case: eqP | done].
case Hs : (s _)  => [e|] //; case=> He //; rewrite -He {d He}.
case Hs': (s' _) => [e'|] //.
     by exists s'; case: eqP=> He //; last first;
     move/substE in Hsub;
     have Hsub' := (Hsub e' v Hs');
     rewrite Hs in Hsub'; injection Hsub';
     rewrite //= Hsub.
by exists (add s' v e); split; [done | apply/sub_st_add].
Qed.

(** **** Atom Matching Completeness: 
Let [a] be an atom, [ga] a ground atom and [s] a substitution
that instantiates [a] to [ga]. Then, seeding the atom matching algorithm with [s'], an arbitrary restriction
of [s], outputs a better matching solution than [s], i.e, a substitution [r] that is smaller or equal to [s]. *)
Lemma match_atom_complete ga a s s' :
 sub_st s' s -> satom a s = to_atom ga ->
 exists2 r, match_atom s' a ga = Some r & sub_st r s.
Proof.
case: a ga => [[s_a arg_a] pfa] [[s_g arg_g] pfs] //= Hsub [hsym Harg].
rewrite /match_atom /= hsym eqxx /=.
have ->: size arg_a = size arg_g.
  by move/(congr1 size): Harg; rewrite !size_map.
rewrite eqxx {s_a s_g hsym pfa pfs}.
elim: arg_a arg_g s' Hsub Harg => [| h l IHl] [| gh gl] //= s' Hsub.
  by exists s'.
case; move=> Ht Hl.
have [r' [Hs'r Hr]] := match_term_complete Hsub Ht.
have [r'' H Hr_sub] := IHl _ _ Hr Hl.
by exists r''; rewrite // Hs'r.
Qed.

(** Let [a] be an atom, [ga] a ground atom and [v] a grounding. Instantiating [a] with the coercion of
[v] equals the lifting of [ga] iff the grounding of [a] with [v] equals [ga] *)
Lemma to_gr_atomP a v ga :
  satom a (to_sub v) = to_atom ga <-> gr_atom v a = ga.
Proof.
case: a ga => [[s_a arg_a] pfa] [[s_g arg_g] pfg];
split; case => hs harg; apply/val_inj => /= {pfa pfg}.
  congr RawGAtom => //=.
  elim: arg_g arg_a harg => [|ag arg_g ihag] [|aa arg_a] //.
  by rewrite /= to_subE => -[->] ha; rewrite ihag.
congr RawAtom => //=.
elim: arg_g arg_a harg => [|ag arg_g ihag] [|aa arg_a] //.
by rewrite /= to_subE => -[->] ha; rewrite ihag.
Qed.

Lemma match_ptl_complete s' ss0 i cl v :
 s' \in ss0 -> sub_st s' (to_sub v) ->
 all (mem i) (body_gcl (gr_cl v cl)) ->
 exists2 r, r \in match_pbody (body_cl cl) i ss0 &
            sub_st r (to_sub v).
Proof.
case: cl => head body //=.
elim: body s' ss0 => [| hd tl] => //= [ | IHl ] s' ss0  Hs' H_sub H_mem //.
  exists s'; [exact: Hs' | exact: H_sub].
case/andP: H_mem => [H_in H_mem].
have HH : exists2 ga, ga \in i & gr_atom v hd = ga.
  by exists (gr_atom v hd).
case: HH=> [ga Hga_in Hga].
move/to_gr_atomP in Hga.
have [r' Hr' Hr'_sub] := (@match_atom_complete ga hd (to_sub v) s' H_sub Hga).
have Hr'_all : r' \in match_atom_all i hd s'.
  by apply/match_atomsP; exists ga.
have [s Hs Hs_sub] := IHl r' (match_atom_all i hd s') Hr'_all Hr'_sub H_mem.
by exists s; [apply/match_pbody_cons; exists s' | done].
Qed.

Lemma match_tl_complete i cl v :
 all (mem i) (body_gcl (gr_cl v cl)) ->
 exists2 r, r \in match_pbody (body_cl cl) i [set emptysub] &
                  sub_st r (to_sub v).
Proof.
by apply/(@match_ptl_complete emptysub); [rewrite inE| exact/subst0s].
Qed.

(** Let [ss0] be a substitution set. If [r] is in the result of extending substitutions in [ss0]
with bindings matching the [tl] atom list against the ground atoms of an interpretation [i], then
there exists a substitution [s] in [ss0] that [r] extends. *)
Lemma match_atom_all_sub tl i r ss0 :
 r \in match_pbody tl i ss0 ->
  exists2 s, s \in ss0 & sub_st s r.
Proof.
elim: tl ss0 => [| a l IHl] //=.
by rewrite /match_pbody /foldS; exists r.
rewrite /match_pbody //=.
move=> ss0. move/bindP => Hr.
case: Hr => [s Hs Hr] //.
have [s' H_in Hs'] := (IHl (match_atom_all i a s) Hr).
exists s. exact: Hs.
move/match_atomsP in H_in.
case: H_in=> [ga Hga HH].
move/esym in HH.
apply: subst_trans (match_atom_sub HH).
exact: Hs'.
Qed.

(** Let [r] in the result of extending substitutions in [ss0]
with bindings matching the [tl] atom list against the ground atoms of an interpretation [i].
Then, there exists a ground atom list [gtl], such that [gtl] is the instantiation of [t] with [r]
and all the atoms in [gtl] are in [i]. *)
Lemma match_pbody_sound tl i r ss0 :
  r \in match_pbody tl i ss0 ->
      exists2 gtl, stail tl r = [seq to_atom ga | ga <- gtl]
                   & all (mem i) gtl.
Proof.
elim: tl ss0 => [|a l IHl] /=.
  by exists [::].
move=> ss0.
case/match_pbody_cons => /= [s0 Hs0 Hrs].
have /= [gtl [H_tl H_mem]] := (IHl (match_atom_all i a s0) Hrs) => {IHl}.
have [s Hs Hsub] := match_atom_all_sub Hrs.
have/match_atomsP [ga Hga] := Hs.
exists (ga :: gtl).
rewrite H_tl //=.
move/esym in q.
move: (match_atom_sound q) => H.
have H_r := satom_sub Hsub H.
by rewrite H_r.
by rewrite /= H_mem Hga.
Qed.

Lemma r_dom_term d t r : sterm r t = Val d -> term_vars t \subset dom r.
Proof.
case: t => [v|c] //=; last by rewrite sub0set.
by rewrite sub1set inE; case: (r v).
Qed.

Lemma r_dom_atom a ga r : satom a r = to_atom ga -> atom_vars a \subset dom r.
Proof.
case: a ga => [[sym args] pfa] [[gsym gargs] pfg] [hs harg].
rewrite /atom_vars /= hs {pfa pfg hs}.
elim: args gargs harg => [ | a args IHa] [ | ga gargs] //=.
  by rewrite /raw_atom_vars big_nil sub0set.
by rewrite /raw_atom_vars big_cons subUset; case=> /r_dom_term -> /IHa.
Qed.

Lemma seq_inj T (x y : T) (xs ys : seq T) :
  [:: x & xs] = [:: y & ys] -> x = y /\ xs = ys.
Proof. by case. Qed.

Lemma r_dom_body tl gtl r : stail tl r = [seq to_atom ga | ga <- gtl] ->
                            tail_vars tl \subset dom r.
Proof.
elim: tl gtl => [ | a arg IHa] [ | ga gargs] //=.
  by rewrite /tail_vars big_nil sub0set.
move=> hl; have [/r_dom_atom hs /IHa hha] := seq_inj hl.
by rewrite /tail_vars big_cons subUset hs hha.
Qed.

Lemma match_tl_sound tl i r :
  r \in match_body i tl ->
        exists2 gtl, stail tl r = [seq to_atom ga | ga <- gtl]
                     & all (mem i) gtl.
Proof. exact/match_pbody_sound. Qed.

(** **** Clause Consequence Soundness: 
Let [cl] be a safe clause and [i] an interpretation.
If the clause consequence operator derives no new facts from [cl], then [i] is a model for [cl].*)
Lemma cons_cl_sound def cl i :
  safe_cl cl -> cons_clause def cl i \subset i -> cl_true cl i .
Proof.
move=> h_safe; rewrite /cons_clause => /subsetP h_fp v.
apply/implyP=> h_tl; apply/h_fp/imsetP=> {h_fp}.
have [r r_in_match r_sub_v] := match_tl_complete h_tl.
exists r; first by [].
case: cl h_safe h_tl r_in_match => /= hd tl h_safe h_tl r_in_match.
have [gtl Hgtl _] := match_tl_sound r_in_match.
have h_g : exists ga, satom hd r = to_atom ga.
  exact/sub_dom_ga/(subset_trans h_safe)/r_dom_body/Hgtl.
rewrite -(to_sub_gra def hd v); case: h_g => ga hga.
have h1 := (gr_atom_defP def hga).
have h_sub := satom_sub r_sub_v hga.
have h2 := (gr_atom_defP def h_sub).
by rewrite h1 h2.
Qed.

(** **** Forward Chain Soundness: 
Let [p] be a safe program and [i] an interpretation.
If [i] is the fixpoint of one iteration of forward chain, then [i] is a model for [p]. *)
Lemma fwd_chain_sound def p i :
  prog_safe p -> fwd_chain def p i = i -> prog_true p i .
Proof.
move/allP=> h_safe /setUidPl /bigcups_seqP => h_cls ?.
  by apply/allP=> ? h; apply: (cons_cl_sound (h_safe _ h)); apply: h_cls.
Qed.

Lemma to_gr_sub def t s : gr_term_def def s t = gr_term (to_gr def s) t.
Proof. by case: t=> [var | val] //=; rewrite ffunE //=. Qed.

Lemma gr_atom_defE def s a : gr_atom (to_gr def s) a = gr_atom_def def s a.
Proof.
case: a => [[s_a arg_a] pfa] //=; apply/val_inj => /=; congr RawGAtom.
elim: arg_a {pfa} => [ |t arg_a IHl] //=.
by rewrite IHl; congr cons; rewrite to_gr_sub.
Qed.

Lemma tail_mem def s tl gtl i :
 stail tl s = [seq to_atom ga | ga <- gtl] ->
 all (mem i) gtl ->
 all (mem i) [seq gr_atom (to_gr def s) x | x <- tl].
Proof.
elim: tl gtl => [ | h l] Hl gtl //= H_mem //=.
move: H_mem; case: gtl=> [ | gh gl] //.
rewrite map_cons => hss /andP[hin hmem]; have [hhd htl]:= seq_inj hss.
apply/andP; split.
  by rewrite gr_atom_defE (gr_atom_defP def hhd).
by apply/(Hl gl htl hmem).
Qed.

(** **** Clause Consequence Stability: 
Let [cl] be a clause and [i] an interpretation satisfying [c].
Then, the clause consequence operator derives no new facts from [cl]. *)
Lemma cons_cl_stable def cl i : cl_true cl i -> cons_clause def cl i \subset i.
Proof.
rewrite/cl_true/cons_clause/gcl_true //= => Hclause.
rewrite sub_imset_pre.
apply/subsetP=> s /match_tl_sound [gtl Htl Hmem].
have Hcl := Hclause (to_gr def s); move/implyP in Hcl.
by rewrite inE -gr_atom_defE; apply/Hcl/tail_mem; last exact: Hmem.
Qed.

(** Let [p] be a program. Any interpretation [i] that is a model of [p] is a fixpoint of one iteration of forward chain *)
Lemma fwd_chain_stable def p i : prog_true p i -> fwd_chain def p i = i.
Proof.
move=> p_true; apply/setUidPl/bigcups_seqP=> cl h_in _.
by apply/cons_cl_stable=> v; have/allP := p_true v; exact.
Qed.

(** Forward Chain reflection lemma: Given a safe program [p], an interpretation [i]
is a model of [p] iff it is a fixpoint of one iteration of forward chain. *)
Lemma fwd_chainP def p i (p_safe : prog_safe p) :
  reflect (prog_true p i) (fwd_chain def p i == i).
Proof. apply/(iffP eqP); [exact: fwd_chain_sound | exact: fwd_chain_stable]. Qed.

(** Given a program [p] and an interpretation [i]. The symbols in the strict result (without [i]) of applying forward
chain on [p] given [i] are among the head symbols of [p]. *)
Lemma sym_pengine_subset_hsymp def p i :
  {subset sym_i ((fwd_chain def p i) :\: i) <= hsym_prog p}.
Proof.
move=> s; case/imsetP=> ga; rewrite !inE => /andP [/negbTE h].
rewrite h; case/bigcup_seqP=> cl cl_in. rewrite andbT.
by case/imsetP=> nu nu_in -> ->; apply/mapP; exists cl.
Qed.

(** **** Forward Chain Extensionality: 
If two programs [p1] and [p2] are extensionally equal, then
the output of forward chain on [p1] equals that on [p2]. *)
Lemma eq_fwd_chain def p1 p2 i :
  p1 =i p2 -> fwd_chain def p1 i = fwd_chain def p2 i.
Proof.
by move=> h; apply/setP=> ga; rewrite !inE (eq_big_idem _ _ (@setUid _) h).
Qed.

(** **** Forward Chain Decomposition: 
The result of applying forward chain on the concatenation of
programs [p1] and [p2], given an interpretation [i] equals the union of forward chain on [p1] given [i]
with forward chain on [p2] given [i]. *)
Lemma fwd_chain_cat def p1 p2 i :
  fwd_chain def (p1 ++ p2) i = fwd_chain def p1 i :|: fwd_chain def p2 i.
Proof. by apply/setP=> ga; rewrite ?(big_cat, inE) orbACA orbb. Qed.

(** Let [ga] be a ground atom in the output of applying forward chain on [p], given [i].
Then, either [ga] is in [i] or its symbol among the head symbols in [p]. *)
Lemma fwd_chain_sym def p i ga :
  (ga \in fwd_chain def p i) ->
  (ga \in i) || (sym_gatom ga \in hsym_prog p).
Proof.
case: (ga \in i) / boolP => [|/negbTE h] /=.
  by rewrite /fwd_chain !inE => ->.
rewrite inE h => /bigcup_seqP[cl ?].
rewrite andbT; case/imsetP=> ? ? ->.
by apply/mapP; exists cl.
Qed.

(** Let [ga] be a ground atom in the output of iterating the application of forward chain on [p],
given [i], [k] times. Then, either [ga] is in [i] or its symbol is among the head symbols in [p]. *)
Lemma iter_fwd_chain_sym def p i ga k :
  (ga \in iter k (fwd_chain def p) i) ->
  (ga \in i) || (sym_gatom ga \in hsym_prog p).
Proof.
by elim: k=> [-> //|k h] /fwd_chain_sym /orP [/h|->]; rewrite ?orbT.
Qed.

(** Atom Matching Decomposition: 
Let [i1], [i2] be two interpretations,
The substitution set extending a substitution [s] with bindings matching [a]
against the union of [i1] and [i2] equals the union of the substitution set
extending [s] with bindings matching [a] against [i1] with that extending [s]
with bindings matching [a] against [i2]. *)
Lemma match_atom_allU s a i1 i2 :
  match_atom_all (i1 :|: i2) a s =
  match_atom_all i1 a s :|:
  match_atom_all i2 a s.
Proof.
apply/setP=> nu; rewrite !inE; apply/imsetP/orP.
  by case=> ga; rewrite !inE; case/orP=> /mem_imset ha ->; auto.
by case=> /imsetP[ga] hga hnu; exists ga; rewrite ?inE ?hga ?orbT.
Qed.

Definition sym_tl tl := [seq sym_atom (val x) | x <- tl].

(** Atom Matching Modularity: 
Let [i1], [i2] be two interpretations.
If the symbol of an atom [a] does not appear among those in [i2], then
extending a substitution [nu] with bindings matching [a] against the union of [i1] and [i2]
equals that of extending [nu] with bindings matching [a] against [i1]. *)
Lemma match_atom_all_strata nu a i1 i2 :
  sym_atom a \notin sym_i i2 ->
  match_atom_all (i1 :|: i2) a nu =
  match_atom_all i1 a nu.
Proof.
move=> h_dis; apply/setP=> nnu; rewrite !inE imsetU !inE.
suff -> : Some nnu \in [set match_atom nu a ga | ga in i2] = false.
  by rewrite orbF.
apply/imsetP=> -[ga gain /esym] /match_atom_sound /(congr1 (sym_atom \o val)) h.
by case/negP: h_dis; apply/imsetP; exists ga.
Qed.

(** Body Matching Modularity: 
Let [tl] be an atom list and [i1], [i2] interpretations.
If the symbols in [tl] do not appear in [i2], then the result of matching [tl] against
the union of [i1] with [i2] equals the result of matching [tl] against [i1]. *)
Lemma match_body_strata tl i1 i2 :
  [disjoint sym_tl tl & sym_i i2] ->
  match_body (i1 :|: i2) tl = match_body i1 tl.
Proof.
move=> h_dis; apply: eq_foldS => a a_in nu.
apply: match_atom_all_strata => {nu}.
rewrite disjoint_has in h_dis.
apply: contra h_dis; case/imsetP=> ga hga /= hs.
apply/hasP; exists (sym_atom a).
  by apply/mapP; exists a.
by apply/imsetP; exists ga.
Qed.

Open Scope SET.

(** **** Forward Chain Modularity: 
Let [p] be a program and [i], [ip] interpretations.
If [i] is a model for [p] and the symbols in [p] do not appear in [ip], then the
result of applying forward chain on [p], starting from the union of [i] with [ip]
adds no new facts. *)
Lemma fwd_chain_mod def p i ip
      (h_tr   : prog_true p i)
      (h_strata : [disjoint sym_prog p & sym_i ip]) :
  fwd_chain def p (i :|: ip) = i :|: ip.
Proof.
have U := (fwd_chain_stable def h_tr).
rewrite /fwd_chain /cons_clause in U *.
suff E: \bigcup_(cl <- p) ([set gr_atom_def def s (head_cl cl)
                        | s in match_body (i :|: ip) (body_cl cl)]) =
        \bigcup_(cl <- p) ([set gr_atom_def def s (head_cl cl)
                        | s in match_body i (body_cl cl)]).
  by rewrite E -{3}U [i :|: bigop _ _ _]setUC setUAC [_ :|: i]setUC.
set f1 := bigop _ _ _.
set f2 := bigop _ _ _.
rewrite [f1]big_seq_cond [f2]big_seq_cond {f1 f2 U}.
apply: eq_bigr => cl; rewrite andbT => cl_in.
suff -> : match_body (i :|: ip) (body_cl cl)  =
          match_body i (body_cl cl) by [].
apply: match_body_strata.
rewrite !disjoint_has in h_strata *.
apply: contra h_strata; case/hasP=> s hst hs.
apply/hasP; exists s; last by [].
by apply/flatten_mapP; exists cl; rewrite // inE hst orbT.
Qed.

(** Lemmas about forward chain iteration. *)
Lemma iter_fwd_chain_stable def pp i k
  (h_tr : prog_true pp i) :
  iter k (fwd_chain def pp) i = i.
Proof.
elim: k i h_tr => [|ns ihns] ci hstb //=.
by rewrite ihns // fwd_chain_stable.
Qed.

Lemma iter_fwd_chain_subset def pp i k :
  i \subset iter k (fwd_chain def pp) i.
Proof.
elim: k => //= k ihk; rewrite (subset_trans (fwd_chain_inc i pp def)) //.
exact: fwd_chain_mon.
Qed.

End Soundness.
End Datalog.


Lemma fix_iter T (f : T -> T) n s (s_fix : s = f s) : s = iter n f s.
Proof. by elim: n => //= n {1}<-. Qed.

Lemma iter_leq_fix T (f : T -> T) x n m (i_eq: iter n f x = iter n.+1 f x) :
  n <= m -> iter m f x = iter m.+1 f x.
Proof. by move=>/subnK<-; elim: {m}(m-n) => //= m {2}<-. Qed.

(* note: minsetP lemma subsumes all this *)
Section iter_mon.

Variables (T : finType).
Implicit Types (s : {set T}) (f : {set T} -> {set T}).

Definition monotone   f := forall s1 s2, s1 \subset s2 -> f s1 \subset f s2.

Definition increasing f := forall s, s \subset f s.

Variables (f : {set T} -> {set T}) (f_mon : monotone f).

Lemma iter_mon n : monotone (iter n f).
Proof. by elim: n => // n ihn s1 s2 /= s_in; exact/f_mon/ihn. Qed.

Variable (lb : {set T}) (f_lb : forall s, lb \subset s -> lb \subset f s).

Definition iterf n := iter n f lb.

Lemma subset_iterf m n : m <= n -> iterf m \subset iterf n.
Proof.
move/subnK<-; rewrite /iterf addnC iter_add; apply/iter_mon.
by elim: {n m} (n-m); [rewrite ?fsubset_refl | move=> n ihn; apply/f_lb].
Qed.

End iter_mon.

Section Fixpoints.

Variables (T : finType) (s0 ub : {set T}).

Hypothesis (s0_bound : s0 \subset ub).

Implicit Types (s : {set T}) (f : {set T} -> {set T}).

Variables (f : {set T} -> {set T}).

Definition ubound := forall s, s  \subset ub -> f s \subset ub.

Hypothesis (f_mono : monotone f) (f_inc : increasing f) (f_ubound: ubound).

Notation iterf_incr n := (iterf f s0 n).
Notation lfp_incr     := (iterf f s0 #|ub|).

Lemma iterf_incr_bound n : (iterf_incr n) \subset ub.
Proof. by elim: n => /= [|n ihn]; rewrite ?lb_bound ?f_ubound //=. Qed.

(** Adapted from the lfpE lemma in http://www.ps.uni-saarland.de/extras/jaritp14/
   (C) Christian Doczkal and Gert Smolka *)
Lemma lfpE : lfp_incr = f lfp_incr.
Proof.
suff/exists_eqP: [exists k : 'I_#|ub|.+1 , iterf_incr k == iterf_incr k.+1].
   case=> k E; exact/(iter_leq_fix E)/leq_ord.
apply/contraT; rewrite negb_exists => /forallP /= H.
have/(_ #|ub|.+1 (leqnn _)): forall k , k <= #|ub|.+1 -> k <= #|iterf_incr k|.
  elim=> // n IHn Hn.
  rewrite (leq_ltn_trans (IHn (ltnW Hn))) ?proper_card //.
  rewrite properEneq subset_iterf // ?andbT.
  exact: H (Ordinal Hn).
  move=> s hs; have := f_mono hs; have := f_inc s0.
  apply: subset_trans.
rewrite leqNgt ltnS subset_leq_card ?f_ubound //.
exact/iterf_incr_bound.
Qed.

Lemma min_lfp_all s (hs : s0 \subset s) (sfp : s = f s) : lfp_incr \subset s.
Proof. by rewrite (fix_iter #|ub| sfp); apply/iter_mon. Qed.

Lemma has_lfp :
  { lfp : {set T} | lfp = f lfp
                  /\ lfp = iter #|ub| f s0
                  /\ forall s', s0 \subset s' -> s' = f s' -> lfp \subset s'}.
Proof.
by exists lfp_incr; rewrite -lfpE /lfp_incr; repeat split; apply/min_lfp_all.
Qed.

End Fixpoints.

Section Completeness.

Variable n   : nat.
Variable st  : finType.
Variable ct  : finType.
Variable def : constant ct.
Variable ar  : {ffun st -> nat}.
Variable p   : program n ct ar.

Hypothesis p_safe : prog_safe p.

Notation gatom := (gatom ct ar).
Definition bp : {set gatom} := setT.

(** Proof that B(P) is a model of the safe program [p]. *)
Lemma bpM : prog_true p bp.
Proof. by move=> gr; apply/allP=> cl cl_in; apply/implyP; rewrite inE. Qed.

Lemma fwd_chain_complete :
{ m : {set gatom} &
{ n : nat | [/\ prog_true p m
              , m = iter n (fwd_chain def p) set0
              & forall m', prog_true p m' -> m \subset m']}}.
Proof.
have h_inc : increasing (fwd_chain def p).
  by move=> i; apply: fwd_chain_inc.
have h_mon := fwd_chain_mon p def.
have h_fp  := fwd_chain_stable def bpM.
have h_ub  :  ubound bp (fwd_chain def p).
  by move=> ss H; rewrite subsetT.
have h_lb  : set0 \subset bp by rewrite /bp.
have [m [m_fix [m_def m_min]]] := has_lfp h_lb h_mon h_inc h_ub.
exists m, #|bp|; do ! split; auto.
  exact/(fwd_chain_sound p_safe)/esym/m_fix.
by move=> m' /(fwd_chain_stable def)/esym/m_min; apply; rewrite sub0set.
Qed.

Print Assumptions fwd_chain_complete.

(** **** Forward Chain Completeness: 
Let [p] be a safe program. The iterative forward chain
inference engine terminates (after iterating as many times as there are elements in B(P)) 
and outputs a minimal model for [p]. *)
Lemma incr_fwd_chain_complete (s0 : {set gatom}) :
{ m : {set gatom} &
{ n : nat | [/\ prog_true p m
              , n = #|bp|
              , m = iter n (fwd_chain def p) s0
              & forall (m' : {set gatom}), s0 \subset m' -> prog_true p m' -> m \subset m']}}.
Proof.
have h_inc : increasing (fwd_chain def p).
  by move=> i; apply: fwd_chain_inc.
have h_mon := fwd_chain_mon p def.
have h_fp  := fwd_chain_stable def bpM.
have h_ub  :  ubound bp (fwd_chain def p).
  by move=> ss H; rewrite subsetT.
have h_lb  : s0 \subset bp by rewrite /bp.
have [m [m_fix [m_def m_min]]] := has_lfp h_lb h_mon h_inc h_ub.
exists m, #|bp|; do ! split; auto.
  exact/(fwd_chain_sound p_safe)/esym/m_fix.
by move=> m' hs /(fwd_chain_stable def)/esym/m_min; apply.
Qed.

End Completeness.

Module Exports.

Canonical cons_subType.
Canonical cons_eqType.
Canonical cons_choiceType.
Canonical cons_countType.
Canonical cons_subCountType.
Canonical cons_finType.
Canonical cons_subFinType.
Canonical raw_gatom_eqType.
Canonical raw_gatom_choiceType.
Canonical raw_gatom_countType.
Canonical gatom_subType.
Canonical gatom_eqType.
Canonical gatom_choiceType.
Canonical gatom_countType.
Canonical gatom_subCountType.
Canonical gatom_finType.
Canonical gatom_subFinType.
Canonical term_eqType.
Canonical term_choiceType.
Canonical raw_atom_eqType.
Canonical raw_atom_choiceType.
Canonical atom_subType.
Canonical atom_eqType.
Canonical atom_choiceType.
Canonical clause_eqType.
Canonical clause_choiceType.
End Exports.
