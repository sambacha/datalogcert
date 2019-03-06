(************************************************************************************)
(**                                                                                 *)
(**                             The DatalogCert Library                             *)
(**                                                                                 *)
(**             CNRS & Université Paris-Sud, Université Paris-Saclay            *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require pengine.
Module P := pengine.
Import P.Exports.

Coercion P.ua  : P.atom  >-> P.raw_atom.
Coercion P.uga : P.gatom >-> P.raw_gatom.

(** * Stratified Datalog in Coq *)
Section DataLog.

Variable n        : nat.
Variable constype : finType.
Variable symtype  : finType.
Variable arity    : {ffun symtype -> nat}.

(** Syntax and Enconding *)
Section Syntax.

Definition psymtype := [finType of bool * symtype].

Definition parity : {ffun psymtype -> nat} :=
  [ffun ps => arity ps.2].

Definition constant  := P.constant constype.

Definition      gatom := P.gatom constype arity.
Definition     pgatom := P.gatom constype parity.

Definition raw_gatom  := P.raw_gatom constype symtype.
Definition raw_pgatom := P.raw_gatom constype psymtype.

Implicit Types (ga : gatom) (pga : pgatom) (gra : raw_gatom).

Definition sym_gatom  := P.sym_gatom.
Definition arg_gatom  := P.arg_gatom.
Definition size_gatom ga  := size (arg_gatom ga).

Definition gatom_eta  := P.gatom_eta.

(** Ground Literals *)
Inductive glit := GLit of bool * gatom.

Definition gatom_glit gl := let: GLit (_, ga) := gl in ga.
Definition flag_glit  gl := let: GLit (b, _)  := gl in b.
Definition sym_glit   gl := sym_gatom (gatom_glit gl).

Section GLitChoiceType.

Definition glit_rep l := let: GLit s := l in s.
Definition glit_pre l := let: s      := l in GLit s.
Lemma glit_repK : cancel glit_rep glit_pre.
Proof. by case. Qed.

Canonical glit_eqType     := Eval hnf in EqType     glit (CanEqMixin     glit_repK).
Canonical glit_choiceType := Eval hnf in ChoiceType glit (CanChoiceMixin glit_repK).

End GLitChoiceType.

(** Ground Clauses *)
Inductive  gclause       := GClause of gatom & seq glit.
Definition head_gcl gcl  := let: GClause h b := gcl in h.
Definition body_gcl gcl  := let: GClause h b := gcl in b.
Definition hsym_gcl gcl  := sym_gatom (val (head_gcl gcl)).
Definition bsym_gcl gcl  := [seq sym_glit x | x <- body_gcl gcl].
Definition sym_gcl  gcl  := hsym_gcl gcl :: bsym_gcl gcl.

Notation interp  := {set  gatom}.
Notation pinterp := {set pgatom}.

Implicit Types (i m : interp) (gcl : gclause).

Definition glit_true i l :=
  if flag_glit l then gatom_glit l \in i else gatom_glit l \notin i.

Definition gcl_true gcl i :=
  all (glit_true i) (body_gcl gcl) ==> (head_gcl gcl \in i).

(** Terms *)
Definition term      := P.term n constype.

Definition atom      := P.atom n constype arity.
Definition patom     := P.atom n constype parity.

Definition raw_atom  := P.raw_atom n constype symtype.
Definition raw_patom := P.raw_atom n constype psymtype.

Implicit Types (a : atom) (pa : patom).

Definition sym_atom  := P.sym_atom.
Definition arg_atom  := P.arg_atom.
Definition size_atom (a : atom) := size (arg_atom a).

(** Open literals *)
Inductive lit :=
  | Lit of bool * atom.

Definition of_lit l := let: Lit l := l in l.

Canonical lit_subType     := Eval hnf in [newType for of_lit].
Canonical lit_eqType      := Eval hnf in EqType _     [eqMixin     of lit by <: ].
Canonical lit_choiceType  := Eval hnf in ChoiceType _ [choiceMixin of lit by <:].
Canonical lit_finType     := Eval hnf in ChoiceType _ [choiceMixin of lit by <:].

Definition sym_lit  l := let: Lit (_, a) := l in sym_atom (val a).
Definition flag_lit l := let: Lit (b, _) := l in b.
Definition atom_lit l := let: Lit (_, a) := l in a.

(** Open clauses *)
Inductive clause : Type := Clause of atom & seq lit.

Definition clause_rep cl := let: Clause hd tl := cl in (hd, tl).
Definition clause_pre cl := let: (hd, tl)     := cl in Clause hd tl.
Lemma clause_repK : cancel clause_rep clause_pre.
Proof. by case. Qed.

Canonical clause_eqType     := Eval hnf in EqType     clause (CanEqMixin     clause_repK).
Canonical clause_choiceType := Eval hnf in ChoiceType clause (CanChoiceMixin clause_repK).

(** Program *)
Definition program     := seq clause.
Definition head_cl  cl := let: Clause h _ := cl in h.
Definition body_cl  cl := let: Clause _ b := cl in b.

Definition hsym_cl cl := sym_atom (val (head_cl cl)).
Definition bsym_cl cl := [seq sym_lit x | x <- body_cl cl].
Definition sym_cl  cl := hsym_cl cl :: bsym_cl cl.

Definition hsym_prog p := [seq hsym_cl cl | cl <- p].
Definition bsym_prog p := flatten [seq bsym_cl cl | cl <- p].
Definition sym_prog  p := flatten [seq  sym_cl cl | cl <- p].

Definition atoms_cl cl  := head_cl cl :: [seq atom_lit l | l <- body_cl cl].
Definition atoms_prog p := flatten [seq  atoms_cl cl  | cl <- p].

Implicit Types (ss : {set symtype}).

Definition slice_prog p ss := [seq cl <- p | hsym_cl cl \in ss].
Definition lits_prog  p    := flatten [seq body_cl cl | cl <- p].
Definition nlit_prog  p    := [seq l <- lits_prog p | ~~ flag_lit l].

Lemma slice_progU p ss1 ss2 :
  slice_prog p (ss1 :|: ss2) =i slice_prog p ss1 ++ slice_prog p ss2.
Proof. by move=> cl; rewrite mem_cat !mem_filter !inE andb_orl. Qed.

Lemma slice_progP p ss : {subset hsym_prog (slice_prog p ss) <= ss}.
Proof. by move=> ? /mapP[?]; rewrite mem_filter; case/andP=> ?? ->. Qed.

End Syntax.

Section Grounding.

Definition gr := P.gr n constype.

Implicit Types (nu : gr) (t : term) (a : atom) (cl : clause).

Definition gr_term nu t  := P.gr_term nu t.
Definition gr_atom nu a  := P.gr_atom nu a.
Definition gr_lit  nu l  := GLit (flag_lit l, gr_atom nu (atom_lit l)).
Definition gr_cl   nu cl := GClause (gr_atom nu (head_cl cl)) (map (gr_lit nu) (body_cl cl)).

Lemma bsyms_gr_clause gr cl :
  bsym_gcl (gr_cl gr cl) = bsym_cl cl.
Proof.
case: cl => hd bd; rewrite /bsym_cl /bsym_gcl /gr_cl /=.
by rewrite -map_comp; apply eq_in_map=> [[]] [b a] hl.
Qed.

End Grounding.

Section Semantics.

(** Semantics of Stratified Datalog *)

Definition cl_true cl i  := forall nu : gr, gcl_true (gr_cl nu cl) i.

Definition prog_true p i :=
  forall nu : gr, all (fun cl => gcl_true (gr_cl nu cl) i) p.

Lemma eq_prog_true p1 p2 (hp : p1 =i p2) i :
  prog_true p1 i <-> prog_true p2 i.
Proof. by split=> pt nu; [rewrite -(eq_all_r hp)| rewrite (eq_all_r hp)].
Qed.

End Semantics.

(** Encoding to positive programs *)
Section Encoding.

Definition pclause  : Type := P.clause  n constype parity.
Definition pgclause : Type := P.gclause   constype parity.
Definition pprogram : Type := P.program n constype parity.

Notation interp  := {set gatom}.
Notation pinterp := {set pgatom}.
Notation cinterp := (interp * interp)%type.

Implicit Types (def : constant) (s : symtype) (ps : psymtype).
Implicit Types (ss : {set symtype})
               (pss : {set psymtype}).

Implicit Types (c : constant) (t : term).
Implicit Types (gr : gr).

Implicit Types (a : atom) (pa : patom) (ga : gatom) (pga : pgatom).
Implicit Types (l : lit) (gl : glit).
Implicit Types (cl : clause) (pcl : pclause).
Implicit Types (p : program) (pp : pprogram).
Implicit Types (i : interp) (pi : pinterp) (ci : cinterp).

Lemma psym_mon (pp1 pp2 : pprogram) :
  {subset pp1 <= pp2} ->
  {subset P.sym_prog pp1 <= P.sym_prog pp2}.
Proof.
move=> hsub ?. case/flatten_mapP => cl ha /mapP [a ? ->].
apply/flatten_mapP; exists cl; first exact: hsub.
by apply/mapP; exists a.
Qed.

Definition flag_psym ps := let: (b, _) := ps in b.
Definition  sym_psym ps := let: (_, s) := ps in s.

Definition encodes s  := (true, s).
Definition uncodes ps := sym_psym ps.

Definition flag_pgatom pga := flag_psym (P.sym_gatom (val pga)).
Definition  sym_pgatom pga := sym_psym  (P.sym_gatom (val pga)).

Prenex Implicits sym_atom sym_gatom P.head_cl P.body_cl.

Section GenAtom.

Notation gen_ratom := (P.raw_atom n constype).
Notation gen_atom := (P.atom n constype).

Notation gen_rgatom := (P.raw_gatom constype).
Notation gen_gatom  := (P.gatom constype).

Definition map_raw_atom_sym (st1 st2 : finType)
           (f : st1 -> st2) (gena : gen_ratom st1) :
  gen_ratom st2 := P.RawAtom (f (sym_atom gena)) (arg_atom gena).

Lemma map_raw_atom_proof
  (st1 st2 : finType)
  (ar1 : {ffun st1 -> nat})
  (ar2 : {ffun st2 -> nat})
  (f : st1 -> st2)
  (har : forall x, ar1 x = ar2 (f x))
  (gena : gen_atom ar1) :
 P.wf_atom ar2 (map_raw_atom_sym f gena).
Proof. by case: gena => [[s arg] pf]; rewrite /P.wf_atom -har. Qed.

Definition map_atom_sym
           (st1 st2 : finType)
           (ar1 : {ffun st1 -> nat})
           (ar2 : {ffun st2 -> nat})
           (f : st1 -> st2)
           (har : forall x, ar1 x = ar2 (f x))
           (gena : gen_atom ar1) := P.Atom (map_raw_atom_proof har gena).

Definition map_raw_gatom_sym (st1 st2 : finType)
           (f : st1 -> st2) (gena : gen_rgatom st1) :
  gen_rgatom st2 := P.RawGAtom (f (sym_gatom gena)) (arg_gatom gena).

Lemma map_raw_gatom_proof
  (st1 st2 : finType)
  (ar1 : {ffun st1 -> nat})
  (ar2 : {ffun st2 -> nat})
  (f : st1 -> st2)
  (har : forall x, ar1 x = ar2 (f x))
  (gena : gen_gatom ar1) :
 P.wf_gatom ar2 (map_raw_gatom_sym f gena).
Proof. by case: gena => [[s arg] pf]; rewrite /P.wf_gatom -har. Qed.

Definition map_gatom_sym
           (st1 st2 : finType)
           (ar1 : {ffun st1 -> nat})
           (ar2 : {ffun st2 -> nat})
           (f : st1 -> st2)
           (har : forall x, ar1 x = ar2 (f x))
           (gena : gen_gatom ar1) := P.GAtom (map_raw_gatom_proof har gena).

End GenAtom.

Lemma arP  x : arity x = parity (encodes x).
Proof. by rewrite ffunE. Qed.

Lemma parP x : parity x = arity (uncodes x).
Proof. by rewrite ffunE. Qed.

Definition encodea  := map_atom_sym  arP.
Definition uncodea  := map_atom_sym parP.

Definition encodega := map_gatom_sym  arP.
Definition uncodega := map_gatom_sym parP.

Definition flips ps := let: (b, s) := ps in (~~b, s).

Lemma farP  x : parity x = parity (flips x).
Proof. by case: x => b s /=; rewrite !ffunE. Qed.

Definition flipa  := map_atom_sym  farP.
Definition flipga := map_gatom_sym farP.

Definition encodel (l : lit)  : patom :=
  let: Lit (b, a) := l         in
  let: pa         := encodea a in
  if b then pa else flipa pa.

Definition uncodel pa  :=
  let: a         := uncodea pa in
  if flag_psym (sym_atom pa) then Lit (true, a) else Lit (false, a).

Definition encodegl (gl : glit)  : pgatom :=
  let: GLit (b, a) := gl         in
  let: pga          := encodega a in
  if b then pga else flipga pga.

Definition encodecl cl :=
  P.Clause ((encodea \o head_cl) cl) [seq encodel l | l <- body_cl cl].

Definition uncodecl pcl :=
  Clause ((uncodea \o P.head_cl) pcl) [seq uncodel l | l <- P.body_cl pcl].

Definition encodegcl gcl : pgclause :=
  P.GClause ((encodega \o head_gcl) gcl) [seq encodegl gl | gl <- body_gcl gcl].

Definition encodep (p : program) : pprogram := [seq encodecl cl | cl <- p].

Definition uncodep (p : pprogram) : program := [seq uncodecl cl | cl <- p].

(** Monotonicity properties *)
Lemma encodep_mon p1 p2 :
  {subset p1 <= p2} -> {subset (encodep p1) <= (encodep p2)}.
Proof.
  by move=> hp ?; rewrite/encodep; case/mapP=> ? ? ->; apply: map_f; exact: hp.
Qed.

Lemma uncodesK ps : reflect (encodes (uncodes ps) = ps) (flag_psym ps).
Proof. by case: ps => [[] s] //=; constructor. Qed.

Lemma uncodesKn ps : reflect (flips (encodes (uncodes ps)) = ps) (~~ flag_psym ps).
Proof. by case: ps => [[] s] //=; constructor. Qed.

Lemma encodegaK : cancel encodega uncodega.
Proof.
by move=> ga; apply/val_inj; case: ga => [[? ?] ?] /=; congr P.RawGAtom.
Qed.

Lemma encodegafK : cancel (flipga \o encodega) uncodega.
Proof.
by move=> ga; apply/val_inj; case: ga => [[? ?] ?] /=; congr P.RawGAtom.
Qed.

Lemma inj_iff T U x y (f : T -> U) (f_inj : injective f) :
  f x = f y <-> x = y.
Proof. by split=> [/f_inj|->]. Qed.

Lemma uncodegaK pga :
  reflect (encodega (uncodega pga) = pga) (flag_pgatom pga).
Proof.
have U := inj_iff (encodega (uncodega pga)) pga val_inj.
apply: (equivP _ U) => /= {U}.
apply: (equivP (uncodesK _)).
split; case: pga => [[s arg] pf] => /= hyp; [congr P.RawGAtom; auto|].
by case: hyp.
Qed.

Lemma uncodegaKn pga :
  reflect (flipga (encodega (uncodega pga)) = pga) (~~ flag_pgatom pga).
Proof.
have U := inj_iff (flipga (encodega (uncodega pga))) pga val_inj.
apply: (equivP _ U) => /= {U}.
apply: (equivP (uncodesKn _)).
split; case: pga => [[s arg] pf] => /= hyp; [congr P.RawGAtom; auto|].
by case: hyp.
Qed.

Lemma uncodegaKD : {in flag_pgatom, cancel uncodega encodega}.
Proof. by move=> x /uncodegaK. Qed.

Lemma uncodegaKDn : {in predC flag_pgatom, cancel uncodega (flipga \o encodega)}.
Proof. by move=> x /uncodegaKn. Qed.

Lemma encodeaK : cancel encodea uncodea.
Proof. by case=> [[s l] pf]; apply/val_inj. Qed.

Definition pos_sym (x : psymtype) := let: (_, x) := x in (true, x).

Lemma posAR ps : parity ps = parity (pos_sym ps).
Proof. by case: ps => s b; rewrite !ffunE. Qed.

Lemma uncodeaK pa : encodea (uncodea pa) = map_atom_sym posAR pa.
Proof.
apply/val_inj; case: pa => [[sym args] pf] /=.
by congr P.RawAtom; case: sym {pf}.
Qed.

Lemma encodelK : cancel encodel uncodel.
Proof.
case=> [[[] a]]; congr (Lit (_,_)) => /=.
  by rewrite encodeaK.
by case: a => [[s l] pf]; apply/val_inj.
Qed.

Lemma uncodelK : cancel uncodel encodel.
Proof.
move=> -[[[] s] t arg ?]; apply/val_inj.
by rewrite /uncodel; case: ifP => //= hfl; congr P.RawAtom; rewrite hfl.
Qed.

Lemma encodeclK : cancel encodecl uncodecl.
Proof.
case=> [[]] => /= s arg bd; congr Clause.
  exact: encodeaK.
by rewrite -map_comp map_id_in // => y _; exact: encodelK.
Qed.

Definition hd_cl_pos pcl := flag_psym (P.hsym_cl pcl).

Lemma uncodeclK : {in hd_cl_pos, cancel uncodecl encodecl}.
Proof.
case=> [hd bd] hcl_pos; congr P.Clause.
  rewrite /= uncodeaK; apply/val_inj => /=.
  by case: hd hcl_pos => [[[[] s] args] pf] h.
by rewrite -map_comp map_id_in //; move=> x hx; exact: uncodelK.
Qed.

Lemma encodepK : cancel encodep uncodep.
Proof. exact: (mapK encodeclK). Qed.

Lemma cl_encodep pcl p : pcl \in encodep p -> pcl \in hd_cl_pos.
Proof. by case/mapP=> [hd /= _] ->. Qed.

Lemma mem_encodep p :
  {in hd_cl_pos, forall pcl, pcl \in encodep p = (uncodecl pcl \in p)}.
Proof.
move=> pcl h; rewrite -{1}[pcl]uncodeclK ?mem_map //.
exact: can_inj encodeclK.
Qed.

Lemma mem_uncodep pp cl :
  encodecl cl \in pp -> cl \in uncodep pp.
Proof. by move=> hcl; apply/mapP; exists (encodecl cl); rewrite ?encodeclK. Qed.

Lemma encodes_hsym s p :
  encodes s \in P.hsym_prog (encodep p) -> s \in hsym_prog p.
Proof.
case/mapP=> pcl h_in hs; apply/mapP; exists (uncodecl pcl).
  by rewrite -mem_encodep //; case: pcl hs {h_in} => -[[[f sy] args] wf] tl [].
by case: pcl h_in hs => -[[[f sy] args] wf] tl _ [].
Qed.

Lemma uncodes_hsym ps pp :
  ps \in P.hsym_prog pp -> (uncodes ps) \in hsym_prog (uncodep pp).
Proof.
case/mapP=> pcl h_pcl->; apply/mapP; exists (uncodecl pcl) => //.
by apply/mapP; exists pcl.
Qed.

Lemma mem_sym_prog s p :
  (encodes s) \in P.sym_prog (encodep p) -> s \in sym_prog p.
Proof.
case/flatten_mapP=> pcl hpcl /mapP [pa hpa] hs.
apply/flatten_mapP; exists (uncodecl pcl).
  by rewrite -mem_encodep ?(cl_encodep hpcl).
move: hpa; rewrite inE; case/orP => [/eqP hpa|hpa]; rewrite inE; apply/orP.
  left; case: pa hs hpa => [ [[f sa] args] wf] //= [hf ->].
  by rewrite /uncodecl /hsym_cl /= => <-.
right; case: pa hs hpa => [ [[f sa] args] wf] //= [hf ->].
move=> uh; apply/mapP. exists (uncodel (P.Atom wf)) => //.
  by apply/mapP; exists (P.Atom wf).
by rewrite /uncodel; case: ifP.
Qed.

Lemma gr_atomE nu a :
  encodega (gr_atom nu a) = P.gr_atom nu (encodea a).
Proof. exact/val_inj. Qed.

Lemma gr_litE nu l :
  encodegl (gr_lit nu l) = P.gr_atom nu (encodel l).
Proof. case: l => -[[] l]; exact/val_inj. Qed.

Lemma gr_clauseE nu cl :
  encodegcl (gr_cl nu cl) = P.gr_cl nu (encodecl cl).
Proof.
by congr P.GClause; [exact: gr_atomE|rewrite -!map_comp; apply/eq_map/gr_litE].
Qed.

Section Safety.

Definition term_vars := P.term_vars.
Definition atom_vars := P.atom_vars.
Definition lit_vars  l  : {set 'I_n} := atom_vars (atom_lit l).
Definition tail_vars tl : {set 'I_n} := \bigcup_(t <- tl) lit_vars t.

Definition cl_safe cl := atom_vars (head_cl cl) \subset tail_vars (body_cl cl).

Definition prog_safe p := all cl_safe p.

Lemma sliced_prog_safe p ss : prog_safe p -> prog_safe (slice_prog p ss).
Proof.
rewrite/slice_prog=> /allP h; apply/allP=> ?; rewrite mem_filter;
by case/andP=> _ ?; apply: h.
Qed.

Lemma atom_varsE a : atom_vars a = P.atom_vars (encodea a).
Proof. by []. Qed.

Lemma lit_varsE l : lit_vars l = P.atom_vars (encodel l).
Proof. by rewrite/lit_vars atom_varsE; case: l; do 2! case. Qed.

Lemma tail_varsE tl : tail_vars tl = P.tail_vars [seq encodel l | l <- tl].
Proof. by rewrite/P.tail_vars big_map; apply: eq_bigr; move=> i _; exact: lit_varsE. Qed.

Lemma encode_cl_safe cl : cl_safe cl = P.safe_cl (encodecl cl).
Proof. by rewrite/P.safe_cl/cl_safe atom_varsE tail_varsE. Qed.

Lemma encode_prog_safe p : prog_safe p = P.prog_safe (encodep p).
Proof. by rewrite/P.prog_safe all_map; apply/eq_all/encode_cl_safe. Qed.

End Safety.

Section Complemented.

(** **** Complements and their properties *)

(** Symbol collection for an interpretation *)
Definition isyms i : {set symtype} := [set sym_gatom (val ga) | ga in i].

(** Reflection lemma for the symbol collection of an interpretation *)
Lemma isymsP s i :
  reflect (exists2 ga, (ga \in i) & (sym_gatom ga == s)) (s \in isyms i).
Proof.
apply/(iffP idP).
  by case/imsetP=> ga hga hs; exists ga=>//; rewrite hs.
by case=> ga hga /eqP hs; apply/imsetP; exists ga=>//.
Qed.

(** Symbol collection for interpretation union *)
Lemma isymsU i1 i2 : isyms (i1 :|: i2) = isyms i1 :|: isyms i2.
Proof. exact: imsetU. Qed.

Lemma isymsI i1 i2 : isyms (i1 :&: i2) \subset isyms i1 :&: isyms i2.
Proof.
apply/subsetP=> s; rewrite inE; case/imsetP=> ga; rewrite inE.
by case/andP=> h1 h2 ->; rewrite !mem_imset.
Qed.

(** Soundness of interpretation symbol collection *)
Lemma mem_isyms i ga : ga \in i -> sym_gatom ga \in isyms i.
Proof. by move=> h_in; apply/imsetP; exists ga. Qed.

(** Symbol collection for cinterpretation *)
Definition ci_syms ci : {set symtype} := isyms ci.1 :|: isyms ci.2.

(** Slicing interpretations with a given symbol *)
Definition slice_inter s i : interp := [set x in i | sym_gatom x == s].

(** Reflection lemma for slicing interpretations with a symbol *)
Lemma slice_interP s i ga :
  (ga \in slice_inter s i) = (ga \in i) && (sym_gatom ga == s).
Proof. by rewrite inE. Qed.

(** Slicing setT with a given symbol *)
Definition all_gatoms s : interp := [set x : gatom | sym_gatom x == s].

(** Slicing soundness lemma *)
Lemma setT_slice s : all_gatoms s = slice_inter s setT.
Proof. by rewrite /slice_inter setIdE setTI. Qed.

(** Slicing interpretation with a set of symbols *)
Definition i_ssym ss i : interp := [set x in i | sym_gatom x \in ss].

(** Slicing reflection lemma *)
Lemma i_ssymP ss i ga :
  reflect (ga \in i /\ sym_gatom ga \in ss)
          (ga \in i_ssym ss i).
Proof. by apply/(iffP idP); rewrite !inE; case/andP; try split. Qed.

Lemma i_ssym0 ss : i_ssym ss set0 = set0.
Proof. by apply/setP=> ?; rewrite !inE. Qed.

(** Slicing interpretation union *)
Lemma i_ssymU ss i1 i2 :
  i_ssym ss (i1 :|: i2) = i_ssym ss i1 :|: i_ssym ss i2.
Proof. by apply/setP=> ga; rewrite !inE andb_orl. Qed.

(** Slicing interpretation intersection *)
Lemma i_ssymI ss i1 i2 :
  i_ssym ss (i1 :&: i2) = i_ssym ss i1 :&: i_ssym ss i2.
Proof. by apply/setP=> ga; rewrite !inE andbACA andbb. Qed.

(** Slicing interpretation difference *)
Lemma i_ssymD ss i1 i2 : i_ssym ss (i1 :\: i2) = i_ssym ss i1 :\: i_ssym ss i2.
Proof.
by apply/setP=> ga; rewrite !inE negb_and andbCA andb_orl andNb orbF andbCA andbA.
Qed.

(** Slicing is idempotent *)
Lemma i_ssym_idem ss i : i_ssym ss (i_ssym ss i) = i_ssym ss i.
Proof. by rewrite /i_ssym !setIdE -setIA setIid. Qed.

(** Slicing of an interpretation [i] with a set of symbols [ss] is empty
   if [ss] and the set of symbols in [i] are disjoint *)
Lemma isyms_ssym ss i : isyms (i_ssym ss i) = ss :&: isyms i.
Proof.
rewrite /i_ssym !setIdE; apply/setP=> s; rewrite !inE.
apply/imsetP/idP=> [[ga]|]; rewrite ?inE; case/andP=> h1 h2.
  by move->; rewrite mem_imset ?h2.
by case/imsetP: h2 => ga hga hgs; exists ga; rewrite // !inE hga -hgs.
Qed.

Lemma i_ssymIT ss i : ss :&: isyms i = set0 -> i_ssym ss i = set0.
Proof. by rewrite -isyms_ssym; move/eqP; rewrite imset_eq0; move/eqP. Qed.

(** Slicing of an interpretation [i] with a symbols set [ss] is a subset
   of the slicing of setT with [ss] *)
Lemma i_ssymST ss i : i_ssym ss i \subset i_ssym ss setT.
Proof. by rewrite /i_ssym !setIdE setTI subsetIr. Qed.

(** Complemented slicing of an interpretation with a symbol set *)
Definition ic_ssym ss i := i_ssym ss (~: i).

(** Reflection lemma for the complemented slicing of an interpretation
  with a set of symbols *)
Lemma ic_ssymP ss i ga :
  reflect (ga \notin i /\ sym_gatom ga \in ss)
          (ga \in ic_ssym ss i).
Proof. by apply: (iffP (i_ssymP _ _ _)); rewrite inE. Qed.

(** Soundness lemma for the complemented slicing of an interpretation
   with a symbol set *)
Lemma icK_ssym ss i : ic_ssym ss i = i_ssym ss setT :\: i_ssym ss i.
Proof. by rewrite -i_ssymD setTD. Qed.

(** Complemented slicing of an intepretation union with a symbol set *)
Lemma ic_ssymU ss i1 i2 :
  ic_ssym ss (i1 :|: i2) = ic_ssym ss i1 :&: ic_ssym ss i2.
Proof. by rewrite /ic_ssym setCU i_ssymI. Qed.

(** Slicing and complemented slicing and disjoint *)
Lemma ic_ssymIC ss i : i_ssym ss i :&: ic_ssym ss i = set0.
Proof. by rewrite -i_ssymI setICr i_ssym0. Qed.

(** Complemented slicing of setT with a set of symbols is empty *)
Lemma ic_ssymT ss i : ic_ssym ss setT = set0.
Proof. by rewrite /ic_ssym setCT i_ssym0. Qed.

(** Slicing setT with symbol set [ss] equals the slicing of an interpretation [i]
    with [ss] if [ss] and the set of symbols in [i] are disjoint *)
Lemma ic_ssymIT ss i : ss :&: isyms i = set0 -> ic_ssym ss i = i_ssym ss setT.
Proof. by rewrite icK_ssym => /i_ssymIT ->; rewrite setD0. Qed.

(** Union of slicing and complemented slicing of an interpretation [i] with [ss]
   equals the slicing of setT with [ss] *)
Lemma ic_ssymUC ss i : i_ssym ss i :|: ic_ssym ss i = i_ssym ss setT.
Proof. by rewrite /ic_ssym -i_ssymU setUCr. Qed.

(** Slicing an interpretation [i] with [ss] is invariant wrt
   complemented slicing with [ss] *)
Lemma ic_ssymK ss i : i_ssym ss (ic_ssym ss i) = ic_ssym ss i.
Proof. exact: i_ssym_idem. Qed.

(** Symbols of the (complemented) slicing of an interpretation [i] with [ss]
   are a subset of [ss] *)
Lemma ic_symsS ss i : isyms (ic_ssym ss i) \subset ss.
Proof. by rewrite isyms_ssym subsetIl. Qed.

Lemma i_symsS ss i : isyms (i_ssym ss i) \subset ss.
Proof. by rewrite isyms_ssym subsetIl. Qed.

(** Slicing an interpretation [i] with [ss] equals the
   complemented slicing of the complement of [i] with [ss] *)
Lemma iCic_ssym ss i : i_ssym ss i = ic_ssym ss (~: i).
Proof. by rewrite /ic_ssym setCK. Qed.

(** Slicing the complement of an interpretation [i] with [ss] equals
   the complemented slicing of [i] with [ss] *)
Lemma icCi_ssym ss i : i_ssym ss (~: i) = ic_ssym ss i.
Proof. by rewrite iCic_ssym setCK. Qed.

(* Well-complemented cinterp *)
Definition ciC ss ci : cinterp := (ci.1, ic_ssym ss ci.1 :|: ci.2).

(** **** Bijection on interpretations *)

(** Transforming a cinterp, i.e pairing of positive and negative-flag atoms
   into a pinterp containg only positive-flag atoms *)
Definition c2p ci : pinterp :=
  [set encodega             ga | ga in ci.1 ] :|:
  [set (flipga \o encodega) ga | ga in ci.2 ].

(** Transforming a pinterp into a cinterp by separating
   the positive and negative-flag atoms *)
Definition p2c pi : cinterp :=
  ([set uncodega ga | ga in pi &    flag_pgatom ga],
   [set uncodega ga | ga in pi & ~~ flag_pgatom ga]).

(** p2c is left inverse of c2p *)
Lemma c2pK : cancel c2p p2c.
Proof.
case=> ci1 ci2; congr (_,_); apply/setP => ga; apply/imsetP/idP.
+ case=> pga; rewrite !inE => /andP[/orP hor /uncodegaK hga] ha.
  case: hor => /imsetP /= [ega egain] hega.
    by rewrite ha hega ?(encodegaK, encodegafK).
  by move/uncodegaK: hga; rewrite hega; case: ega {hega egain}.
+ by move=> gain; exists (encodega ga); rewrite ?encodegaK // !inE mem_imset.
+ case=> pga; rewrite !inE => /andP[/orP hor /uncodegaKn hga] ha.
  case: hor => /imsetP /= [ega egain] hega.
    by move/uncodegaKn: hga; rewrite hega; case: ega {hega egain}.
  by rewrite ha hega ?(encodegaK, encodegafK).
+ move=> gain; exists ((flipga \o encodega) ga); rewrite ?encodegafK // !inE andbC //.
  by rewrite mem_imset // orbT.
Qed.

(** c2p is left inverse of p2c *)
Lemma p2cK : cancel p2c c2p.
Proof.
move=> x; apply/setP=> pga; rewrite !inE; apply/orP/idP; first case.
+ case/imsetP=> ga; case/imsetP => ega; rewrite inE => /andP[xin].
  by move=> /uncodegaK hflag -> ->; rewrite hflag.
+ case/imsetP=> ga; case/imsetP => ega; rewrite inE => /andP[xin].
  by move=> /uncodegaKn hflag -> ->; rewrite /= hflag.
case: (flag_pgatom pga) / boolP; [left|right]; apply/imsetP.
  exists (uncodega pga).
    by apply/imsetP; exists pga; rewrite // inE p H.
  by move/uncodegaK: p => ->.
exists (uncodega  pga).
  by apply/imsetP; exists pga; rewrite // inE i H.
by move/uncodegaKn: i => {1}<-.
Qed.

(** c2p transformation is bijective *)
Lemma c2p_bij : bijective c2p.
Proof. exact: Bijective c2pK p2cK. Qed.

(** Reflection lemma for c2p transformation *)
Lemma ciP pga ci : pga \in (c2p ci) =
                           if flag_pgatom pga then (uncodega pga) \in ci.1
                           else (uncodega pga) \in ci.2.
Proof.
apply/idP/idP.
  by rewrite !inE; case/orP; case/imsetP => [ga ga_in ->] /=;
     rewrite ?encodegaK ?encodegafK.
by rewrite !inE; case: ifP=> hf ha; apply/orP; [left|right];
   apply/imsetP; exists (uncodega pga); rewrite // ?uncodegaKD ?uncodegaKDn // inE hf.
Qed.

(** Monotonicity of c2p transformation *)
Lemma c2p_mon ci1 ci2 :
 ci1.1 \subset ci2.1 -> ci1.2 \subset ci2.2 -> c2p ci1 \subset c2p ci2.
Proof. by move => c1 c2; rewrite setUSS ?imsetS. Qed.

(** c2p transformations are subsets if the corresponding components are subsets *)
Lemma c2pS ci1 ci2 :
  c2p ci1 \subset c2p ci2 = (ci1.1 \subset ci2.1) && (ci1.2 \subset ci2.2).
Proof.
apply/subsetP/andP=> [hs| [h1 h2] pga].
+ split; apply/subsetP=> ga hga.
    by move: (hs (encodega ga)); rewrite !ciP /= encodegaK; apply.
  by move: (hs ((flipga \o encodega) ga)); rewrite !ciP encodegafK; apply.
+ by rewrite !ciP -!fun_if; apply: subsetP; case: ifP.
Qed.

(** Characterization of injective function image *)
Lemma f_imset (T1 T2 : finType) (f : T1 -> T2)
      (f_inj : injective f) (x : T1) (A : {set T1}) :
  (f x \in f @: A) = (x \in A).
Proof.
apply/imsetP/idP; first by case=> w win /f_inj->.
by move=> w; exists x.
Qed.

(** Characterization of c2p membership of an encoded ground literal *)
Lemma encodelitP gl ci :
  (encodegl gl \in c2p ci) =
  (gatom_glit gl \in (if flag_glit gl then ci.1 else ci.2)).
Proof.
case: ifP; case: gl => -[[] a] //= _.
by rewrite !inE orb_idr (f_imset (can_inj encodegaK))  //; case/imsetP.
by rewrite !inE orb_idl (f_imset (can_inj encodegafK)) //; case/imsetP.
Qed.

(** **** Strata and their properties *)
Section Strata.

Definition strata := seq {set symtype}.

(** negative dependency condition: a symbol [s] is not among those of
negated atom in a program [p] *)
Definition negdep s p := s \in [seq sym_lit l | l <- nlit_prog p].

(** positive dependency condition: the set of symbols in the body of a clause
[cl] is a subset of a given symbol set [ss] *)
Definition posdep ss cl := bsym_cl cl \subset ss.

(** stratification conditions *)
Fixpoint is_strata_rec p str acc :=
  match str with
  | [::]      => [set x in sym_prog p] == acc
  | ss :: str => [&& is_strata_rec p str (acc :|: ss)
                   , [disjoint acc & ss]
                   , all (predC (negdep^~(slice_prog p (acc :|: ss)))) (enum ss)
                   & all (posdep (acc :|: ss)) (slice_prog p (acc :|: ss))
                 ]
  end.

Definition is_strata p str := is_strata_rec p str set0.

(** imposing the additional non-emptiness condition for strata, i.e, a stratification
thus has finitely many elements. *)
Definition is_strata_strong p str :=
  is_strata_rec p str set0 && all (predC1 set0) str.

(** Automatic generation of strata: all possible strata *)
Definition strata_type := { s_l : 'I_#|symtype|.+1 & s_l.-tuple {set symtype} }.

Definition sttl (x : strata_type) : seq {set symtype} := projT2 x.

Definition compute_strata p : option strata :=
  omap sttl [pick x : strata_type | is_strata_strong p (sttl x)].

(** If strata does not contain empty sets, we can establish the corresponding
reflection characterization, by a cardinality argument *)
Lemma compute_strataP p :
  if compute_strata p is Some str
  then is_strata_strong p str
  else ~~ [exists x : strata_type, is_strata_strong p (sttl x)].
Proof.
rewrite /compute_strata; case: pickP => //= hs.
by rewrite negb_exists; apply/forallP=> s; rewrite hs.
Qed.

Lemma mem_bodies_prog p1 p2
  (h_sub : {subset p1 <= p2}) :
  {subset lits_prog p1 <= lits_prog p2}.
Proof.
move=> l; case/flatten_mapP=> cl /h_sub hin2 lin.
by apply/flatten_mapP; exists cl.
Qed.

Lemma mem_neglit p1 p2
  (h_sub : {subset p1 <= p2}) :
  {subset nlit_prog p1 <= nlit_prog p2}.
Proof.
move=> x; rewrite !mem_filter => /andP[->].
by move/(mem_bodies_prog h_sub).
Qed.

Lemma mem_negdep s p1 p2 (h_sub : {subset p1 <= p2}) :
  negdep s p1 -> negdep s p2.
Proof.
case/mapP => l /(mem_neglit h_sub) l_in ->.
by apply/mapP; exists l.
Qed.

Lemma sliced_prog_negdep p ss :
  all (predC (negdep^~ p))                (enum ss) ->
  all (predC (negdep^~(slice_prog p ss))) (enum ss).
Proof.
apply: sub_all => s; apply/contra/mem_negdep => x.
by rewrite mem_filter; case/andP.
Qed.

End Strata.

(** **** Auxiliary results for the main proof *)

Lemma cup_decomp (K : finType) (i : {set K}) :
  i = (\bigcup_(x in i) [set x])%SET.
Proof.
apply/setP=> x; apply/idP/bigcupP.
  by move=> xin; exists x; rewrite ?mem_enum ?inE.
by case=> [u uin]; rewrite inE => /eqP->.
Qed.

Lemma bigcup_enum (T : finType) (P : {set T} -> Prop) ss
      (F : symtype -> {set T}) :
  P (\bigcup_(s <- enum ss) F s) ->
  P (\bigcup_(s in ss) F s).
Proof. by rewrite big_filter. Qed.

Lemma fcup_filter (K : finType) (J : finType) (ss : {set K}) (i : {set J})
      (P : K -> J -> bool)
      (hP : forall ix, ix \in i -> exists2 s, s \in ss & P s ix) :
  i = \bigcup_(s in ss) [set x in i | P s x].
Proof.
apply/setP=> x; apply/idP/bigcupP=> [ xin | [y yin]].
  by have [s sin hp] := hP _ xin; exists s => //; rewrite inE xin hp.
by rewrite inE => /andP[->].
Qed.

Lemma fcup_decomp (K : finType) (i : {set K}) :
  i = \bigcup_(x in i) [set x].
Proof.
apply/setP=> x; apply/idP/bigcupP=> [w|[w win]].
  by exists x; rewrite ?inE.
by rewrite in_set1 => /eqP->.
Qed.

(** **** Properties of a single step of the positive engine, AKA pengine_step *)
Definition bp : pinterp := setT.

Definition pengine_step pdef pp ci0 :=
  p2c (iter #|bp| (P.fwd_chain pdef pp) (c2p ci0)).

Definition is_min_pmodel pi pp ci0 :=
  forall pi', (c2p ci0) \subset pi' -> P.prog_true pp pi' -> pi \subset pi'.

(** The pengine needs three conditions: soundness, minimality & boundeness *)
Lemma pengine_trueP pdef pp ci0
      (p_safe: P.prog_safe pp) :
  [/\ P.prog_true pp (c2p (pengine_step pdef pp ci0))
   ,  is_min_pmodel (c2p (pengine_step pdef pp ci0)) pp ci0
   &  c2p (pengine_step pdef pp ci0) \subset bp].
Proof.
have [m [n' [h_true h_step h_fix h_bound] ]] :=
  P.incr_fwd_chain_complete pdef p_safe (c2p ci0).
rewrite /pengine_step p2cK.
repeat split.
+ by rewrite h_step in h_fix; rewrite h_fix in h_true.
+ rewrite/is_min_pmodel=> pi h_spi h_pi.
  rewrite -h_step -h_fix; exact: h_bound.
+ by rewrite -h_step -h_fix subsetT.
Qed.

(** **** Well-Complementation:
 A complemented interpretation [ci] is _well-complemented_ w.r.t a set of symbols [ss],
 if all well-formed atoms using [ss]-symbols are in at least one of the components of [ci]. *)
Section Part.

Variable (T : finType).

Implicit Types (A B S : {set T}) (f : {set T} -> {set T}).

Definition part A B S := (A :|: B == S) && (A :&: B == set0).

Lemma partP A B S x : part A B S -> x \in S -> (x \in A) || (x \in B).
Proof. by move=> /andP[/eqP<- _]; rewrite inE. Qed.

Definition partf f A B S := (f A :|: f B == f S) && (f A :&: f B == set0).

Lemma partfP f A B S x : partf f A B S -> x \in f S -> (x \in f A) || (x \in f B).
Proof. by move=> /andP[/eqP<- _]; rewrite inE. Qed.

End Part.

(** well-complementation property *)
Definition ci_wc ss ci := partf (i_ssym ss) ci.1 ci.2 setT.

(** Let [ss] be a symbol set, [ga] a ground atom and [ci] a complemented interpretation.
If the symbol of [ga] is in [ss] and [ci] is well-complemented w.r.t [ss], then
either 1) [ga] is in the subset of the positive component [ci.1] of [ci] whose symbols
are in [ss] or 2) [ga] in the subset of the negative component [ci.2] of [ci] whose symbols
are in [ss]. *)
Lemma wfP ss ci ga (hsym : sym_gatom ga \in ss) :
  ci_wc ss ci -> (ga \in i_ssym ss ci.1) || (ga \in i_ssym ss ci.2).
Proof.
move/partfP=> h; move: (h ga); rewrite !inE !andTb=> hh.
by move: (hh hsym); rewrite !hsym !andbT; case/orP=> -> //; apply/orP; right.
Qed.

(** **** Properties of the complementation step *)

Definition sanitize_model ci := ci.1.

Section WellComplemented.

Variable (ci : cinterp).
Variable (sp ss : {set symtype}).
Let ssp := (sp :|: ss).

Variable (h_ci_wc : ci_wc sp ci).

Definition ciU ci1 ci2 := (ci1.1 :|: ci2.1, ci1.2 :|: ci2.2).

Notation "A :||: B" := (ciU A B) (at level 52, left associativity) : set_scope.

Lemma issymU ss1 ss2 i1 i2 :
  isyms i1 \subset ss1 -> isyms i2 \subset ss2 ->
  i_ssym (ss1 :|: ss2) (i1 :|: i2) = i_ssym ss1 i1 :|: i_ssym ss2 i2.
Proof.
rewrite !sub_imset_pre => /subsetP h1 /subsetP h2; apply/setP=> ga.
move: (h1 ga) (h2 ga); rewrite !inE.
case: (ga \in i1) / boolP => [? -> | _ _] //.
case: (ga \in i2) / boolP => [? -> | _ _] //.
by rewrite /= orbT.
Qed.

Lemma issymUT ss1 ss2 :
  i_ssym (ss1 :|: ss2) setT = i_ssym ss1 setT :|: i_ssym ss2 setT.
Proof. by apply/setP=> ?; rewrite !inE !andTb. Qed.

Lemma setUIsub (T : finType) (A B C D : {set T}) :
  A :|: B = C :|: D -> B :&: C = set0 -> D :&: C = set0 -> C \subset A.
Proof.
move=> hU h_bc h_dc; move: (congr1 (setI C) hU).
rewrite setIC [C :&:_]setIC !setIUl setIid.
by rewrite h_bc h_dc !setU0; move/setIidPr.
Qed.

Lemma setUI {T : finType} (A B C D : {set T}) :
  A :|: B = C :|: D ->
  B :&: A = set0 -> D :&: A = set0 -> B :&: C = set0 -> D :&: C = set0 ->
  A = C.
Proof.
move=> h hba hda hbc hdc; apply/eqP; rewrite eqEsubset; apply/andP; split.
exact: (@setUIsub _ C D A B); try assumption; symmetry.
exact: (@setUIsub _ A B C D); try assumption.
Qed.

Lemma issymI ss1 ss2 i1 i2 :
  ss1 :&: ss2 = set0 -> i_ssym ss1 i1 :&: i_ssym ss2 i2 = set0.
Proof.
move/setP=> hI; apply/setP=> x; rewrite /i_ssym in_set0 !inE.
apply/andP => [[]] /andP [hi1 hs1] /andP [hi2 hs2].
by move: (hI (sym_gatom x)); rewrite in_set0 inE hs1 hs2 andbT.
Qed.

Lemma wcUP ss1 ss2 ci1 ci2 : ss1 :&: ss2 = set0 ->
  {subset ci_syms ci1 <= ss1} -> {subset ci_syms ci2 <= ss2} ->
  ci_wc ss1 ci1 -> ci_wc ss2 ci2 -> ci_wc (ss1 :|: ss2) (ci1 :||: ci2).
Proof.
move=> hI h1 h2; rewrite/ci_wc/partf issymUT.
move=> /andP [/eqP hU1 /eqP hI1] /andP [/eqP hU2 /eqP hI2].
move/subsetP : h1; rewrite subUset; case/andP=> h11 h12;
move/subsetP : h2; rewrite subUset; case/andP=> h21 h22.
rewrite (issymU h11 h21) (issymU h12 h22) setUACA.
rewrite -(issymU h21 h22) -(issymU h11 h12) !setUid.
apply/andP; split; last first.
+ rewrite setIUl setIUr hI1 set0U setIUr hI2 setU0 setU_eq0.
  by apply/andP; split; apply/eqP; apply/issymI =>//; rewrite setIC.
+ apply/eqP; rewrite -?hU1 -?hU2 //=.
  rewrite -[i_ssym ss1 ci1.1 :|: _] issymU //=.
  rewrite -[i_ssym ss2 ci2.1 :|: _] issymU //=.
  by rewrite !setUid.
Qed.

Lemma ci_wcU ssU i11 i12 i21 i22 :
  ci_wc ssU (i11 :|: i12, i21 :|: i22) = ci_wc ssU ((i11, i21) :||: (i12, i22)).
Proof. by []. Qed.

Lemma p2cU pi1 pi2 : p2c (pi1 :|: pi2) = p2c pi1 :||: p2c pi2.
Proof.
congr (_, _); apply/setP=> pga; rewrite !inE.
  apply/imsetP/orP=> [ [pga0] | ].
    rewrite !inE; case/andP; case/orP => hga pgau -> /=.
      by left; apply/imsetP; exists pga0; rewrite // inE hga.
    by right; apply/imsetP; exists pga0; rewrite // inE hga.
  by case; case/imsetP=> pga0; rewrite !inE;
     case/andP => hga hf ->; exists pga0; rewrite // !inE ?hga // orbC.
apply/imsetP/orP => [[pga0]|].
  rewrite !inE; case/andP; case/orP => hga pgau -> /=.
    by left; apply/imsetP; exists pga0; rewrite // inE hga.
  by right; apply/imsetP; exists pga0; rewrite // inE hga.
by case; case/imsetP=> pga0; rewrite !inE;
   case/andP => hga hf ->; exists pga0; rewrite // !inE ?hga // orbC.
Qed.

End WellComplemented.

Section ComplementTrue.

Variable (p : program).

(** *** Lemma 3: compl_cinter is a model of the encoded program *)

(** ** Step [0/3]: proof for a single ground atom and a single clause *)
Lemma gaC_cl_true cl s ga ci :
 sym_gatom ga = s -> ~ negdep s [:: cl] ->
 P.cl_true (encodecl cl) (c2p ci) ->
 P.cl_true (encodecl cl) (c2p (ci.1, [set ga] :|: ci.2)).
Proof.
case: cl=> h b; rewrite/encodecl/=.
set pcl := P.Clause _ _.
move=> hs hd pt gr; have/implyP {pt} pt := pt gr.
rewrite/P.gcl_true /=.
set gpcl := P.gr_cl gr pcl in pt *.
rewrite /P.gcl_true; apply/implyP; move/allP=> h_all.
suff: all (mem (c2p ci)) (P.body_gcl gpcl).
  by move/pt; apply/subsetP/c2p_mon; [done | apply: subsetUr].
apply/allP=> gl h_gl; move: (h_all gl h_gl); rewrite/c2p /=.
rewrite !inE; case/orP; first by move=> hh; apply/orP; left.
move/imsetP=> hh; apply/orP; case: hh => [ga' h_in h_eq].
move: h_in; rewrite inE; case/orP; last first.
  by move=> hh; right; apply/imsetP; exists ga'.
rewrite inE => /eqP hh.
move {h_all pt}; subst; exfalso.
(* Contradiction *)
apply: hd; rewrite /negdep/nlit_prog/lits_prog /=.
rewrite /gpcl /pcl {gpcl pcl} in h_gl.
case/mapP: h_gl => /= enc_l /mapP[l in_b ->] h_neg {enc_l}.
apply/mapP; exists l.
  by rewrite mem_filter cats0 in_b; case: l h_neg {in_b} => [[[]]].
by case: ga h_neg => s args []; case: l {in_b} => [[[]] a] // [].
Qed.

(** ** Step [1/3]: proof for adding a single complement *)
Lemma gaC_prog_true s ga ci
  (hndep : ~~ negdep s p)
  (hsym  : sym_gatom ga = s) :
  P.prog_true (encodep p) (c2p ci) ->
  P.prog_true (encodep p) (c2p (ci.1, ga |: ci.2)).
Proof.
move=> hp gr; apply/allP => cl clin.
have cl_pos : cl \in hd_cl_pos by case/mapP: clin => ocl _ ->.
have U: P.cl_true (encodecl (uncodecl cl)) (c2p ci).
  move=> hgr; have/allP := hp hgr => /(_ cl clin); rewrite uncodeclK //.
have V: ~ negdep s [:: uncodecl cl].
  apply/negP/(contra _ hndep)/mem_negdep => cl'; rewrite inE => /eqP ->.
  move: clin; rewrite -{1}[cl]uncodeclK //.
  by rewrite (mem_map (can_inj encodeclK)).
by have := gaC_cl_true hsym V U gr; rewrite uncodeclK.
Qed.

(** ** Step [2/3]: proof for adding the complement set for a single symbol *)
Lemma isC_prog_true s i ci
  (hnp : ~~ negdep s p) :
  {in i, forall ga, sym_gatom ga = s} ->
  P.prog_true (encodep p) (c2p ci) ->
  P.prog_true (encodep p) (c2p (ci.1, i :|: ci.2)).
Proof.
rewrite (fcup_decomp i).
elim/big_rec: _ => [| ix i_s hi ih hsym pt]; first by rewrite set0U.
have hsix: sym_gatom ix = s by apply: hsym; rewrite !inE eqxx.
have his:  P.prog_true (encodep p) (c2p (ci.1, i_s :|: ci.2)).
  by apply: ih => // igg igs; apply: hsym; rewrite !inE igs orbT.
by rewrite -setUA; exact: gaC_prog_true hnp hsix his.
Qed.

Lemma isC_prog_true' i1 i2 s i
  (hnp : ~~ negdep s p) :
  {in i, forall ga, sym_gatom ga = s} ->
  P.prog_true (encodep p) (c2p (i1, i2)) ->
  P.prog_true (encodep p) (c2p (i1, i :|: i2)).
Proof. exact: isC_prog_true. Qed.

(** ** Step [3/3]: proof for adding the complement set for a set of symbols *)
Lemma issC_prog_true ss i ci
      (hnp : all (predC (negdep^~p)) (enum ss))
      (hin : {in i, forall ga, sym_gatom ga \in ss})
      (htr : P.prog_true (encodep p) (c2p ci)) :
  P.prog_true (encodep p) (c2p (ci.1, i :|: ci.2)).
Proof.
have hfilter ix : ix \in i -> exists2 s, s \in ss & sym_gatom ix == s.
  by move/hin; exists (sym_gatom ix).
rewrite (fcup_filter hfilter) {hfilter} in hin *.
elim/big_rec: _ => [| ix i_s ixin ih] in hin *; first by rewrite set0U.
rewrite -setUA; apply: isC_prog_true'.
  by move/allP: hnp => /(_ ix); apply; rewrite mem_enum.
  by move=> x; rewrite inE => /andP[h1 /eqP].
by apply: ih => //; move=> x xin; apply/hin; rewrite in_setU xin orbT.
Qed.

(** Program validity is invariant wrt model complementation *)
Lemma ciC_prog_true ss ci :
  all (predC (negdep^~ p)) (enum ss) ->
  P.prog_true (encodep p) (c2p ci) ->
  P.prog_true (encodep p) (c2p (ciC ss ci)).
Proof.
by move=> ?; apply: (@issC_prog_true ss _); try move=> ? /ic_ssymP [_ ?].
Qed.

End ComplementTrue.

(** **** Well-complemented models are models of negated programs *)
Lemma sanitize_gcl_true ss ci gcl :
  ci_wc ss ci         ->
  bsym_gcl gcl \subset ss ->
  P.gcl_true (encodegcl gcl) (c2p ci) ->
  gcl_true gcl (sanitize_model ci).
Proof.
case: gcl=> hd /= bd wf_c hs /implyP /= ht; apply/implyP => /= hall.
rewrite /bsym_gcl /body_gcl in hs.
have := @ciP (encodega hd) ci; rewrite encodegaK /= => U.
rewrite -U {U} ; apply: {hd} ht; rewrite all_map /= /preim.
apply/allP=> l hl; rewrite /= encodelitP.
move/allP: hall => h; move: (h l hl) => {h}.
rewrite /glit_true; case: ifP => ht //=.
have U: gatom_glit l \in i_ssym ss setT.
  apply/i_ssymP; rewrite in_setT; split=>//.
  by move/subsetP: hs; apply; apply/mapP; exists l.
rewrite /ci_wc in wf_c; have/partfP hh := wf_c.
by move/orP: (hh (gatom_glit l) U); case; move/i_ssymP; case=> ->.
Qed.

(** **** Satisfiability Preservation for Clauses:
Let [ss] be a symbol set, [ci] a complemented interpretation and [cl] a clause.
Assume [ci] is well-complemented w.r.t [ss] and the [cl] symbols are in [ss]
(positive dependency condition). If the encoding of [ci] satisfies the encoding of
[cl], then the positive component [ci.1] of [ci] satsifies [cl]. *)
Lemma sanitize_cl_true ss ci cl :
  ci_wc ss ci       ->
  bsym_cl cl \subset ss ->
  P.cl_true (encodecl cl) (c2p ci) ->
  cl_true cl (sanitize_model ci).
Proof.
move=> wf_c hsym hpt gr; apply: (sanitize_gcl_true wf_c).
  by case: cl {hpt} hsym => /= [s arg]; rewrite bsyms_gr_clause.
by rewrite gr_clauseE.
Qed.

(** **** Satisfiability Preservation for Programs:
Let [ss] be a symbol set, [pi] a positive intepretation and [p] a program.
Assume the uncoding of [pi] is well-complemented w.r.t [ss] and all body symbols in [p]
are in [ss] (positive dependency condition). If [pi] is a model of the encoding of
[p] then the positive component of the uncoding of [pi] is a model of [p]. *)
Lemma sanitize_prog_true ss pi p :
  ci_wc ss (p2c pi) ->
  {in p, forall cl, bsym_cl cl \subset ss} ->
  P.prog_true (encodep p) pi ->
  prog_true p (sanitize_model (p2c pi)).
Proof.
move=> wf_p cl_in pt nu; have := pt nu; rewrite all_map.
move/allP=> h; apply/allP=> cl h_cl.
apply: (@sanitize_gcl_true ss) =>//.
  by move: (cl_in cl h_cl); rewrite bsyms_gr_clause.
by rewrite gr_clauseE p2cK; apply h.
Qed.

End Complemented.

Notation "A :||: B" := (ciU A B) (at level 52, left associativity) : set_scope.

Section Evaluation.

(** cumulative model wrt to a set of symbols ss *)
Definition sinterp := (cinterp * {set symtype})%type.
Implicit Types (str : strata) (si : sinterp).

Variables (pdef : constant) (p : program) (p_sf : prog_safe p).

Let bound := bp.

(** stratified evaluation *)
Fixpoint eval_prog str si : sinterp :=
  match str with
  | [::]     => si
  | ss :: ps =>
    let m_next  := pengine_step pdef (encodep (slice_prog p (si.2 :|: ss))) si.1   in
    let m_compl := ciC ss m_next                                                   in
    eval_prog ps (m_compl, si.2 :|: ss)
  end.

(** **** Injectivity:
If [pp1] and [pp2] are extensionally equal "positive" programs, then their
positive evaluations, given a complemented interpretation [ci], are equal. *)
Lemma eq_pengine_step def pp1 pp2 ci (eq_p : pp1 =i pp2) :
  pengine_step def pp1 ci = pengine_step def pp2 ci.
Proof.
rewrite /pengine_step; elim: #|_| => //= m /(can_inj p2cK) ->.
by rewrite (P.eq_fwd_chain _ _ eq_p).
Qed.

(** **** Stability:
If [pp] is a safe "positive" program and [ci], a complemented interpretation
whose encoding is a model of [pp], then the positive evaluation of [pp], given [ci],
adds no further facts. *)
Lemma pengine_stable def pp ci
  (h_sf : P.prog_safe pp)
  (h_tr : P.prog_true pp (c2p ci)) :
  pengine_step def pp ci = ci.
Proof. by rewrite /pengine_step P.iter_fwd_chain_stable ?c2pK. Qed.

(** **** Subsumption:
If [pp] is a positive program, then, given an arbitrary complemented interpretation [ci],
the encoding of the positive evaluation of [pp] contains the encoding of [ci]. *)
Lemma pengine_subset def pp ci :
  c2p ci \subset c2p (pengine_step def pp ci).
Proof. by rewrite p2cK; exact: P.iter_fwd_chain_subset. Qed.

(** **** Symbol Stratifiability:
Let [pp] be a positive program and [ci], an arbitrary complemented interpretation. 
The ground atoms in the output of the positive evaluation of [pp] given [ci] are either:
1) _initial_, i.e, in [ci] or 2) _derived_, i.e, their symbols are among the head clause symbols
in [pp] *)
Lemma pengine_sym def pp ci pga :
  (pga \in c2p (pengine_step def pp ci)) ->
  (pga \in c2p ci) || (sym_gatom pga \in P.hsym_prog pp).
Proof. by rewrite p2cK; move/P.iter_fwd_chain_sym. Qed.

(** **** Positivity:
Let [p'] be a program and [ci], an arbitrary complemented interpretation.
The positive evaluation of the encoding of [p'], given [ci], adds no facts to
the negative component [ci.2] of [ci]. *) 
Lemma pengine_idN def p' ci :
  (pengine_step def (encodep p') ci).2 = ci.2.
Proof.
suff: (pengine_step def (encodep p') ci).2 \subset ci.2.
  have: ci.2 \subset (pengine_step def (encodep p') ci).2.
    have := pengine_subset def (encodep p') ci.
    by rewrite c2pS; case/andP.
  by move=> h1 h2; apply/eqP; rewrite eqEsubset h1 h2.
apply/subsetP=> ga.
set pe := pengine_step _ _ _.
have /= h := (ciP ((flipga \o encodega) ga) pe).
rewrite encodegafK in h. rewrite -h. move/pengine_sym.
rewrite ciP encodegafK /=; case/orP =>//.
  by case/mapP=> cl; case/mapP=> ucl hin ->.
Qed.

Lemma setUDP (T : finType) (A B : {set T}) :
  A \subset B ->
  A :|: B = A :|: (B :\: A).
Proof. by move=> sub_ab; apply/setP => ga; rewrite !inE orb_andr orbN. Qed.

(** **** Modularity:
Assume [ci], a complemented interpretation. Let [pb] and [pn] be positive programs, 
such that the head symbols in [pn] are not among the symbols in [pb] and the encoding of [ci]
is a model of [pb]. The positive evaluation of the the concatenation of [pb] and [pn], 
given ci, equals the union of the positive evaluations of [pb] and [pn], respectively, given [ci]. *) 
Lemma pengine_cat def pb pn ci
      (h_ss  : [disjoint P.hsym_prog pn & P.sym_prog pb])
      (h_tr  : P.prog_true pb (c2p ci)) :
 pengine_step def (pb ++ pn) ci =
 pengine_step def pb ci :||: pengine_step def pn ci.
Proof.
rewrite -p2cU; congr p2c.
elim: #|_| => [|k ihn]; first by rewrite setUid.
rewrite /= P.fwd_chain_cat // ihn.
have : iter k (P.fwd_chain def pn) (c2p ci) :\: c2p ci \subset
       P.fwd_chain def pn (iter k (P.fwd_chain def pn) (c2p ci)).
  rewrite subDset.
  have/setUidPr ->: c2p ci \subset
                    P.fwd_chain def pn (iter k (P.fwd_chain def pn) (c2p ci)).
    have/subset_trans -> // := P.iter_fwd_chain_subset def pn (c2p ci) k.
    exact/P.fwd_chain_inc.
  exact/P.fwd_chain_inc.
set fc := P.fwd_chain def.
move/setUidPr=> {1}<-.
rewrite [fc pb (iter k _ _) :|: (_ :|: _)]setUA.
congr (_ :|: _); last first.
  rewrite P.iter_fwd_chain_stable //.
  suff -> : c2p ci :|: iter k (P.fwd_chain def pn) (c2p ci) =
            iter k (P.fwd_chain def pn) (c2p ci).
    by [].
  exact/setUidPr/P.iter_fwd_chain_subset.
rewrite [iter _ (fc pb) _]P.iter_fwd_chain_stable //.
rewrite setUDP ?P.iter_fwd_chain_subset //.
(* Set of symbols in the heads of pn *)
rewrite /fc P.fwd_chain_mod // ?P.fwd_chain_stable //.
rewrite disjoint_has; apply/hasP => -[sy sin /=] /imsetP[ga].
rewrite inE; case/andP=> [/negbTE hn /P.iter_fwd_chain_sym] /orP[].
  by rewrite hn.
move=> hga hsy; rewrite hsy /= in sin.
move: h_ss; rewrite disjoint_has => /hasP [].
by exists sy; rewrite hsy /= ?hga ?sin.
Qed.

Lemma gr_patomE (nu : gr) (pa : patom) :
   uncodega (P.gr_atom nu pa) = gr_atom nu (uncodea pa).
Proof. exact/val_inj. Qed.

Lemma prog_true_pos p' ci ss :
  prog_true p' ci.1          ->
  {subset sym_prog p' <= ss} ->
  ci_wc ss ci       ->
  P.prog_true (encodep p') (c2p ci).
Proof.
move=> htp hsym hwc nu; apply/allP => cl clin; apply/implyP=> hall.
have cl_in': uncodecl cl \in p'.
  by case/mapP: clin => cl' cl'i ->; rewrite encodeclK.
have/allP/(_ (uncodecl cl) cl_in')/implyP clT := htp nu.
suff/clT: all (glit_true ci.1) (body_gcl (gr_cl nu (uncodecl cl))).
  rewrite ciP.
  have ->: flag_pgatom (P.head_gcl (P.gr_cl nu cl)).
    by case/mapP: clin=> cl' cli' ->.
  by rewrite /= gr_patomE.
clear clT.
rewrite !all_map in hall *.
apply/allP=> pga hpga.
have /allP hp := hall.
have := hp pga hpga.
rewrite /=; case: pga hpga=> [[[[] sy] args] wfa] ha; rewrite ciP.
  by rewrite gr_patomE.
rewrite gr_patomE /glit_true /=.
set gra := gr_atom _ _ .
move: hwc; rewrite /ci_wc /partf.
case/andP=> [/eqP /setP /(_ gra) h1 /eqP /setP /(_ gra) h2].
move: h1 h2; rewrite !inE /=.
case: (gra \in ci.1) => //.
case: (gra \in ci.2) => //=.
have -> //: sy \in ss.
apply: hsym; apply/flatten_mapP; exists (uncodecl cl); rewrite //.
rewrite inE; apply/orP; right.
apply/mapP; exists (uncodel (P.Atom wfa)); rewrite //.
by apply/mapP; exists (P.Atom wfa).
Qed.

(** **** Incrementality:
Let [p] be a stratifiable program, [si] a cumulative interpretation and [ss], a current
stratum. Assume that: 1) the symbols of the encoded slicing of [p] with the accumulated
strata [si.2] are not among the head symbols of the encoded program slicing of [p] with [ss],
2) the symbols in the slicing of [p] with [si.2] are in si.2, 3) [si.1] is well-complemented
w.r.t [si.2] and 4) the positive component [si.1.1] satisfies the slicing of [p] with [si.2].
Then, the positive evaluation of the encoded slicing of [p] with the accumulated strata [si.2]
and the current stratum [ss] increments [si.1.1] with a set of positive facts [si_ss] whose symbols
are in [ss]. *)
Lemma ci_wc_decomposition ss si :
  [disjoint P.hsym_prog (encodep (slice_prog p ss))
   & P.sym_prog (encodep (slice_prog p si.2))] ->
  {subset sym_prog (slice_prog p si.2) <= si.2} ->
  ci_wc si.2 si.1 ->
  prog_true (slice_prog p si.2) si.1.1 ->
  (exists2 si_ss,
     pengine_step pdef
       (encodep (slice_prog p (ss :|: si.2))) si.1 = (si.1.1 :|: si_ss, si.1.2)
     & {subset isyms si_ss <= ss}).
Proof.
move=> h_dis h_str h_wc hp.
set ep_ssi := encodep _.
set ep_ss  := encodep (slice_prog p ss).
set ep_si  := encodep (slice_prog p si.2).
pose pe pp := pengine_step pdef pp si.1.
set pe_ssi := pengine_step _ _ _.
+ exists ((pe ep_ssi).1 :\: si.1.1).
  rewrite [pe_ssi]surjective_pairing /=; congr (_, _); rewrite /pe; last first.
  exact: pengine_idN.
  have ht: si.1.1 \subset (pengine_step pdef ep_ssi si.1).1.
    by have := pengine_subset pdef ep_ssi si.1; rewrite c2pS; case/andP.
  by rewrite -setUDP //; apply/esym/setUidPr.
+ have p_catE : ep_ssi =i ep_si ++ ep_ss.
    have hU := slice_progU p ss si.2.
    have hI := can_inj encodeclK.
    move=> i; rewrite mem_cat; apply/mapP/orP.
    case=> cl; rewrite hU mem_cat; case/orP=> hmem ->; rewrite !mem_map //; eauto.
    by case => /mapP [cl hmem ->]; exists cl; rewrite // hU mem_cat hmem // orbC.
  have pi_sf: P.prog_safe ep_si.
    by rewrite -encode_prog_safe; apply: sliced_prog_safe.
  have pi_tr: P.prog_true ep_si (c2p si.1).
    exact: (prog_true_pos hp _ h_wc) => //.
  have peUE : pe ep_ssi = pe ep_si :||: pe ep_ss.
    by rewrite /pe (eq_pengine_step _ _ p_catE) pengine_cat.
  have hga : forall ga, ga \in (pengine_step pdef ep_ss si.1).1 ->
             encodega ga \in c2p (pengine_step pdef ep_ss si.1).
    by move=> ga; rewrite ciP /= encodegaK.
  move=> s /imsetP[ga]; move: peUE; rewrite/pe => ->.
  rewrite !inE (pengine_stable _ _ pi_tr) //; move/andP=>[h1 /orP [h2 | h2]].
    by rewrite h2 in h1.
  move: (hga ga h2); move/pengine_sym; rewrite ciP /= encodegaK.
  case/orP.
    by move=> h3; rewrite h3 in h1.
  by move=> /encodes_hsym /slice_progP hs ->.
Qed.

(** model minimality condition *)
Definition str_min_model (prev_i next_i : interp) p :=
  forall i', prev_i \subset i' -> prog_true p i' -> next_i \subset i'.

(** Let [p] be a program, [str] strata to be processed and [acc], already accumulated strata.
For any well-complemented intepretation, whose positive component is a model of the encoded
slicing of [p] with [acc], the computed model for the encoded slicing of [p] with the [acc] and the
current stratum [ss], given a complemented interpretation [ci_acc], is _minimal_ w.r.t all models of
the encoded slicing of [p] with [acc] containing [ci_acc]. *)
Fixpoint is_min_str_rec str acc :=
  match str with
  | [::]     => True
  | ss :: ps =>
    (forall (ci_acc : cinterp),
        ci_wc acc ci_acc ->
        isyms ci_acc.1 \subset acc ->
        isyms ci_acc.2 \subset acc ->
        prog_true (slice_prog p acc) ci_acc.1 ->
        forall (i_ss : interp),
          i_ssym ss i_ss = i_ss ->
          let p_next := slice_prog p (acc :|: ss) in
          prog_true p_next (ci_acc.1 :|: i_ss) ->
          (pengine_step pdef (encodep p_next) ci_acc).1 \subset (ci_acc.1 :|: i_ss))
    /\ is_min_str_rec ps (acc :|: ss)
  end.

Lemma sym_progU p' : sym_prog p' =i hsym_prog p' ++ bsym_prog p'.
Proof.
rewrite/sym_prog/hsym_prog/bsym_prog/sym_cl/hsym_cl/bsym_cl/sym_atom /= => s.
apply/idP/idP; rewrite mem_cat; try move/orP.
+ case/flatten_mapP=> [[h b] [h_cl hh]]; apply/orP; rewrite in_cons in hh.
  case/orP: hh.
  - move/eqP => ->; left; apply/mapP; exists (Clause h b)=> //=.
  - right; apply/flatten_mapP; exists (Clause h b)=> //=.
+ case.
  - case/mapP=> cl h hs; apply/flatten_mapP; exists cl=> //=; rewrite hs in_cons.
      by apply/orP; left.
  - case/flatten_mapP=> [[h b] [h_cl hh]]; apply/flatten_mapP.
    exists (Clause h b)=> //=; case/mapP: hh=> l hl=> ->; rewrite in_cons.
      by apply/orP; right; apply/mapP; exists l.
Qed.

Lemma i_ssym_disj ss1 ss2 i1 i2 :
  [disjoint ss1 & ss2] -> i_ssym ss1 i1 :&: i_ssym ss2 i2 = set0.
Proof. by move=> h; apply/issymI/eqP; rewrite setI_eq0. Qed.

(** Model minimality is a consequence of the strata invariant conditions, i.e,
is relative to the stratification. *)
Lemma minimality str acc : is_strata_rec p str acc -> is_min_str_rec str acc.
Proof.
elim: str acc => // ss ps ih acc.
case/and4P=> h1 h2 h3 h4; split; last exact: ih.
move=> ci_acc acc_wc ci_acc1_sym ci_acc2_sym acc_true i_ss sym_i_ss p_sss ss_true.
set pp_sss := encodep  _.
have pp_sf : P.prog_safe pp_sss.
  by rewrite -encode_prog_safe; apply: sliced_prog_safe.
have hhsub : c2p ci_acc \subset c2p (ci_acc.1 :|: i_ss, ci_acc.2 :|: (ic_ssym ss i_ss)).
  by rewrite c2pS; apply/andP; split=> //=; apply/subsetUl.
have h_cwc : ci_wc (acc :|: ss) (ci_acc.1 :|: i_ss, ci_acc.2 :|: ic_ssym ss i_ss).
  move: acc_wc; rewrite/ci_wc/partf /= => /andP [/eqP hU /eqP hI]; apply/andP.
  split; apply/eqP; rewrite !issymU //=; try exact: ic_symsS; try exact: i_symsS.
   + by rewrite setUAC setUA hU setUAC ic_ssymK -setUA ic_ssymUC issymUT.
   + rewrite -sym_i_ss; exact: i_symsS.
   + have hh1 : i_ssym ss i_ss :&: i_ssym acc ci_acc.2 = set0.
       by rewrite setIC; exact: i_ssym_disj.
     rewrite ic_ssymK !setIUl !setIUr hI ic_ssymIC set0U setU0 hh1 setU0 -icCi_ssym. 
     by rewrite i_ssym_disj.
   + rewrite -sym_i_ss; exact: i_symsS.
have h_sym : {subset sym_prog (slice_prog p (acc :|: ss)) <= acc :|: ss}.
  move=> s; rewrite (sym_progU (slice_prog p (acc :|: ss))) mem_cat; case/orP.
  + exact: @slice_progP p (acc :|: ss) s.
  + rewrite/bsym_prog; case/flatten_mapP=> cl h_cl h_s; move/allP: h4=> h.
    move: (h cl h_cl); rewrite/posdep; move/subsetP=> hs; exact: (hs s h_s).
have hpos :=  @prog_true_pos (slice_prog p (acc :|: ss))
                   (ci_acc.1 :|: i_ss, ci_acc.2 :|: (ic_ssym ss i_ss))
                   (acc :|: ss) ss_true h_sym h_cwc.
have [_ hp_min _] := @pengine_trueP pdef pp_sss ci_acc pp_sf.
by have HH := (hp_min _  hhsub hpos); rewrite c2pS in HH; case/andP: HH.
Qed.

(** The stratified evaluation invariant is:
   - the positive output is a model for the accumulated set of symbols.
   - the set of *all* the symbols in the slicing of the program with the
     accumulated strata symbols is a subset of the latter
   - the output is well-complemented wrt to the set of symbols.
   - the output symbols are a subset of the accumulated set of symbols.
 *)
Definition si_invariant si :=
  [/\ prog_true (slice_prog p si.2) (sanitize_model si.1)
   ,  {subset sym_prog (slice_prog p si.2) <= si.2}
   ,  ci_wc si.2 si.1
   &  ci_syms si.1 \subset si.2].

(** **** Soundness and Completeness of Stratified Evaluation:
Let [p] be a program and [str] a stratification and [si] a cumulative interpretation.
If [si] satisfies the invariant conditions, then the output interpretation of the stratified
evaluation of the slicing of [p] with the accumulated strata [si.2], given [si], 
also satisfies them. *)
Lemma eval_prog_true si str :
  is_strata_rec p str si.2 ->
  si_invariant si ->
  si_invariant (eval_prog str si).
Proof.
(** structural induction on the list of stratas *)
elim: str si => // ss ps ihs si.
case/and4P=> /= [str_ps strI str_pss str_bsym] [si_true si_sss si_wc si_sub].
set pss := si.2 :|: ss in str_ps str_pss *.
set p_ps  := slice_prog p si.2 in si_true *.
set p_pss := slice_prog p pss  in str_pss *.
(** proving safety of encoding *)
have pp_sf : P.prog_safe (encodep p_pss).
  by rewrite -encode_prog_safe; apply sliced_prog_safe.
have [cpp_true cpp_min cpp_bound] := pengine_trueP pdef si.1 pp_sf.
have cmpl_true := ciC_prog_true str_pss cpp_true.
apply: (ihs (ciC ss (pengine_step pdef (encodep p_pss) si.1), pss) str_ps).
rewrite /si_invariant [(_,_).1] /= [(_,_).2] /=.
have bstr : {in p_pss, forall cl : clause, bsym_cl cl \subset pss}.
  by move/allP: str_bsym; move=> h cl hcl; exact: (h cl hcl).
have h_sym : {subset sym_prog (slice_prog p si.2) <= si.2} by [].
have h_dis : [disjoint P.hsym_prog (encodep (slice_prog p ss))
                     & P.sym_prog  (encodep (slice_prog p si.2))].
  suff: [disjoint hsym_prog (slice_prog p ss) &  sym_prog (slice_prog p si.2)].
    rewrite !disjoint_has; apply: contra => /hasP /= [[[] ps']]; last first.
      by case/mapP => pcl // /mapP[cl hcl ->].
    move=> hhead hbod; apply/hasP; exists ps'; last exact/mem_sym_prog.
    by have /= := (uncodes_hsym hhead); rewrite encodepK.
  have/disjoint_trans ->//: hsym_prog (slice_prog p ss) \subset ss.
    exact/subsetP/slice_progP.
  rewrite disjoint_sym.
  have/disjoint_trans ->//: sym_prog (slice_prog p si.2) \subset si.2.
  exact/subsetP/h_sym.
have [si_ss hss hsi] := ci_wc_decomposition h_dis h_sym si_wc si_true.
have hh := (sanitize_prog_true _ bstr cmpl_true); rewrite c2pK in hh.
have h_wc : ci_wc pss (ciC ss (pengine_step pdef (encodep p_pss) si.1)).
  rewrite /p_pss /pss setUC hss /ciC.
  rewrite [(_, _).1]/= [(_, _).2]/= [ss :|: _]setUC [_ :|: si.1.2]setUC ci_wcU.
  apply wcUP; try assumption.
  + by rewrite -setI_eq0 in strI; move/eqP: strI.
  + by move/subsetP: si_sub.
  + move=> x; rewrite in_setU [(_, _).1]/= [(_, _).2]/=.
    case/orP; first by move: (hsi x).
    by move/isymsP=> [ga hin /eqP hs]; move: hin; rewrite !inE -hs; case/andP.
  + rewrite /ci_wc [(_, _).1] /= [(_, _).2] /= /partf.
    apply/andP; split.
    * apply/eqP; rewrite ic_ssymU i_ssymI !ic_ssymK setUIr ic_ssymUC.
      - have hI : ss :&: isyms si.1.1 = set0.
        move: si_sub; rewrite subUset; case/andP=> hs1 hs2.
        have Hs1 := setSI ss hs1; rewrite (disjoint_setI0 strI) subset0 in Hs1.
        by move/eqP: Hs1; rewrite setIC.
      by rewrite (ic_ssymIT hI); apply/setIidPr/subsetUr.
    * by rewrite ic_ssymK ic_ssymU setICA ic_ssymIC setI0.
repeat split; try assumption.
+ by apply hh.
+ clear hss cmpl_true cpp_bound pp_sf cpp_true hh h_wc.
  move=> s /flatten_mapP [cl hcl]; rewrite inE; case/orP.
    by move: hcl; rewrite mem_filter => /andP[u hu] /eqP ->.
  exact/subsetP/bstr.
+ rewrite /p_pss /pss [si.2 :|: _]setUC hss /ci_syms [(_, _).1]/= [(_, _).2]/=.
  have H : isyms (ic_ssym ss (si.1.1 :|: si_ss) :|: si.1.2)
       = isyms (ic_ssym ss (si.1.1 :|: si_ss)) :|: isyms si.1.2.
    by rewrite isymsU.
  rewrite H isymsU setUA setUAC [_:|: isyms si.1.2]setUC setUA setUC.
  rewrite [_ :|: isyms si_ss]setUC setUA; apply setUSS.
    by rewrite subUset; move/subsetP: hsi=> ->; rewrite andbT; apply: ic_symsS.
  by move: si_sub; rewrite/ci_syms setUC.
Qed.

End Evaluation.
End Encoding.
End DataLog.


