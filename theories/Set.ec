require import Logic.
require import Int.
require import Fun.

(* For this specification, almost everything is axiomatized.
   This is a prime candidate for 1) realization, and 2) refinement types. *)

type 'a set.

(* These will all be axiomatized *)
op empty : 'a set.
op add   : 'a -> 'a set -> 'a set.
op pick  : 'a set -> 'a.
op rm    : 'a -> 'a set -> 'a set.
op union : 'a set -> 'a set -> 'a set.
op inter : 'a set -> 'a set -> 'a set.
op mem   : 'a -> 'a set -> bool.
op card  : 'a set -> int.
op fold_right : ('a -> 'b -> 'b) -> 'b -> 'a set -> 'b.

(* Derived operators and predicates *)
op singleton (x:'a) : 'a set = add x empty.
op is_empty (X:'a set) : bool = X = empty.
op cPmem X (x:'a) = mem x X.

(* Extensional Equality *)
pred (==) (X1 X2:'a set) = forall (x:'a),
  mem x X1 <=> mem x X2.

lemma eq_refl: forall (X:'a set), X == X by [].

lemma eq_sym: forall (X Y:'a set), X == Y => Y == X by [].

lemma eq_trans: forall (X Y Z:'a set),
  X == Y => Y == Z => X == Z
by [].

axiom extensionality: forall (X1 X2:'a set),
  X1 == X2 => X1 = X2.

(* Subset *)
pred (<=) (X1 X2:'a set) = forall x,
  mem x X1 => mem x X2.

lemma sub_refl: forall (X:'a set), X <= X by [].

lemma sub_anti_sym: forall (X Y:'a set),
  X <= Y => Y <= X => X == Y
by [].

lemma sub_trans: forall (X Y Z:'a set),
  X <= Y => Y <= Z => X <= Z
by [].

(** Specification of operators *)
(* empty *)
axiom empty_mem: forall (x:'a), !mem x empty.

lemma empty_subset: forall (X:'a set), empty <= X by [].

(* add *)
axiom add_mem: forall (x y:'a) X, 
  mem x (add y X) <=> mem x X \/ x = y.

axiom add_card: forall (x:'a) X, 
  !mem x X => card (add x X) = card X + 1.

lemma mem_add: forall (x:'a) X,
  mem x X => X = add x X.
proof.
intros x X x_in_X; apply extensionality; smt.
save.

lemma add_subset: forall (x:'a) X,
  X <= add x X
by [].

(* pick *)
axiom pick_spec: forall (X:'a set), 
  X <> empty => mem (pick X) X.

lemma pick_singleton: forall (x:'a), 
  pick (singleton x) = x
by [].

(* rm *)
axiom rm_spec_not_mem: forall (x:'a) X,
  !mem x X => rm x X = X.

axiom rm_spec_mem: forall (x:'a) X,
  mem x X => add x (rm x X) = X.

axiom rm_mem: forall (x:'a) X,
  !mem x (rm x X).

lemma rm_subs: forall (x:'a) X,
  rm x X <= X
by [].

lemma rm_add: forall (x:'a) (xs:'a set),
  !(mem x xs) =>
  rm x (add x xs) = xs by (intros x xs h;apply extensionality;delta (==);smt).

lemma add_rm: forall (x:'a) (xs:'a set),
  (mem x xs) =>
  (add x (rm x xs)) = xs by (intros x xs h;apply extensionality;delta (==);smt).

theory Induction.

axiom induction_det: forall (P:('a set) cpred),
  P empty =>
  (forall S, let x = pick S in P (rm x S) => P S) =>
  forall S, P S.

lemma induction: forall (P:('a set) cpred),
  P empty =>
  (forall x S, !mem x S => P S => P (add x S)) =>
  forall S, P S.
intros P empt hyp S.
cut lem : ((S <> empty) => P S);last smt.
elim/induction_det S;first (simplify;split).
intros S0 x h nempty.
rewrite -(add_rm<:'a> x S0 _);first smt.
apply hyp;smt.
save.

end Induction.

import Induction.

(* fold *)
axiom fold_nil: forall (f:'a -> 'b -> 'b) (e:'b),
  fold_right f e empty = e.
axiom fold_rm: forall (f:'a -> 'b -> 'b) (e:'b) xs,
  let x = pick xs in
    fold_right f e xs = f x (fold_right f e (rm x xs)).

(* map *)
op map(f:('a -> 'b)) : 'a set -> 'b set = fold_right (lambda (x:'a), add (f x)) empty.
lemma map_nil: forall (f:'a -> 'b),
  map f empty = empty by [].
lemma map_cons: forall (f:'a -> 'b) xs,
  let x = pick xs in
  map f xs = add (f x) (map f (rm x xs)) by [].


(* card *)
axiom card_empty: card<:'a> empty = 0.
axiom card_rm: forall (x:'a) S, mem x S => card S = 1 + card(rm x S).

pred (* local *) cP_card_pos (X:'a set) = 0 <= card X.
lemma card_pos: forall (X:'a set), 0 <= card X.
proof.
intros X;cut IH: (cP_card_pos X);
  [apply (induction cP_card_pos) | idtac]; smt.
save.

lemma rm_card: forall (x:'a) X,
  card(rm x X) <= card X
by [].

pred (* local *) cP_is_empty_card(X:'a set) = card X = 0 => is_empty X.
lemma is_empty_card: forall (X:'a set),
  card X = 0 => is_empty X. 
proof.
intros X;cut IH: (cP_is_empty_card X);
  [apply (induction cP_is_empty_card) | idtac]; smt.
save.

(* singleton *)
lemma singleton_card: forall (x:'a),
  card (singleton x) = 1
by [].

(* filter *)
op filter: 'a cpred -> 'a set -> 'a set.

axiom filter_mem: forall (x:'a) P X,
  mem x (filter P X) <=> (mem x X /\ P x).

axiom filter_card: forall (P:'a cpred) X, 
  card (filter P X) = card X - card (filter (cpNot P) X). 

axiom filter_cPeq_in: forall (x:'a) X,
  mem x X => filter ((=) x) X = singleton x.

axiom filter_cPeq_card_in : forall (x:'a) X,
  mem x X => card (filter ((=) x) X) = 1.

axiom filter_cPtrue : forall (X:'a set), filter cpTrue X = X.

lemma filter_subset: forall (P:'a cpred) X,
 filter P X <= X
by [].

(* union *) 
axiom union_mem: forall (x:'a) X Y,
  mem x (union X Y) <=> (mem x X \/ mem x Y).

lemma union_empty: forall (X:'a set),
  union X empty = X.
proof.
intros X; apply extensionality; smt.
save.

lemma union_comm: forall (X Y:'a set),
  union X Y = union Y X.
proof.
intros X Y; apply extensionality; intros x; smt.
save.

lemma union_add: forall (x:'a) X Y,
  add x (union X Y) = union (add x X) Y.
proof.
intros x X Y; apply extensionality; intros y;smt.
save.

lemma subset_union1: forall (X Y:'a set),
  X <= union X Y
by [].

pred (* local *) cP_subset_union(X:'a set) = forall Y,
  X <= Y => exists Z, Y = union X Z.

lemma subset_union2: forall (X Y:'a set),
  X <= Y => exists Z, Y = union X Z.
proof.
intros X; cut H0: (cP_subset_union X).
  apply (induction cP_subset_union).
    smt.
    intros x S H H0;cut H1: (forall Y, (add x S) <= Y => (exists Z, Y = union (add x S) Z)).
      intros Y H1;cut H2 : (S <= Y).
        smt.
        cut H3: (forall Y, S <= Y => exists Z, Y = union S Z).
          smt.
          cut H4: (exists Z, Y = union S Z).
            apply (H3 Y _); assumption.
            elim H4;intros Z H5;smt.
      smt.
  smt.
save.

pred (* local *) cP_union_card1(X:'a set) = forall Y,
  card (union X Y) <= card(X) + card(Y).
lemma union_card1: forall (X Y:'a set),
  card (union X Y) <= card (X) + card(Y).
proof.
intros X;cut H: (cP_union_card1 X);
  [apply (induction cP_union_card1) | idtac]; smt.
save.

pred (* local *) cP_union_card2(Y:'a set) = forall (X:'a set),
  card X <= card (union X Y).
lemma union_card2: forall (Y X:'a set),
  card X <= card (union X Y).
proof. 
intros Y;cut H: (cP_union_card2 Y).
apply (induction cP_union_card2).
  smt.
  intros x S H H1;cut H0 : (forall X, card X <= card (union X (add x S))).
    intros X;cut H2: (card X <= card (union X S)).
      smt.
      cut H3: (card (union X S) <= card (union X (add x S))).
        cut H4: (card (union X (add x S)) = card (add x (union X S)));smt.
        smt.
    smt.
  smt.
save.

lemma subset_card: forall (X Y:'a set),
  X <= Y => (card X) <= (card Y).
proof.
intros X Y H;cut H0: (exists Z, Y = union X Z).
  smt.
  elim H0;intros Z H1;cut H2: (card X <= card (union X Z));
    smt.
save.

(* intersection *)
axiom inter_mem: forall (x:'a) X Y,
  mem x (inter X Y) <=> (mem x X /\ mem x Y).

lemma inter_empty: forall (X:'a set),
  inter X empty = empty.
proof.
intros X; apply extensionality; smt.
save.

lemma inter_comm: forall (X Y:'a set),
  inter X Y = inter Y X.
proof.
intros X Y; apply extensionality; smt.
save.

lemma inter_add: forall (x:'a) X Y,
  add x (inter X Y) = inter (add x X) (add x Y).
proof.
intros x X Y; apply extensionality.
cut ext: (forall y, mem y (add x (inter X Y)) = mem y (inter (add x X) (add x Y))); smt.
save.

lemma inter_add2: forall (x:'a) X Y,
  mem x Y => add x (inter X Y) = inter (add x X)  Y.
proof.
intros x X Y x_in_Y; apply extensionality; smt.
save.

lemma inter_add3: forall (x:'a) X Y,
  !mem x Y => (inter X Y) = inter (add x X) Y.
proof.
intros x X Y x_nin_Y; apply extensionality;
  delta (==) beta=> x'; rewrite 2!inter_mem;
  case (x = x'); smt.
save.

lemma subset_inter: forall (X Y:'a set),
  inter X Y <= X
by [].

lemma card_inter: forall (X Y:'a set),
  card (inter X Y) <= card X
by [].

pred (*local *) cP_union_inter(X:'a set) = forall Y,
  card (union X Y) + card (inter X Y) = card X + card Y.

lemma card_union_inter: forall (X Y:'a set),
  card (union X Y) + card (inter X Y) = card X + card Y.
proof. 
intros X;cut IH: (cP_union_inter X).
  apply (induction cP_union_inter).
    smt.
    intros x S H H0;cut H1: (forall Y, card (union (add x S) Y) + card (inter (add x S) Y) =
                                         card (add x S) + card Y).
      intros Y;cut H8: (card (union S Y) + card (inter S Y) = card S + card Y).
        smt.
        cut H2: (mem x Y => card(union (add x S) Y) + card (inter (add x S) Y) = card (add x S) + card Y).
          intros H3;cut H4: (card (add x (inter S Y)) = card (inter (add x S) Y)).
            cut H5: (add x (inter S Y) = (inter (add x S) Y));smt.
            cut H5: (!mem x (inter S Y)).
              smt.
              cut H6: (card (inter (add x S) Y) = 1 + card (inter S Y)).
                smt.
                cut H7: (card (add x S) = 1 + card S);smt.
          cut H3: (!mem x Y => card (union (add x S) Y) + card (inter (add x S) Y) =
                                 card (add x S) + card Y).
            intros H4;cut H5: (card (inter S Y) = card (inter (add x S) Y)).
              smt.
              cut H6: (!mem x (union S Y)).
                smt.
                cut H7: (card (union (add x S) Y) = 1 + card (union S Y));smt.
      smt.
    smt.
  smt.
save.

require import Real.
require import Distr.

(* Uniform distribution on a (finite) set *)
theory Duni.
  op duni: 'a set -> 'a distr.

  axiom supp_def: forall (x:'a) X, in_supp x (duni X) <=> mem x X.

  axiom mu_def: forall (X:'a set) P, 
    !is_empty X => mu (duni X) P = (card (filter P X))%r / (card X)%r. 

  axiom mu_def_empty: forall (P:'a cpred), mu (duni empty) P = 0%r.

  axiom mu_x_def_in: forall (x:'a) X, 
    mem x X => mu_x (duni X) x = 1%r / (card X)%r. 

  axiom mu_x_def_notin: forall (x:'a) X, 
    !mem x X => mu_x (duni X) x = 0%r.

  lemma weight_def: forall (X:'a set), 
    weight (duni X) = if is_empty X then 0%r else 1%r.
  proof.
    intros X; case (is_empty X); intros H.
    smt. 
    delta weight; simplify. 
    rewrite (mu_def<:'a> X Fun.cpTrue _).
    assumption.
    rewrite (filter_cPtrue<:'a> X).
    cut W: ((card X)%r <> 0%r); smt.
  qed.
end Duni.

(** Restriction of a distribution (sub-distribution) *)
theory Drestr.
  op drestr: 'a distr -> 'a set -> 'a distr.
 
  axiom supp_def: forall (x:'a) d X, 
    in_supp x (drestr d X) <=> in_supp x d /\ !mem x X.
  
  axiom mu_x_def_notin: forall (x:'a) d X, 
    in_supp x d => !mem x X => mu_x (drestr d X) x = mu_x d x.

  lemma mu_x_def_in: forall (x:'a) d X, 
    in_supp x d => mem x X => mu_x (drestr d X) x = 0%r by [].

  axiom weight_def: forall (d:'a distr) X, 
    weight (drestr d X) = weight d - mu d (cPmem X).
end Drestr.

(** Scaled restriction of a distribution *)
theory Dexcepted.
  op (\) (d:'a distr, X:'a set) : 'a distr = Dscale.dscale (Drestr.drestr d X).

  lemma supp_def : forall (x:'a) d X,
    (in_supp x (d \ X) => (in_supp x d /\ !mem x X)) /\
    ((in_supp x d /\ !mem x X) => in_supp x (d \ X)).
  proof.
  intros d X x;split.
    intros in_supp;split;smt.
    intros in_supp_nmem;smt.
  save.
    
  lemma mu_x_def : forall (x:'a) d X,
    mu_x (d \ X) x = 
    (in_supp x (d \ X)) ? mu_x d x / (weight d - mu d (cPmem X)) : 0%r.
  proof.
    intros x d X; rewrite /(\).
    case (weight d - mu d (cPmem X) = 0%r)=> weight.
      by rewrite /mu_x Dscale.mu_x_def_0 ?Drestr.weight_def //
                 /in_supp
                 (_: (0%r < mu_x (Dscale.dscale (Drestr.drestr d X)) x) = false)=> //=;
         first smt.
      by smt.
  qed.

  lemma mu_weight_def : forall (d:'a distr) X,
    weight (d \ X) = (weight d = mu d (cPmem X)) ? 0%r : 1%r
  by [].
end Dexcepted.
