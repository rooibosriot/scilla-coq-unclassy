From mathcomp.ssreflect 
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
From Contracts
Require Import Automata2.
Require Import Arith Bool Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Crowdfunding.
(* Encoding of the Crowdfunding contract from the Scilla whitepaper *)

(******************************************************
contract Crowdfunding
 (owner     : address,
  max_block : uint,
  goal      : uint)

(* Mutable state description *)
{
  backers : address => uint = [];
  funded  : boolean = false;
}

(* Transition 1: Donating money *)
transition Donate
  (sender : address, value : uint, tag : string)
  (* Simple filter identifying this transition *)
  if tag == "donate" =>

  bs <- & backers;
  blk <- && block_number;
  let nxt_block = blk + 1 in
  if max_block <= nxt_block
  then send (<to -> sender, amount -> 0,
	      tag -> main,
	      msg -> "deadline_passed">, MT)
  else
    if not (contains(bs, sender))
    then let bs1 = put(sbs, ender, value) in
         backers := bs1;
         send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "ok">, MT)
    else send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "already_donated">, MT)

(* Transition 2: Sending the funds to the owner *)
transition GetFunds
  (sender : address, value : uint, tag : string)
  (* Only the owner can get the money back *)
  if (tag == "getfunds") && (sender == owner) =>
  blk <- && block_number;
  bal <- & balance;
  if max_block >= blk
  then if goal <= bal
       then funded := true;
            send (<to -> owner, amount -> bal,
                   tag -> "main", msg -> "funded">, MT)
       else send (<to -> owner, amount -> 0,
                   tag -> "main", msg -> "failed">, MT)
  else send (<to -> owner, amount -> 0, tag -> "main",
   	      msg -> "too_early_to_claim_funds">, MT)

(* Transition 3: Reclaim funds by a backer *)
transition Claim
  (sender : address, value : uint, tag : string)
  if tag == "claim" =>
  blk <- && block_number;
  if blk <= max_block
  then send (<to -> sender, amount -> 0, tag -> "main",
              msg -> "too_early_to_reclaim">, MT)
  else bs <- & backers;
       bal <- & balance;
       if (not (contains(bs, sender))) || funded ||
          goal <= bal
       then send (<to -> sender, amount -> 0,
                   tag -> "main",
	           msg -> "cannot_refund">, MT)
       else
       let v = get(bs, sender) in
       backers := remove(bs, sender);
       send (<to -> sender, amount -> v, tag -> "main",
              msg -> "here_is_your_money">, MT)

 *******************************************************)

Record crowdState := CS {
   owner_mb_goal : address * nat * value;
   backers : seq (address * value);
   funded : bool;
}.

(* Administrative setters/getters *)
Definition get_owner cs : address := (owner_mb_goal cs).1.1.
Definition get_goal cs : value := (owner_mb_goal cs).2.
Definition get_max_block cs : nat := (owner_mb_goal cs).1.2.


Definition set_backers cs bs : crowdState :=
  CS (owner_mb_goal cs) bs (funded cs).

Definition set_funded cs f : crowdState :=
  CS (owner_mb_goal cs) (backers cs) f.

(* Defining three layers of initial states *)
(* Parameters *)
Variable init_owner : address.
Variable init_max_block : nat.
Variable init_goal : value.
Variable init_address : address.
(* Initial crowdfunding state *)
Definition init_state : crowdState :=
  CS (init_owner, init_max_block, init_max_block) [::] false.
(* Initial contract state *)
Definition init_cstate : cstate crowdState :=
  CState init_address 0 init_state.
(* Initial world *)
Definition init_world : world crowdState :=
mkW emptymsg init_cstate b0 None.

Definition pred := world crowdState -> Prop.
Variable prot : Protocol crowdState.

Definition reachability : world crowdState -> world crowdState -> Prop := fun w1 w2 => step_world prot w1 = w2.

(* Path definitions *)
Definition path := nat -> world crowdState.
Definition firstp (p : path) : world crowdState := p 0.
Definition path_predicate (p : path) := forall n, reachability (p n) (p (S n)).
(* Good path sigma-type definitions *)
Definition gpath : Type := {p : path & path_predicate p}.
(* Projection functions for sigma type good paths *)
Definition gpath_proj1 : gpath -> (nat -> world crowdState) :=
  fun gp => match gp with
            | existT a _ => a
            end.
Coercion gpath_proj1 : gpath >-> Funclass. 
Definition gpath_proj2 (gp : gpath) : (path_predicate (gpath_proj1 gp)) :=
  match gp with
  | existT _ b => b
  end.
Definition first (gp : gpath) : world crowdState := (gpath_proj1 gp 0).

(* A cacophany of path constructions *)
(* Constructing a random path *) 
Fixpoint step_n_times (w : world crowdState) (n : nat) :=
  match n with
  | 0 => w
  | S n' => step_world prot (step_n_times w n')
  end.

Definition make_path (w : world crowdState) : path := step_n_times w.

Lemma rewrite_step_world_S :
  forall (n : nat) (w : world crowdState),
    step_n_times w (S n) = step_world prot (step_n_times w n).
Proof. reflexivity. Qed.

Lemma step_world_swap_helper :
  forall (n : nat) (w : world crowdState),
    step_world prot (step_n_times w n) =
    step_n_times (step_world prot w) n.
Proof.
  intros n w.
  induction n.
  - reflexivity.
  - rewrite rewrite_step_world_S.
    rewrite IHn.
    rewrite rewrite_step_world_S.
    reflexivity.
Qed.

Lemma step_world_swap :
  forall n : nat,
    step_world prot (step_n_times (step_world prot init_world) n) =
    step_n_times (step_world prot (step_world prot init_world)) n.
Proof.
  induction n.
  - reflexivity.
  - rewrite step_world_swap_helper.
    reflexivity.
Qed.

Lemma step_world_ind :
  forall n : nat,
    step_world prot (step_n_times init_world n) = step_n_times init_world (S n).
Proof.
  induction n.
  - simpl; reflexivity.
  - simpl. reflexivity.
Qed.

Lemma about_p : path_predicate (make_path init_world).
Proof.
  unfold path_predicate.
  induction n.
  - simpl. unfold reachability. reflexivity.
  - unfold reachability in *.
    unfold make_path in *.
    rewrite <- IHn.
    simpl. reflexivity.
Qed.

Lemma about_p_hole :
  forall w : world crowdState,
    path_predicate (make_path w).
Proof.
  unfold path_predicate.
  induction n.
  - simpl. unfold reachability. reflexivity.
  - unfold reachability in *.
    unfold make_path in *.
    rewrite <- IHn.
    simpl. reflexivity.
Qed.

Definition gp : gpath := (existT _ (make_path init_world) about_p).
(* Can you make a sigma type with a dependent type? *)
Parameter generic_world : world crowdState.
Check (about_p_hole generic_world).
Definition gp_hole (w : world crowdState) : gpath := (existT _ (make_path w) (about_p_hole w)).
(* The answer is yes *)

(* Constructing an offset path *)
Definition make_offset_path (p : path) : path := fun n => p (S n).
Definition make_offset_path' (gp : gpath) : path := fun n => gpath_proj1 gp (S n).
Lemma about_offset_path :
  forall p : path,
    path_predicate p ->
    path_predicate (make_offset_path p).
Proof.
  intros p H_p.
  unfold make_offset_path.
  unfold path_predicate in *.
  intro n. 
  exact (H_p (S n)).
Qed.
Lemma about_offset_path' :
  forall gp : gpath,
    path_predicate (make_offset_path' gp). 
Proof.
  intro gp.
  destruct gp. unfold path_predicate in p.
  unfold make_offset_path'.
  unfold gpath_proj1.
  unfold path_predicate.
  intros n.
  exact (p (S n)).
Qed.

Definition gp_offset (p : path) (pred : path_predicate p) : gpath :=
  (existT _ (make_offset_path p) (about_offset_path pred)).
Definition gp_offset' (gp : gpath) : gpath :=
  (existT _ (make_offset_path' gp) (about_offset_path' gp)).

(* Constructing a backwards offset path *)
Definition make_backwards_offset_path (w0 : world crowdState) (p : path) : path :=
  fun n => match n with 0 => w0 | _ => (p (n.-1)) end.
Definition make_backwards_offset_path' (w0 : world crowdState) (gp : gpath) : path :=
  fun n => match n with 0 => w0 | _ => (gpath_proj1 gp (n.-1)) end.
Lemma about_backwards_offset_path :
  forall (p : path) (w0 : world crowdState),
    path_predicate p ->
    reachability w0 (p 0) -> 
    path_predicate (make_backwards_offset_path w0 p).
Proof.
  intros p w0 H_p.
  unfold make_backwards_offset_path.
  unfold path_predicate in *.
  destruct n.
  simpl. exact H.
  simpl. replace (n-0) with n.
  Focus 2. rewrite subn0. reflexivity.
  apply (H_p n).
Qed.
Lemma about_backwards_offset_path' :
  forall (gp : gpath) (w0 : world crowdState),
    reachability w0 (gpath_proj1 gp 0) -> 
    path_predicate (make_backwards_offset_path' w0 gp). 
Proof.
  intros gp w0 H_0.
  destruct gp. unfold path_predicate in p.
  unfold make_backwards_offset_path'.
  unfold gpath_proj1.
  unfold path_predicate.
  destruct n.
  simpl. exact H_0.
  simpl. replace (n-0) with n. Focus 2. rewrite subn0. reflexivity.
  apply (p n).
Qed.
Definition gp_backwards_offset
           (w0 : world crowdState) (p : path)
           (pred : path_predicate p)
           (r : reachability w0 (p 0)) : gpath :=
  (existT _ (make_backwards_offset_path w0 p) (about_backwards_offset_path pred r)).
Definition gp_backwards_offset'
           (w0 : world crowdState) (gp : gpath)
           (r : reachability w0 (gpath_proj1 gp 0)) : gpath :=
  (existT _ (make_backwards_offset_path' w0 gp) (about_backwards_offset_path' r)).    
(* Satisfaction definition *)
Definition satisfies (w : world crowdState) (p : pred) : Prop := p w.
(* I'm not sure that the following metalogic entail is necessary *)
Definition entails (p q : pred) : Prop :=
  forall w, (satisfies w p) -> (satisfies w q).
Definition equiv (p q : pred) : Prop := entails p q /\ entails q p.
 
Axiom LEM : forall P : Prop, P \/ ~ P.
Notation "w '|=' p" := (satisfies w p) (at level 80, no associativity).

(* Temporal operator definitions *)
Parameter Top : pred.
Parameter Bottom : pred.
Axiom about_top : forall w, Top w.
Axiom about_bottom : forall w, Bottom w -> False.
Definition Neg p : pred := fun w => (w |= p) -> False.
Definition Conj p q : pred := fun w => (w |= p) /\ (w |= q).
Definition Disj p q : pred := fun w => (w |= p) \/ (w |= q).
Definition Impl p q : pred := fun w => ~ (w |= p) \/ (w |= q).

(* Temporal operator definitions *)
(* AX says 'in every next state', all gpaths beginning with w next satisfy p. *)
Definition AllNext (p : pred) := fun w =>  
  forall gp : gpath, first gp = w -> gp 1 |= p.
(* EX says 'in some next state', all gpaths beginning with w next satisfy p. *)
Definition ExistsNext (p : pred) := fun w =>  
  exists gp : gpath, first gp = w /\ gp 1 |= p.
(* AG says all states along all paths beginning with  w satisfy p, including w. *)
Definition AllBox (p : pred) := fun w =>  
  forall gp : gpath, first gp = w -> forall n, gp n |= p.
(* EG says that there exists a path beginning with w along which all states satisfy p. *)
Definition ExistsBox (p : pred) := fun w =>  
  exists gp : gpath, first gp = w /\ forall n, gp n |= p.
(* AF says all paths beginning with w contain a future state which satisfies p. *)
Definition AllFuture (p : pred) := fun w =>  
  forall gp : gpath, first gp = w -> exists n, gp n |= p.
(* EF says that there exists a path beginning with a future state which satisfies p. *)
Definition ExistsFuture (p : pred) := fun w =>  
  exists gp : gpath, first gp = w /\  exists n, gp n |= p.
(* AU says that all paths beginning with w satisfy p Until q. *)
Definition AllUntil (p q : pred) := fun w =>  
  forall gp : gpath, first gp = w -> exists n, gp n |= q /\ forall m, m < n -> gp m |= p.
(* EU says that there exists a path beginning with w that satifies p Until q. *)
Definition ExistsUntil (p q : pred) := fun w =>  
  exists gp : gpath, first gp = w /\ exists n, gp n |= q /\ forall m, m < n -> gp m |= p.

(* Extended temporal operator definitions *)
Definition AllRelease (p q : pred) := fun w => 
  Neg (ExistsUntil (Neg p) (Neg q)) w.
Definition ExistsRelease (p q : pred) := fun w => 
  Neg (AllUntil (Neg p) (Neg q)) w.
Definition AllWait (p q : pred) := fun w => 
  AllRelease q (Disj p q) w.
Definition ExistsWait (p q : pred) := fun w =>
  ExistsRelease q (Disj p q) w.

(* Notation definitions *)
Notation "p <=> q" := (equiv p q) (at level 35, no associativity).
Notation "! p" := (Neg p) (at level 60, right associativity).
Notation "p && q" := (Conj p q) (at level 40, left associativity).
Notation "p || q" := (Disj p q).
Notation "p --> q" := (Impl p q) (at level 35, no associativity).
Notation "'AG' p" := (AllBox p) (at level 35, no associativity).
Notation "'EG' p" := (ExistsBox p) (at level 35, no associativity).
Notation "'AX' p" := (AllNext p) (at level 35, no associativity).
Notation "'EX' p" := (ExistsNext p) (at level 35, no associativity).
Notation "'AF' p" := (AllFuture p) (at level 35, no associativity).
Notation "'EF' p" := (ExistsFuture p) (at level 35, no associativity). 
Notation "'A' '[' p 'U' q ']'" := (AllUntil p q) (at level 35, no associativity).
Notation "'E' '[' p 'U' q ']'" := (ExistsUntil p q) (at level 35, no associativity).
Notation "'A' '[' p 'R' q ']'" := (AllRelease p q) (at level 35, no associativity).
Notation "'E' '[' p 'R' q ']'" := (ExistsRelease p q) (at level 35, no associativity).
Notation "'A' '[' p 'W' q ']'" := (AllWait p q) (at level 35, no associativity).
Notation "'E' '[' p 'W' q ']'" := (ExistsWait p q) (at level 35, no associativity).

Theorem ctl_1 : forall (P : pred),
    AG P <=> (P && AX (AG P)).
Proof. Admitted.
Theorem ctl_2 : forall (P : pred),
    (P && AX (AG P)) <=> AG P.
Proof. Admitted.
Theorem ctl_3 : forall (P : pred),
    EG P <=> (P && EX (EG P)).
Proof. Admitted.      
Theorem ctl_4 : forall (P : pred),
    (P && EX (EG P)) <=> EG P.
Proof. Admitted.
Theorem equiv_1 : forall (P : pred),
    AX P <=> ! (EX (! P)).
Proof. Admitted.
Theorem equiv_2 : forall (P : pred),
    AF P <=> ! (EG (! P)).
Proof. Admitted.
Theorem equiv_3 : forall (P : pred),
    AG P <=> ! (EF (!P)).
Proof. Admitted.
Theorem equiv_4 : forall (P : pred),
    AF P <=> A [Top U P]. 
Proof. Admitted.
Theorem equiv_5 : forall (P : pred),
    EF P <=> E [Top U P].
Proof. Admitted.
Theorem equiv_6 : forall (P Q : pred),
    A [P U Q] <=> E [!P U (!P && !Q)] && AF Q.
Proof. Admitted.


(*********************************************************)
(********************* Transitions ***********************)
(*********************************************************)

(* Transition 1 *)
(*
transition Donate
  (sender : address, value : uint, tag : string)
  (* Simple filter identifying this transition *)
  if tag == "donate" =>

  bs <- & backers;
  blk <- && block_number; 
  let nxt_block = blk + 1 in
  if max_block <= nxt_block
  then send (<to -> sender, amount -> 0,
	      tag -> main,
	      msg -> "deadline_passed">, MT)
  else
    if not (contains(bs, sender))
    then let bs1 = put(sbs, ender, value) in
         backers := bs1;
         send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "ok">, MT)
    else send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "already_donated">, MT)
 *)

(* Definition of the protocol *)
Variable crowd_addr : address.

Notation tft := (trans_fun_type crowdState).
Definition ok_msg := [:: (0, [:: 1])].
Definition no_msg := [:: (0, [:: 0])].

Definition donate_tag := 1.
Definition donate_fun : tft := fun id bal s m bc =>
  if method m == donate_tag then
    let bs := backers s in
    let nxt_block := block_num bc + 1 in
    let from := sender m in
    if get_max_block s <= nxt_block
    then (s, Some (Msg 0 crowd_addr from 0 no_msg))
    else if all [pred e | e.1 != from] bs
         (* new backer *)
         then let bs' := (from, val m) :: bs in
              let s'  := set_backers s bs' in
              (s', Some (Msg 0 crowd_addr from 0 ok_msg))
         else (s, Some (Msg 0 crowd_addr from 0 no_msg))
  else (s, None).

Definition donate := CTrans donate_tag donate_fun.

(* Transition 2: Sending the funds to the owner *)
(*
transition GetFunds
  (sender : address, value : uint, tag : string)
  (* Only the owner can get the money back *)
  if (tag == "getfunds") && (sender == owner) =>
  blk <- && block_number;
  bal <- & balance;
  if max_block < blk
  then if goal <= bal
       then funded := true;   
            send (<to -> owner, amount -> bal,
                   tag -> "main", msg -> "funded">, MT)
       else send (<to -> owner, amount -> 0,
                   tag -> "main", msg -> "failed">, MT)
  else send (<to -> owner, amount -> 0, tag -> "main",
   	      msg -> "too_early_to_claim_funds">, MT)
 *)

Definition getfunds_tag := 2.
Definition getfunds_fun : tft := fun id bal s m bc =>
  let: from := sender m in
  if (method m == getfunds_tag) && (from == (get_owner s)) then
    let blk := block_num bc + 1 in
    if (get_max_block s < blk)
    then if get_goal s <= bal
         then let s' := set_funded s true in
              (s', Some (Msg bal crowd_addr from 0 ok_msg))
         else (s, Some (Msg 0 crowd_addr from 0 no_msg))
    else (s, Some (Msg 0 crowd_addr from 0 no_msg))
  else (s, None).

Definition get_funds := CTrans getfunds_tag getfunds_fun.

(* Transition 3: Reclaim funds by a backer *)
(*
transition Claim
  (sender : address, value : uint, tag : string)
  if tag == "claim" =>
  blk <- && block_number;
  if blk <= max_block
  then send (<to -> sender, amount -> 0, tag -> "main",
              msg -> "too_early_to_reclaim">, MT)
  else bs <- & backers;
       bal <- & balance;
       if (not (contains(bs, sender))) || funded ||
          goal <= bal
       then send (<to -> sender, amount -> 0,
                   tag -> "main",
	           msg -> "cannot_refund">, MT)
       else
       let v = get(bs, sender) in
       backers := remove(bs, sender);
       send (<to -> sender, amount -> v, tag -> "main",
              msg -> "here_is_your_money">, MT)
*)

Definition claim_tag := 3.
Definition claim_fun : tft := fun id bal s m bc =>
  let: from := sender m in
  if method m == claim_tag then
    let blk := block_num bc in
    if blk <= get_max_block s
    then
      (* Too early! *)
      (s, Some (Msg 0 crowd_addr from 0 no_msg))
    else let bs := backers s in
         if [|| funded s | get_goal s <= bal]
         (* Cannot reimburse: campaign suceeded *)
         then (s, Some (Msg 0 crowd_addr from 0 no_msg))
         else let n := seq.find [pred e | e.1 == from] bs in
              if n < size bs
              then let v := nth 0 (map snd bs) n in
                   let bs' := filter [pred e | e.1 != from] bs in
                   let s'  := set_backers s bs' in
                   (s', Some (Msg v crowd_addr from 0 ok_msg))
              else
                (* Didn't back or already claimed *)
                (s, None)
  else (s, None).

Definition claim := CTrans claim_tag claim_fun.

Program Definition crowd_prot : Protocol crowdState :=
  @CProt _ crowd_addr 0 init_state [:: donate; get_funds; claim] _.

Lemma crowd_tags : tags crowd_prot = [:: 1; 2; 3].
Proof. by []. Qed.

(* 
Lemma find_leq {A : eqType} (p : pred (A * nat)) (bs : seq (A * nat)) :
  nth 0 [seq i.2 | i <- bs] (seq.find p bs) <= sumn [seq i.2 | i <- bs].
Proof.
elim: bs=>//[[a w]]bs/=Gi; case:ifP=>_/=; first by rewrite leq_addr.
by rewrite (leq_trans Gi (leq_addl w _)).
Qed.
*)

(***********************************************************)
(**             Correctness properties                    **)
(***********************************************************)

(************************************************************************

1. The contract always has sufficient balance to reimburse everyone,
unless it's successfully finished its campaign:

The "funded" flag is set only if the campaign goals were reached, then
all money goes to owner. Otherwise, the contract keeps all its money
intact.

Perhaps, we should make it stronger, adding a temporal property that
one's reimbursement doesn't change.

************************************************************************)

Definition notfunded : pred :=
  fun w => funded (state (st w)) = false.
Definition balance_sufficient : pred :=
  fun s => sumn (map snd (backers (state (st s)))) <= balance (st s).

Lemma temporal_balance_backed :
    init_world |= AG (notfunded --> balance_sufficient).
Proof.
  unfold satisfies.
  unfold AllBox.
  intros gp H_first n. 
  unfold satisfies, Impl.
  destruct gp as [p r]; simpl.
  unfold path_predicate in r.
  remember n as path_index.
  induction n.
  - right.  
    unfold satisfies.
    rewrite Heqpath_index.
    simpl in H_first.
    rewrite H_first.
    unfold init_world; unfold init_cstate; unfold init_state.
    unfold balance_sufficient.
    (* Now we have a mess on our hands, but for base case it's alright *)
    simpl. reflexivity.  (* Hurray! *)
  - assert (reachability (p n) (p n.+1)). 
    exact (r n).
    unfold reachability in H.
    unfold step_world in H.
    destruct st.
    (* NOW we have a real mess. *)
    (* How to get a clean case distinction on the three transitions? *)
Abort.

(* Ilya's proof for non-temporal model: 
apply: safe_ind=>[|[id bal s]bc m M Hi]//.
rewrite crowd_tags !inE in M.
(* Get the exact transitions and start struggling... *)
rewrite /= /apply_prot; case/orP: M; [|case/orP]=>/eqP M; rewrite M/=.

(* Donate transition *)
rewrite /donate_fun M eqxx.
case: ifP=>/=_; [move/Hi=>{Hi}Hi|].
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
case: ifP=>/=_; move/Hi=>{Hi}Hi; last first.
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
by rewrite subn0 /balance_backed/= in Hi *; rewrite addnC leq_add2r.

(* Get funds transition. *)
rewrite /getfunds_fun M eqxx.
case: ifP=>//=_; case:ifP=>//=_;[|move/Hi=>{Hi}Hi]; last first.
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
case: ifP=>//=_; move/Hi=>{Hi}Hi.
by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).

(* Claim funds back *)
rewrite /claim_fun M eqxx.
case: ifP=>//=_; [move/Hi=>{Hi}Hi|].
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
case: ifP=>//=X.
- case/orP: X; first by rewrite /balance_backed/==>->.
  by move=>_/Hi Z; rewrite subn0; apply: (leq_trans Z (leq_addr (val m) bal)).
case: ifP=>//=G/=; move/Hi=>/={Hi}Hi.
rewrite addnC.
have H1: nth 0 [seq i.2 | i <- backers s]
             (seq.find [pred e | e.1 == sender m] (backers s)) <=
         sumn [seq i.2 | i <- backers s] by apply: find_leq.
move: (leq_trans H1 Hi)=> H2.
rewrite -(addnBA _ H2); clear H2.
suff H3: sumn [seq i.2 | i <- backers s & [pred e | e.1 != sender m] i] <=
         bal - nth 0 [seq i.2 | i <- backers s]
                   (seq.find [pred e | e.1 == sender m] (backers s)).
- by apply: (leq_trans H3 (leq_addl (val m) _ )).
clear M.
suff H2: sumn [seq i.2 | i <- backers s & [pred e | e.1 != sender m] i] <=
         sumn [seq i.2 | i <- backers s] -
         nth 0 [seq i.2 | i <- backers s] (seq.find [pred e | e.1 == sender m] (backers s)).
- by apply: (leq_trans H2); apply: leq_sub.
clear Hi H1 X G bc bal id crowd_addr init_goal init_max_block init_owner.
move: (backers s)=>bs{s}.
elim:bs=>//[[a v]] bs/= Hi/=; case:ifP; last first.
- move/negbT; case: ifP=>//= _ _; rewrite addnC -addnBA//subnn addn0.
  clear Hi; elim: bs=>//={a v}[[a v]]bs/=.
  case:ifP=>//=_ H; first by rewrite leq_add2l. 
  by rewrite (leq_trans H (leq_addl _ _)).
move/negbTE=>->/={a}; rewrite -(leq_add2l v) in Hi. 
by rewrite addnBA in Hi; last by apply: find_leq.
Qed. *)

(***********************************************************************)
(******           Proving temporal properties                     ******)
(***********************************************************************)

(* Contribution of backer b is d is recorded in the `backers` *)
Definition donated b (d : value) st :=
  (filter [pred e | e.1 == b] (backers (state st))) == [:: (b, d)].

(* b doesn't claim its funding back *)
Definition no_claims_from b (q : bstate * message) := sender q.2 != b.

(************************************************************************

2. The following lemma shows that the donation record is going to be
preserved by the protocol since the moment it's been contributed, as
long, as no messages from the corresponding backer b is sent to the
contract. This guarantees that the contract doesn't "drop" the record
about someone's donations.

In conjunctions with sufficient_funds_safe (proved above) this
guarantees that, if the campaign isn't funded, there is always a
necessary amount on the balance to reimburse each backer, in the case
of failure of the campaign.

************************************************************************)
(* 
Lemma donation_preserved (b : address) (d : value):
  since_as_long crowd_prot (donated b d)
                (fun _ s' => donated b d s') (no_claims_from b).
Proof.
(* This is where we would need a temporal logic, but, well.. *)
(* Let's prove it out of the definition. *)
elim=>[|[bc m] sc Hi]st st' P R; first by rewrite /reachable'=>/=Z; subst st'.
rewrite /reachable'/==>E. 
apply: (Hi (post (step_prot crowd_prot st bc m))); last 2 first; clear Hi.
- by move=>q; move:(R q)=>{R}R G; apply: R; apply/In_cons; right.
- rewrite E; set st1 := (step_prot crowd_prot st bc m); clear E R P.
  by case: sc st1=>//=[[bc' m']] sc st1/=.   
clear E.
have N: sender m != b. 
- suff B: no_claims_from b (bc, m) by [].
  by apply: R; apply/In_cons; left.
case M: (method m \in tags crowd_prot); last first.
- by move/negbT: M=>M; rewrite (bad_tag_step bc st M).
case: st P=>id a s; rewrite /donated/==>D. 
case/orP: M; [|case/orP;[| rewrite orbC]]=>/eqP T; 
rewrite /apply_prot T/=. 
- rewrite /donate_fun T/=; case: ifP=>//_; case: ifP=>//_/=.
  by move/negbTE: N=>->. 
- by rewrite /getfunds_fun T/=; case: ifP=>//_; case: ifP=>//_; case:ifP.
rewrite /claim_fun T/=; case:ifP=>//_; case: ifP=>//_; case: ifP=>//=X.
rewrite -filter_predI/=; move/eqP:D=><-; apply/eqP.
elim: (backers s)=>//=x xs Hi; rewrite Hi; clear Hi.
case B: (x.1 == b)=>//=.
by move/eqP: B=>?; subst b; move/negbTE: N; rewrite eq_sym=>/negbT=>->.
Qed. *)

(************************************************************************

3. The final property: if the campaign has failed (goal hasn't been
reached and the deadline has passed), every registered backer can get
its donation back.

TODO: formulate and prove it.

************************************************************************)
(*
Lemma can_claim_back b d st bc:
  (* We have donated, so the contract holds that state *)
  donated b d st ->
  (* Not funded *)
  ~~(funded (state st)) ->
  (* Balance is small: not reached the goal *)
  balance st < (get_goal (state st)) ->
  (* Block number exceeds the set number *)
  get_max_block (state st) < block_num bc ->
  (* Can emit message from b *)
  exists (m : message),
    sender m == b /\
    out (step_prot crowd_prot st bc m) = Some (Msg d crowd_addr b 0 ok_msg).
Proof.
move=>D Nf Nb Nm.
exists (Msg 0 b crowd_addr claim_tag [::]); split=>//.
rewrite /step_prot.
case: st D Nf Nb Nm =>id bal s/= D Nf Nb Nm.
rewrite /apply_prot/=/claim_fun/=leqNgt Nm/= leqNgt Nb/=.
rewrite /donated/= in D.
move/negbTE: Nf=>->/=; rewrite -(has_find [pred e | e.1 == b]) has_filter.
move/eqP: D=>D; rewrite D/=.
congr (Some _); congr (Msg _ _ _ _ _). 
elim: (backers s) D=>//[[a w]]bs/=; case:ifP; first by move/eqP=>->{a}/=_; case. 
by move=>X Hi H; move/Hi: H=><-. 
Qed.
*)

(************************************************************************

4. Can we have a logic that allows to express all these properties
declaratively? Perhaps, we could do it in TLA?

(This is going to be our future work.)

************************************************************************)

End Crowdfunding.
