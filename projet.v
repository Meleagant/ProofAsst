(* Ceci est le projet du cours d'assistants de preuves du MPRI 2-7-2 *)
(* Josselin GIET M2 DI/ENS *)


(* II. Implementing the decision procedure *)
(* ======================================= *)

(* II.2. Building the tactic *)
(* ------------------------- *)

(* 1- *)
Ltac tauto1 :=
    match goal with
    (* ===/  Easy rules  \=== *)
    (* ---------------------- *)
    (* Rule : [Ax] *)
    | _ : ?A |- ?A =>
        idtac "Ax";
        assumption
    (* Rule : [False - E] *)
    | _ : False |- _ =>
        idtac "False - E";
        contradiction
    (* Rule : [True - I] *)
    | |- True =>
        idtac "True - I";
        auto

    (* ===/  Rules for ->  \=== *)
    (* ----------------------- *)
    (* Rule : [-> - I]*)
    | |- ?A -> ?B =>
        idtac "->-I";
        intro; tauto1
    (* Rule : [-> - E]*)
    | H : ?A -> ?B |- ?C =>
        idtac "->-E";
        let Ha := fresh in
        let Hb := fresh in
        assert (Hb : B);
            [
                assert( Ha : A);
                [
                    clear H; tauto1
                |
                    apply H in Ha;
                    assumption
                ]
            |
            clear H; tauto1]

    (* ===/  Rules for \/  \=== *)
    (* ----------------------- *)
    (* Rule : [\/ - I] *)
    | |- ?A \/ ?B =>
        idtac "\/-I";
        (left; tauto1) || (right; tauto1)
    (* Rule : [\/ - E] *)
    | H: ?A \/ ?B |- _ =>
        idtac "\/-E";
        destruct H; [tauto1 | tauto1]

    (* ===/  Rules for /\  \=== *)
    (* ----------------------- *)
    (* Rule : [/\ - I] *)
    | |- ?A /\ ?B =>
        idtac "/\-I";
        split; [tauto1 | tauto1] 
    (* Rule : [/\ - E] *)
    | H: ?A /\ ?B |- _ =>
        idtac "/\-E";
        destruct H; tauto1
    end.

(* 2- *)
(* Some tests that are all solved by a call ro tauto1 !*)
Section Tests.
    Variable A : Prop.
    Variable B : Prop.
    Variable C : Prop.
    Lemma Test1 : False -> A.
    Proof.
        tauto1.
    Qed.
    Lemma Test2 : A /\ B -> A.
    Proof.
        tauto1.
    Qed.
    Lemma Test3 : A /\ B -> B.
    Proof.
        tauto1.
    Qed.
    Lemma Test4 : A /\ B -> B /\ A.
    Proof.
        tauto1.
    Qed.
    Lemma Test5 : A -> A \/ B.
    Proof.
        tauto1.
    Qed.
    Lemma Test6 : B -> A \/ B.
    Proof.
        tauto1.
    Qed.
    Lemma Test7 : ( A -> C ) -> ( B -> C ) -> A \/ B -> C.
    Proof.
        tauto1.
    Qed.
    Lemma Test8 : A -> ( A -> B ) -> B.
    Proof.
        tauto1.
    Qed.
    Lemma test9 : A -> ( A -> B ) -> ( B -> C ) -> B.
    Proof.
        tauto1.
    Qed.
    Lemma test10 : A -> ( A -> B ) -> ( B -> C ) -> C.
    Proof.
        tauto1.
    Qed.
    Lemma test_fast : A /\ B \/ True.
    Proof.
        tauto1.
    Qed.
End Tests.

(* II.3 Backtrack control *)
(* ---------------------- *)

(* 1- *)
(* Les règles réversibles sont : 
    - [-> - I]
    - [/\ - I]
    - [/\ - E]
    - [\/ - I]
    - [\/ - E]
La règle [-> - E] n'est pas réversible en effet si on considère le séquent : 

   C |- A        B, C |- C
  ------------------------
       A -> B, C |- C

Le code obtenu est donc un copier coller de tauto1 à un e exception près :
Toutes stratégies non atomiques (i.e. celles qui ne sont pas [Ax] [False-E] ou 
[True-I]) à l'exception de [-> - E] sont de la forme 
  ( <\tactique essayée\> ) + ( idtac "back [rulename]"k; fail 1 )
*)

Ltac tauto2 :=
    match goal with
    (* ===/  Easy rules  \=== *)
    (* ---------------------- *)
    (* Rule : [Ax] *)
    | _ : ?A |- ?A =>
        idtac "Ax";
        assumption
    (* Rule : [False - E] *)
    | _ : False |- _ =>
        idtac "False-E";
        contradiction
    (* Rule : [True - I] *)
    | |- True =>
        idtac "True-I";
        auto

    (* ===/  Rules for ->  \=== *)
    (* ----------------------- *)
    (* Rule : [-> - I]*)
    | |- ?A -> ?B =>
        idtac "->-I";
        (intro; tauto2) + (idtac "back [->-I]"; fail 1)
    (* Rule : [-> - E]*)
    | H : ?A -> ?B |- ?C =>
        idtac "->-E";
        let Ha := fresh in
        let Hb := fresh in
        assert (Hb : B);
            [
                assert( Ha : A);
                [
                    clear H; tauto2
                |
                    apply H in Ha;
                    assumption
                ]
            |
            clear H; tauto2]

    (* ===/  Rules for \/  \=== *)
    (* ----------------------- *)
    (* Rule : [\/ - I] *)
    | |- ?A \/ ?B =>
        idtac "\/-I";
        ((left; tauto2) || (right; tauto2)) + (idtac "back [\/-I]"; fail 1)
    (* Rule : [\/ - E] *)
    | H: ?A \/ ?B |- _ =>
        idtac "\/-E";
        (destruct H; [tauto2 | tauto2]) + (idtac "back [\/-E]"; fail 1)

    (* ===/  Rules for /\  \=== *)
    (* ----------------------- *)
    (* Rule : [/\ - I] *)
    | |- ?A /\ ?B =>
        idtac "/\-I";
        (split; [tauto2 | tauto2]) + (idtac "back [/\-I]"; fail 1) 
    (* Rule : [/\ - E] *)
    | H: ?A /\ ?B |- _ =>
        idtac "/\-E";
        (destruct H; tauto2) + (idtac "back [/\-E]"; fail 1)
    end.

(* 2- *)
Lemma exple_backtracking : forall A B  : Prop,
    (* A /\ A -> A /\ A -> A /\ A -> *) A /\ A -> A /\ A -> (B \/ B) \/ A.
Proof.
    intros A B.
    tauto1.  (* Fait un grand nombre d'essais d'appels de règles *)
    Restart.
    intros A B.
    tauto2. (* Fait beaucoup moins de règles... *)
Qed. 

(* III. Formalizing the tactic *)
(* ========================== *)

(* III.1. Tactic steps *)
(* ------------------- *)

(* 1- *)

Require Import List Arith.

Inductive form : Set :=
    | Leaf : nat -> form (* Axiom was already taken :( *)
    | True_form : form
    | False_form : form
    | Impl : form -> form -> form
    | And : form -> form -> form
    | Or : form -> form -> form .

Print List.

Definition seq : Set :=
    (list form)* form.


(* 2- *)

Fixpoint equal_form (f1 f2 : form) : bool :=
  match f1, f2 with
  | Leaf n1, Leaf n2 => beq_nat n1 n2
  | True_form, True_form 
  | False_form, False_form => true
  | Impl f1g f1d, Impl f2g f2d => andb (equal_form f1g f2g) (equal_form f1d f2d)
  | And f1g f1d, Impl f2g f2d => andb (equal_form f1g f2g) (equal_form f1d f2d)
  | Or f1g f1d, Impl f2g f2d => andb (equal_form f1g f2g) (equal_form f1d f2d) 
  | _, _ => false
  end.


Fixpoint in_bool (l : list form) (f : form) :=
  match l with
  | nil => false
  | cons f' l' => orb (equal_form f' f) (in_bool l' f)
  end.

Definition is_leaf ( seq : seq ) : bool :=
    match snd seq with
    | True_form => true                   (* Si on doit prouver le TOP *)
    | Leaf _ as f =>                      (* Quand le but est une variable *)
      orb (in_bool (fst seq) f)             (* On regarde si elle n'est pas dans les hypothèses *)
          (in_bool (fst seq) False_form)    (* Sinon, on regarde si on a l'hypothèse BOTTOM *)
    | _ => in_bool (fst seq) False_form   (* Pour les autres cas, on regarde si on a l'hypothèse BOTTOM *)
    end.

Print is_leaf.

(* 3- *)

Definition subgoals := list (list seq).

Fixpoint merge_subgoals (l1 : subgoals) (l2 : subgoals) : subgoals :=
  match l1 with 
  | nil => l2
  | hd::tl => hd::(merge_subgoals tl l2)
  end.

Definition picked_hyp := list (form * list form).

Fixpoint add_hyp (to_add : form) (hyps : picked_hyp) : picked_hyp :=
  match hyps with
  | nil => nil 
  | cons (hyp, other_hyps) tl => 
    (hyp, cons to_add other_hyps) :: (add_hyp to_add tl)
  end.

Fixpoint pick_hyp_aux ( hyps : list form ) : picked_hyp :=
  match hyps with
  | nil => nil
  | cons hd tl => 
   (hd, tl) :: (add_hyp hd (pick_hyp_aux tl))
  end.

Definition pick_hyp (seq : seq) : picked_hyp :=
  pick_hyp_aux (fst seq).

Definition intro_rules (seq : seq) : subgoals :=
  match snd seq with
  | Leaf _ | True_form | False_form => nil
  | Impl premisse conclusion =>
    ((cons premisse (fst seq), conclusion)::nil )::nil
  | And left_form right_form =>
    ((fst seq, left_form) :: (fst seq, right_form) ::nil)::nil
  | Or left_form right_form =>
    ((fst seq, left_form)::nil) :: ((fst seq, right_form)::nil)::nil
  end.

Definition elim_rules (hyps : form * list form) (goal : form) : subgoals :=
  match fst hyps with
  | Leaf _ | True_form | False_form => nil
  | Impl premisse conclusion =>
    ((snd hyps, premisse) :: (conclusion::(snd hyps), goal) :: nil)::nil
  | And left_form right_form =>
    ((left_form::right_form::(snd hyps), goal)::nil)::nil
  | Or left_form right_form =>
    ( (left_form :: (snd hyps), goal) :: (right_form :: (snd hyps), goal) :: nil )::nil
  end.


  
Fixpoint elim_rules_multi (hyps : picked_hyp) (goal : form) : subgoals :=
  match hyps with
  | nil => nil
  | hyp :: tl => merge_subgoals (elim_rules hyp goal) (elim_rules_multi tl goal)
  end.

Definition step (seq : seq) : subgoals :=
  merge_subgoals (intro_rules seq) (elim_rules_multi (pick_hyp seq) (snd seq)).

(* 4- *)

Fixpoint tauto (fuel : nat) (seqt : seq) : bool :=
  if is_leaf seqt then
    true
  else
    match fuel with
    | 0 => false
    | S n =>
      (* le nom « étrange » donné à subgoalz corrige les problèmes de typage
         pour éviter le shadowing du type par la variable *)
      let subgoalz := step seqt in
      let fix handle_subgoal (subgoal: list seq) : bool :=
        match subgoal with
        | nil => true 
        | seq :: tl => andb(tauto n seq) (handle_subgoal tl)
        end in
      let fix handle_subgoals (subgoalz: subgoals) : bool :=
        match subgoalz with
        | nil => false
        | subgoal :: tl => orb (handle_subgoal subgoal) (handle_subgoals tl)
        end in
      handle_subgoals subgoalz
    end. 


(* III.2. Termination *)
(* ------------------ *)

(* 1- *)

Fixpoint size_form (f : form) : nat :=
  match f with
  | Leaf _ | True_form | False_form => 1
  | Impl f1 f2 => 1 + (size_form f1) + (size_form f2)
  | And f1 f2 => 1 + (size_form f1) + (size_form f2)
  | Or f1 f2 => 1 + (size_form f1) + (size_form f2)
  end.

Fixpoint size_hyps (hyps : list form) : nat :=
  match hyps with
  | nil => 0
  | hyp :: hyps => (size_form hyp) + (size_hyps hyps)
  end.

Definition size_seq (seq : seq) : nat :=
  let hyps := fst seq in
  let goal := snd seq in
  (size_hyps hyps) + (size_form goal).

(* 2- *)

Lemma size_decrease : 
  forall s : seq, forall s' : seq, forall subgoal : list seq, 
  (In subgoal (step s)) /\ (In s' subgoal) -> (size_seq s') < (size_seq s).
Proof.
  intros s s' sg.
  intros H.
  
  simpl.
Admitted.

(* III.3. Soundness *)
(* ---------------- *)

(* 1- *)
Fixpoint sem (f : form) (sem_nat : nat -> Prop) : Prop :=
    match f with
    | True_form => True
    | False_form => False
    | Leaf n => sem_nat n
    | Impl f1 f2 => (sem f1 sem_nat) -> (sem f2 sem_nat)
    | And f1 f2 => (sem f1 sem_nat) /\ (sem f2 sem_nat)
    | Or f1 f2 => (sem f1 sem_nat) \/ (sem f2 sem_nat)
    end.


Fixpoint sem_hyps (hyps : list form) (sem_nat : nat -> Prop) :=
  match hyps with
  | nil => True 
  | hyp :: hyps => (sem hyp sem_nat) /\ (sem_hyps hyps sem_nat)
  end.

Definition seq_valid (s : seq) : Prop :=
    forall sem_nat : nat -> Prop, 
    sem_hyps (fst s) sem_nat -> sem (snd s) sem_nat.

Lemma Leaf_sound : forall s : seq, is_leaf s  -> sem  
