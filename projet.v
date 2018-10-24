(* Ceci est le projet du cours d'assistants de preuves *)
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
End Tests.

(* II.3 Backtrack control *)
(* ---------------------- *)

(* TODO *)

(* III. Formalizing the tactic *)
(* ========================== *)

(* III.1. Tactic steps *)
(* ------------------- *)

Require Import List.

Inductive form : Type :=
    | Leaf : nat -> form (* Axiom was already taken :( *)
    | True_form : form
    | False_form : form
    | Impl : form -> form -> form
    | And : form -> form -> form
    | Or : form -> form -> form .

Print List.

Definition seq : Type :=
    (list form)* form.

Print In.
Print true.
Print True.

Definition is_leaf ( seq : seq ) : bool :=
    match snd seq with
    | True_form => true
    | Leaf n => (
        match In (Leaf n) (fst seq) with
        | True => true
        (* | _ => false *)
        end
    )
    | _ => (
        match In False_form (fst seq) with
        | False => false
        (* | _ => true *)
        end
    )
    end.

Print is_leaf.

Print or.

(* III.3. Soundness *)
(* ---------------- *)

(* 1- *)
Fixpoint sem (f : form) : Prop :=
    match f with
    | True_form => True
    | False_form => False
    | Leaf _ => True (* TODO *)
    | Impl f1 f2 => (sem f1) -> (sem f2)
    | And f1 f2 => (sem f1) /\ (sem f2)
    | Or f1 f2 => (sem f1) \/ (sem f2)
    end.

Definition seq_valid (s : seq) : Prop :=
    sem (fst s) -> sem (snd s).

Lemma Leaf_sound : forall s : seq, is_leaf s  -> sem  