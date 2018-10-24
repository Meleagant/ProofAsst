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

(* We « forget » the variables. It raises a few warnings, 
	but nothing alarming *)
Reset A. 
Reset B. 
Reset C. 
