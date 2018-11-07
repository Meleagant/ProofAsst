(* Ceci est le projet du cours d'assistants de preuves du MPRI 2-7-2 *)
(* Josselin GIET M2 DI/ENS *)


(* II. Implementing the decision procedure *)
(* ======================================= *)

(* II.2. Building the tactic *)
(* ------------------------- *)


(* ___  ___     ____      _
  |_ _||_ _|   |___ \    / |
   | |  | |      __) |   | |
   | |  | |  _  / __/  _ | |
  |___||___|(_)|_____|(_)|_|
*)
(*  _              _        _
   | |_ __ _ _   _| |_ ___ / |
   | __/ _` | | | | __/ _ \| |
   | || (_| | |_| | || (_) | |
    \__\__,_|\__,_|\__\___/|_|
*)

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

(*  ___  ___     ____      ____
   |_ _||_ _|   |___ \    |___ \
    | |  | |      __) |     __) |
    | |  | |  _  / __/  _  / __/
   |___||___|(_)|_____|(_)|_____|
*)
(* Voici les tests : tous résolus par un appel à tauto1 ! *)
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


(* ___  ___     _____    _ 
  |_ _||_ _|   |___ /   / |
   | |  | |      |_ \   | |
   | |  | |  _  ___) |_ | |
  |___||___|(_)|____/(_)|_|
*)
(* Les règles réversibles sont : 
    - [-> - I]
    - [/\ - I]
    - [/\ - E]
    - [\/ - I] 
      /!\ La version utilisée est `(left; tauto1) || (right; tauto1)`
    - [\/ - E]

La règle [-> - E] n'est pas réversible en effet si on considère le séquent : 

   C |- A        B, C |- C
  ========================
       A -> B, C |- C

Le code obtenu est donc un « copier-coller » de tauto1 à un changement près :
Toutes stratégies non atomiques (i.e. celles qui ne sont pas [Ax] [False-E] ou 
[True-I]) à l'exception de [-> - E] sont dès lors de la forme 
  ( <\tactique essayée\> ) + ( idtac "back [rulename]"k; fail 1 )
*)
(* _              _       ____  
  | |_ __ _ _   _| |_ ___|___ \ 
  | __/ _` | | | | __/ _ \ __) |
  | || (_| | |_| | || (_) / __/ 
   \__\__,_|\__,_|\__\___/_____|
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

(* ___  ___     _____    ____  
  |_ _||_ _|   |___ /   |___ \ 
   | |  | |      |_ \     __) |
   | |  | |  _  ___) |_  / __/ 
  |___||___|(_)|____/(_)|_____|
*)
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

(* Quelques importations utiles ... *)
Require Import List Arith Bool.

(* ___  ___  ___     _     _ 
  |_ _||_ _||_ _|   / |   / |
   | |  | |  | |    | |   | |
   | |  | |  | |  _ | | _ | |
  |___||___||___|(_)|_|(_)|_|
*)
(*  __
   / _| ___  _ __ _ __ ___
  | |_ / _ \| '__| '_ ` _ \
  |  _| (_) | |  | | | | | |
  |_|  \___/|_|  |_| |_| |_|
*)
(* Définition du type des formules. *)
Inductive form : Set :=
    | Leaf : nat -> form
    | True_form : form
    | False_form : form
    | Impl : form -> form -> form
    | And : form -> form -> form
    | Or : form -> form -> form .

(* ___  ___  __ _
  / __|/ _ \/ _` |
  \__ \  __/ (_| |
  |___/\___|\__, |
               |_|
*)
(* Définition du type d'un séquant. *)
Definition seq : Set :=
    (list form)* form.

(* ___  ___  ___     _     ____
  |_ _||_ _||_ _|   / |   |___ \
   | |  | |  | |    | |     __) |
   | |  | |  | |  _ | | _  / __/
  |___||___||___|(_)|_|(_)|_____|
*)
(* Tout d'abord, une fonction annexe qui décide si deux formules sont égales *)
Fixpoint equal_form (f1 f2 : form) : bool :=
  match f1, f2 with
  | Leaf n1, Leaf n2 => beq_nat n1 n2
  | True_form, True_form 
  | False_form, False_form => true
  | Impl f1g f1d, Impl f2g f2d => andb (equal_form f1g f2g) (equal_form f1d f2d)
  | And f1g f1d, And f2g f2d => andb (equal_form f1g f2g) (equal_form f1d f2d)
  | Or f1g f1d, Or f2g f2d => andb (equal_form f1g f2g) (equal_form f1d f2d) 
  | _, _ => false
  end.

(* Le lemme qui vérifie la validité de la fonction précédente.
   On ne vérifie qu'une implication, mais c'est suffisant pour la suite.
   La preuve ne peut pas se faire avec une simple induction,
   on utilise donc une récurrence forte, par un point fixe. *)
Lemma equal_form_sound : forall f1 f2 : form, 
  (equal_form f1 f2) = true -> f1 = f2.
Proof.
  fix Hl 1.
  intros f1 f2.
  destruct f1,f2;
  simpl; intro H; first [inversion H  ].
  + apply beq_nat_true in H; rewrite H; reflexivity.
  + reflexivity.
  + reflexivity.
  + apply andb_true_iff in H; destruct H as [H_1 H_2].
    apply Hl in H_1.
    apply Hl in H_2.
    rewrite H_1; rewrite H_2.
    reflexivity.
  + apply andb_true_iff in H; destruct H as [H_1 H_2].
    apply Hl in H_1.
    apply Hl in H_2.
    rewrite H_1; rewrite H_2.
    reflexivity.
+ apply andb_true_iff in H; destruct H as [H_1 H_2].
    apply Hl in H_1.
    apply Hl in H_2.
    rewrite H_1; rewrite H_2.
    reflexivity.
Qed.


(* De même, on se donne une fonction booléenne qui teste si une formule
   est présente dans une liste de formules. *) 
Fixpoint in_bool (l : list form) (f : form) :=
  match l with
  | nil => false
  | cons f' l' => orb (equal_form f' f) (in_bool l' f)
  end.

(* Ce lemme montre que la fonction est la contrepartie booléenne valide de In. *)
Lemma in_bool_soound :
  forall f : form, forall l : list form,
  in_bool l f = true -> In f l.
Proof.
  intros f l.
  induction l.
  + intro H; simpl in H; inversion H.
  + intro H; simpl in H.
    simpl.
    apply orb_true_iff in H.
    destruct H as [ H | H].
    - apply equal_form_sound in H; left; assumption.
    - apply IHl in H; right; assumption.
Qed.

(* _         _             __
  (_)___    | | ___  __ _ / _|
  | / __|   | |/ _ \/ _` | |_
  | \__ \   | |  __/ (_| |  _|
  |_|___/___|_|\___|\__,_|_|
*)
(* Cette fonction teste si on peut appliquer 
   au séquent un des cas de base du calcul intuitionniste. *)
Definition is_leaf ( seq : seq ) : bool :=
    match snd seq with
    | True_form => true
    (* Si on doit prouver le TOP *)
    | Leaf _ as f =>
    (* Quand le but est une variable *)
      orb (in_bool (fst seq) f)
          (* On regarde si elle n'est pas dans les hypothèses *)
          (in_bool (fst seq) False_form)
          (* Sinon, on regarde si on a l'hypothèse BOTTOM *)
    | _ => in_bool (fst seq) False_form
    (* Pour les autres cas, on regarde si on a l'hypothèse BOTTOM *)
    end.

(* ___  ___  ___     _     _____
  |_ _||_ _||_ _|   / |   |___ /
   | |  | |  | |    | |     |_ \
   | |  | |  | |  _ | | _  ___) |
  |___||___||___|(_)|_|(_)|____/
*)

(* Quelques définitions de types utils dans la suite ...*)
Definition subgoals := list (list seq).
Definition picked_hyp := list (form * list form).

(* Cette fonction auxiliaire permet de mettre en valmeur une hypothèse *)
Fixpoint pick_hyp_aux ( hyps acc : list form ) : picked_hyp :=
  match hyps with
  | nil => nil
  | hd :: tl => (hd, acc++tl) :: (pick_hyp_aux tl (hd::acc))
  end.

(* Un lemme de validité associé à la fonction ci-dessus.
   Elle est assez technique, mais elle permet de voir l'intérêt
   d'une seule fonction avec accumulateur. *)
Lemma pick_hyp_aux_sound :
  forall l acc: list form, 
  forall p_hyps : form * list form,
    In p_hyps (pick_hyp_aux l acc) -> 
      In (fst p_hyps) l /\
      forall f : form, In f (snd p_hyps) -> (In f l \/ In f acc).
Proof.
  intros l.
  induction l; intros acc p_hyps H.
  + split.
    - simpl. contradiction.
    - intros; simpl; contradiction.
  + split.
    - simpl in H.
      destruct H.
      ++ left; rewrite <- H; simpl; auto.
      ++ simpl. right. eapply IHl with (acc := a::acc); assumption.
    - intros f Hf.
      simpl in H.
      destruct H.
      ++ rewrite <- H in Hf. simpl in Hf.
        apply in_app_or in Hf.
        destruct Hf.
        +++ right; auto.
        +++ left; simpl; right; assumption.
      ++ assert (In (fst p_hyps) l /\ (forall f : form, In f (snd p_hyps) -> In f l \/ In f (a::acc))).
        +++ apply (IHl (a::acc) p_hyps). assumption.
        +++ destruct H0 as [H04 H0].
            assert (In f l \/ In f (a :: acc)).
            -- apply H0; assumption.
            -- simpl in H1; destruct H1.
              * left; simpl; right; assumption.
              * destruct H1.
                ** left; simpl; left; assumption.
                ** right; assumption.
Qed.

(*       _      _        _
   _ __ (_) ___| | __   | |__  _   _ _ __
  | '_ \| |/ __| |/ /   | '_ \| | | | '_ \
  | |_) | | (__|   <    | | | | |_| | |_) |
  | .__/|_|\___|_|\_\___|_| |_|\__, | .__/
  |_|                          |___/|_|
*)
Definition pick_hyp (seq : seq) : picked_hyp :=
  pick_hyp_aux (fst seq) nil.

(* Cette fonction gère les règles d'introduction : 
   elles sont dirigées par la forme du but *)
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
  | hyp :: tl => (elim_rules hyp goal) ++ (elim_rules_multi tl goal)
  end.

Definition elim_rules_final (seq : seq) : subgoals :=
  (elim_rules_multi (pick_hyp seq) (snd seq)).

(*     _
   ___| |_ ___ _ __
  / __| __/ _ \ '_ \
  \__ \ ||  __/ |_) |
  |___/\__\___| .__/
              |_|
*)
Definition step (seq : seq) : subgoals :=
  (intro_rules seq) ++ (elim_rules_final seq).

(* ___  ___  ___     _    _  _
  |_ _||_ _||_ _|   / |  | || |
   | |  | |  | |    | |  | || |_
   | |  | |  | |  _ | | _|__   _|
  |___||___||___|(_)|_|(_)  |_|
*)
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


(* ___  ___  ___     ____      _
  |_ _||_ _||_ _|   |___ \    / |
   | |  | |  | |      __) |   | |
   | |  | |  | |  _  / __/  _ | |
  |___||___||___|(_)|_____|(_)|_|
*)

(*     _              __
   ___(_)_______     / _| ___  _ __ _ __ ___
  / __| |_  / _ \   | |_ / _ \| '__| '_ ` _ \
  \__ \ |/ /  __/   |  _| (_) | |  | | | | | |
  |___/_/___\___|___|_|  \___/|_|  |_| |_| |_|
*)
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

(*     _
   ___(_)_______     ___  ___  __ _
  / __| |_  / _ \   / __|/ _ \/ _` |
  \__ \ |/ /  __/   \__ \  __/ (_| |
  |___/_/___\___|___|___/\___|\__, |
                                 |_|
*)
Definition size_seq (seq : seq) : nat :=
  let hyps := fst seq in
  let goal := snd seq in
  (size_hyps hyps) + (size_form goal).

(* ___  ___  ___     ____      ____
  |_ _||_ _||_ _|   |___ \    |___ \
   | |  | |  | |      __) |     __) |
   | |  | |  | |  _  / __/  _  / __/
  |___||___||___|(_)|_____|(_)|_____|
*)
(* Quelques remarques sur la preuve de terminaison :
   - Elle commence par deux lemmes qui monternt que le séquents sont plus petits
     si on applique une règle d'introduction ou d'élimination.
     Ces lemmes ont des preuves longues mais qui ne présentent pas de 
     difficulté.
   - Viennent ensuite deux lemmes qui expriment des propriétés sur la 
     concaténation des listes : présevation des éléments et
     de la taille totale des hypothèses
   - Puis un lemme technique pour le cas des règles d'élimination et 
     notamment le cas de la fonction pick_hyp. 
   - Le lemme final est le lemme `size_decrease` *)
Require Import Omega.



Lemma size_decrease_intro : 
  forall s : seq, forall s' : seq, forall subgoal : list seq, 
  (In subgoal (intro_rules s)) /\ (In s' subgoal) 
    -> (size_seq s') < (size_seq s).
Proof.
  intros s s' sg.
  unfold intro_rules.
  case_eq (snd s).
  - intros n H9 H; destruct H as [H1 H2]; unfold In in H1; contradiction.
  - intros H9 H; destruct H as [H1 H2]; unfold In in H1; contradiction.
  - intros H9 H; destruct H as [H1 H2]; unfold In in H1; contradiction.
  - intros f1 f2 Hs H.
    destruct H as [H1 H2].
    assert (s' = (f1 :: fst s, f2)).
    + unfold In in H1.
      destruct H1; try contradiction.
      rewrite <- H in H2.
      unfold In in H2.
      destruct H2; try contradiction.
      rewrite H0; reflexivity.
    + unfold size_seq.
      rewrite H; rewrite Hs.
      simpl; omega.
  - intros f1 f2 Hs H.
    destruct H as [H1 H2].
    unfold In in H1.
    destruct H1; try contradiction.
    rewrite <- H in H2.
    unfold In in H2; unfold In in H2.
    destruct H2.
    * unfold size_seq.
      rewrite <- H0; rewrite Hs.
      simpl; omega.
    * destruct H0; try contradiction.
      unfold size_seq.
      rewrite <- H0; rewrite Hs.
      simpl; omega.
  - intros f1 f2 Hs H.
    destruct H as [H1 H2].
    unfold In in H1.
    destruct H1.
    + rewrite <- H in H2.
      unfold In in H2.
      destruct H2; try contradiction.
      unfold size_seq.
      rewrite <- H0; rewrite Hs.
      simpl; omega.
    + destruct H; try contradiction.
      rewrite <- H in H2.
      destruct H2; try contradiction.
      unfold size_seq.
      rewrite <- H0; rewrite Hs.
      simpl; omega.
Qed.

Lemma size_decrease_elim : 
  forall hyps : form*list form, forall goal : form, forall s' : seq, forall subgoal : list seq, 
  (In subgoal (elim_rules hyps goal)) /\ (In s' subgoal) -> 
  (size_seq s') < (size_seq ((fst hyps)::(snd hyps), goal)).
Proof.
  intros hyps goal s' sg.
  unfold elim_rules.
  case_eq (fst hyps).
  - intros n H9 H; destruct H as [H1 H2]; unfold In in H1; contradiction.
  - intros H9 H; destruct H as [H1 H2]; unfold In in H1; contradiction.
  - intros H9 H; destruct H as [H1 H2]; unfold In in H1; contradiction.
  - intros f1 f2 Hs H.
    destruct H as [H1 H2].
    unfold In in H1.
    destruct H1 as [H1 | H1]; try contradiction.
    rewrite <- H1 in H2.
    unfold In in H2.
    destruct H2 as [H2 | H2].
    + rewrite <- H2.
      unfold size_seq; simpl; omega.
    + destruct H2 as [H2|H2]; try contradiction.
      rewrite <- H2.
      unfold size_seq; simpl; omega.
  - intros f1 f2 Hs H.
    destruct H as [H1 H2].
    unfold In in H1.
    destruct H1 as [H1|H1]; try contradiction.
    rewrite <- H1 in H2.
    unfold In in H2.
    destruct H2 as [H2|H2]; try contradiction.
    rewrite <- H2.
    unfold size_seq; simpl; omega.
  - intros f1 f2 Hs H.
    destruct H as [H1 H2].
    unfold In in H1.
    destruct H1 as [H1 | H1 ]; try contradiction.
    rewrite <- H1 in H2.
    unfold In in H2.
    destruct H2 as [H2 | H2].
    + rewrite <- H2.
      unfold size_seq; simpl; omega.
    + destruct H2 as [H2|H2]; try contradiction.
      rewrite <- H2.
      unfold size_seq; simpl; omega.
Qed.

Lemma size_equal_concat : 
  forall l1 l2 : list form,
  size_hyps (l1++l2) = size_hyps l1 + size_hyps l2.
Proof.
  intros l1 l2; induction l1; simpl; omega.
Qed.


Lemma concat_in : 
  forall f : list seq,
  forall l1 l2 : list (list seq),
  In f (l1 ++ l2) -> In f l1 \/ In f l2.
Proof.
  intros f l1; induction l1.
  + intros l2 H; simpl in H; right; assumption.
  + simpl; intros l2 H. destruct H.
    - left; left; assumption.
    - apply IHl1 in H; destruct H.
      * left; right; assumption. 
      * right; assumption.
Qed.

Lemma size_decrease_elim_final_aux : 
  forall s s' : seq, forall sg : list seq,
  forall l acc : list form,
  In sg (elim_rules_multi (pick_hyp_aux l acc) (snd s)) /\ In s' sg ->
  size_seq s' < size_hyps l + size_hyps acc + size_form (snd s).
Proof.
  intros s s' sg l.
  induction l.
  - intros acc H; destruct H as [H0 H1]; simpl in H0; contradiction.
  - intros acc H. destruct H as [H0 H1]; simpl in H0.
    apply concat_in in H0; destruct H0.
    + simpl.
      assert ( (size_seq s') < (size_seq ((fst (a, acc ++ l))::(snd (a, acc ++ l)), (snd s)))).
      * apply (size_decrease_elim (a, acc ++ l) (snd s) s' sg).
        split; assumption.
      * simpl in H0. unfold size_seq in H0. simpl in H0.
        unfold size_seq.
        assert (size_hyps (acc ++ l) = size_hyps acc + size_hyps l).
          -- apply size_equal_concat.
          -- rewrite H2 in H0; omega.
   + simpl.
     assert (size_seq s' < size_hyps l + size_hyps (a::acc) + size_form (snd s)).
    * apply (IHl (a::acc)).
      split; assumption.
    * simpl in H0; omega.
Qed.

Lemma size_decrease_elim_final : 
  forall s : seq, forall s' : seq, forall subgoal : list seq, 
  (In subgoal (elim_rules_final s)) /\ (In s' subgoal) 
    -> (size_seq s') < (size_seq s).
Proof.
  intros s s' sg.
  unfold elim_rules_final; simpl.
  unfold pick_hyp. unfold size_seq.
  intro H.
  assert (size_seq s' < size_hyps (fst s) + size_hyps nil + size_form (snd s)).
  + apply (size_decrease_elim_final_aux s s' sg (fst s) nil); assumption.
  + simpl in H0; unfold size_seq in H0; omega.
Qed.

(*     _                _
   ___(_)_______     __| | ___  ___ _ __ ___  __ _ ___  ___
  / __| |_  / _ \   / _` |/ _ \/ __| '__/ _ \/ _` / __|/ _ \
  \__ \ |/ /  __/  | (_| |  __/ (__| | |  __/ (_| \__ \  __/
  |___/_/___\___|___\__,_|\___|\___|_|  \___|\__,_|___/\___|
*)
Lemma size_decrease :
  forall s : seq, forall s' : seq, forall subgoal : list seq, 
  (In subgoal (step s)) /\ (In s' subgoal) -> (size_seq s') < (size_seq s).
Proof.
  intros s s' sg.
  intros H; destruct H as [H0 H1].
  unfold step in H0.
  apply concat_in in H0.
  destruct H0.
  - apply (size_decrease_intro s s' sg); auto.
  - apply (size_decrease_elim_final s s' sg); auto.
Qed.

(* III.3. Soundness *)
(* ---------------- *)

(* ___  ___  ___     _____    _ 
  |_ _||_ _||_ _|   |___ /   / |
   | |  | |  | |      |_ \   | |
   | |  | |  | |  _  ___) |_ | |
  |___||___||___|(_)|____/(_)|_|
*)

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

Lemma Leaf_sound : forall s : seq, is_leaf s = true  -> seq_valid s.
Proof.
  intros s H.
  unfold seq_valid.
  unfold is_leaf in H; destruct (snd s); simpl in H.
  + apply orb_true_iff in H; destruct H.
    - unfold seq_valid.
      intros sem_nat H_hyps; simpl.
Admitted.
  
  
