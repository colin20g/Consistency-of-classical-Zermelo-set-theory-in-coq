(** April 14, 2025
    
    The consistency of classical Zermelo set theory in coq.
    Author: Colin20G.

    This program has been verified to compile successfully with Coq 8.16,
    and also on the https://coq.vercel.app/ website (at this date).

    The following document is a self-contained formalized proof of the consistency
    of Zermelo set theory (i.e. the same as Zermelo-Fraenkel but with replacement
    removed) with classical logic and without the axiom of choice.
    The proof is written in default COQ without any axioms
    (hence using intuitionist logic in the metatheory).
    
    After a small preliminary section, the text consists in three parts:
    the introduction of formal Zermelo theory with some of its properties,
    a general semantic and then a specific model in which the result is established.
    
    A proof of ZF consistency in COQ (assuming a further type theoretical axiom of choice)
    by Benjamin Werner can be found here:
    https://github.com/rocq-archive/zfc/blob/master/zfc.v
    In the present document we borrow his model and tweak it (with double negations
    in formulas) in order to validate classical logic.

 *)

Section Preliminary_useful_logical_results.

  Lemma iff_implies (a1 a2 b1 b2: Prop): (a1 <-> a2) -> (b1 <-> b2) ->
                                         ((a1 -> b1) <-> (a2 -> b2)).
  Proof.
    intros P Q; split; intros M N; apply Q; apply M; apply P; apply N.
  Defined.

  Lemma iff_forall (T: Type) (f g: T -> Prop) (A: forall t: T, f t <-> g t):
    (forall x: T, f x) <-> (forall x: T, g x).
  Proof.
    intros; split; intros P y; apply A; apply P.
  Defined.

End Preliminary_useful_logical_results.

Section Formal_Zermelo_set_theory.

  (** The definition of formulas of first order logic is given with De Bruijn indices
      (search the web for a definition: the terms obtained are barely readable for humans
      but this representation of formulaqs is very convenient for theoretical investigation).
      The proof system we'll use is an Hilbert system with modus ponens and generalization
      rule (adapted to the De Bruijn reprsentation).
      The proof system we describe is very compact and again, not really readable so we
      introduce afer this section, a seond section "further topics" ntended to help the reader
      relate this compact presentation to maybe more familiar presentations of first order
      logic and set theory (in other terms: we are really dealing with Zermelo set theory
      and not something else...).
   *)
    
  Section The_core_system.
    
    Inductive set_formula: Set:=
    |sf_belongs: nat -> nat -> set_formula
    |sf_equal: nat -> nat -> set_formula
    |sf_false: set_formula
    |sf_implies: set_formula -> set_formula -> set_formula
    |sf_all: set_formula -> set_formula.

    Notation "v € w":= (sf_belongs v w) (at level 40).
    Notation "v == w":= (sf_equal v w) (at level 40).
    Notation "x -o y":= (sf_implies x y) (right associativity, at level 41).
    Notation "§":= (sf_false).
    Notation F:= (set_formula).

    Section Definition_of_basic_letter_substitution_operations.

      Definition shift_environment (e: nat -> nat) (p: nat): nat:=
        match p with
        | 0 => 0
        | S q => S (e q)
        end.

      Fixpoint sf_substitution (env: nat -> nat) (f: F) {struct f}: F:=
        match f with
        |sf_belongs x y => sf_belongs (env x) (env y)
        |sf_equal x y => sf_equal (env x) (env y)
        |sf_false => sf_false
        |sf_implies a b => sf_implies (sf_substitution env a)
                             (sf_substitution env b)
        |sf_all g => sf_all (sf_substitution (shift_environment env) g)
        end.

      Definition sf_constant_embedding:= sf_substitution S.
      Definition sf_predicate_constant_embedding:=
        sf_substitution (shift_environment S).

      Definition app_env (t x: nat):nat:= match x with |0 => t |S y => y end.
      Definition sf_apply (P: F) (t: nat):= sf_substitution (app_env t) P.
      
    End Definition_of_basic_letter_substitution_operations.  

    (** We define other connectors and elementary notions below;
        please note that the notation "... -o ..." is defined as associative to the right,
        which means that "a -o b -o c" means "a -o (b -o c)" and not "(a -o b) -o c".
        The reader who is not familiar with these abreviations from propositional logic
        is invited to check them with truth tables. *)

    Definition sf_and (a b: F): F:= 
      (a -o b -o §) -o §.

    Definition sf_or (a b: F): F:=
      (a -o §) -o (b -o §) -o §.

    Definition sf_not (a: F): F:= (a -o §).

    Definition sf_equiv (a b: F): F:= sf_and (a -o b) (b -o a).

    Definition sf_ex (p: F):=  (sf_all (p -o §)) -o §.

    Definition sf_set_is_empty (v: nat):F:= sf_all (0 € (S v) -o §).

    Definition sf_is_pair_of (pab a b: nat): F:=
      sf_all (sf_equiv (0 € (S pab)) (sf_or (0 == (S a)) (0 == (S b)))).

    Definition sf_is_union_of (ux x: nat):F :=
      sf_all (sf_equiv (0 € (S ux))
                (sf_ex (sf_and (1 € 0) (0 € (S (S x)))))).

    Definition sf_included (x y: nat): F:= sf_all (0 € (S x) -o 0 € (S y)).

    Definition sf_is_power_set_of (px x: nat): F:=
      sf_all (sf_equiv (0 € (S px)) (sf_included 0 (S x))).

    Definition sf_is_defined_by_comprehension_from (comp_x_P x: nat) (P: F):=
      sf_all (sf_equiv (0 € (S comp_x_P)) (sf_and (0 € (S x)) P)).

    Definition sf_is_successor_of (sx x: nat): F :=
      sf_all (sf_equiv (0 € S (sx)) (sf_or (0 € (S x)) (0 == (S x)))).

    Definition sf_is_inductive (indu: nat): F:=
      sf_and
        (sf_ex (sf_and (sf_set_is_empty 0) (0 € (S indu))))
        (sf_all ((0 € S (indu)) -o (sf_ex (sf_and (sf_is_successor_of 0 1)
                                             (0 € (S (S indu))))))).

    (** Now it is time to define the notion of a formal proof in Zermelo Set Theory,
        in the form of an Hilbert system (see e.g. wikipedia for a survey of these). *)

    Inductive ZST_Theorem: F -> Set:=
    (** Inference rules *)
    |zst_inference_modus_ponens: forall A B: F,
        ZST_Theorem (A -o B) -> ZST_Theorem A -> ZST_Theorem B
    |zst_inference_generalization: forall (A P: F),
        ZST_Theorem ((sf_constant_embedding P) -o A) -> ZST_Theorem (P -o sf_all A)           
    (** Logical axioms *)
    |zst_logical_axiom_1: forall A B: F, ZST_Theorem (A -o B -o A)
    |zst_logical_axiom_2: forall A B C: F, ZST_Theorem ((A -o B -o C) -o (A -o B) -o (A -o C)) 
    |zst_logical_axiom_3: forall A: F, ZST_Theorem (((A -o §) -o §) -o A)
    |zst_logical_axiom_4: forall (P:F) (t: nat),
        ZST_Theorem ((sf_all P) -o (sf_apply P t))
    (** Equality properties*)
    |zst_equality_reflexivity:
      ZST_Theorem (sf_all (0 == 0))              
    |zst_Leibniz_rule: forall (f: F) (x y: nat), 
        ZST_Theorem (x == y -o sf_apply f x -o sf_apply f y)
    (** Specific set theoretical axioms*)
    |zst_extensionality:
      ZST_Theorem
        (sf_all (sf_all ((sf_all (sf_equiv (0 € 2) (0 € 1))) -o (sf_equal 1 0))))
    |zst_empty_set_existence: ZST_Theorem (sf_ex (sf_set_is_empty 0))
    |zst_pair_existence:
      ZST_Theorem (sf_all (sf_all (sf_ex (sf_is_pair_of 0 2 1))))
    |zst_union_existence:
      ZST_Theorem (sf_all (sf_ex (sf_is_union_of 0 1)))
    |zst_power_set_existence: 
      ZST_Theorem (sf_all (sf_ex (sf_is_power_set_of 0 1)))
    |zst_scheme_of_comprehension:
      forall P: F,
        ZST_Theorem
          (sf_all (sf_ex (sf_is_defined_by_comprehension_from
                            0 1 (sf_predicate_constant_embedding P))))
    |zst_infinite_set_existence:
      ZST_Theorem (sf_ex (sf_is_inductive 0)).

  End The_core_system.
  
  (** The following paragraph "further topics" of the section "Formal Zermelo Set Theory"
      will not be used in the consistency proof but is introduced in order to convince
      the reader we are dealing with Zermelo theory, since the de Bruijn representation above
      is obfuscated. We introduce more syntactic substitution operations, Va
      more readable (hopefully) versions of the axioms of set theory we've introduced above
      and a complete natural deduction system for classical logic in order to prove that
      every predicate calculus theorem is also a theorem of the ZST system previously
      introduced.
   *)
  
  Section Further_topics.

    Notation "v € w":= (sf_belongs v w) (at level 40).
    Notation "v == w":= (sf_equal v w) (at level 40).
    Notation "x -o y":= (sf_implies x y) (right associativity, at level 41).
    Notation "§":= (sf_false).
    Notation F:= (set_formula).

    Section Advanced_letter_substitution_and_its_properties.

      Definition nat_eq_dec: forall (p q: nat), sumbool (p = q) (p <> q).
      Proof.
        intro p; induction p; intro q. destruct q. left; reflexivity. right; discriminate.
        destruct q. right; discriminate. destruct (IHp q) as [Y|N].
        left; apply eq_S; apply Y. right; intro F; apply N; apply eq_add_S; apply F.
      Defined.

      Definition binding_env (x v: nat):nat:=
        match (nat_eq_dec x v) with |left _ => 0 |right _ => S v end.
      Definition sf_lambda (x: nat): F -> F:= sf_substitution (binding_env x).
      Definition sf_forall (x: nat) (p: F):= sf_all (sf_lambda x p).

      Definition sf_exists (x: nat) (p: F):= sf_ex (sf_lambda x p).

      (** NB: sf_exists is well defined in terms of sf_forall, indeed: *)

      Theorem sf_forall_exists_equality: forall (a: F) (x: nat),
          sf_exists x a = (sf_forall x (a -o §)) -o §.
      Proof.
        unfold sf_exists; unfold sf_forall; simpl; reflexivity.
      Defined.
      
      Definition replacement_env (x t y: nat): nat :=
        match (nat_eq_dec x y) with |left _ => t|right _ => y end.
      Definition sf_specify (f: F) (x t: nat): F:=
        (sf_substitution (replacement_env x t) f).
      
      Inductive sf_free_variable (v: nat): F -> Prop:=
      |sffv_belongs_left: forall x: nat, sf_free_variable v (sf_belongs v x)
      |sffv_belongs_right: forall x: nat, sf_free_variable v (sf_belongs x v)
      |sffv_equal_left: forall x: nat, sf_free_variable v (sf_equal v x)
      |sffv_equal_right: forall x: nat, sf_free_variable v (sf_equal x v)
      |sffv_implies_left: forall a b: F, sf_free_variable v a -> sf_free_variable v (a -o b) 
      |sffv_implies_right: forall a b: F, sf_free_variable v b -> sf_free_variable v (a -o b)
      |sffv_all: forall g: F, sf_free_variable (S v) g -> sf_free_variable v (sf_all g).

      Theorem sf_cov_pointwise_equality:
        forall (f: F) (env1 env2: nat -> nat)
               (eqenv: forall v: nat, sf_free_variable v f -> env1 v = env2 v),
          sf_substitution env1 f = sf_substitution env2 f.
      Proof.
        intro f; induction f; intros; simpl.
        rewrite (eqenv n). rewrite (eqenv n0). reflexivity.
        apply sffv_belongs_right. apply sffv_belongs_left.
        rewrite (eqenv n). rewrite (eqenv n0). reflexivity.
        apply sffv_equal_right. apply sffv_equal_left. reflexivity. apply f_equal2.
        apply IHf1. intros; apply eqenv; apply sffv_implies_left; assumption.
        apply IHf2. intros; apply eqenv; apply sffv_implies_right; assumption.
        apply f_equal. apply IHf; intros. destruct v. simpl; reflexivity. simpl; apply eq_S.
        apply eqenv; apply sffv_all; assumption.
      Defined.

      Theorem sf_cov_composition_equality: forall  (f: F) (env1 env2: nat -> nat),
          sf_substitution env1 (sf_substitution env2 f) =
            sf_substitution (fun k: nat => env1 (env2 k)) f.
      Proof.
        intro f; induction f; intros; simpl. reflexivity. reflexivity. reflexivity.
        apply f_equal2. apply IHf1. apply IHf2. apply f_equal. rewrite IHf.
        apply sf_cov_pointwise_equality; intros; destruct v; simpl; reflexivity.
      Defined.

      Theorem sf_cov_identity_equality:
        forall (f: F), sf_substitution (fun i: nat => i) f = f.
      Proof.
        induction f; simpl. reflexivity. reflexivity. reflexivity. apply f_equal2; assumption.
        apply f_equal. transitivity (sf_substitution (fun i: nat => i) f).
        apply sf_cov_pointwise_equality. intros x A; destruct x; simpl; reflexivity.
        assumption.
      Defined.

      Theorem sf_lambda_apply: forall (f: F) (x t: nat),
          sf_apply (sf_lambda x f) t = sf_specify f x t.
      Proof.
        intros. unfold sf_apply. unfold sf_lambda. unfold sf_specify.
        rewrite sf_cov_composition_equality. apply sf_cov_pointwise_equality. intros v A.
        unfold binding_env. unfold replacement_env.
        destruct (nat_eq_dec x v); simpl; reflexivity.
      Defined.

      Theorem sf_unfree_lambda_constant_embedding:
        forall (p: F) (x: nat), (~ sf_free_variable x p) ->
                                sf_lambda x p = sf_constant_embedding p.
      Proof.
        intros p x A; unfold sf_lambda; unfold sf_constant_embedding.
        apply sf_cov_pointwise_equality; intros v B; unfold binding_env.
        destruct (nat_eq_dec x v). rewrite e in A; contradiction. reflexivity.
      Defined.

      Section Other_Properties_of_free_variables.

        (** The first three results of this section characterize the free variables of
            the image of a formula by a letter substitution. *)

        Theorem sf_cov_free_variable_forward (v: nat) (f: F):
          sf_free_variable v f ->
          forall (env: nat -> nat), sf_free_variable (env v) (sf_substitution env f).
        Proof.
          intro fv; induction fv; intros; simpl. apply sffv_belongs_left.
          apply sffv_belongs_right.
          apply sffv_equal_left. apply sffv_equal_right.
          apply sffv_implies_left; apply IHfv. apply sffv_implies_right; apply IHfv.
          apply sffv_all. assert (S (env v) = shift_environment env (S v)) as E.
          simpl; reflexivity. rewrite E. apply IHfv.
        Defined.

        Theorem sf_cov_free_variable_backwards (f: F): forall (env: nat -> nat) (w: nat),
            sf_free_variable w (sf_substitution env f) ->
            exists v: nat, sf_free_variable v f /\ env v = w.
        Proof.
          induction f; intros; simpl.
          inversion H. exists n; split. apply sffv_belongs_left. reflexivity.
          exists n0; split. apply sffv_belongs_right. reflexivity.
          inversion H. exists n; split. apply sffv_equal_left. reflexivity.
          exists n0; split. apply sffv_equal_right. reflexivity. inversion H. inversion H.
          destruct (IHf1 env w H1) as (v, (P, Q)); exists v; split.
          apply sffv_implies_left; assumption. assumption.
          destruct (IHf2 env w H1) as (v, (P, Q)); exists v; split.
          apply sffv_implies_right; assumption. assumption. inversion H.
          destruct (IHf (shift_environment env) (S w) H1) as (u, (P, Q)). destruct u.
          simpl in Q; absurd (0 = S w). discriminate. assumption. exists u; split.
          apply sffv_all; assumption. simpl in Q; apply eq_add_S; assumption.  
        Defined.

        (** Summary: *)

        Theorem sf_cov_free_variable (env: nat -> nat) (a: F) (y: nat):
          (sf_free_variable y (sf_substitution env a) <->
             exists x: nat, sf_free_variable x a /\ env x = y).
        Proof.
          split. apply sf_cov_free_variable_backwards. intros A; destruct A as (x, (B, C)).
          rewrite <- C. apply sf_cov_free_variable_forward; apply B.
        Defined.      

        (** What are the free variables of "sf_forall x a" where a is a formula and x a letter?
            We show that sf_forall is well behaved in that respect. *)

        Theorem sf_forall_free_variable_characterization (x y: nat) (a: F):
          (sf_free_variable y (sf_forall x a)) <->
            (sf_free_variable y a /\ x <> y).
        Proof.
          unfold sf_forall; unfold sf_lambda; split; intro P. inversion P.
          apply sf_cov_free_variable_backwards in H0. destruct H0 as (v, (Q, R)).
          unfold binding_env in R. destruct (nat_eq_dec x v) as [Y|N]. absurd (0 = S y).
          discriminate. apply R. apply eq_add_S in R. rewrite <- R. split; assumption.
          destruct P as (Q, R). apply sffv_all. assert (S y = binding_env x y) as E.
          unfold binding_env. destruct (nat_eq_dec x y). contradiction. reflexivity. rewrite E.
          apply sf_cov_free_variable_forward. assumption.
        Defined.    

        (** Below we detail how sf_forall and sf_specify behave together. *)
        
        Theorem sf_forall_specify_1 (x t: nat) (a: F):
          sf_specify (sf_forall x a) x t = sf_forall x a.
        Proof.
          unfold sf_specify. unfold sf_forall. unfold sf_lambda. simpl. apply f_equal.
          repeat rewrite sf_cov_composition_equality. apply sf_cov_pointwise_equality.
          intros v A; unfold replacement_env; unfold binding_env.
          destruct (nat_eq_dec x v) as [Y1|N1]. simpl; reflexivity. simpl.
          destruct (nat_eq_dec x v). contradiction. reflexivity.
        Defined.
        
        Theorem sf_forall_specify_2 (x y t: nat) (a: F):
          x <> y -> x <> t -> sf_specify (sf_forall x a) y t = sf_forall x (sf_specify a y t).
        Proof.
          intros A B. unfold sf_specify. unfold sf_forall. simpl. unfold sf_lambda.
          apply f_equal. repeat rewrite sf_cov_composition_equality.
          apply sf_cov_pointwise_equality; intros v C. unfold replacement_env.
          unfold binding_env. destruct (nat_eq_dec y v) as [Y1|N1]. 
          destruct (nat_eq_dec x v) as [Y2|N2]. rewrite <- Y1 in Y2. contradiction. simpl.
          destruct (nat_eq_dec x t) as [Y3|N3]. contradiction. destruct (nat_eq_dec y v).
          reflexivity. contradiction. destruct (nat_eq_dec x v) as [Y4|N4]. simpl; reflexivity.
          simpl. destruct (nat_eq_dec y v). contradiction. reflexivity.
        Defined.

        Theorem sf_forall_specify_3 (x y z: nat) (a: F):
          x <> y -> y <> z -> x <> z -> (~ sf_free_variable z a) ->
          sf_specify (sf_forall x a) y x =
            sf_forall z (sf_specify (sf_specify a x z) y x).
        Proof.
          intros A B C D. unfold sf_specify. unfold sf_forall. unfold sf_lambda. simpl.
          repeat rewrite sf_cov_composition_equality. apply f_equal.
          apply sf_cov_pointwise_equality; intros v E.
          unfold replacement_env. unfold binding_env. destruct (nat_eq_dec x v) as [Y1|N1].
          simpl. destruct (nat_eq_dec y z) as [Y2|N2]. contradiction.
          destruct (nat_eq_dec z z). reflexivity. absurd (z = z). assumption. reflexivity.
          simpl. destruct (nat_eq_dec y v) as [Y3|N3]. destruct (nat_eq_dec z x) as [Y4| N4].
          apply eq_sym in Y4; contradiction. reflexivity. destruct (nat_eq_dec z v) as [Y5| N5].
          rewrite Y5 in D; contradiction. reflexivity.
        Defined.      
        
      End Other_Properties_of_free_variables.
      
    End Advanced_letter_substitution_and_its_properties.

    Section Properties_of_ZST_proofs_and_more_readable_forms_of_them.

      (** The following result establishes that proofs are invariant by letter substitution *)
      
      Definition zst_proof_letter_substitution (f: F) (pr: ZST_Theorem f):
        forall (env: nat -> nat), ZST_Theorem (sf_substitution env f).
      Proof.
        assert (forall (P: F)(env: nat -> nat) (t: nat),
                   sf_substitution env (sf_apply P t) =
                     sf_apply (sf_substitution (shift_environment env) P) (env t)) as D.
        intros; unfold sf_apply; repeat rewrite sf_cov_composition_equality.
        apply sf_cov_pointwise_equality; intros v W; destruct v; simpl; reflexivity.
        induction pr; intro env; simpl.
        apply zst_inference_modus_ponens with (A:= sf_substitution env A).
        apply IHpr1. apply IHpr2.
        assert (sf_substitution (shift_environment env) (sf_constant_embedding P) =
                  sf_constant_embedding (sf_substitution env P)) as E.
        unfold sf_constant_embedding; repeat rewrite sf_cov_composition_equality.
        apply sf_cov_pointwise_equality; intros v W; simpl; reflexivity.
        apply zst_inference_generalization. rewrite <- E. apply IHpr; assumption.
        apply zst_logical_axiom_1. apply zst_logical_axiom_2. apply zst_logical_axiom_3.
        rewrite D. apply zst_logical_axiom_4. apply zst_equality_reflexivity.
        repeat rewrite D; apply zst_Leibniz_rule. apply zst_extensionality.
        apply zst_empty_set_existence. apply zst_pair_existence. apply zst_union_existence.
        apply zst_power_set_existence. 
        assert
          (sf_substitution
             (shift_environment (shift_environment (shift_environment env)))
             (sf_predicate_constant_embedding P) =
             sf_predicate_constant_embedding
               (sf_substitution (shift_environment (shift_environment env)) P)
          ) as E.
        unfold sf_predicate_constant_embedding; repeat rewrite sf_cov_composition_equality.
        apply sf_cov_pointwise_equality; intros v W; destruct v; simpl; reflexivity.
        repeat rewrite E. apply zst_scheme_of_comprehension. apply zst_infinite_set_existence.
      Defined.

      (** The result above allows more commonly known versions of certains axioms and inference
    rules: *)
      
      Definition zst_readable_generalization_rule
        (P A: F) (x: nat) (nf: ~ sf_free_variable x P):
        ZST_Theorem (P -o A) -> ZST_Theorem (P -o (sf_forall x A)).
      Proof.
        intro pr. apply zst_proof_letter_substitution with (env:= binding_env x) in pr.
        simpl in pr. fold (sf_lambda x P) in pr. fold (sf_lambda x A) in pr.
        rewrite (sf_unfree_lambda_constant_embedding P x nf) in pr.
        apply zst_inference_generalization in pr. apply pr.
      Defined.

      Definition zst_readable_special_case_property (A: F) (x t: nat):
        ZST_Theorem ((sf_forall x A) -o (sf_specify A x t)).
      Proof.
        unfold sf_forall. rewrite <- sf_lambda_apply. apply zst_logical_axiom_4.
      Defined.

      Definition zst_simple_tautology (a:F): ZST_Theorem (a -o a).
      Proof.
        apply zst_inference_modus_ponens with (A:= a -o a -o a).
        apply zst_inference_modus_ponens with (A:= a -o (a -o a) -o a).
        apply zst_logical_axiom_2. apply zst_logical_axiom_1. apply zst_logical_axiom_1.
      Defined.
      
      Definition zst_hypothesis_free_generalization (a: F):
        ZST_Theorem a -> ZST_Theorem (sf_all a).
      Proof.
        intro pr. apply zst_inference_modus_ponens with (A:= § -o §).
        apply zst_inference_generalization. simpl.
        apply zst_inference_modus_ponens with (A:= a).
        apply zst_logical_axiom_1. apply pr. apply zst_simple_tautology.
      Defined.
      
      Definition zst_readable_hypothesis_free_generalization (a: F) (x: nat):
        ZST_Theorem a -> ZST_Theorem (sf_forall x a).
      Proof.
        intro pr. apply zst_proof_letter_substitution with (env:= binding_env x) in pr.
        apply zst_hypothesis_free_generalization. apply pr.
      Defined.
      
      Definition zst_readable_Leibniz_rule (a: F) (s t x: nat):
        ZST_Theorem (s == t -o (sf_specify a x s) -o (sf_specify a x t)).
      Proof.
        repeat rewrite <- sf_lambda_apply; apply zst_Leibniz_rule.
      Defined.

      Ltac mp r := apply zst_inference_modus_ponens with (A:= r).
      Ltac sa:= apply zst_logical_axiom_2.
      Ltac ka:= apply zst_logical_axiom_1.
      Ltac ia:= apply zst_simple_tautology.
      
      Definition zst_syllogism (a b c: F): ZST_Theorem (a -o b) -> ZST_Theorem (b -o c) ->
                                           ZST_Theorem (a -o c).
      Proof.
        intros P Q. mp (a -o b). mp (a -o b -o c). sa. mp (b -o c). ka. assumption. assumption.
      Defined.
      
      Definition zst_syllogism_2 (a b c: F):
        ZST_Theorem (a -o b) -> ZST_Theorem ((c -o a) -o (c -o b)).
      Proof.
        intro P. mp (c -o a -o b). sa. mp (a -o b). ka. assumption. 
      Defined.

      Ltac syl r:= apply zst_syllogism with (b:= r).
      Ltac syl2:= apply zst_syllogism_2.
      
      Definition zst_permutation (a b c: F):
        ZST_Theorem (a -o b -o c) -> ZST_Theorem (b -o a -o c).
      Proof.
        intros P. mp (b -o a -o b). mp (b -o (a -o b) -o a -o c). sa. mp ((a -o b) -o a -o c).
        ka. mp (a -o b -o c). sa. assumption. ka.
      Defined.  

      Ltac perm:= apply zst_permutation.

      Section More_readable_forms_of_the_set_theoretical_axioms.

        (** We recall that in de Bruijn implementation of formulas,
   variables are exactly integers. So we get formulas like "sf_forall 1, F(1)"
   Which is the same thing as "sf_forall x, F(x)"*)

        Definition zst_readable_extensionality:
          ZST_Theorem
            (sf_forall 1 (sf_forall 2 ((sf_forall 3 (sf_equiv (3 € 1) (3 € 2))) -o 1 == 2))).
        Proof.
          simpl; apply zst_extensionality.
        Defined.

        Definition zst_readable_empty_set_existence:
          ZST_Theorem (sf_exists 1 (sf_forall 2 (sf_not (2 € 1)))).
        Proof.
          simpl; apply zst_empty_set_existence.
        Defined.
        
        Definition zst_readable_pair_existence:
          ZST_Theorem
            (sf_forall 1
               (sf_forall 2
                  (sf_exists 3
                     (sf_forall 4 (sf_equiv (4 € 3) (sf_or (4 == 1) (4 == 2))))))).
        Proof.
          simpl; apply zst_pair_existence.
        Defined.

        Definition zst_readable_union_existence:
          ZST_Theorem
            (sf_forall 1
               (sf_exists 2
                  (sf_forall 3
                     (sf_equiv (3 € 2) (sf_exists 4 (sf_and (3 € 4) (4 € 1))))))).
        Proof.
          simpl; apply zst_union_existence.
        Defined.

        Definition zst_readable_power_set_existence:
          ZST_Theorem
            (sf_forall 1
               (sf_exists 2
                  (sf_forall 3
                     (sf_equiv (3 € 2) (sf_forall 4 (4 € 3 -o 4 € 1)))))).
        Proof.
          simpl; apply zst_power_set_existence.
        Defined.

        Definition zst_readable_scheme_of_comprehension:
          forall (P: F),
            (~ sf_free_variable 2 P) ->
            ZST_Theorem
              (sf_forall 1
                 (sf_exists 2
                    (sf_forall 3
                       (sf_equiv (3 € 2) (sf_and (3 € 1) P))))
              ).
        Proof.
          intros P A. unfold sf_forall. unfold sf_exists. unfold sf_ex. unfold sf_lambda. simpl.
          repeat rewrite sf_cov_composition_equality.
          assert (sf_substitution
                    (fun k : nat =>
                       shift_environment (shift_environment (binding_env 1))
                         (shift_environment (binding_env 2) k)) (sf_lambda 3 P)
                  =
                    sf_predicate_constant_embedding
                      (sf_substitution
                         (fun j: nat =>
                            match j with
                            |0 => 2
                            |1 => 1
                            |2 => 0
                            |3 => 0
                            |S (S (S (S x))) => S (S (S (S (S (S x)))))
                            end)
                         P
                      )
                 ) as E. unfold sf_lambda. 
          unfold sf_predicate_constant_embedding. repeat rewrite sf_cov_composition_equality.
          apply sf_cov_pointwise_equality. intros v B. unfold binding_env.
          destruct v. simpl; reflexivity. destruct v. simpl; reflexivity. destruct v.
          contradiction. destruct v. simpl; reflexivity. simpl; reflexivity.
          unfold sf_lambda in E. repeat rewrite sf_cov_composition_equality in E. rewrite E.
          unfold binding_env. simpl. apply zst_scheme_of_comprehension.
        Defined.

        (** We finish this list of axioms by the axiom of infinite, whose formulation is
   a bit longer so we introduce abreviations first*)

        Notation var2_is_empty:= (sf_forall 3 (sf_not (3 € 2))).
        Notation var3_is_sucessor_of_var2:=
          (sf_forall 4 (sf_equiv (4 € 3) (sf_or (4 € 2) (4 == 2)))).

        Definition zst_readable_infinite_set_existence:
          ZST_Theorem
            (sf_exists 1
               (sf_and
                  (sf_exists 2 (sf_and var2_is_empty (2 € 1)))
                  (sf_forall 2 (sf_implies (2 € 1) (sf_exists 3 (sf_and
                                                                   var3_is_sucessor_of_var2
                                                                   (3 € 1)))))
            )).
        Proof.
          simpl. apply zst_infinite_set_existence.
        Defined.
        
      End More_readable_forms_of_the_set_theoretical_axioms.
      
      Section Natural_deduction_for_ZST_Theorems.

        Section List_belonging.

          Variable T: Type.
          Variable x: T.

          (** We define below what it means for the variable x declared above,
          to belong to any list*)
          
          Inductive list_membership: list T -> Type:=
          |lm_head: forall l: list T, list_membership (cons x l)
          |lm_tail: forall (h: T) (t: list T), list_membership t -> list_membership (cons h t).
          
        End List_belonging.

        Fixpoint sf_sequent (g: list F) (x: F) {struct g}: F:=
          match g with
          | nil => x
          | cons h t => (sf_sequent t (h -o x))
          end.

        Notation "g |- x":= (ZST_Theorem (sf_sequent g x)) (at level 42).

        (** In what follows we develop natural deduction for Zermelo theory*)

        Definition z_nd_tool: forall (gamma: list F) (x y: F),
            ZST_Theorem (x -o y) ->
            ZST_Theorem ((sf_sequent gamma x) -o (sf_sequent gamma y)).
        Proof.
          intro g; induction g; intros. simpl; assumption. apply IHg; syl2; assumption.
        Defined.

        Definition z_nd_double_negation_elim (gamma: list F) (x: F):
          gamma |- (x -o §) -o § -> gamma |- x.
        Proof.
          apply zst_inference_modus_ponens; apply z_nd_tool; apply zst_logical_axiom_3.
        Defined.

        (** The result below says that every theorem of Zermelo set theory as defined above
     can be introduced on the fly as a theorem of natural deduction, enabling the
     free use of the axioms of the former into the latter. *)
        
        Definition z_nd_zst_theorem_intro: forall (gamma: list F) (x: F),
            ZST_Theorem x -> gamma |- x.
        Proof.
          intro gamma; induction gamma; intros x pr. simpl; apply pr. simpl; apply IHgamma.
          mp x. ka. apply pr.
        Defined.

        (**Conversely, every theorem obtained in natural deduction with an empty list of
     hypotheses is a theorem of Zermelo set theory.*)
        Definition z_nd_to_zst_theorem (x: F): nil |- x -> ZST_Theorem x.
        Proof.
          simpl; intro; assumption.
        Defined.
        
        Definition z_nd_head (x: F) (gamma: list F): cons x gamma |- x.
        Proof.
          simpl; apply z_nd_zst_theorem_intro with (x:= x -o x). ia.
        Defined.
        
        Definition z_nd_weakening_rule (gamma: list F) (a b: F):
          gamma |- b -> (cons a gamma) |- b.
        Proof.
          intro pr; apply zst_inference_modus_ponens with (A:= (sf_sequent gamma b)).
          simpl; apply z_nd_tool. ka. apply pr.
        Defined.

        Definition z_nd_axiom_rule (x: F) (gamma: list F):
          list_membership F x gamma -> gamma |- x.
        Proof.
          intro m; induction m. apply z_nd_head. apply z_nd_weakening_rule; assumption.
        Defined.    

        (** Natural deduction rules for propositional connectors *)

        (** Implication *)
        Definition z_nd_implies_intro (gamma: list F) (a b: F):
          (cons a gamma) |- b -> gamma |- (a -o b).
        Proof.
          simpl; intro; assumption.
        Defined.

        Definition z_nd_implies_elim: forall (gamma: list F) (a b: F),
            gamma |- (a -o b) -> gamma |- a -> gamma |- b.
        Proof.
          intro g; induction g; intros p q; simpl. apply zst_inference_modus_ponens. intros A B.
          apply zst_inference_modus_ponens with (B:= sf_sequent g ((a -o p) -o (a -o q))) in A.
          apply (IHg (a -o p) (a -o q)); assumption. apply z_nd_tool; sa.
        Defined.    

        (** Negation *)
        
        Definition z_nd_not_intro (gamma: list F) (a: F):
          (cons a gamma) |- sf_false -> gamma |- sf_not a.
        Proof.
          apply z_nd_implies_intro.
        Defined.

        Definition z_nd_not_elim (gamma: list F) (a: F):
          gamma |- (sf_not a) -> gamma |- a -> gamma |- sf_false.
        Proof.
          apply z_nd_implies_elim.
        Defined.

        Definition z_nd_classical_absurdity (gamma: list F) (a: F):
          (cons (sf_not a) gamma) |- sf_false -> gamma |- a.
        Proof.
          intro P. apply z_nd_double_negation_elim. apply z_nd_not_intro. apply P.
        Defined.      

        (** Conjunction*)

        Definition z_nd_and_intro (gamma: list F) (a b: F):
          gamma |- a -> gamma |- b -> gamma |- (sf_and a b).
        Proof.
          intros P Q. apply z_nd_implies_intro. apply z_nd_implies_elim with (a:= b).
          apply z_nd_implies_elim with (a:= a). apply z_nd_head. 
          apply z_nd_weakening_rule; apply P. apply z_nd_weakening_rule; apply Q.
        Defined.

        Definition z_nd_and_left_elim (gamma: list F) (a b: F):
          gamma |- (sf_and a b) -> gamma |- a.
        Proof.
          intro P. apply z_nd_double_negation_elim. apply z_nd_implies_intro.
          apply z_nd_implies_elim with (a:= a -o b -o §). apply z_nd_weakening_rule; apply P.
          apply z_nd_implies_intro. apply z_nd_implies_intro. apply z_nd_implies_elim with (a:= a).
          apply z_nd_weakening_rule; apply z_nd_weakening_rule; apply z_nd_head.
          apply z_nd_weakening_rule; apply z_nd_head.
        Defined.      

        Definition z_nd_and_right_elim (gamma: list F) (a b: F):
          gamma |- (sf_and a b) -> gamma |- b.
        Proof.
          intro P. apply z_nd_double_negation_elim. apply z_nd_implies_intro.
          apply z_nd_implies_elim with (a:= a -o b -o §). apply z_nd_weakening_rule; apply P.
          apply z_nd_implies_intro. apply z_nd_implies_intro. apply z_nd_implies_elim with (a:= b).
          apply z_nd_weakening_rule; apply z_nd_weakening_rule; apply z_nd_head. apply z_nd_head.
        Defined.      

        (** Disjunction *)

        Definition z_nd_or_left_intro (gamma: list F) (a b: F):
          gamma |- a -> gamma |- (sf_or a b).
        Proof.
          intro P. apply z_nd_implies_intro. apply z_nd_implies_intro.
          apply z_nd_implies_elim with (a:= a). apply z_nd_weakening_rule; apply z_nd_head.
          apply z_nd_weakening_rule; apply z_nd_weakening_rule; apply P.
        Defined.

        Definition z_nd_or_right_intro (gamma: list F) (a b: F):
          gamma |- b -> gamma |- (sf_or a b).
        Proof.
          intro P. apply z_nd_implies_intro. apply z_nd_implies_intro.
          apply z_nd_implies_elim with (a:= b). apply z_nd_head.
          apply z_nd_weakening_rule; apply z_nd_weakening_rule; apply P.
        Defined.

        Definition z_nd_or_elim (gamma: list F) (a b c: F):
          gamma |- (sf_or a b) -> (cons a gamma) |- c -> (cons b gamma) |- c -> gamma |- c.
        Proof.
          intros P Q R. apply z_nd_double_negation_elim. apply z_nd_implies_intro.
          apply z_nd_implies_elim with (a:= b -o §). apply z_nd_implies_elim with (a:= a -o §).
          apply z_nd_weakening_rule. apply P.
          apply z_nd_implies_intro. apply z_nd_implies_elim with (a:= c).
          apply z_nd_weakening_rule. apply z_nd_head.
          apply z_nd_weakening_rule with (a:= c -o §) (gamma := gamma) (b:= a -o c); apply Q.
          apply z_nd_implies_intro. apply z_nd_implies_elim with (a:= c).
          apply z_nd_weakening_rule. apply z_nd_head.
          apply z_nd_weakening_rule with (a:= c -o §) (gamma := gamma) (b:= b -o c); apply R.
        Defined.

        (** Equality*)
        
        Definition z_nd_equality_intro (gamma: list F) (t: nat):
          gamma |- t == t.
        Proof.
          apply z_nd_zst_theorem_intro. mp (sf_all (0 == 0)).
          apply zst_logical_axiom_4 with (t:= t) (P:= 0 == 0). apply zst_equality_reflexivity.
        Defined.

        Definition z_nd_equality_elim_with_apply (gamma: list F) (a: F) (s t: nat):
          gamma |- s == t -> gamma |- sf_apply a s -> gamma |- sf_apply a t.
        Proof.
          intros P Q. apply z_nd_implies_elim with (a:= sf_apply a s).
          apply z_nd_implies_elim with (a:= s == t). apply z_nd_zst_theorem_intro.
          apply zst_Leibniz_rule. apply P. apply Q.
        Defined.

        Definition z_nd_equality_elim (gamma: list F) (a: F) (x s t: nat):
          gamma |- s == t -> gamma |- sf_specify a x s -> gamma |- sf_specify a x t.
        Proof.
          repeat rewrite <- sf_lambda_apply; apply z_nd_equality_elim_with_apply.
        Defined.    
        
        Section Premiminary_tools_for_quantifiers_in_natural_deduction.

          Definition zst_and_implies (a b c: F):
            ZST_Theorem ((sf_and a b) -o c) -> ZST_Theorem (a -o b -o c).
          Proof.
            intro pr. apply z_nd_to_zst_theorem. repeat apply z_nd_implies_intro.
            apply z_nd_implies_elim with (a:= sf_and a b). repeat apply z_nd_weakening_rule.
            apply pr. apply z_nd_and_intro. apply z_nd_weakening_rule; apply z_nd_head.
            apply z_nd_head.
          Defined.
          
          Definition zst_all_implies (a b: F):
            ZST_Theorem (sf_all (a -o b) -o (sf_all a) -o (sf_all b)).
          Proof.
            assert (forall (e: nat -> nat) (p q: F),
                       sf_substitution e (sf_and p q) =
                         sf_and (sf_substitution e p) (sf_substitution e q)) as C.
            intros e p q; simpl; reflexivity.
            assert
              (forall p: F, sf_apply (sf_substitution (shift_environment S) p) 0 = p) as D.
            intros p; unfold sf_apply; rewrite sf_cov_composition_equality.
            transitivity (sf_substitution (fun i: nat => i) p).
            apply sf_cov_pointwise_equality. intros v A; destruct v; simpl; reflexivity.
            apply sf_cov_identity_equality.
            assert (forall p: F,
                       ZST_Theorem
                         ((sf_all (sf_substitution (shift_environment S) p)) -o p)) as E.
            intros. apply eq_rec with
              (x:= sf_apply (sf_substitution (shift_environment S) p) 0)
              (y:= p)
              (P:= fun r: F =>
                     ZST_Theorem (sf_all (sf_substitution (shift_environment S) p) -o r)).
            apply zst_logical_axiom_4. apply D.
            apply zst_and_implies. apply zst_inference_generalization.
            apply z_nd_to_zst_theorem. apply z_nd_implies_intro. unfold sf_constant_embedding.
            rewrite C. apply z_nd_implies_elim with (a:= a).
            apply z_nd_implies_elim with (a:= sf_substitution S (sf_all (a -o b))).
            apply z_nd_zst_theorem_intro. apply E.
            apply z_nd_and_left_elim with (b:=sf_substitution S (sf_all a)).
            apply z_nd_head. 
            apply z_nd_implies_elim with (a:= sf_substitution S (sf_all a)).
            apply z_nd_zst_theorem_intro. apply E.
            apply z_nd_and_right_elim with (a:=sf_substitution S (sf_all (a -o b))).
            apply z_nd_head. 
          Defined.      

          Fixpoint sf_list_substitution (env: nat -> nat) (l: list F) {struct l}: list F:=
            match l with
            | nil => nil
            | cons h t => cons (sf_substitution env h) (sf_list_substitution env t)
            end.

          Fixpoint sf_list_constant_embedding (l: list F) {struct l}: list F:=
            match l with
            | nil => nil
            | cons h t => cons (sf_constant_embedding h) (sf_list_constant_embedding t)
            end.

          Theorem sf_list_constant_embedding_equality (l: list F):
            sf_list_constant_embedding l = sf_list_substitution S l.
          Proof.
            induction l; simpl. reflexivity. apply f_equal2. reflexivity. apply IHl.
          Defined.      

          Inductive sf_list_free_variable (v: nat): (list F) -> Prop:=
          |sflfv_head: forall (t: list F) (h: F),
              sf_free_variable v h -> sf_list_free_variable v (cons h t)
          |sflfv_tail: forall (t: list F) (h: F),
              sf_list_free_variable v t -> sf_list_free_variable v (cons h t).
          
          Theorem sf_list_cov_pointwise_equality:
            forall (l: list F) (env1 env2: nat -> nat)
                   (eqenv: forall v: nat, sf_list_free_variable v l -> env1 v = env2 v),
              sf_list_substitution env1 l = sf_list_substitution env2 l.
          Proof.
            intro l; induction l; intros e1 e2 eqenv; simpl. reflexivity.
            apply f_equal2. apply sf_cov_pointwise_equality. intros v A. apply eqenv.
            apply sflfv_head; apply A. apply IHl. intros v A. apply eqenv.
            apply sflfv_tail; apply A.
          Defined.

          Definition sf_cov_sequent_equality (gamma: list F): forall (a: F) (env: nat -> nat),
              sf_substitution env (sf_sequent gamma a) =
                sf_sequent (sf_list_substitution env gamma) (sf_substitution env a).
          Proof.
            induction gamma; intros b e; simpl. reflexivity. rewrite IHgamma. apply f_equal.
            simpl; reflexivity.
          Defined.

          Theorem sf_list_unfree_lambda_constant_embedding:
            forall (l: list F) (x: nat),
              (~ sf_list_free_variable x l) ->
              sf_list_substitution (binding_env x) l = sf_list_constant_embedding l.
          Proof.
            intros l x A. rewrite sf_list_constant_embedding_equality.
            apply sf_list_cov_pointwise_equality. intros v B.
            unfold binding_env; destruct (nat_eq_dec x v). rewrite e in A; contradiction.
            reflexivity.
          Defined.        

          Definition z_nd_proof_letter_substitution (gamma: list F) (a: F)
            (pr: gamma |- a):
            forall (env: nat -> nat),
              (sf_list_substitution env gamma) |- sf_substitution env a.
          Proof.
            intro env. apply zst_proof_letter_substitution with (env := env) in pr.
            rewrite sf_cov_sequent_equality in pr. apply pr.
          Defined.        
          
        End Premiminary_tools_for_quantifiers_in_natural_deduction.
        
        (** Quantifiers *)

        (** Unreadable all *)
        
        Definition z_nd_all_intro: forall (gamma: list F) (a: F),
            (sf_list_constant_embedding gamma) |- a -> gamma |- (sf_all a).
        Proof.
          induction gamma; simpl; intros b. apply zst_hypothesis_free_generalization.
          intro P; apply IHgamma in P. apply z_nd_implies_intro.
          apply z_nd_implies_elim with (a:= sf_all (sf_constant_embedding a)).
          apply z_nd_weakening_rule. 
          apply z_nd_implies_elim with (a:= sf_all ((sf_constant_embedding a) -o b)).
          apply z_nd_zst_theorem_intro. apply zst_all_implies. apply P.
          apply z_nd_implies_elim with (a:= a). apply z_nd_zst_theorem_intro.
          apply zst_inference_generalization. ia. apply z_nd_head.
        Defined.    
        
        Definition z_nd_all_elim: forall (gamma: list F) (a: F) (t: nat),
            gamma |- sf_all a -> gamma |- (sf_apply a t).
        Proof.
          intros gamma a t; apply zst_inference_modus_ponens; apply z_nd_tool;
            apply zst_logical_axiom_4.
        Defined.    

        (** Readable forall*)
        
        Definition z_nd_forall_intro:
          forall (gamma: list F) (a: F) (x: nat) (nf: ~ sf_list_free_variable x gamma),
            gamma |- a -> gamma |- (sf_forall x a).
        Proof.
          intros gamma a x A pr.
          apply z_nd_proof_letter_substitution with (env:= binding_env x) in pr.
          rewrite sf_list_unfree_lambda_constant_embedding in pr. apply z_nd_all_intro;
            apply pr.
          apply A.
        Defined.

        Definition z_nd_forall_elim: forall (gamma: list F) (a: F) (x t: nat),
            gamma |- (sf_forall x a) -> gamma |- (sf_specify a x t).
        Proof.
          intros gamma a x t pr. rewrite <- sf_lambda_apply. apply z_nd_all_elim. apply pr.
        Defined.

        (** Unreadable ex *)

        Definition z_nd_ex_intro: forall (gamma: list F) (a: F) (t: nat),
            gamma |- (sf_apply a t) -> gamma |- (sf_ex a).
        Proof.
          intros gamma a t pr. apply z_nd_not_intro.
          apply z_nd_not_elim with (a:= sf_apply a t).
          assert (sf_not (sf_apply a t) = sf_apply (a -o §) t) as E.
          unfold sf_apply; simpl; reflexivity. rewrite E. apply z_nd_all_elim. apply z_nd_head.
          apply z_nd_weakening_rule; assumption.
        Defined.

        Definition z_nd_ex_elim: forall (gamma: list F) (a b: F),
            gamma |- (sf_ex a) ->
                     (cons a (sf_list_constant_embedding gamma)) |-
              (sf_constant_embedding b) -> gamma |- b.
        Proof.
          intros gamma a b P Q. apply z_nd_implies_intro in Q.
          assert (sf_list_constant_embedding (cons (b -o §) gamma) |- (a -o §)) as L.      
          apply z_nd_not_intro. apply z_nd_implies_elim with (a:= sf_constant_embedding b).
          apply z_nd_weakening_rule. simpl; unfold sf_constant_embedding; apply z_nd_head.
          apply z_nd_implies_elim with (a:= a). apply z_nd_weakening_rule; simpl;
            apply z_nd_weakening_rule; apply Q. apply z_nd_head. apply z_nd_all_intro in L.
          apply z_nd_classical_absurdity. apply z_nd_implies_elim with (a:= sf_all (a -o §)).
          apply z_nd_weakening_rule; apply P. apply L.
        Defined.      

        (** Readable exists *)

        Definition z_nd_exists_intro: forall (gamma: list F) (a: F) (x t: nat),
            gamma |- (sf_specify a x t) -> gamma |- (sf_exists x a).
        Proof.
          intros gamma a x t pr. rewrite <- sf_lambda_apply in pr.
          apply z_nd_ex_intro with (t:= t). apply pr.
        Defined.      

        Definition z_nd_exists_elim:
          forall (gamma: list F) (a b: F) (x: nat)
                 (nfg: ~ sf_list_free_variable x gamma)
                 (nfb: ~ sf_free_variable x b),
            gamma |- (sf_exists x a) -> (cons a gamma) |- b -> gamma |- b.
        Proof.
          intros gamma a b x nfg nfb P Q.  
          apply z_nd_proof_letter_substitution with (env:= binding_env x) in Q.
          simpl in Q. 
          rewrite sf_list_unfree_lambda_constant_embedding in Q.
          apply z_nd_ex_elim with (a:= sf_lambda x a). apply P.
          rewrite <- sf_unfree_lambda_constant_embedding with (x:= x) (p:= b). apply Q.
          apply nfb. apply nfg.       
        Defined.      
        
      End Natural_deduction_for_ZST_Theorems.
      
    End Properties_of_ZST_proofs_and_more_readable_forms_of_them.

  End Further_topics.

End Formal_Zermelo_set_theory.

Section General_semantics_and_semantical_correction_of_substitution_operations.

  (** In this section we define how to interpret formulas in a general setting. *)
  Variable M: Type.
  Variable m_bel m_eq: M -> M -> Prop.

  Definition model_shift_environment (env: nat -> M) (new_obj: M) (p: nat): M:=
    match p with
    | 0 => new_obj
    | S q => env q
    end.

  Notation F:= set_formula.
  Notation "x -o y":= (sf_implies x y) (right associativity, at level 41).
  
  Fixpoint sf_interpretation (env: nat -> M) (f: F) {struct f}: Prop:=
    match f with
    |sf_belongs x y => m_bel (env x) (env y)
    |sf_equal x y => m_eq (env x) (env y)
    |sf_false => False
    |sf_implies a b => (sf_interpretation env a) -> (sf_interpretation env b)
    |sf_all g => forall (x: M),
        sf_interpretation (model_shift_environment env x) g
    end.

  (** We do not yet introduce a correction theorem for the proof system defined in the
      first chapter. The reason is simply becayse it is not true for general models.
      The correction theorem will be true however for the specific model we'll define in the
      next chapter.
   *)
  
  Theorem sf_intp_pointwise_equality:
    forall (f: F) (env1 env2: nat -> M)
           (eqenv: forall v: nat, sf_free_variable v f -> env1 v = env2 v),
      sf_interpretation env1 f <-> sf_interpretation env2 f.
  Proof.
    intro f; induction f; intros; simpl.
    rewrite (eqenv n). rewrite (eqenv n0). apply iff_refl.
    apply sffv_belongs_right. apply sffv_belongs_left.
    rewrite (eqenv n). rewrite (eqenv n0). apply iff_refl.
    apply sffv_equal_right. apply sffv_equal_left. apply iff_refl. apply iff_implies.
    apply IHf1. intros; apply eqenv; apply sffv_implies_left; assumption.
    apply IHf2. intros; apply eqenv; apply sffv_implies_right; assumption.
    apply iff_forall; intro u. apply IHf; intros. destruct v.
    simpl; reflexivity. simpl; apply eqenv. apply sffv_all; assumption.
  Defined.

  Theorem sf_intp_composition_equality:
    forall  (f: F) (env1 : nat -> M) (env2: nat -> nat),
      sf_interpretation env1 (sf_substitution env2 f) <->
        sf_interpretation (fun k: nat => env1 (env2 k)) f.
  Proof.
    intro f; induction f; intros; simpl. apply iff_refl. apply iff_refl. apply iff_refl.
    apply iff_implies. apply IHf1. apply IHf2. apply iff_forall; intro u.
    apply iff_trans with
      (B:= sf_interpretation (fun k: nat => ((model_shift_environment env1 u)
                                               (shift_environment env2 k))) f). apply IHf.
    apply sf_intp_pointwise_equality; intros. destruct v; simpl; reflexivity.
  Defined.

  (** The remainder section of this chapter relates interpretation and certain syntactical
   operations defined in the previous chapter, in order to prove they are well behaved
   and actually have their intended meaning. *)

  Theorem sf_constant_embedding_semantical_correction
    (f: F) (env: nat -> M):
    forall x: M,
      sf_interpretation (model_shift_environment env x) (sf_constant_embedding f) <->
        sf_interpretation env f.
  Proof.
    intro x. unfold sf_constant_embedding.
    apply iff_trans with
      (B:= sf_interpretation (fun k: nat =>(model_shift_environment  env x) (S k)) f).
    apply sf_intp_composition_equality. simpl. apply iff_refl.
  Defined.    
  
  Theorem sf_apply_semantical_correction (f: F) (env: nat -> M) (t: nat):
    sf_interpretation env (sf_apply f t) <->
      sf_interpretation (model_shift_environment env (env t)) f.
  Proof.
    unfold sf_apply. 
    apply iff_trans with (B:= sf_interpretation (fun k: nat => env (app_env t k)) f).
    apply sf_intp_composition_equality. apply sf_intp_pointwise_equality; intros v A.
    destruct v; simpl; reflexivity.
  Defined.
  
  Definition model_environment_letter_edition
    (env: nat -> M) (variable_to_be_reassigned: nat) (new_object: M) (y: nat): M:=
    match (nat_eq_dec variable_to_be_reassigned y) with
    | left _ => new_object
    | right _ => env y
    end.
  
  Theorem sf_predicate_constant_embedding_semantical_correction
    (f: F) (env: nat -> M):
    forall x y: M,
      sf_interpretation
        (model_shift_environment (model_shift_environment env y) x)
        (sf_predicate_constant_embedding f) <->
        sf_interpretation (model_shift_environment env x) f.
  Proof.
    intros x y. unfold sf_predicate_constant_embedding.
    apply iff_trans with
      (B:= sf_interpretation
             (fun k: nat =>
                (model_shift_environment (model_shift_environment env y) x)
                  ((shift_environment S) k)) f).
    apply sf_intp_composition_equality. simpl. apply sf_intp_pointwise_equality; intros v A.
    destruct v; simpl; reflexivity.
  Defined.    

  Theorem sf_forall_semantical_correction (f: F) (x: nat) (env: nat -> M):
    sf_interpretation env (sf_forall x f) <->
      forall s: M, sf_interpretation (model_environment_letter_edition env x s) f.
  Proof.
    simpl; apply iff_forall; intro s. unfold sf_lambda.
    apply iff_trans with
      (B:= sf_interpretation
             (fun k: nat =>
                (model_shift_environment env s)
                  (binding_env x k)) f). apply sf_intp_composition_equality.
    apply sf_intp_pointwise_equality; intros v A. unfold model_environment_letter_edition.
    unfold binding_env. destruct (nat_eq_dec x v); simpl; reflexivity.
  Defined.
      
  Theorem sf_specify_semantical_correction (f: F) (env: nat -> M) (x t: nat):
    sf_interpretation env (sf_specify f x t) <->
      sf_interpretation (model_environment_letter_edition env x (env t)) f.
  Proof.
    unfold sf_specify.
    apply iff_trans with (B:= sf_interpretation (fun k: nat => env (replacement_env x t k)) f).
    apply sf_intp_composition_equality. apply sf_intp_pointwise_equality; intros v A.
    unfold replacement_env. unfold model_environment_letter_edition.
    destruct (nat_eq_dec x v); reflexivity.
  Defined.

  Theorem sf_generalization_rule_semantical_correction (a b: F):
    (forall env: nat -> M, sf_interpretation env ((sf_constant_embedding a) -o b)) ->
    forall env: nat -> M, sf_interpretation env (a -o sf_all b).
  Proof.
    intros A env B x. simpl in A; apply A. apply sf_constant_embedding_semantical_correction.
    apply B.
  Defined.

  Theorem sf_special_case_rule_semantical_correction (f: F) (t: nat) (env: nat -> M):
    sf_interpretation env ((sf_all f) -o sf_apply f t).
  Proof.
    simpl; intro A. apply sf_apply_semantical_correction. apply A.
  Defined.
      
End General_semantics_and_semantical_correction_of_substitution_operations.

Section Construction_of_the_Zermelo_model.

Inductive Ens: Type:=
|e_intro: forall A: Type, (A -> Ens) -> Ens.

Definition e_classical_extensional_equality: forall x y: Ens, Prop.
Proof.
  simple induction 1; intros A f eq1.
  simple induction 1; intros B g eq2.
  apply and. apply (forall x: A, ~ (forall y: B, ~ (eq1 x (g y)))).
  apply (forall y: B, ~ (forall x: A, ~ (eq1 x (g y)))).
Defined.

Notation "m == n":= (e_classical_extensional_equality m n) (at level 41).
  
Definition regular (P: Prop):= (~~ P) -> P.

Theorem regular_false: regular False.
Proof.
  intro A; apply A; intro B; assumption.
Defined.

Theorem regular_implies: forall (A B: Prop), regular B -> regular (A -> B).
Proof.
  intros A B r s t. apply r. intro u. apply s. intro v. apply u. apply (v t).
Defined.

Theorem regular_forall (T: Type) (f: T -> Prop):
  (forall t: T, regular (f t)) -> regular (forall t: T, f t).
Proof.
  intros A B s. apply A. intro t. apply B. intro u. apply t; apply u.
Defined.

Theorem regular_and (A B: Prop): regular A -> regular B -> regular (A /\ B).
Proof.
  intros p q r; split. apply p. intro s. apply r. intro t. apply s; apply t. apply q; intro k.
  apply r; intro l. apply k; apply l.
Defined.

Theorem regular_neg (P: Prop): regular (~ P).
Proof.
  intros f g; apply f; intro h; contradiction.
Defined.

Theorem regular_ens_eq: forall x y: Ens, regular (x == y).
Proof.
  induction x. induction y. simpl.
  apply regular_and; apply regular_forall; intro; apply regular_neg.
Defined.

Notation "a >-< b":= (((a -> b) -> (b -> a) -> False) -> False) (at level 43).
Notation "a %% b":= ((a -> b -> False) -> False) (at level 43).

Lemma reg_alt_equiv_intro (p q: Prop):
  (p <-> q) -> (p >-< q).
Proof.
  intros A B. apply B; apply A.
Defined.  

Lemma reg_alt_and_intro (p q: Prop):
  (p /\ q) -> (p %% q).
Proof.
  intros A B. apply B; apply A.
Defined.

Lemma regular_alternate_and (A B: Prop) (rA: regular A) (rB: regular B):
  (A /\ B) <-> ((A -> B -> False) -> False).
Proof.
  split; intro P. intro Q. destruct P; apply Q; assumption. split. apply rA; intro F; apply P.
  intros; apply F; assumption. apply rB; intro F; apply P.
  intros; apply F; assumption.
Defined.

Lemma regular_alternate_equiv (A B: Prop) (rA: regular A) (rB: regular B):
  (A <-> B) <-> (((A -> B) -> (B -> A) -> False) -> False).
Proof.
  apply regular_alternate_and; apply regular_implies; assumption. 
Defined.

Definition e_belongs (x y: Ens): Prop:=
  match y with
  |e_intro A f => ~ (forall a: A, ~ x == f a)
  end.

Notation "m € n":= (e_belongs m n) (at level 41).

Theorem regular_belongs (x y: Ens): regular (x € y).
Proof.
  destruct y; apply regular_neg.
Defined.

Theorem e_eq_sym: forall x y: Ens, x == y -> y == x.
Proof.
  intro x; induction x. intro y; induction y. simpl. intro P; destruct P as (P1, P2). split.
  intros y1 Q. apply (P2 y1). intros x1 R. apply (Q x1). apply H; assumption.
  intros x2 M. apply (P1 x2). intros y2 N. apply (M y2). apply H; assumption.
Defined.  

Theorem e_eq_refl: forall x: Ens, x == x.
Proof.
  intro x; induction x. simpl; split; intros s P; apply (P s); apply H.
Defined.

Lemma e_eq_rev_trans: forall x y z: Ens, x == y -> x == z -> y == z.
Proof.
  intro x; induction x. intros y z. destruct y as (B, f). destruct z as (C, g).
  simpl; intros P Q; destruct P as (P1, P2); destruct Q as (Q1, Q2); split; intros t F.
  apply (P2 t). intros s G. apply (Q1 s). intros u K. apply (F u). apply (H s); assumption.
  apply (Q2 t). intros s G. apply (P1 s). intros u K. apply (F u). apply (H s); assumption.
Defined.  

Theorem e_eq_trans: forall x y z: Ens, x == y -> y == z -> x == z.
Proof.
  intros x y z F G; apply (e_eq_rev_trans y). apply e_eq_sym; assumption. assumption.
Defined.

Theorem e_eq_bel_left_compatibility:
  forall x y z: Ens, x == y -> x € z -> y € z.
Proof.
  intros x y z e. destruct z as (A, f). simpl. intros F G. apply F. intros t K.
  apply (G t). apply e_eq_rev_trans with (x:= x); assumption.
Defined.

Theorem e_eq_bel_right_compatibility:
  forall x y z: Ens, x == y -> z € x -> z € y.
Proof.
  intros x y z e. destruct x as (A, f). destruct y as (B, g). simpl in e.
  destruct e as (e1, e2). simpl. intros P Q. apply P. intros s R. apply (e1 s). intros t T.
  apply (Q t). apply e_eq_trans with (y:= f s); assumption.
Defined.

Theorem e_extensionality: forall x y: Ens, (forall z: Ens, z € x <-> z € y) -> x == y.
Proof.
  intros x y. destruct x as (A, f). destruct y as (B, g). simpl.
  intro P; split; intros s Q. destruct (P (f s)) as (P1, P2). apply P1.
  intro F; apply (F s); apply e_eq_refl. intros t G. apply (Q t); apply G.
  destruct (P (g s)) as (P1, P2). apply P2.
  intro F; apply (F s); apply e_eq_refl. intros t G. apply (Q t); apply e_eq_sym; apply G.
Defined.  

Theorem e_alternate_extensionality:
  forall x y: Ens, (forall z: Ens, z € x >-< z € y) -> x == y.
Proof.
  intros x y A. apply e_extensionality; intro z. apply regular_alternate_equiv.
  apply regular_belongs. apply regular_belongs. apply A.
Defined.

Definition e_empty_set: Ens.
Proof.
  apply (e_intro Empty_set). apply Empty_set_rect.
Defined.

Theorem e_empty_set_is_empty: forall x: Ens, ~ (x € e_empty_set).
Proof.
  intros x F. simpl in F. apply F. intros a G. apply Empty_set_ind; apply a.
Defined.

Definition e_pair (a b: Ens): Ens:=
  e_intro bool (fun x: bool => match x with |true => a |false => b end).

Theorem e_pair_characterization (a b: Ens):
  forall x: Ens, (x € e_pair a b) <-> ((~ x == a) -> (~ x == b) -> False).
Proof.
  intro x; simpl; split. intros P Q R. apply P. intro t; induction t; assumption.
  intros P Q. apply P; intro F. apply (Q true); apply F. apply (Q false); apply F.
Defined.

Theorem e_alternate_pair_characterization (a b: Ens):
  forall x: Ens, (x € e_pair a b) >-< ((~ x == a) -> (~ x == b) -> False).
Proof.
  intro x; apply reg_alt_equiv_intro. apply e_pair_characterization.
Defined.

Definition e_comprehension_operator (x: Ens) (P: Ens -> Prop): Ens.
Proof.
  destruct x. apply (e_intro {a: A | P (e a)}). intro p. apply (e (proj1_sig p)).
Defined.

Theorem e_comprehension
  (P: Ens -> Prop) (reg: forall u: Ens, regular (P u))
  (eq_compatible: forall v w: Ens, v == w -> P v -> P w) (a: Ens):
  forall x: Ens, (x € (e_comprehension_operator a P)) <-> (x € a /\ P x).
Proof.
  intro x. destruct a as (A, f). simpl. split. intros L; split. intro F. apply L.
  intros i M. apply (F (proj1_sig i)). apply M. apply reg. intro F. apply L.
  intros j G. apply F. apply e_eq_sym in G. apply (eq_compatible (f (proj1_sig j))). apply G.
  apply (proj2_sig j). intros L M. apply L. intros i N. destruct L as (L1, L2).
  apply (eq_compatible x (f i) N) in L2.
  apply (M (exist (fun j: A => P (f j)) i L2 )); simpl; assumption.
Defined.

Theorem e_alternate_comprehension
  (P: Ens -> Prop) (reg: forall u: Ens, regular (P u))
  (eq_compatible: forall v w: Ens, v == w -> P v -> P w) (a: Ens):
  forall x: Ens, (x € (e_comprehension_operator a P)) >-< (x € a %% P x).
Proof.
  intro; apply reg_alt_equiv_intro. apply iff_trans with (B:= x € a /\ P x).
  apply e_comprehension; assumption. apply regular_alternate_and. apply regular_belongs.
  apply reg.
Defined.  

Definition e_power (x: Ens): Ens:=
  match x with
  |e_intro A f => e_intro
                    (A -> Prop)
                    (fun (c: A -> Prop) =>
                       e_intro (sig c) (fun (p: sig c) => f (proj1_sig p))
                    )
  end.

Notation included:= (fun a b: Ens => forall t: Ens, e_belongs t a -> e_belongs t b).

Theorem e_power_inclusion_characterization (v w: Ens): (v € e_power w) <-> included v w. 
Proof.
  split; intro L. destruct w as (A, f); simpl; intros t M N. apply L. intros c O.
  assert (t € e_intro {x : A | c x} (fun p : {x : A | c x} => f (proj1_sig p))) as E1.
  apply e_eq_bel_right_compatibility with (x:= v); assumption. simpl in E1. apply E1.
  intro; apply N. destruct w as (A, f). simpl. intro M.
  apply (M (fun i: A => (f i) € v)). destruct v as (B, g). simpl; split; intros t N.
  simpl in M. assert ((g t) € e_intro A f) as E2. apply L. simpl. intro F. apply (F t).
  apply e_eq_refl. simpl in E2. apply E2. intros j G.
  assert (~ (forall a: B, ~ f j == g a)) as E3. intro W. apply (W t). apply e_eq_sym; apply G.
  apply (N (exist (fun i: A => ~ (forall a: B, ~ f i == g a)) j E3)) . simpl. apply G.
  destruct t as (u, P). apply P. intros b K. apply (N b). simpl. apply e_eq_sym; assumption.
Defined.

Theorem e_alternate_power_inclusion_characterization (v w: Ens):
  (v € e_power w) >-< included v w. 
Proof.
  apply reg_alt_equiv_intro. apply e_power_inclusion_characterization.
Defined.
  
Definition proj1_e (v: Ens):Type:=
  match v with
  |e_intro T w => T
  end.

Definition proj2_e (v: Ens) (x: proj1_e v): Ens.
Proof.
  destruct v as (T, w). simpl in x. apply (w x).
Defined.

Definition e_union (x: Ens): Ens.
Proof.
  destruct x as (A, f). apply (e_intro (sigT (fun a: A => proj1_e (f a)))). intro p.
  destruct p as (b, u). apply (proj2_e (f b) u).
Defined.

Theorem e_union_characterization (v w: Ens):
  (v € e_union w) <-> ~ (forall t: Ens, ~ (v € t /\ t € w)).
Proof.
  destruct w as (A, f); simpl; split; intros L M. apply L; intros p N. destruct p as (a, Q).
  apply (M (f a)); split. apply e_eq_bel_left_compatibility with (x:= proj2_e (f a) Q).
  apply e_eq_sym; apply N.
  destruct (f a) as (B, g); simpl; intro F; apply (F Q); apply e_eq_refl.
  intro F; apply (F a); apply e_eq_refl. apply L; intros t (N1, N2). apply N2; intros a O.
  assert (v € f a) as E1. apply e_eq_bel_right_compatibility with (x:= t); assumption.
  assert (~ forall i: proj1_e (f a), ~  v == proj2_e (f a) i) as E2. intro F.
  destruct (f a) as (B, g). simpl in E1. simpl in F. contradiction. apply E2. intros i F.
  apply (M (existT (fun s: A => proj1_e (f s)) a i)). apply F.
Defined.  

Theorem e_alternate_union_characterization (v w: Ens):
  (v € e_union w) >-< ~ (forall t: Ens, ~ (v € t %% t € w)).
Proof.
  apply reg_alt_equiv_intro. apply iff_trans with (B:= ~ (forall t: Ens, ~ (v € t /\ t € w))).
  apply e_union_characterization. apply not_iff_compat. apply iff_forall; intro.
  apply not_iff_compat. apply regular_alternate_and; apply regular_belongs.
Defined.

Definition e_add_one_object (x y: Ens):Ens:=
  match x with
  |e_intro A f => e_intro (option A) (fun i: option A => match i with
                                                         | Some j => f j
                                                         | None => y
                                                         end)
  end.

Theorem e_add_one_object_characterization (x y z: Ens):
  (z € e_add_one_object x y) <-> ((~ z € x) -> (~ z == y) -> False).
Proof.
  destruct x as (A, f); simpl; split; intros L M. intro N. apply L. intros a P.
  destruct a. apply M. intro Q. apply (Q a P). contradiction. apply L. intro N.
  apply N. intros a P. apply (M (Some a)); assumption. intro P; apply (M None); apply P.
Defined.

Theorem e_add_one_object_eq_compatibility (x1 x2 y1 y2: Ens):
  x1 == x2 -> y1 == y2 -> e_add_one_object x1 y1 == e_add_one_object x2 y2.
Proof.
  intros P Q; apply e_extensionality; intro z.
  apply iff_trans with (B:= (~ z € x1) -> (~ z == y1) -> False).
  apply e_add_one_object_characterization. 
  apply iff_trans with (B:= (~ z € x2) -> (~ z == y2) -> False). apply iff_implies;
    apply not_iff_compat. split; apply e_eq_bel_right_compatibility. apply P.
  apply e_eq_sym; apply P. apply not_iff_compat; split; intro.
  apply e_eq_trans with (y:= y1); assumption. apply e_eq_trans with (y:= y2). assumption.
  apply e_eq_sym; assumption. apply iff_sym; apply e_add_one_object_characterization. 
Defined.

Definition e_successor (x: Ens): Ens:= e_add_one_object x x.

Theorem e_successor_eq_compatibility (x y: Ens):
  x == y -> e_successor x == e_successor y.
Proof.
  intro P; apply e_add_one_object_eq_compatibility; assumption.
Defined.

Fixpoint e_integer (n: nat) {struct n}: Ens:=
  match n with
  | 0 => e_empty_set
  | S m => e_successor (e_integer m)
  end.

Definition e_nat: Ens:= e_intro nat e_integer.      

Notation e_is_successor:=
  (fun (a b: Ens) =>
     forall x: Ens,
       (
         (
           ((x € a) -> ((~ x € b) -> (~ x == b) -> False)) ->
           (((~ x € b) -> (~ x == b) -> False) -> (x € a)) -> False
         ) -> False
       )
  ).

Lemma e_infinity_successor_aux: forall (x : Ens), e_is_successor (e_successor x) x.
Proof.
  intros x y. apply regular_alternate_equiv with 
    (A:= (y € e_successor x)) (B:= ((~ y € x) -> (~ y == x) -> False)).
  apply regular_belongs. repeat apply regular_implies; apply regular_false.
  apply e_add_one_object_characterization.
Defined.

Lemma classical_ex_intro: forall (T: Type) (P: T -> Prop) (x: T),
    P x -> ~(forall y: T, ~ P y).
Proof.
  intros; intro F. apply (F x); assumption.
Defined.

Theorem e_belongs_direct_intro (A: Type) (f: A -> Ens) (a: A):
  f a € e_intro A f.
Proof.
  simpl; intro F; apply (F a); apply e_eq_refl.
Defined.

Theorem e_classical_existence_of_an_infinite_set:
  (forall N: Ens,
        ~(~(( ~ forall v: Ens, ((forall x: Ens, x € v -> False)  %% v € N) -> False) ->
            (forall x: Ens, x € N ->
                            (~ forall y: Ens,
                                  (
                                     (e_is_successor y x -> y € N -> False) -> False
                                  ) -> False
                            )
            ) -> False))) -> False.
Proof.
  apply classical_ex_intro with (x:= e_nat). 
  assert (forall p q: Prop, p /\ q -> ~ (p -> q -> False)) as L. intros p q M N.
  apply N; apply M. apply L; split. unfold e_nat.
  apply classical_ex_intro with (x:= e_empty_set). apply reg_alt_and_intro. split.
  apply e_empty_set_is_empty. 
  apply e_belongs_direct_intro with (f:= e_integer) (a:=0). intros x B.
  unfold e_nat in B. simpl in B. apply classical_ex_intro with (x:= e_successor x).
  apply L. split. apply e_infinity_successor_aux. apply regular_belongs.
  intro F. apply B. intros a G. apply F.
  apply e_eq_bel_left_compatibility with (x:= e_successor (e_integer a)).
  apply e_successor_eq_compatibility; apply e_eq_sym; apply G.
  apply e_belongs_direct_intro with (f:= e_integer) (a:= (S a)).
Defined.

Section Interpretation_and_soundness.

  Notation F:= (set_formula).
  Notation Z_proves:= (ZST_Theorem).

  Notation val:= (sf_interpretation Ens e_belongs e_classical_extensional_equality).
  
  Theorem sf_interpretation_regular:
    forall (a: F) (env: nat -> Ens), regular (val env a).
  Proof.
    intro a; induction a; intro env; simpl. apply regular_belongs. apply regular_ens_eq.
    apply regular_false. apply regular_implies. apply IHa2.
    apply regular_forall; intro; apply IHa.
  Defined.
  
  Lemma classical_ex_intro_for_sf: forall (h: F) (env: nat -> Ens) (x: Ens),
      val (model_shift_environment Ens env x) h -> val env (sf_ex h).
  Proof.
    intros h env x; simpl.
    apply classical_ex_intro with
      (T:= Ens) (P:= fun t: Ens => val (model_shift_environment Ens env t) h).
  Defined.

  Ltac exi:= apply classical_ex_intro_for_sf.

  Lemma classical_forall_intro_for_sf: forall (h: F) (env: nat -> Ens),
      (forall x: Ens, val (model_shift_environment Ens env x) h) -> val env (sf_all h).
  Proof.
    simpl; intros V env W;  assumption.
  Defined.  

  Theorem sf_ens_compatibility_with_equality (f: F):
    forall
      (env1 env2: nat -> Ens)
      (eqenv: forall v:nat, sf_free_variable v f -> env1 v == env2 v),
      val env1 f <-> val env2 f.
  Proof.
    induction f; intros; simpl. apply iff_trans with (B:= env1 n € env2 n0).
    split; apply e_eq_bel_right_compatibility. apply eqenv. apply sffv_belongs_right.
    apply e_eq_sym. apply eqenv. apply sffv_belongs_right.
    split; apply e_eq_bel_left_compatibility. apply eqenv. apply sffv_belongs_left.
    apply e_eq_sym. apply eqenv. apply sffv_belongs_left.
    apply iff_trans with (B:= env1 n == env2 n0); split.
    intro; apply e_eq_trans with (y:= env1 n0). assumption. apply eqenv.
    apply sffv_equal_right. intro; apply e_eq_trans with (y:= env2 n0).
    assumption. apply e_eq_sym; apply eqenv. apply sffv_equal_right.
    intro; apply e_eq_trans with (y:= env1 n). apply e_eq_sym; apply eqenv.
    apply sffv_equal_left. assumption. intro; apply e_eq_trans with (y:= env2 n).
    apply eqenv; apply sffv_equal_left. assumption. apply iff_refl. apply iff_implies.
    apply IHf1. intros; apply eqenv; apply sffv_implies_left; assumption.
    apply IHf2. intros; apply eqenv; apply sffv_implies_right; assumption.
    apply iff_forall; intro u. apply IHf; intros. destruct v.
    simpl; apply iff_refl. apply e_eq_refl. simpl; apply eqenv. apply sffv_all; assumption.
  Defined.  
  
  Theorem Coq_implies_ZST_soundness:
    forall (a: F), Z_proves a -> forall env: nat -> Ens, val env a.
  Proof.
    intros a pr; induction pr; intro env. simpl in IHpr1; apply IHpr1. apply IHpr2.
    apply sf_generalization_rule_semantical_correction; assumption.
    simpl; intros; assumption.
    simpl; intros x y z; apply (x z (y z)). simpl; apply sf_interpretation_regular.
    apply sf_special_case_rule_semantical_correction.
    simpl; apply e_eq_refl. simpl; intro M. 
    apply imp_iff_compat_r with (B:= (val (model_shift_environment Ens env (env x)) f)).
    apply iff_sym; apply sf_apply_semantical_correction.
    apply imp_iff_compat_r with (B:= (val (model_shift_environment Ens env (env y)) f)).
    apply iff_sym; apply sf_ens_compatibility_with_equality. intros v A; destruct v.
    simpl; assumption. simpl; apply e_eq_refl. apply sf_apply_semantical_correction.  
    simpl; apply e_alternate_extensionality.
    apply classical_ex_intro_for_sf with (x:= e_empty_set). simpl; apply e_empty_set_is_empty.
    apply classical_forall_intro_for_sf; intro a. apply classical_forall_intro_for_sf; intro b.
    apply classical_ex_intro_for_sf with (x:= e_pair a b); simpl. 
    apply (e_alternate_pair_characterization a b).
    apply classical_forall_intro_for_sf; intro x.
    apply classical_ex_intro_for_sf with (x:= e_union x); simpl.
    intro v; apply (e_alternate_union_characterization v x).
    apply classical_forall_intro_for_sf; intro x.
    apply classical_ex_intro_for_sf with (x:= e_power x); simpl.
    intro v; apply (e_alternate_power_inclusion_characterization v x).
    apply classical_forall_intro_for_sf; intro a.
    apply classical_ex_intro_for_sf with
      (x:= e_comprehension_operator
             a (fun y: Ens =>
                  val
                    (model_shift_environment Ens (model_shift_environment Ens env a) y) P)).
    simpl.
    assert (forall A B: Prop, (A <-> B) -> A -> B) as Z. intros A B W; apply W.
    apply Z with (A:= forall x : Ens,
                     x
                       € e_comprehension_operator a
                       (fun y : Ens =>
                          val (model_shift_environment Ens
                                 (model_shift_environment Ens env a) y) P)
                       >-<
                       (x € a
                          %%
                          val
                          (model_shift_environment Ens (model_shift_environment Ens env a)
                             x)
                          P)
                 ). apply iff_forall; intro. repeat apply iff_implies.
    apply iff_refl. apply iff_refl. apply iff_sym.
    apply sf_predicate_constant_embedding_semantical_correction. apply iff_refl.
    apply iff_refl. apply iff_refl. apply iff_sym.
    apply sf_predicate_constant_embedding_semantical_correction. apply iff_refl.
    apply iff_refl. apply iff_refl. apply iff_refl. apply iff_refl.
    apply e_alternate_comprehension. intros; apply sf_interpretation_regular.
    intros v w E; apply Z; apply sf_ens_compatibility_with_equality.
    intros k A; destruct k. simpl; assumption. simpl; apply e_eq_refl.
    simpl. apply e_classical_existence_of_an_infinite_set.    
  Defined.    

  (** The master result we've been expecting is below*)
   
  Theorem
    Axiom_free_intuitionist_Coq_proves_the_consistency_of_Zermelo_set_theory_with_classical_logic:
    (Z_proves sf_false) -> False.
  Proof.
    intro W. apply (Coq_implies_ZST_soundness sf_false W (fun _: nat => e_empty_set)).
  Defined.
  
End Interpretation_and_soundness.

End Construction_of_the_Zermelo_model.
