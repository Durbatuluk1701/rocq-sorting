From Sorting Require Import SortingHeader.


(* Insertion Sort *)

(* The rough idea of insertion sort is:
"""
1. Take the head of the list
2. Recursively sort the tail of the list
3. Insert the head into the sorted tail at the appropriate position
"""
*)

(* Lets start by defining our insertion function.
Critically, we will *assume* that the list we are inserting into is already sorted.
*)

Fixpoint insert (x : nat) (l : list nat) : list nat.
Admitted.

(* Here is a fun way to do it with dependent types!

  This ensures that the output of the function is correct, without any additional lemmas needed!
  """
  Definition dep_insert (x : nat) 
      : forall il : {l : list nat | sorted l}, 
        {l : list nat | sorted l /\ 
          forall y, (count y (proj1_sig il) + if Nat.eqb x y then 1 else 0) = count y l }.
    ref (
      @Fix _ (fun l1 l2 => length (proj1_sig l1) < length (proj1_sig l2)) 
      _
      _
      (fun l F =>
      let Hsl := proj2_sig l in
      match (proj1_sig l) as l' return (proj1_sig l) = l' -> _ with
      | nil => fun HL => exist _ [x] (conj (sorted_singleton x) _)
      | h :: l'' => fun HL => _
      end eq_refl)
    ).
    - eapply well_founded_ltof.
    - (* base case *)
      ff l; neqbsimpl.
    - destruct (x <=? h) eqn:Hle.
      * ref (exist _ (x :: h :: l'') (conj _ _)).
        + neqbsimpl.
          econstructor; ff.
        + ff l; neqbsimpl.
      * ff. 
        erewrite sorted_spec in Hsl.
        destruct Hsl as [Hnl Hsl'].
        destruct (F (exist _ l'' Hsl')) as [rl'' [Hsrl'' Hcrl'']].
        ff.
        ref (exist _ (h :: rl'') (conj _ _)); ff.
        erewrite sorted_spec; split; ff; neqbsimpl; ff l.
        pp (Hcrl'' x0).
        ff l; neqbsimpl; ff.
        eapply Hnl.
        erewrite <- Permutation_Equals_Count.count_in.
        erewrite <- Permutation_Equals_Count.count_in in H.
        ff l.
  Defined.
  """
*)

Lemma insert_sorted : forall x l,
  sorted l ->
  sorted (insert x l).
Proof.
Admitted.
  (* intros.
  prep_induction H.
  induction H; ff; neqbsimpl; try (econstructor; ff l; fail).
  - econstructor; ff l.
    econstructor.
  - econstructor; ff l.
    econstructor.
  - econstructor; ff.
    pp (IHsorted x); ff; neqbsimpl.
  - econstructor; ff l.
    pp (IHsorted x0); ff; neqbsimpl.
  - econstructor; ff l.
    pp (IHsorted x0); ff; neqbsimpl.
Qed. *)

Lemma insert_count_cons : forall x y l,
  count x (insert y l) = count x l + if Nat.eqb x y then 1 else 0.
Proof.
Admitted.

Fixpoint insertion_sort (l : list nat) : list nat.
Admitted.

Theorem insertion_sort_correct : sort_correct insertion_sort.
Proof.
Admitted.
