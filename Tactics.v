From Stdlib Require Import List Arith.
From Sorting Require Export Candy.


Ltac2 Notation "neqbsimpl" :=
  try (rewrite Nat.eqb_eq in *); 
  try (rewrite Nat.leb_le in *); 
  try (rewrite Nat.leb_nle in *); 
  try (rewrite Nat.eqb_neq in *); 
  try (rewrite Nat.eqb_refl in *); 
  try (rewrite Nat.ltb_irrefl in *);
  subst;
  try lia.