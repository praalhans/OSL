(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

From Coq Require Import ZArith.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Ensembles.
From Coq Require Import List.

Definition SomeZ (v: Z) := Some v.
Coercion SomeZ: Z >-> option.

Definition heap := Z -> option Z.
Definition dom (h: heap): Ensemble Z :=
  fun n => h n <> None.

