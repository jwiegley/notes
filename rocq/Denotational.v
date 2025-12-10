(*
 * Denotational Design, Interactively
 *
 * This is an interactive workbook for exploring the process of denotional
 * design, using a real example to show how meaning and homomorphisms can
 * be used to improve our understanding of software and lead us to better
 * implementations.
 *
 * by Conal Elliott and John Wiegley
 *)

Require Import Coq.Reals.Reals.

(* We'll start things off by provided a simple definition of "color", and
   define any image by the following mathematical construct: a mapping from
   real space to colors. *)

Definition color := R.

Definition image := R * R -> color.

(* Given this definition of images, and a definition for black, define the
   meaning of an all-black image. *)

Definition black := 0%R.

Definition all_black_image : image := fun _ => black.

(* Now define how to flip an image along the Y-axis, so that the left becomes
   the right and vice versa. *)

Definition flip_horizontally (img : image) : image := fun '(x, y) =>
  img (negate x) y.

