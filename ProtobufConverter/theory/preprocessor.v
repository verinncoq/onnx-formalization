From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Strings.Ascii.

(*returns true if the character c is linefeed*)
Definition isLinefeed (c : ascii) : bool :=
  let n := nat_of_ascii c in (n =? 10).

(*
Removes comments starting with //.
Has two states: removing = true and removing = false.
If removing is true, every character gets removed. When a linefeed is found, removing is set back to false.
If removing is false, no character gets removed. When two slashs one after the other are found, removing is set to true.
The slashs are also removed then.
*)
Fixpoint remove_comments_recursive (s: string) (removing: bool) : string :=
  match s with
  | EmptyString => ""
  | String a s' => match removing with
                  | true => (*when removing is true, we are looking for the linefeed to stop the removing*)
                            match isLinefeed a with
                            | true => String a (remove_comments_recursive s' false)
                            | false => remove_comments_recursive s' true
                            end
                  | false => (*when removing is false, we are looking for two slashes to start the removing*)
                             match a with
                             | "/"%char => match s' with
                                      | EmptyString => String a EmptyString
                                      | String "/"%char s'' => remove_comments_recursive s'' true
                                      | String a' s'' => String a' (remove_comments_recursive s'' false)
                                      end
                             | a' => String a' (remove_comments_recursive s' false)
                             end
                  end
  end.

(*Wraps remove_comments_recursive to start with removing = false*)
Definition remove_comments (s: string) : string := remove_comments_recursive s false.