(* Loader file for HOL Light and Proofdisplay.  #use this from the
   hol-light directory. *)

(* Directory path is still a hack.  Refer to the proofdisplay directory. *)

(* Load hol.ml up to and including drule.ml. *)
#use "hol1.ml";;

(* Load wrappers and wrapping code, and wrap the inference rules before
   loading the rest of HOL Light, so tactics code will use the wrapped
   versions. *)
#use "../proofdisplay/rule_wrappers.ml";;

(* Load the proof presentation code. This could be done later, as nothing
   depends on it. *)
#use "../proofdisplay/proof_display.ml";;

(* Load the rest of hol.ml. *)
hol2();;
