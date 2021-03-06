(* Loader file for HOL Light and Proofdisplay.  #use this from the
   hol-light directory. *)

(* Directory path is still a hack.  Refer to the proofdisplay directory. *)

(* Load hol.ml up to and including drule.ml. *)
#use "hol1.ml";;

(* Load wrappers and wrapping code, and wrap the inference rules before
   loading the rest of HOL Light, so tactics code will use the wrapped
   versions. *)
#use "../proofdisplay/rule_wrappers.ml";;

(* Wrap the primitive inference rules. *)
wrap_rules();;

(* Load support for accessing theorem names *)
#use "../proofdisplay/theorem_names.ml";;

(* Load the proof presentation code. This could be done later, as nothing
   depends on it. *)
#use "../proofdisplay/proof_display.ml";;

(* Load more of hol.ml. *)
hol2();;

(* Wrap the more advanced inference rules. *)
wrap_rules();;

hol3();;

(* Repeat this at any time to get the latest info about theorems. *)
record_names();;

(* Turn on recording of inference steps. *)
record_deps := true;
