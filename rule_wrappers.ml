
#use "Tactician/lib.ml";;
#use "Tactician/mlobject.ml";;
#use "Tactician/mltype.ml";;


(* THEOREM DEPENDENCY RECORDING *)

(* Flag to turn recording on and off dynamically *)

let record_deps = ref false;;

(* Type to represent dependency info about a theorem. *)

type dep_info = {
  theorem: thm;
  rule_name: string;
  args: mlobject list;
  deps: thm list;
  step_id: int ref
};;

(* The hash table that maps from a theorem to dep_info about the
   step that derived it. *)
let theorem_deps =
  let deps = Hashtbl.create 1000 in
  (* This code would set the exact type of theorem_deps, but results
     in a circular dependency, so we let execution fix the types later.
  let refl_t = REFL `T` in
  let info = create_dep_info refl_t "dummy" [] in
  Hashtbl.add deps (string_of_thm refl_t) info;
  Hashtbl.clear deps;
   *)
  deps;;

(* List of all dep_info objects *)
let derivations = ref [];;

(* Utility for finding an info having the given theorem in a list, etc. *)
let info_has_thm th info =
  th = info.theorem;;

(* Returns the thm object of just those args that are theorems, in order. *)
let filter_theorems (args:mlobject list) =
  itlist (fun arg results ->
           match arg with
           | Mthm th -> th :: results
           | _ -> results)
         args [];;

(* Returns a dep_info indicating that no dependency information
   for the theorem was found. *)
let no_dep_info th = {
      theorem = th; rule_name = "?"; args = []; deps = []; step_id = ref (-1)
  };;

(* Finds the dep_info of a theorem by looking it up in the
   theorem_deps database; or returns (no_dep_info th) if none found. *)
let find_dep_info th : dep_info =
  try List.find (info_has_thm th) !derivations
  with Not_found -> no_dep_info th;;

(*
  try List.find (fun info -> info.theorem == th)
                (Hashtbl.find_all theorem_deps (string_of_thm th))
  with Not_found ->
    List.iter (fun info -> print_thm info.theorem; print_string "\n")
               (Hashtbl.find_all theorem_deps (string_of_thm th));
    no_dep_info th;;
*)

(* Create a dep_info object from the given information. *)
let create_dep_info th name inputs : dep_info = {
    theorem = th;
    rule_name = name;
    args = inputs;
    deps = filter_theorems inputs;
    step_id = ref 1
};;

(* Use operations in this section to record information about theorems. *)

(* This runs as part of the execution of wrapped inference rules. *)
let record_derivation theorem rule_name (inputs:mlobject list) =
  (if !record_deps then
    let info = (create_dep_info theorem rule_name inputs) in
      derivations := info :: !derivations;
      let thm_string = string_of_thm theorem in
        Hashtbl.add theorem_deps thm_string info);
  theorem;;

let pair_record_derivation ((thm1, thm2) as theorems)
                           rule_name (inputs:mlobject list) =
  ignore (record_derivation thm1 rule_name inputs);
  ignore (record_derivation thm2 rule_name inputs);
  theorems;;

let list_record_derivation (theorems:thm list)
                           rule_name (inputs:mlobject list) =
  List.iter (fun th -> ignore (record_derivation th rule_name inputs)) theorems;
  theorems;;


(* Wrapper functions *)

(*
let thmpair_wrapper (name:string) ((th1:thm),(th2:thm)) : thm * thm =
  record_derivation 
*)

let conv_wrapper name (rule:term->thm) (arg:term) : thm =
  record_derivation (rule arg) name [Mterm arg];;

let term_conv_wrapper name (rule:term->term->thm) (arg1:term) (arg2:term) : thm =
  record_derivation (rule arg1 arg2) name [Mterm arg1; Mterm arg2];;

let thm_conv_wrapper name (rule:thm->term->thm) (th:thm) tm : thm =
  record_derivation (rule th tm) name [Mthm th; Mterm tm];;

let thmlist_conv_wrapper name (rule:thm list->term->thm) ths (tm:term) : thm =
  record_derivation (rule ths tm) name [mk_thlist ths; Mterm tm];;

let rule_wrapper name (rule:thm->thm) (th:thm) : thm =
  record_derivation (rule th) name [Mthm th];;

let drule_wrapper name (rule:thm->thm->thm) (th1:thm) (th2:thm) : thm =
  record_derivation (rule th1 th2) name [Mthm th1; Mthm th2];;

let prule_wrapper name (rule:thm*thm->thm) ((th1:thm),(th2:thm)) : thm =
  record_derivation (rule (th1, th2)) name [Mtuple [Mthm th1; Mthm th2]];;

let trule_wrapper name (rule:thm->thm->thm->thm)
                    (th1:thm) (th2:thm) (th3:thm) : thm =
  record_derivation (rule th1 th2 th3) name [Mthm th1; Mthm th2; Mthm th3];;

let term_rule_wrapper name (rule:term->thm->thm) tm (th:thm) : thm =
  record_derivation (rule tm th) name [Mterm tm; Mthm th];;

let termpair_rule_wrapper name (rule:term*term->thm->thm)
                          (tm1,tm2) (th:thm) : thm =
  record_derivation (rule (tm1, tm2) th)
                    name
                    [Mtuple [Mterm tm1; Mterm tm2]; Mthm th];;

let termthmpair_rule_wrapper name (rule:term*thm->thm->thm)
                                  (tm,th0) (th:thm) : thm =
  record_derivation (rule (tm, th0) th)
                    name
                    [Mtuple [Mterm tm; Mthm th0]; Mthm th];;

let termlist_rule_wrapper name (rule:term list->thm->thm) tms (th:thm) : thm =
  record_derivation (rule tms th)
                    name
                    [Mlist (map (fun tm -> Mterm tm) tms); Mthm th];;

(* From wrappers.ml *)
let inst_to_mlobject theta =
  Mlist (map (fun (tm1,tm2) -> Mtuple [Mterm tm1; Mterm tm2])
              theta);;

let terminst_rule_wrapper name (rule:(term*term)list->thm->thm)
                            theta (th:thm) : thm =
  record_derivation (rule theta th) name [inst_to_mlobject theta; Mthm th];;

(* From wrappers.ml *)
let tyinst_to_mlobject tytheta =
  Mlist (map (fun (ty1,ty2) -> Mtuple [Mtype ty1; Mtype ty2])
             tytheta);;

let typeinst_rule_wrapper name (rule:(hol_type*hol_type)list->thm->thm)
                            tytheta (th:thm) : thm =
  let ml_inst = tyinst_to_mlobject tytheta in
  record_derivation (rule tytheta th) name [ml_inst; Mthm th];;

(*

let instantation_rule_wrapper name (rule:instantiation->thm->thm)
let thmlist_rule_wrapper name (rule:thm list->thm->thm) ths (th:thm) : thm =
let pairrule_wrapper name (rule:thm->thm*thm) (th:thm) : thm * thm =
let multirule_wrapper name (rule:thm->thm list) (th:thm) : thm list =
let conv_conv_wrapper name (mc:conv->conv) (xc:xconv) (tm:term) : thm =
let stringconv_conv_wrapper name (mc:string->conv->conv)
let conv_rule_wrapper name (mr:conv->thm->thm) (xc:xconv) (th:thm) : thm =
let bconv_conv_wrapper name (mc:conv->conv->conv) (xc1:term->thm) (xc2:term->thm)
let mconvthmlist_conv_wrapper name
let mconvthmlist_rule_wrapper name

*)


(* The following OCaml utilities were stolen from
   Tactician/autopromote.ml, which stole several as referenced. *)

(* Executes at top level any OCaml expression given as a string. *)
let exec x =
  (ignore o Toploop.execute_phrase false Format.std_formatter o
   !Toploop.parse_toplevel_phrase o Lexing.from_string) x;;


(* From typing/env.ml: *)

exec
 ("type env_t = {
     values: (path_t * value_description) tbl;\n" ^
  (if (let v = String.sub Sys.ocaml_version 0 4 in v = "3.09" or v = "3.10")
     then ""
     else "  annotations: dummy;\n") ^
  "  constrs: dummy;
     labels: dummy;
     types: dummy;
     modules: (path_t * module_type) tbl;
     modtypes: dummy;
     components: dummy;
     classes: dummy;
     cltypes: dummy;
     summary: dummy};;");;


(* Generic operations on recent OCaml table entries *)

let lastStamp = ref 0;;
let currentStamp = ref 0;;

let is_new t =
   if (t > !lastStamp)
     then ((if (t > !currentStamp) then currentStamp := t);
           true)
     else false;;

let rec do_ocaml_table (f:string*'a->unit) (t:('a)tbl) : unit =
  match t with
  | Empty -> ()
  | Node (t1,d,t2,_) ->
      ((if (is_new d.ident.stamp) then f (d.ident.name,d.data));
       do_ocaml_table f t1;
       do_ocaml_table f t2);;

let rec htable_elems0 (t:('a)tbl) ixs0 =
  match t with
  | Empty            -> ixs0
  | Node (t1,d,t2,_) -> let ix = (d.ident.name,d.data) in
                        htable_elems0 t1 (ix :: (htable_elems0 t2 ixs0));;
let htable_elems t = htable_elems0 t [];;

let rec ocaml_table_find (x:string) (t:('a)tbl) : 'a =
  assoc x (htable_elems t);;


(* Returns the wrapper function for a given abstract type *)

let wrapper_name absty =
  match absty with
  | Aconv
       -> Some "conv_wrapper"
  | Aarrow[Aterm;Aconv]
       -> Some "term_conv_wrapper"
  | Aarrow[Athm;Aconv]
       -> Some "thm_conv_wrapper"
  | Aarrow[Alist(Athm);Aconv]
       -> Some "thmlist_conv_wrapper"
  | Aarrow[Athm;Athm]
       -> Some "rule_wrapper"
  | Aarrow[Athm;Athm;Athm]
       -> Some "drule_wrapper"
  | Aarrow[Atuple[Athm;Athm];Athm]
       -> Some "prule_wrapper"
  | Aarrow[Athm;Athm;Athm;Athm]
       -> Some "trule_wrapper"
  | Aarrow[Aterm;Athm;Athm]
       -> Some "term_rule_wrapper"
  | Aarrow[Atuple[Aterm;Aterm];Athm;Athm]
       -> Some "termpair_rule_wrapper"
  | Aarrow[Atuple[Aterm;Athm];Athm;Athm]
       -> Some "termthmpair_rule_wrapper"
  | Aarrow[Alist(Aterm);Athm;Athm]
       -> Some "termlist_rule_wrapper"
  | Aarrow[Alist(Atuple[Aterm;Aterm]);Athm;Athm]
       -> Some "terminst_rule_wrapper"
  | Aarrow[Alist(Atuple[Atype;Atype]);Athm;Athm]
       -> Some "typeinst_rule_wrapper"
(*
  | Aarrow[Aname"instantiation";Athm;Athm]
       -> Some "instantation_rule_wrapper"
  | Aarrow[Alist(Athm);Athm;Athm]
       -> Some "thmlist_rule_wrapper"
  | Aarrow[Athm;Atuple[Athm;Athm]]
       -> Some "pairrule_wrapper"
  | Aarrow[Athm;Alist(Athm)]
       -> Some "multirule_wrapper"
  | Aarrow[Aconv;Athm;Athm]
       -> Some "conv_rule_wrapper"
  | Aarrow[Aconv;Aconv]
       -> Some "conv_conv_wrapper"
  | Aarrow[Astring;Aconv;Aconv]
       -> Some "stringconv_conv_wrapper"
  | Aarrow[Aconv;Aconv;Aconv]
       -> Some "bconv_conv_wrapper"
  | Aarrow [Aarrow[Aconv;Aconv];Alist(Athm);Aconv]
       -> Some "mconvthmlist_conv_wrapper"
  | Aarrow [Aarrow[Aconv;Aconv];Alist(Athm);Athm;Athm]
       -> Some "mconvthmlist_rule_wrapper"
  (* Tactic-related wrappers *)
  | Atactic
       -> Some "tactic_wrap"
  | Aarrow[Astring;Atactic]
       -> Some "string_tactic_wrap"
  | Aarrow[Aterm;Atactic]
       -> Some "term_tactic_wrap"
  | Aarrow[Atuple[Aterm;Aterm];Atactic]
       -> Some "termpair_tactic_wrap"
  | Aarrow[Alist(Aterm);Atactic]
       -> Some "termlist_tactic_wrap"
  | Athm_tactic
       -> Some "thmtactic_wrap"
  | Aarrow[Aterm;Athm_tactic]
       -> Some "term_thmtactic_wrap"
  | Aarrow[Alist(Athm);Atactic]
       -> Some "thmlist_tactic_wrap"
  | Aarrow[Astring;Athm_tactic]
       -> Some "string_thmtactic_wrap"
  | Aarrow[Aconv;Atactic]
       -> Some "conv_tactic_wrap"
  | Aarrow[Aarrow[Athm;Athm];Atactic]
       -> Some "rule_tactic_wrap"
  | Aarrow[Aarrow[Aconv;Aconv];Alist(Athm);Atactic]
       -> Some "mconvthmlist_tactic_wrap"
  (* Xthms *)
  | Axthm
       -> Some "name_xthm"
*)
  (* Otherwise *)
  | _  -> None;;


(* Installing the wrapper functions *)

let rec wrapper_command pfx (name,vd) =
  let pname = pfx ^ name in
  let wrap = (wrapper_name o normalise_abstype o abstract_typeexpr)
                 vd.val_type in
  match wrap with
    Some wrapfn
       -> Some ("let " ^ name ^ " = " ^
                    wrapfn ^ " \"" ^ pname ^ "\" " ^ pname ^ ";;")
  | _  -> None;;



(* Back to non-stolen code now: *)


let rec wrap_rule (name,vd) =
  match (wrapper_command "" (name,vd)) with
    Some cmd -> exec cmd
  | _        -> ();;

(* Finds all theorems and inference rules defined at top level and
   wraps them with code to record their calling if they have not
   already been wrapped. *)
let wrap_rules () =
  let env = Obj.magic !Toploop.toplevel_env in
  (do_ocaml_table (fun (name, (_, vd)) ->
                       print_string name;
                       print_string "\n";
                       wrap_rule (name,vd))
                  env.values;
  lastStamp := !currentStamp);;


(* Mapping from theorems to their names *)

(* The hash table that maps named theorems to their names.  This is
   generated by iterating through all top-level variable bindings,
   picking up whatever name binding occurs last. *)
(* TODO: Store a list of theorems in each table entry, and modify theorem_name
   to search the list to find one identical to the input. *)
(* TODO: Support multiple names for the same theorem in the API. *)
let theorem_names =
  let table = Hashtbl.create 1000 in
  let refl = REFL `T` in
  Hashtbl.replace table (string_of_thm refl) "REFL_T";
  Hashtbl.clear table;
  table;;


let theorem_name theorem =
  Hashtbl.find theorem_names (string_of_thm theorem);;

let record_theorem_name theorem name =
  Hashtbl.replace theorem_names (string_of_thm theorem) name;;

let rec record_theorem_name1 (theorem_name,vd) =
  let absty = (normalise_abstype o abstract_typeexpr) vd.val_type in
  match absty with
  | Athm  ->
    let command = "record_theorem_name " ^ theorem_name ^
                  "\"" ^ theorem_name ^ "\";;" in
    exec command
  (*
  | Atuple[Athm;Athm]
       -> Some "thm_pair_wrapper"
  *)
  | _ -> ();;


(* Call this to update the theorem-to-name mappings to reflect current
   top-level variable bindings. *)
let record_theorems() =
  let env = Obj.magic !Toploop.toplevel_env in
  do_ocaml_table (fun (name, (_, vd)) ->
                      (* print_string ("Theorem " ^ name ^ "\n"); *)
                      record_theorem_name1(name,vd))
                  env.values;;


(* More utilities *)

(* Returns the first index where elt occurs in elts, starting from 0,j
   or else -1 if not found. *)
let find_index elt elts =
  let rec finder i head tail =
    if elt == head
    then i
    else match tail with
         | (h :: t) -> finder (i + 1) h t
         | [] ->  -1 in
  finder 0 (hd elts) (tl elts);;
  
(* Returns a list of key/value pairs for all bindings of all keys
   in the theorem_deps hash table. *)
let all_deps() =
  let add_binding key value results =
    (key, value) :: results in
  Hashtbl.fold add_binding theorem_deps [];;

(* Dump out information of a dep_info. *)
let print_rule_info (info:dep_info) = 
  let thm_string = (string_of_thm info.theorem) in
  let thm_name =
     try Hashtbl.find theorem_names thm_string with Not_found -> "" in
  let print_from th =
    (print_string "\n  from ";
     print_qterm (concl th)) in
  print_string thm_string;
  if String.length thm_name > 0 then
    (print_string " ("; print_string thm_name; print_string ")");
  print_string "  by ";
  print_string info.rule_name; 
  print_string " args = ";
  print_int (length info.args);
  List.iter print_from info.deps;
  print_string "\n";;

(* Assigns step numbers (step_id) to each info in the given list,
   starting at 1. *)
let number_steps steps =
  let rec renumber steps n =
    match steps with
    | head :: tail -> head.step_id := n; renumber tail (n + 1)
    | [] -> () in
  renumber steps 1;;

let linear_proof theorem =
  let all_steps = ref [no_dep_info (REFL `T`)] in
  all_steps := [];
  let rec linearize th =
    try ignore (List.find (info_has_thm th) !all_steps)
    with Not_found ->
      all_steps := (find_dep_info th) :: !all_steps;
      List.iter linearize (find_dep_info th).deps in
  linearize theorem;
  number_steps !all_steps;
  !all_steps;;

(* Print a list of inference rule arguments, mlobjects. *)
let print_rule_args args =
  let print_arg arg =
    match arg with
    | Mterm tm -> print_string (string_of_term tm)
    | Mthm th ->
      let number = !((find_dep_info th).step_id) in
      if number >= 0
      then print_int number
      else print_string ("\n  `" ^ (string_of_thm th) ^ "`")
    | _ -> print_string "..." in
  print_seplist print_arg ", " args;;

let print_step info =
  let thm_string = (string_of_thm info.theorem) in
  let thm_name =
     try Hashtbl.find theorem_names thm_string with Not_found -> "" in
  print_int !(info.step_id);
  print_string " ";
  print_string thm_string;
  (if String.length thm_name > 0 then
     (print_string " ("; print_string thm_name; print_string ")")
   else
     (print_string " by ";
      print_string info.rule_name)
  );
  if length info.args > 0 then
    (print_string " of ";
     print_rule_args info.args);
  print_string "\n";;

let print_linear_proof theorem =
  let proof = linear_proof theorem in
  List.iter print_step proof;;

(* Print all steps in the derivations database as if they were a proof.
   Prints them out reversed so the steps first created come first. *)
let print_derivations () =
  let steps = List.rev !derivations in
  number_steps steps;
  List.iter print_step steps;;

(* Convenience functions *)

(* Typical usage is ppp top_thm.  Here top_thm is not yet defined. *)
let ppp f = print_linear_proof (f());;


(* Actually wrap rules now. *)

wrap_rules();;
