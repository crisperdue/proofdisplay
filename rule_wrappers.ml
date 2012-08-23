(* Define some HOL Light types here so this code can be loaded
   before most of the HOL system itself.
*)
type conv = term->thm;;
type label = int;;
type instantiation =
  (int * term) list * (term * term) list * (hol_type * hol_type) list;;


(* Utilities this code needs *)
#use "Tactician/lib.ml";;
#use "Tactician/mlobject.ml";;
#use "Tactician/mltype.ml";;

(* Retain handles to all the original unwrapped primitive inference
   functions. *)
let REFL_orig = REFL;;
let TRANS_orig = TRANS;;
let MK_COMB_orig = MK_COMB;;
let ABS_orig = ABS;;
let BETA_orig = BETA;;
let ASSUME_orig = ASSUME;;
let EQ_MP_orig = EQ_MP;;
let DEDUCT_ANTISYM_RULE_orig = DEDUCT_ANTISYM_RULE;;
let INST_TYPE_orig = INST_TYPE;;
let INST_orig = INST;;


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
  let info = create_dep_info TRUTH "dummy" [] in
  Hashtbl.add deps (string_of_thm refl_t) info;
  Hashtbl.clear deps;
   *)
  deps;;

(* List of all dep_info objects *)
let derivations = ref [];;

(* Tests whether an info has the given theorem. *)
let thm_has_derivation th info =
  th == info.theorem;;

let primitive_rules = [
  "REFL"; "TRANS"; "MK_COMB"; "ABS"; "BETA"; "ASSUME"; "EQ_MP";
  "DEDUCT_ANTISYM_RULE"; "INST_TYPE"; "INST"
];;

(* Finds the dep_info of a theorem by looking it up in the
   theorem_deps database; or returns (no_dep_info th) if none found.
   Finds the oldest derivation as an aid to skipping of no-op steps
   such as instantiations that do nothing.
*)
let find_derivation th : dep_info =
  let high_level derivation =
    not (List.mem derivation.rule_name primitive_rules) in
  let derivs = List.find_all (thm_has_derivation th) !derivations in
  (* We prefer to present a high-level derivation where possible. *)
  (* Sometimes it might be a no-op (e.g. instantiation) and in that
     case use a low-level derivation. *)
  let high_derivs = List.find_all high_level derivs in
  if (high_derivs != [] &&
      (let high = last high_derivs in not (List.memq high.theorem high.deps)))
  then last high_derivs
  else (try last derivs with Failure _ -> {
    theorem = th; rule_name = "?"; args = []; deps = []; step_id = ref 0
  });;

(* Scans the args recursively for theorems, returning a list of them. *)
let input_theorems (args:mlobject list) =
  let rec add_theorems arg results =
    itlist (fun arg1 results1 ->
            match arg1 with
            | Mthm th -> th :: results1
            | Mtuple items -> add_theorems items results1
            | Mlist items -> add_theorems items results1
            | _ -> results1)
      arg results in
  add_theorems args [];;

(* Create a dep_info object from the given information. *)
let create_dep_info th name inputs : dep_info = {
    theorem = th;
    rule_name = name;
    args = inputs;
    deps = input_theorems inputs;
    step_id = ref (-1)
};;



(* Operations that record information about theorems. *)

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


(* Wrapper functions.  These are called with the first two arguments
   at rule wrapping time.  During execution of a proof the function
   will be called with the remaining arguments, causing it to run the
   wrapped rule, recording arguments and the result. *)

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
let tyinst_to_mlobject tytheta =
  Mlist (map (fun (ty1,ty2) -> Mtuple [Mtype ty1; Mtype ty2])
             tytheta);;

let typeinst_rule_wrapper name (rule:(hol_type*hol_type)list->thm->thm)
                            tytheta (th:thm) : thm =
  let ml_inst = tyinst_to_mlobject tytheta in
  record_derivation (rule tytheta th) name [ml_inst; Mthm th];;

let inst_to_mlobject theta =
  Mlist (map (fun (tm1,tm2) -> Mtuple [Mterm tm1; Mterm tm2])
              theta);;

let terminst_rule_wrapper name (rule:(term*term)list->thm->thm)
                          theta (th:thm) : thm =
  record_derivation (rule theta th) name [inst_to_mlobject theta; Mthm th];;

let instantiation_to_mlobject (inst:instantiation) =
  let (ntms,theta,tytheta) = inst in
  let ntms' = Mlist (map (fun (n,tm) -> Mtuple [Mint n; Mterm tm]) ntms) in
  let theta' = inst_to_mlobject theta in
  let tytheta' = tyinst_to_mlobject tytheta in
  Mtuple [ntms';theta';tytheta'];;

let instantiation_rule_wrapper name (rule:instantiation->thm->thm)
                               theta (th:thm) : thm =
  record_derivation (rule theta th) name
    [instantiation_to_mlobject theta; Mthm th];;

let thmlist_rule_wrapper name (rule:thm list->thm->thm) ths (th:thm) : thm =
  record_derivation (rule ths th) name
    [mk_thlist ths; Mthm th];;

let pairrule_wrapper name (rule:thm->thm*thm) (th:thm) : thm * thm =
  let pair = rule th in
  let mthm = Mthm th in
  ignore (record_derivation (fst pair) name [mthm]);
  ignore (record_derivation (snd pair) name [mthm]);
  pair;;

let multirule_wrapper name (rule:thm->thm list) (th:thm) : thm list =
  let result = rule th in
  let args = [Mthm th] in
  let record result = ignore (record_derivation result name args) in
  List.iter record result;
  result;;

let conv_conv_wrapper name (mc:conv->conv) (c:conv) (tm:term) : thm =
  record_derivation (mc c tm) name [Mconv c; Mterm tm];;

let stringconv_conv_wrapper name (mc:string->conv->conv)
                            (s:string) (c:conv) (tm:term) : thm =
  record_derivation (mc s c tm) name [Mstring s; Mconv c; Mterm tm];;
  
let conv_rule_wrapper name (mr:conv->thm->thm) (c:conv) (th:thm) : thm =
  record_derivation (mr c th) name [Mconv c; Mthm th];;

let bconv_conv_wrapper name (mc:conv->conv->conv) (c1:term->thm) (c2:term->thm)
                       (tm:term) : thm =
  record_derivation (mc c1 c2 tm) name [Mconv c1; Mconv c2; Mterm tm];;

(* TODO:

let mconvthmlist_conv_wrapper name
       (mmconv:(conv->conv)->(thm)list->conv)
       (mc:conv->conv) (ths:(thm)list) (tm:term) : thm =
let mconvthmlist_rule_wrapper name
       (mmconv:(conv->conv)->(thm)list->thm->thm)
       (mc:conv->conv) (ths:(thm)list) (th:thm) : thm =

YIKES:
let bmeta_srule_wrap0 (x,args0)
                     (create_argobj1:'a->mlobject) (create_argobj2:'b->mlobject)
          (mr:('a->thm)->('b->thm)->thm)
          (xr1:'a->xthm) (xr2:'b->xthm) : xthm =
let metasrule_rule_wrap0 (x,args,i)
                     (create_argobj1:'b->mlobject) (create_argobj2:'b->mlobject)
  (mmr:(('a->thm)->'b->thm)->thm) (xmr:('a->xthm)->'b->xthm) : xthm =

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


(* Generic operations on recent OCaml table entries, cut and pasted
   from Tactician/autopromote.ml. *)

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

(* End of copied code section. *)


(* Returns the name of a function of suitable type to wrap functions of
   the given abstract type. *)
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
  | Aarrow[Aname"instantiation";Athm;Athm]
       -> Some "instantiation_rule_wrapper"
  | Aarrow[Alist(Athm);Athm;Athm]
       -> Some "thmlist_rule_wrapper"
  | Aarrow[Athm;Atuple[Athm;Athm]]
       -> Some "pairrule_wrapper"
  | Aarrow[Athm;Alist(Athm)]
       -> Some "multirule_wrapper"
(* These wrappers seem to work OK, but unfortunately a lot of the conversions
   I find passed in as arguments do not have top-level name bindings and
   it is not clear how to present these kinds of steps in a readable way.
*)
(*
  | Aarrow[Aconv;Athm;Athm]
       -> Some "conv_rule_wrapper"
  | Aarrow[Aconv;Aconv]
       -> Some "conv_conv_wrapper"
  | Aarrow[Astring;Aconv;Aconv]
       -> Some "stringconv_conv_wrapper"
  | Aarrow[Aconv;Aconv;Aconv]
       -> Some "bconv_conv_wrapper"
  | Aarrow [Aarrow[Aconv;Aconv];Alist(Athm);Aconv]
      -> (Printf.printf "Unsupported: %s\n" "mconvthmlist_conv_wrapper"; None)
*)
(*       -> Some "mconvthmlist_conv_wrapper" *)
  | Aarrow [Aarrow[Aconv;Aconv];Alist(Athm);Athm;Athm]
      -> (Printf.printf "Unsupported: %s\n" "mconvthmlist_rule_wrapper"; None)
(*       -> Some "mconvthmlist_rule_wrapper" *)
  (* Tactic-related wrappers *)
(* This application does not try to wrap tactics. *)
(*
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
*)
  (* Otherwise *)
  | _  -> None;;


(* Returns a command string that defines the given name as a wrapper
   that will call the current binding of the (prefixed) name. *)
let rec wrapper_command pfx (name,vd) =
  let pname = pfx ^ name in
  let wrap = (wrapper_name o normalise_abstype o abstract_typeexpr)
                 vd.val_type in
  match wrap with
    Some wrapper_name
    -> Some (Printf.sprintf "let %s = %s \"%s\" %s;;"
               name wrapper_name pname pname)
  | _  ->
      (let desc = abstract_typeexpr vd.val_type in
      match desc with
      | Aarrow[_;Athm] -> Printf.printf "Unwrapped rule: %s\n" name
      | _ -> ());
      None;;

(* Execute code to wrap extra functionality around the given name. *)
let rec wrap_rule (name,vd) =
  match (wrapper_command "" (name,vd)) with
    Some cmd -> exec cmd
  | _        -> ();;

(* Does the name end with "_orig"? *)
let ends_with s ending =
   let len = String.length s in
   let ending_len = String.length ending in
   if len > ending_len
   then (String.sub s (len - ending_len) ending_len = ending)
   else false;;

(* Finds all theorems and inference rules defined at top level since
   the last call to wrap_rules, and wraps them with code to record
   their calling if they have not already been wrapped. Skips names
   ending with _orig, so original bindings may be retained under
   such names.
*)
let wrap_rules () =
  let env = Obj.magic !Toploop.toplevel_env in
  (do_ocaml_table (fun (name, (_, vd)) ->
                     if not (ends_with name "_orig") then wrap_rule (name,vd))
                  env.values;
  lastStamp := !currentStamp);;


(* Don't actually wrap rules now. *)
(* wrap_rules();; *)
