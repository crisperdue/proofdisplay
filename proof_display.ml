open Printf;;

(* Utility functions *)

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
  
let printf_seplist p sep xs =
  if (xs = [])
    then ()
    else (p (hd xs);
          do_list (fun x -> printf "%s" sep; p x) (tl xs));;

(* Returns a list of key/value pairs for all bindings of all keys
   in the theorem_deps hash table. *)
let all_deps() =
  let add_binding key value results =
    (key, value) :: results in
  Hashtbl.fold add_binding theorem_deps [];;

(* Printing *)

(* Lower-level dump of a dep_info. *)
let print_rule_info (info:dep_info) = 
  let thm_string = (string_of_thm info.theorem) in
  let thm_name = theorem_name info.theorem in
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

let rec trace_used_steps theorem =
  let info = find_derivation theorem in
  if !(info.step_id) > 0
  then ()
  else (info.step_id := 1; List.iter trace_used_steps info.deps);;

let linear_proof theorem =
  List.iter (fun step -> step.step_id := 0) !derivations;
  trace_used_steps theorem;
  let step_needed info = !(info.step_id) > 0 in
  let steps = rev (List.filter step_needed !derivations) in
  let counter = ref 1 in
  (List.iter (fun info -> info.step_id := !counter; counter := !counter + 1)
     steps;
   steps);;

(* Print a list of inference rule arguments, mlobjects. *)
let print_rule_args args =
  let rec print_arg arg =
    match arg with
    | Mname name -> printf "%s" name
    | Mstring str -> printf "%S" str
    | Mterm tm -> printf "`%s`" (string_of_term tm)
    | Mthm th ->
      let name = theorem_name th in
      let number = !((find_derivation th).step_id) in
      if String.length name > 0
      then printf "%s" name
      else if number > 0
      then printf "%d" number
      else printf "\n `%s`" (string_of_thm th)
    | Mconv cv ->
      let name = conv_name cv in
      printf "%s" (if name = "" then "<conv>" else name)
    | Mtuple items ->
      printf_seplist print_arg ", " items
    | Mlist items ->
      printf_seplist print_arg ", " items
    | _ -> printf "..." in
  printf_seplist print_arg ", " args;;

(* Print a single dep_info as a proof step. *)
let print_step info =
  let thm_string = (string_of_thm info.theorem) in
  let thm_name = theorem_name info.theorem in
  (if String.length thm_name > 0 then
     printf "%d (%s)" !(info.step_id) thm_name
   else
     printf "%d %s" !(info.step_id) info.rule_name
  );
  if length info.args > 0 then
    (printf " of ";
     print_rule_args info.args);
  printf ":\n%s" thm_string;
  printf "\n";;

let print_linear_proof theorem =
  let proof = linear_proof theorem in
  List.iter print_step proof;;

(* Print all steps in the derivations database as if they were a proof.
   The derivations list should be reversed before calling this. *)
let print_derivations () =
  let steps = !derivations in
  number_steps steps;
  List.iter print_step steps;;

(* Convenience functions *)

(* Typical usage is ppp top_thm.  Here top_thm is not yet defined. *)
let ppp f = print_linear_proof (f());;
