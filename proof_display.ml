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
    | Mterm tm -> printf "%s" (string_of_term tm)
    | Mthm th ->
      let number = !((find_dep_info th).step_id) in
      if number >= 0
      then printf "%d" number
      else printf "\n `%s`" (string_of_thm th)
    | _ -> printf "..." in
  printf_seplist print_arg ", " args;;

(* Print a single dep_info as a proof step. *)
let print_step info =
  let thm_string = (string_of_thm info.theorem) in
  let thm_name = theorem_name info.theorem in
  printf "%d %s" !(info.step_id) thm_string;
  (if String.length thm_name > 0 then
     printf " (%s)" thm_name
   else
     printf " by %s" info.rule_name
  );
  if length info.args > 0 then
    (printf " of ";
     print_rule_args info.args);
  printf "\n";;

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


