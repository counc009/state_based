(* The goal of the verifier is that given a "reference" interpretation (the
 * result of interpreting the Formal Language Query) and a "candidate"
 * interpretation (the result of interpreting the generated Ansible program) we
 * check whether the candidate matches the reference.
 *
 * To do this for the moment we verify that each input/output state pair in the
 * reference has a "matching" state pair in the candidate. To identify that a
 * pair matches we need 1) that the assumptions in the candidate's input state
 * are consistent with those in reference's input state [ideally we want the
 * candidate's input state to only include assumptions from the reference's
 * input state but if it has additional assumptions we record that to permit
 * better analysis] and 2) that the actions in the candidate's output state
 * include all those from the reference's output state [again, ideally it would
 * be exactly the actions in the reference's but we'll record additional
 * actions that are taken]
 *
 * Note that this process actually involves a unification-like piece since there
 * may be unknown values in the reference solution which is allowed to take a
 * particular value (rather than having to be an arbitrary value). We determine
 * which unknowns are allowed to be arbitrary values by checking that they do
 * not appear as attribute values in the initial state (since such unknowns are
 * an assumption about the initial state).
 * FIXME: I think ideally we would track whether each unknown is a forall or
 * existential unknown (where unknowns generated during interpretation would be
 * forall but those generated via the GenUnknown expression would be
 * existential). Having this would be useful for the task described below since
 * it could be used to have existential variables to describe the set of
 * possible behaviors where we only need one of them from the candidate.
 *
 * In the future (TODO) we would like to be able to be able to interpret formal
 * queries to produce a set of sets of input/output states where only one
 * member of each set needs to be satisfied (for instance members of the same
 * set might reflect different ways to update the sudoers file) but the basis
 * of that is still checking equivalence of pairs of states so the approach
 * described above is still the core of that algorithm.
 *)

module Interp = Modules.Target.TargetInterp
module Ast = Modules.Target.Ast_Target

module IntSet : Set.S with type elt = int = Set.Make(Int)
module IntMap : Map.S with type key = int = Map.Make(Int)

(* Identify the universal variables *)
let universal_vars ((p, _): (Interp.prg_type * Ast.value)) : IntSet.t =
  let rec add_unknowns (v: Ast.value) s =
    match v with
    | Unknown (Loop i, _) | Unknown (Val i, _) -> IntSet.add i s
    | Literal (_, _) -> s
    | Function (_, v, _) -> add_unknowns v s
    | Pair (x, y, _) -> add_unknowns x (add_unknowns y s)
    | Constructor (_, _, v) -> add_unknowns v s
    | Struct (_, r) -> Ast.FieldMap.fold (fun _ -> add_unknowns) r s
    | ListVal (_, v) -> add_unknowns v s
  in let rec process_elems (elems : Interp.state Interp.ElementMap.t) s =
    Interp.ElementMap.fold (fun _ -> process_state) elems s
  and process_attrs
    (attrs : (Ast.value * Interp.state) Interp.AttributeMap.t) s =
    Interp.AttributeMap.fold
      (fun _ ((v, state) : Ast.value * Interp.state) set ->
        process_state state (add_unknowns v set))
      attrs
      s
  and process_state (state: Interp.state) s =
    let (elems, attrs) = match state with State (elsm, ats) -> (elsm, ats)
    in process_elems elems (process_attrs attrs s)
  in process_state p.init IntSet.empty

(* For the outcome of our verification we either decide the candidate is
 * incompatible with the reference (because it makes conflicting assumptions
 * or does not perform some necessary actions) or it is compatible though even
 * in that case we may report additional assumptions that are needed or
 * additional actions that were performed
 *)
(*type outcome = Incompatible of unit
             | Compatible   of unit*)

type unification = Value of Ast.value | Unknown of int
type unifier = unification IntMap.t

type state_diff = StateDiff of state_diff Interp.ElementMap.t
                       * (Ast.value option * state_diff) Interp.AttributeMap.t
type outcome = { m: unifier; constraints: unit; assumptions: state_diff;
                 actions: state_diff }

let is_empty (d: state_diff) : bool =
  match d with
  | StateDiff (elems, attrs) -> Interp.ElementMap.is_empty elems
                             && Interp.AttributeMap.is_empty attrs

let add_attr (a: Ast.attribute) (d: state_diff) (diff: state_diff) =
  match diff with
  | StateDiff (elms, ats) ->
      StateDiff (elms, Interp.AttributeMap.add a (None, d) ats)

let add_elem e (d: state_diff) (diff: state_diff) : state_diff =
  match diff with
  | StateDiff (elms, ats) ->
      StateDiff (Interp.ElementMap.add e d elms, ats)

let empty_diff : state_diff =
  StateDiff (Interp.ElementMap.empty, Interp.AttributeMap.empty)

let rec state_to_diff (s: Interp.state) : state_diff =
  match s with
  | State (elems, attrs) ->
      StateDiff (
        Interp.ElementMap.map state_to_diff elems,
        Interp.AttributeMap.map (fun (v, s) -> (Some v, state_to_diff s)) attrs
      )

let rec add_state_to_diff (d: state_diff) (s: Interp.state) : state_diff =
  match d, s with
  | StateDiff (elems_d, attrs_d), State (elems_s, attrs_s) ->
      let new_elems =
        Interp.ElementMap.merge (fun _ state_d state_s ->
          match state_d, state_s with
          | None, None -> None
          | Some d, None -> Some d
          | None, Some s -> Some (state_to_diff s)
          | Some d, Some s -> Some (add_state_to_diff d s))
        elems_d elems_s
      in let new_attrs =
        Interp.AttributeMap.merge (fun _ res_d res_s ->
          match res_d, res_s with
          | None, None -> None
          | Some d, None -> Some d
          | None, Some (v, s) -> Some (Some v, state_to_diff s)
          | Some (_, d), Some (v, s) -> Some (Some v, add_state_to_diff d s))
        attrs_d attrs_s
      in StateDiff (new_elems, new_attrs)

let add_attrs (ats: (Ast.value * Interp.state) Interp.AttributeMap.t)
              (diff: state_diff) : state_diff =
  match diff with
  | StateDiff (elems, attrs) ->
      let new_attrs = Interp.AttributeMap.merge (fun _ diff attr ->
        match diff, attr with
        | None, None -> None
        | Some d, None -> Some d
        | None, Some (v, s) -> Some (Some v, state_to_diff s)
        | Some (_, d), Some (v, s) -> Some (Some v, add_state_to_diff d s))
        attrs ats
      in StateDiff (elems, new_attrs)

let add_elems (elms: Interp.state Interp.ElementMap.t) (diff: state_diff) =
  match diff with
  | StateDiff (elems, attrs) ->
      let new_elems = Interp.ElementMap.merge (fun _ diff elem ->
        match diff, elem with
        | None, None -> None
        | Some d, None -> Some d
        | None, Some s -> Some (state_to_diff s)
        | Some d, Some s -> Some (add_state_to_diff d s))
        elems elms
      in StateDiff (new_elems, attrs)

let unify_candidate (universals: IntSet.t) (ref: Interp.prg_type * Ast.value)
  (cand: Interp.prg_type * Ast.value) : outcome list =
  let (ref, ref_val) = ref
  in let (cand, cand_val) = cand
  (* unify_values returns None if it cannot unify the values (under the current
   * unifier m) and returns Some (m', b) if it can unify them by assuming the
   * unifier m' and b is true if m' = m and false otherwise (i.e., at this
   * point the unification is unconditional). *)
  in let rec unify_values (rv: Ast.value) (cv: Ast.value) (m : unifier)
    : (unifier * bool) option =
    match rv, cv with
    | Literal (r, _), Literal (c, _) when r = c -> Some (m, true)
    | Function (f, v, _), Function (g, w, _) when f = g -> unify_values v w m
    | Pair (x, y, _), Pair (a, b, _) ->
        Option.bind (unify_values x a m) (fun (m, u1) ->
          Option.bind (unify_values y b m) (fun (m, u2) -> Some (m, u1 && u2)))
    | Constructor (n, b, v), Constructor (p, c, w) when n = p && b = c ->
        unify_values v w m
    | Struct (_, r), Struct (_, t) ->
        (* By checking that they have equal cardinality, and then ensuring that
         * each binding in r is also a binding in s we ensure they have the same
         * set of bindings *)
        if Ast.FieldMap.cardinal r <> Ast.FieldMap.cardinal t then None
        else Ast.FieldMap.fold (fun f v m ->
          Option.bind m (fun (m, u1) ->
            Option.bind (Ast.FieldMap.find_opt f t) (fun w ->
              Option.bind (unify_values v w m) (fun (m, u2) ->
                Some (m, u1 && u2)))))
          r
          (Some (m, true))
    | ListVal (_, v), ListVal (_, w) -> unify_values v w m
    | Unknown (Loop i, _), Unknown (Loop j, _) ->
        begin match IntMap.find_opt i m with
        | Some (Unknown v) -> if v = j then Some (m, true) else None
        | Some (Value _) -> None
        | None ->
            let loop_ref =
              Interp.ValueMap.fold
                (fun v l r -> match r with Some r -> Some r
                  | None -> match l with
                    | Interp.AllUnknown n | LastKnown (n, _)
                      -> if n = i then Some v else None
                    | AllKnown _ -> None)
                ref.loops
                None
            in let loop_cand =
              Interp.ValueMap.fold
                (fun v l r -> match r with Some r -> Some r
                  | None -> match l with
                    | Interp.AllUnknown n | LastKnown (n, _)
                      -> if n = j then Some v else None
                    | AllKnown _ -> None)
                cand.loops
                None
            in match loop_ref, loop_cand with
            (* If we didn't find one, that's an error. Fail to unify *)
            | None, _ | _, None -> None
            | Some v, Some w ->
                Option.bind (unify_values v w m) (fun (m, _) ->
                  Some (IntMap.add i (Unknown j) m, false))
        end
    | Unknown (Val i, _), Unknown (Val j, _) ->
        begin match IntMap.find_opt i m with
        | Some (Unknown v) -> if v = j then Some (m, true) else None
        | Some (Value _) -> None
        (* Note that we can unify a universal variable to variable since it
         * remains universal. As seen below we can't unify universals to
         * particular values *)
        | None -> Some (IntMap.add i (Unknown j) m, false)
        end
    | Unknown (Val _, _), Unknown (Loop _, _)
      | Unknown (Loop _, _), Unknown (Val _, _) -> None
    | Unknown (Val i, _), _ ->
        begin match IntMap.find_opt i m with
        | Some (Unknown _) -> None
        | Some (Value v) -> if v = cv then Some (m, true) else None
        | None -> if IntSet.mem i universals then None
                  else Some (IntMap.add i (Value cv) m, false)
        end
    | _, _ -> None
  (* When we unify states we need to know whether we are unifying an input or
   * not since the candidate is not required to make all the assumptions the
   * reference does but must perform all the actions the reference does. *)
  in let rec unify_states (ref: Interp.state) (cand: Interp.state) 
    (input: bool) (m: unifier) : (unifier * state_diff) list =
    match ref, cand with
    | State (elems_r, attrs_r), State (elems_c, attrs_c) ->
        (* Unifying attributes is easy since we just need to find the same
         * attribute and unify their values and states *)
        let unified_attrs =
          Interp.AttributeMap.fold (fun attr (v_r, s_r) res ->
            List.fold_left (fun res (m, attrs_c, diff) ->
              match Interp.AttributeMap.find_opt attr attrs_c with
              (* A missing attribute is allowed for the input only *)
              | None -> if input then (m, attrs_c, diff) :: res else res
              | Some (v_c, s_c) ->
                  match unify_values v_r v_c m with
                  | None -> res
                  | Some (m, _) ->
                      let new_attrs_c = Interp.AttributeMap.remove attr attrs_c
                      in List.fold_left (fun res (m, d) ->
                        if is_empty d then (m, new_attrs_c, diff) :: res
                        else (m, new_attrs_c, add_attr attr d diff) :: res
                      ) res (unify_states s_r s_c input m)
            ) [] res
          ) attrs_r [(m, attrs_c, empty_diff)]
        (* Unifying elements is much harder since it requires unifying
         * expressions and there may be multiple ways to unify elements
         *)
        in let unified_elems =
          List.concat_map (fun (m, attrs, diff) ->
            (* Add any remaining attributes from the candidate to the diff *)
            let diff = add_attrs attrs diff
            in Interp.ElementMap.fold (fun elem_r s_r res ->
              List.fold_left (fun res (m, elems_c, diff) ->
                let (matched_unconditional, res) =
                  Interp.ElementMap.fold (fun elem_c s_c (uncond, res) ->
                    let (el_r, v_r, b_r) = elem_r
                    in let (el_c, v_c, b_c) = elem_c
                    in if el_r <> el_c || b_r <> b_c then (uncond, res)
                    else match unify_values v_r v_c m with
                    | None -> (uncond, res)
                    | Some (m, u) ->
                        let new_elems_c = Interp.ElementMap.remove elem_c elems_c
                        in (uncond || u,
                        List.fold_left (fun res (m, d) ->
                          if is_empty d then (m, new_elems_c, diff) :: res
                          else (m, new_elems_c, add_elem elem_c d diff) :: res
                        ) res (unify_states s_r s_c input m))
                  ) elems_c (false, res)
                in if input && not matched_unconditional
                then (m, elems_c, diff) :: res
                else res
              ) [] res
            ) elems_r [(m, elems_c, diff)]
          ) unified_attrs
        in List.map (fun (m, elems, diff) -> (m, add_elems elems diff))
                    unified_elems
  in let unify_constraints (m: unifier) : (unifier * unit) option =
    Some (m, ()) (* FIXME *)
  in let unify_prgs (m: unifier) =
    (* To unify we do the following:
     * 1) Unify the initial states (collecting additional assumptions the
     *    candidate makes)
     * 2) Unify the final states (collecting additional actions performed by
     *    the candidate)
     * 3) Unify the boolean and constructor constraints/verify that they are
     *    consistent with the substitutions
     *)
    List.fold_left (fun res (m, assumptions) ->
      List.fold_left (fun res (m, actions) ->
        match unify_constraints m with
        | None -> res
        | Some (m, constrs) -> { m = m; constraints = constrs;
                                 assumptions = assumptions; actions = actions }
                               :: res
      ) res (unify_states ref.final cand.final false m)
    ) [] (unify_states ref.init cand.init true m)
  in match unify_values ref_val cand_val IntMap.empty with
  | None -> []
  | Some (m, _) -> unify_prgs m

let verify (reference: Interp.prg_res list) (candidate: Interp.prg_res list)
  : outcome list list =
  let verify_candidate (universals: IntSet.t) (ref: Interp.prg_type*Ast.value)
    (candidate: Interp.prg_res) : outcome list =
    match candidate with
    | Err _ -> []
    | Ok candidate -> unify_candidate universals ref candidate
  in let verify_result (ref: Interp.prg_res) : outcome list option =
    match ref with
    (* for errors in the reference, return None so that we filter them out *)
    | Err _ -> None
    | Ok ref ->
        (* For each possible outcome in the reference we need to find some
         * outcome(s) in the candidate that match. Because we just need some
         * we concat all the results from the individual candidate outcomes *)
        let var_analysis = universal_vars ref
        in Some (List.concat_map (verify_candidate var_analysis ref) candidate)
        (* NOTE: To really provide good feedback we need to associate the
         * information on additional assumptions/actions with the assumptions
         * already made in this reference outcome *)
  in let results = List.filter_map verify_result reference
  in results

let unification_to_string = function
  | Value v -> Modules.Target.value_to_string v
  | Unknown i -> "?" ^ string_of_int i

let state_diff_to_string (d: state_diff) : string =
  let rec inner if_empty lhs rhs (d: state_diff) =
    let StateDiff(elems, attrs) = d
    in Modules.Target.string_of_list if_empty lhs ", " rhs (fun s -> s)
      (List.map
        (fun (((elem, _), v, neg), s) ->
          (if neg then "not " else "")
          ^ elem ^ "(" ^ Modules.Target.value_to_string v ^ ")"
          ^ inner "" ": < " " >" s)
        (Interp.ElementMap.to_list elems)
      @
      List.map
        (fun ((attr, _), (v, s)) ->
          attr ^ (match v with None -> ""
                  | Some v -> " = " ^ Modules.Target.value_to_string v)
          ^ inner "" ": < " " >" s)
        (Interp.AttributeMap.to_list attrs))
  in inner "<>" "< " " >" d

let outcome_to_string (o: outcome) : string =
  (* FIXME: Print constraints *)
  let { m;  constraints = _; assumptions; actions } = o
  in let map =
    String.concat ", "
      (IntMap.fold (fun i v res ->
        Printf.sprintf "?%d -> %s" i (unification_to_string v) :: res
      ) m [])
  in Printf.sprintf "[ %s ], %s, %s"
    map (state_diff_to_string assumptions) (state_diff_to_string actions)

let print_verification (v: outcome list list) : unit =
  List.iter (fun v ->
    if List.is_empty v then Printf.printf "FAILED TO VERIFY\n"
    else Printf.printf "Unified with: %s\n"
      (String.concat " | " (List.map outcome_to_string v))
  ) v
