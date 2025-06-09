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
type outcome = Incompatible of unit
             | Compatible   of unit

type unification = Value of Ast.value | Unknown of int
type unifier = unification IntMap.t

let unify_candidate (universals: IntSet.t) (ref: Interp.prg_type * Ast.value)
  (cand: Interp.prg_type * Ast.value) : outcome option =
  let (ref, ref_val) = ref
  in let (cand, cand_val) = cand
  in let rec unify_values (rv: Ast.value) (cv: Ast.value) (m : unifier)
    : unifier option =
    match rv, cv with
    | Literal (r, _), Literal (c, _) when r = c -> Some m
    | Function (f, v, _), Function (g, w, _) when f = g -> unify_values v w m
    | Pair (x, y, _), Pair (a, b, _) ->
        Option.bind (unify_values x a m) (unify_values y b)
    | Struct (_, r), Struct (_, t) ->
        (* By checking that they have equal cardinality, and then ensuring that
         * each binding in r is also a binding in s we ensure they have the same
         * set of bindings *)
        if Ast.FieldMap.cardinal r <> Ast.FieldMap.cardinal t then None
        else Ast.FieldMap.fold (fun f v m ->
          Option.bind m (fun m ->
            Option.bind (Ast.FieldMap.find_opt f t) (fun w ->
              unify_values v w m)))
          r
          (Some m)
    | ListVal (_, v), ListVal (_, w) -> unify_values v w m
    | Unknown (Loop i, _), Unknown (Loop j, _) ->
        begin match IntMap.find_opt i m with
        | Some (Unknown v) -> if v = j then Some m else None
        | Some (Value _) -> None
        | None ->
            if IntSet.mem i universals
            then None (* we can't unify because i is universal *)
            else (* Track down what we're looping over in both results so that
                  * we can try to unify them *)
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
                  Option.bind (unify_values v w m) (fun m ->
                    Some (IntMap.add i (Unknown j) m))
        end
    | Unknown (Val i, _), Unknown (Val j, _) ->
        begin match IntMap.find_opt i m with
        | Some (Unknown v) -> if v = j then Some m else None
        | Some (Value _) -> None
        | None -> if IntSet.mem i universals then None
                  else Some (IntMap.add i (Unknown j) m)
        end
    | Unknown (Val _, _), Unknown (Loop _, _)
      | Unknown (Loop _, _), Unknown (Val _, _) -> None
    | Unknown (Val i, _), _ ->
        begin match IntMap.find_opt i m with
        | Some (Unknown _) -> None
        | Some (Value v) -> if v = cv then Some m else None
        | None -> if IntSet.mem i universals then None
                  else Some (IntMap.add i (Value cv) m)
        end
    | _, _ -> None
  in Option.bind (unify_values ref_val cand_val IntMap.empty) (fun _m ->
    failwith "TODO: handle the actual state unification")

let verify (reference: Interp.prg_res list) (candidate: Interp.prg_res list)
  : outcome =
  let verify_candidate (universals: IntSet.t) (ref: Interp.prg_type*Ast.value)
    (candidate: Interp.prg_res) : outcome option =
    match candidate with
    | Err _ -> None
    | Ok candidate -> unify_candidate universals ref candidate
  in let verify_result (ref: Interp.prg_res) : outcome option =
    match ref with
    | Err _ -> None
    | Ok ref ->
        let var_analysis = universal_vars ref
        in let _cmp = List.map (verify_candidate var_analysis ref) candidate
        in failwith "TODO"
  in let _results = List.map verify_result reference
  in failwith "TODO"
