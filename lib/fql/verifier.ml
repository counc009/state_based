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

(* The unifier holds the following information that is necessary to properly
 * handle unifying expressions:
 * - map: maps an unknown to a value or other unknown it is unified with
 * - vmap: maps an unknown to the list of unknowns mapped to it, i.e. if
 *   vmap[i] = xs and j in xs then map[j] = Unknown i
 * - universals: the set of universal unknowns (i.e. unknowns that can only be
 *   unified with other unknowns). This is initialized as the unknowns
 *   appearing as attribute values in the reference's initial state and then
 *   may expand as unknowns are unified to universal unknowns.
 *)
type unifier = { map: unification IntMap.t; vmap: int list IntMap.t;
                 universals: IntSet.t }

let lmap_find (i: int) (map: 'a list IntMap.t) : 'a list =
  match IntMap.find_opt i map with
  | None -> []
  | Some xs -> xs

let lmap_add (i: int) (x: 'a) (map: 'a list IntMap.t) : 'a list IntMap.t =
  IntMap.update i 
    (fun xs -> match xs with None -> Some [x] | Some xs -> Some (x :: xs))
    map

let lmap_extend (i: int) (xs: 'a list) (map: 'a list IntMap.t)
  : 'a list IntMap.t =
  IntMap.update i
    (fun ys -> match ys with None -> Some xs | Some ys -> Some (xs @ ys))
    map

let new_unifier (universals: IntSet.t) : unifier =
  { map = IntMap.empty; vmap = IntMap.empty; universals = universals }

let unifier_find (i: int) (u: unifier) : unification option =
  IntMap.find_opt i u.map

let unifier_add (i: int) (v: unification) (u: unifier) : unifier =
  let { map; vmap; universals } = u
  (* We need to perform 2 updates to map: map i -> v and for any j such that
   * j -> i we update it so that j -> v (in particular this means we use
   * vmap[i] and update those variables' bindings to v *)
  in { map = List.fold_left (fun map j -> IntMap.add j v map)
                (IntMap.add i v map) (lmap_find i vmap);
  (* For vmap, if v = Unknown k then we transfer vmap[i] to be part of vmap[k] *)
       vmap = (match v with Unknown k -> lmap_extend k (lmap_find i vmap) vmap
                         | Value _ -> vmap);
  (* For universals, if v = Unknown k and i is universal, then k is now
   * universal *)
       universals =
         if IntSet.mem i universals
         then match v with Unknown k -> IntSet.add k universals
                         | Value _ -> universals
         else universals
     }

(* The bool in the elements records whether this element itself is part of the
 * diff or only present because of a diff on it *)
type state_diff = StateDiff of (bool * state_diff) Interp.ElementMap.t
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
      StateDiff (Interp.ElementMap.add e (false, d) elms, ats)

let empty_diff : state_diff =
  StateDiff (Interp.ElementMap.empty, Interp.AttributeMap.empty)

let rec state_to_diff (s: Interp.state) : state_diff =
  match s with
  | State (elems, attrs) ->
      StateDiff (
        Interp.ElementMap.map (fun s -> (true, state_to_diff s)) elems,
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
          | None, Some s -> Some (true, state_to_diff s)
          | Some (b, d), Some s -> Some (b, add_state_to_diff d s))
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
        | None, Some s -> Some (true, state_to_diff s)
        | Some (b, d), Some s -> Some (b, add_state_to_diff d s))
        elems elms
      in StateDiff (new_elems, attrs)

let rec evaluate_val (v: Ast.value) (m: unifier) : Ast.value =
  match v with
  | Unknown (Loop i, t) ->
      begin match unifier_find i m with
      | None -> v
      (* This case should not occur *)
      | Some (Value _) -> failwith "Cannot replace Loop unknown with value"
      | Some (Unknown j) -> Unknown (Loop j, t)
      end
  | Unknown (Val i, t) ->
      begin match unifier_find i m with
      | None -> v
      | Some (Value w) -> w
      | Some (Unknown j) -> Unknown (Val j, t)
      end
  | Literal (_, _) -> v
  | Function (f, v, t) ->
      let new_v = evaluate_val v m
      in let (_, _, f_def) = Ast.funcDef f
      in begin match f_def new_v with
      | Reduced w -> w
      | Stuck -> Function (f, new_v, t)
      | Err msg ->
          (* FIXME *)
          failwith ("While substituting an unknown a function evaluation failed: " ^ msg)
      end
  | Pair (x, y, t) -> Pair (evaluate_val x m, evaluate_val y m, t)
  | Constructor (n, c, v) -> Constructor (n, c, evaluate_val v m)
  | Struct (t, r) -> Struct (t, Ast.FieldMap.map (fun v -> evaluate_val v m) r)
  | ListVal (n, w) -> ListVal (n, evaluate_val w m)

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
    let matched =
      match rv, cv with
      | Literal (r, _), Literal (c, _) when r = c -> Some (m, true)
      | Function (f, v, _), Function (g, w, _) when f = g -> unify_values v w m
      | Pair (x, y, _), Pair (a, b, _) ->
          Option.bind (unify_values x a m) (fun (m, u1) ->
            Option.bind (unify_values y b m) (fun (m, u2) ->
              Some (m, u1 && u2)))
      | Constructor (n, b, v), Constructor (p, c, w) when n = p && b = c ->
          unify_values v w m
      | Struct (_, r), Struct (_, t) ->
          (* By checking that they have equal cardinality, and then ensuring
           * that each binding in r is also a binding in s we ensure they have
           * the same set of bindings *)
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
          begin match unifier_find i m with
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
                    Some (unifier_add i (Unknown j) m, false))
          end
      | Unknown (Val i, _), Unknown (Val j, _) ->
          begin match unifier_find i m with
          | Some (Unknown v) -> if v = j then Some (m, true) else None
          | Some (Value _) -> None
          (* Note that we can unify a universal variable to variable since it
           * remains universal. As seen below we can't unify universals to
           * particular values *)
          | None -> Some (unifier_add i (Unknown j) m, false)
          end
      | Unknown (Val _, _), Unknown (Loop _, _)
        | Unknown (Loop _, _), Unknown (Val _, _) -> None
      | Unknown (Val i, _), _ ->
          begin match unifier_find i m with
          | Some (Unknown _) -> None (* Handled this case above *)
          | Some (Value v) ->
              if evaluate_val v m = evaluate_val cv m
              then Some (m, true) else None
          | None -> if IntSet.mem i m.universals then None
                    else Some (unifier_add i (Value cv) m, false)
          end
      (* Variables in the candidate can be constrained to a particular value
       * for instance the reference may assume a particular value for the OS
       * while the candidate may just the variable without matching on it.
       * While technically all variables in the candidate are universal, what
       * we're tracking through m.universals is the variables that can't be
       * constrained to a particular value *)
      | _, Unknown (Val i, _) ->
          begin match unifier_find i m with
          | Some (Unknown _) -> None (* Handled this case above *)
          | Some (Value v) ->
              if evaluate_val v m = evaluate_val rv m
              then Some (m, true) else None
          | None -> if IntSet.mem i m.universals then None
                    else Some (unifier_add i (Value rv) m, false)
          end
      | _, _ -> None
    in match matched with
    | Some res -> Some res
    (* If we failed to unify from above, we can try to unify by evaluation *)
    | None -> if evaluate_val rv m = evaluate_val cv m then Some (m, true)  
              else None
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
    (* To check the constraints, we first check that under the unifier m the
     * constraints don't simplify to a contradiction. Then, we identify if
     * the candidate has constraints not present in the reference and record
     * those *)
    let res_bools =
      Interp.ValueMap.fold (fun v b res -> Option.bind res (fun (m, bools_c) ->
        let v = evaluate_val v m
        in match v with
        | Literal (Bool c, _) when c <> b -> None
        (* This constraint has become trivial and so it doesn't have a match in
         * the candidate *)
        | Literal (Bool c, _) when c = b -> Some (m, bools_c)
        (* TODO: This should try to find a matching constraint in bools_c *)
        | _ -> Some (m, bools_c)
      )) ref.bools (Some (m, cand.bools))
    (* TODO: Handle constructor constraints. *)
    in Option.bind res_bools (fun (m, _) -> Some (m, ()))
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
  in match unify_values ref_val cand_val (new_unifier universals) with
  | None -> []
  | Some (m, _) -> unify_prgs m

(* Removes attributes that are just an unknown value from a state diff, this is
 * useful for cleaning up attributes in the initial states that happen to be
 * accessed in the ansible but not the query
 * TODO: Ideally this would probably only remove unconstrained unknowns
 *)
let rec clear_unknown_attributes (d: state_diff) : state_diff =
  let StateDiff (elems, attrs) = d
  in let clean_elems = Interp.ElementMap.filter_map (fun _ (b, s) ->
    let new_s = clear_unknown_attributes s
    in if is_empty new_s && not b then None else Some (b, new_s)
  ) elems
  in let clean_attrs = Interp.AttributeMap.filter_map (fun _ (v, s) ->
    let new_s = clear_unknown_attributes s
    in match v with
    | None | Some (Ast.Unknown (Val _, _)) ->
        if is_empty new_s then None else Some (None, new_s)
    | Some v -> Some (Some v, new_s)
  ) attrs
  in StateDiff (clean_elems, clean_attrs)

(* To clean-up the actions, we remove ANY attribute (not just those with an
 * unknown value IF the element it's on was contained in the reference). This
 * means we only report differences that imply some major action was performed.
 * There are potentially things we could care about that wouldn't show up
 * because of this (like who should own a particular file) but I think the
 * differences that matter the most are expressed by elements not attributes *)
let rec clear_additional_attributes (d: state_diff) : state_diff =
  let StateDiff (elems, attrs) = d
  in let clean_elems = Interp.ElementMap.filter_map (fun ((el,_),_,_) (b, s) ->
    (* We preserve everything on entirely different elements, except we exclude
     * env() from this because some of the changes are on it are just for
     * processing the Ansible *)
    if b && el <> "env" then Some (b, s)
    else let new_s = clear_additional_attributes s
    in if is_empty new_s then None else Some (b, new_s)
  ) elems
  in let clean_attrs = Interp.AttributeMap.filter_map (fun _ (_, s) ->
    let new_s = clear_additional_attributes s
    in if is_empty new_s then None else Some (None, new_s)
  ) attrs
  in StateDiff (clean_elems, clean_attrs)

let clean_outcome (o: outcome) : outcome =
  let { m; constraints; assumptions; actions } = o
  in let clean_assumptions = clear_unknown_attributes assumptions
  in let clean_actions = clear_additional_attributes actions
  in { m = m; constraints = constraints;
       assumptions = clean_assumptions; actions = clean_actions }

(* To merge multiple state diffs, we use another state-like construct, but this
 * one is significantly different from the others we have seen so far. Firstly,
 * for elements we do not store the positive/negative bool as part of the key,
 * rather we indicate it in the value since a Positive and Negative assumption
 * can cancel out.
 * Similarly, for attributes the value can be one of several options:
 * - No value: this attribute is only recorded because of the state on it
 * - A specific value
 * - Any value: this is used for boolean values where we merge cases that
 *   assume true and false
 * - Some values: if there are some specific values this can take but not all
 *)
module MergedElemMap = struct
  type 'a t = 'a Interp.ElementMap.t
  let empty : 'a t = Interp.ElementMap.empty

  let is_empty (m : 'a t) = Interp.ElementMap.is_empty m

  let add (elem, v) (x : 'a) (m : 'a t)
    = Interp.ElementMap.add (elem, v, false) x m

  let find_opt (elem, v) (m : 'a t)
    = Interp.ElementMap.find_opt (elem, v, false) m

  let update (elem, v) f (m : 'a t)
    = Interp.ElementMap.update (elem, v, false) f m

  let to_list (m: 'a t) = 
    List.map (fun ((e, v, _), x) -> ((e, v), x)) (Interp.ElementMap.to_list m)
end

(* Placeholder means this element only exists for the state on it *)
type merged_elem = Placeholder | Positive | Negative | Canceled
type merged_attr = Value of Ast.value | AnyValue | SomeValues

type merged_diff = MergedDiff of (merged_elem * merged_diff) MergedElemMap.t
                         * (merged_attr * merged_diff) Interp.AttributeMap.t

let empty_merged = MergedDiff (MergedElemMap.empty, Interp.AttributeMap.empty)

type merged_outcomes = { init: merged_diff; final: merged_diff;
                         constraints: unit }

let empty_outcomes : merged_outcomes = {
  init = empty_merged;
  final = empty_merged;
  constraints = ()
}

let merged_empty (m: merged_diff) : bool =
  let MergedDiff (elems, attrs) = m
  in MergedElemMap.is_empty elems && Interp.AttributeMap.is_empty attrs

let rec diff_to_merged (d: state_diff) : merged_diff =
  let StateDiff (elems, attrs) = d
  in let new_elems =
    Interp.ElementMap.fold (fun (elem, v, neg) (keep, s) new_elems ->
      let new_s = diff_to_merged s
      in MergedElemMap.add (elem, v)
        ((if merged_empty new_s && not keep then Canceled
          else if not keep then Placeholder
          else if neg then Negative else Positive), new_s)
        new_elems
    ) elems MergedElemMap.empty
  in let new_attrs =
    Interp.AttributeMap.map (fun (v, s) ->
      let new_s = diff_to_merged s
      in match v with
      | None -> (AnyValue, new_s)
      | Some v -> (Value v, new_s)
    ) attrs
  in MergedDiff (new_elems, new_attrs)

let merge_outcomes (outcomes: outcome list) : merged_outcomes =
  let rec merge_init (s: merged_diff) (o: state_diff) : merged_diff =
    let StateDiff (elems_o, attrs_o) = o
    in let MergedDiff (elems_s, attrs_s) = s
    in let new_elems =
      Interp.ElementMap.fold (fun (elem, v, neg) (keep, s) new_elems ->
        MergedElemMap.update (elem, v) (fun cur ->
          match cur with
          | None ->
              let s = diff_to_merged s
              (* If the state on this is empty and we don't need to keep it
               * then mark this element as canceled since it doesn't matter *)
              in Some ((if merged_empty s && not keep then Canceled
                        else if not keep then Placeholder
                        else if neg then Negative else Positive), s)
          | Some (kind, m) ->
              let new_s = merge_init m s
              in match kind, neg with
              | Positive, true | Negative, false | Canceled, _ 
                -> Some (Canceled, empty_merged)
              | Placeholder, _ when not keep -> Some (Placeholder, new_s)
              | Positive, false | Placeholder, false
                -> Some (Positive, new_s)
              | Negative, true | Placeholder, true
                -> Some (Negative, new_s)
        ) new_elems
      ) elems_o elems_s
    in let new_attrs =
      Interp.AttributeMap.fold (fun attr (v, s) new_attrs ->
        Interp.AttributeMap.update attr (fun cur ->
          match cur with
          | None ->
              let s = diff_to_merged s
              in begin match v with
              | None -> Some (AnyValue, s)
              | Some v -> Some (Value v, s)
              end
          | Some (mv, m) ->
              let new_s = merge_init m s
              in match mv, v with
              | _, None | AnyValue, _ -> Some (AnyValue, new_s)
              | SomeValues, _ -> Some (SomeValues, new_s)
              | Value v, Some w ->
                  if v = w then Some (Value v, new_s)
                  else match Ast.asTruth v, Ast.asTruth w with
                  | Some v, Some w when v <> w -> Some (AnyValue, new_s)
                  | _, _ -> Some (SomeValues, new_s)
        ) new_attrs
      ) attrs_o attrs_s
    in MergedDiff (new_elems, new_attrs)
  in let merge_final = merge_init
  in let merge_constraints () () = ()
  in List.fold_left (fun res (o: outcome) -> {
    (* TODO: Merging states should probably make use of the unifier *)
    init = merge_init res.init o.assumptions;
    final = merge_final res.final o.actions;
    constraints = merge_constraints res.constraints o.constraints
  }) empty_outcomes outcomes

let verify (reference: Interp.prg_res list) (candidate: Interp.prg_res list)
  : merged_outcomes option list =
  let verify_candidate (universals: IntSet.t) (ref: Interp.prg_type*Ast.value)
    (candidate: Interp.prg_res) : outcome list =
    match candidate with
    | Err _ -> []
    | Ok candidate ->
        let outcomes = unify_candidate universals ref candidate
        in let cleaned = List.map clean_outcome outcomes
        in cleaned
    (* TODO: I'd really like to collapse the information in this list, removing
     * things like attributes assigned to (unconstrained) unknown values and
     * simplifying so that if we have a case that assumes P and another ~P we
     * just report no additional assumptions. *)
  in let verify_result (ref: Interp.prg_res) : merged_outcomes option option =
    match ref with
    (* for errors in the reference, return None so that we filter them out *)
    | Err _ -> None
    | Ok ref ->
        (* For each possible outcome in the reference we need to find some
         * outcome(s) in the candidate that match. Because we just need some
         * we concat all the results from the individual candidate outcomes *)
        let var_analysis = universal_vars ref
        in let outcomes = 
          List.concat_map (verify_candidate var_analysis ref) candidate
        in if List.is_empty outcomes
        then Some None
        else Some (Some (merge_outcomes outcomes))
        (* NOTE: To really provide good feedback we need to associate the
         * information on additional assumptions/actions with the assumptions
         * already made in this reference outcome *)
  in let results = List.filter_map verify_result reference
  in results

let unification_to_string : unification -> string = function
  | Value v -> Modules.Target.value_to_string v
  | Unknown i -> "?" ^ string_of_int i

let diff_to_string (d: merged_diff) : string =
  let rec inner if_empty lhs rhs (d: merged_diff) =
    let MergedDiff (elems, attrs) = d
    in Modules.Target.string_of_list if_empty lhs ", " rhs (fun s -> s)
      (List.filter_map
        (fun (((elem, _), v), (k, s)) ->
          let inner_text = inner "" ": < " " >" s
          in let text = 
            elem ^ "(" ^ Modules.Target.value_to_string v ^ ")" ^ inner_text
          in match k with Canceled -> None
          | Placeholder when inner_text = "" -> None
          | Positive | Placeholder -> Some text
          | Negative -> Some ("not " ^ text))
        (MergedElemMap.to_list elems)
      @
      List.filter_map
        (fun ((attr, _), (v, s)) ->
          let text = inner "" ": < " " >" s
          in match v with
          | AnyValue when text = "" -> None
          | AnyValue -> Some (attr ^ text)
          | SomeValues -> Some (attr ^ " = ??" ^ text)
          | Value v ->
              Some (attr ^ " = " ^ Modules.Target.value_to_string v ^ text))
        (Interp.AttributeMap.to_list attrs))
  in inner "<>" "< " " >" d

let outcome_to_string (o: merged_outcomes) : string =
  (* FIXME: Print constraints *)
  let { init; final; constraints = _ } = o
  in Printf.sprintf "%s, %s" (diff_to_string init) (diff_to_string final)

let print_verification (v: merged_outcomes option list) : unit =
  List.iter (fun v ->
    match v with
    | None -> Printf.printf "FAILED TO VERIFY\n"
    | Some v -> Printf.printf "UNIFIED: %s\n" (outcome_to_string v)
  ) v
