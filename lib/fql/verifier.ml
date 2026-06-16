(* The goal of the verifier is that given a "reference" interpretation (the
 * result of interpreting the Formal Language Query) and a "candidate"
 * interpretation (the result of interpreting the generated Ansible program) we
 * check whether the candidate matches the reference.
 *
 * Considering a single execution path through both programs (i.e., a
 * particular initial/final state pair from each of the reference and candidate
 * programs) we determine whether they "match" by checking 1) that the
 * candidate's input state is consistent with the reference's (meaning any
 * shared assumptions are the same but both are allowed additional assumptions
 * that the other does not make) and 2) that the candidate's output state
 * covers the reference's (meaning that any actions performed by the reference
 * are also performed by the candidate but the candidate may perform other
 * actions as well).
 *
 * For considering the entirety of the programs' behaviors then we want to show
 * that every behavior expected by the reference is satisfied by the candidate,
 * meaning that there is some execution path of the candidate which matches the
 * expected behavior, as described above. Now, not every behavior the reference
 * can have is expected because existential variables can introduce options,
 * such as different package names or paths that might be used. In these cases,
 * just one of these options is required to be matched by the candidate.
 *
 * Now the matching process described above involves a unification-like process
 * because any variables from the candidate can be instantiated to match
 * variables or values in the reference) and existential variables in the
 * reference can be instantiated to match values from the candidate.
 *)

let ( let* ) = Option.bind

module Interp = Modules.Target.TargetInterp
module Ast = Modules.Target.Ast_Target

(* A Unifier maps variable numbers to values *)
module Unifier : sig
  type t
  val empty : t

  val eval : Ast.value -> t -> Ast.value
  val add : int -> Ast.value -> t -> t option
  val constrain : Ast.value -> Ast.constr -> t -> t option
end 
= struct
  module M = Map.Make(Int)
  module VM = Interp.ValueMap

  (* This type is kinda nuanced, because we're using a Map which is immutable
   * but then wrapping it in a ref. The reason for this is that we want the
   * Unifier to be observationally persistent, so if u is a unifier and then
   * we assign m = add k v u, m is a unifier with k --> v while u has not
   * changed, but find also performs some background work that is essentially
   * path compression, and since these don't change the observational behavior
   * of the Unifier, it is preferable to be able to record that compression
   * so we don't need to do it again later *)
  type t = { map : Ast.value M.t ref; bools : bool VM.t;
             constrs : (bool * Ast.value) VM.t }

  let empty = { map = ref M.empty; bools = VM.empty;
                constrs = VM.empty }

  (* Given a term fully evaluated under the map, check if we can evaluate
   * further under the constraints *)
  let eval_constraints v { bools; constrs; _ } =
    match VM.find_opt v bools with
    | Some b -> Ast.Literal (Bool b, Bool)
    | None ->
        match VM.find_opt v constrs with
        | Some (which, x) ->
            begin match Interp.type_of_val v with
            | Named n -> Constructor (n, which, x)
            | _ -> failwith "Value is constrained as Constructor but type is not Named"
            end
        | None -> v

  let rec eval (v : Ast.value) ({ map; _ } as u) =
    match v with
    | Unknown ((Loop i | Universal i | Existential i), _) ->
        begin match M.find_opt i !map with
        (* We don't need to use eval_constraints because we never put variables
         * into bools or constrs, we would just put the constraints directly
         * into the map *)
        | None -> v
        | Some v -> let v = eval v u in map := M.add i v !map; v
        end
    (* We don't bother to eval_constraints on literals, since they should never
     * appear *)
    | Literal (_, _) -> v
    | Function (f, v, t) ->
        let new_v = eval v u
        in let (_, _, f_def) = Ast.funcDef f
        in let res =
          match f_def new_v with
          | Reduced w -> w
          | Stuck -> Function (f, new_v, t)
          | Err msg ->
              failwith ("Unifier.eval encountered a function evaluation failure:" ^ msg)
        in eval_constraints res u
    (* Like with literals, a Pair itself never appears in a constraint because
     * it is neither a bool nor a constructor *)
    | Pair (x, y, t) -> Pair (eval x u, eval y u, t)
    (* And again, a constructor value would never be put in the constraints *)
    | Constructor (n, c, v) -> Constructor (n, c, eval v u)
    | Struct (t, r) -> Struct (t, Ast.FieldMap.map (fun v -> eval v u) r)
    | ListVal (n, v) -> eval_constraints (ListVal (n, eval v u)) u

  (* If we attempt to add inconsistent information we return None *)
  let add k v { map; bools; constrs } =
    let error = ref false
    in let res =
      M.update k (function None -> Some v
                  | Some _ -> error := true; Some v) !map
    in if !error
    then None
    else
      let map = ref res
      in let* bools =
        VM.fold (fun v b bools ->
          let* bools = bools
          in let v = eval v { map; bools; constrs = VM.empty }
          in match Ast.asTruth v with
          | Some c -> if b = c then Some bools else None
          | _ ->
              begin match VM.find_opt v bools with
              | None -> Some (VM.add v b bools)
              | Some c -> if b = c then Some bools else None
              end
        ) bools (Some VM.empty)
      (* Because handling the constructors can result in more constraints we
       * may also have to update the bools *)
      in let* (constrs, bools) =
        VM.fold (fun v (which, x) acc ->
          let* (constrs, bools) = acc
          in let v = eval v { map; bools; constrs }
          in let x = eval x { map; bools; constrs }
          in match v with
          | Ast.Constructor (_, w, y) ->
              if which <> w 
              then None
              (* We don't do an in-depth unification because that's very
               * difficult and non-deterministic. Instead we just use a bool
               * condition about their equality *)
              else
                let eqxy : Ast.value =
                  Function (Equal (Interp.type_of_val x),
                    Pair (x, y,
                      Product (Interp.type_of_val x, Interp.type_of_val y)),
                    Primitive Bool)
                in let eq_eval = eval eqxy { map; bools; constrs }
                in begin match Ast.asTruth eq_eval with
                (* Already true, no need to do anything else *)
                | Some true -> Some (constrs, bools)
                | Some false -> None (* Cannot unify, so contradiction *)
                | None ->
                    begin match VM.find_opt eq_eval bools with
                    | None -> Some (constrs, VM.add eq_eval true bools)
                    | Some true -> Some (constrs, bools)
                    | Some false -> None
                    end
                end
          | _ ->
              begin match VM.find_opt v constrs with
              | None -> Some (VM.add v (which, x) constrs, bools)
              | Some (w, y) ->
                  if which <> w
                  then None
                  else 
                    let eqxy : Ast.value =
                      Function (Equal (Interp.type_of_val x),
                        Pair (x, y,
                          Product (Interp.type_of_val x, Interp.type_of_val y)),
                        Primitive Bool)
                    in let eq_eval = eval eqxy { map; bools; constrs }
                    in begin match Ast.asTruth eq_eval with
                    (* Already true, no need to do anything else *)
                    | Some true -> Some (constrs, bools)
                    | Some false -> None (* Cannot unify, so contradiction *)
                    | None ->
                        begin match VM.find_opt eq_eval bools with
                        | None -> Some (constrs, VM.add eq_eval true bools)
                        | Some true -> Some (constrs, bools)
                        | Some false -> None
                        end
                    end
              end
        ) constrs (Some (VM.empty, bools))
      in Some { map; bools; constrs }

  (* We assume that v is fully evaluated under the current unifier *)
  let constrain v (c : Ast.constr) ({ map; bools; constrs } as u) =
    match v with
    (* For unknowns we don't add the information to the constraints but rather
     * put it directly into the map *)
    | Ast.Unknown ((Loop i | Universal i | Existential i), t) ->
        begin match c with
        | IsBool b -> add i (Literal (Bool b, Bool)) u
        | IsConstructor (which, x) ->
            let n =
              match t with
              | Named n -> n
              | _ -> failwith "Value is constrained to be a constructor but does not have Named type"
            in add i (Constructor (n, which, x)) u
        | IsEqual w -> add i w u
        end
    | _ ->
      match c with
      | IsBool b ->
          Some { map; bools = VM.add v b bools; constrs }
      | IsConstructor (which, x) ->
          Some { map; bools; constrs = VM.add v (which, x) constrs }
      | IsEqual w ->
          (* IsEqual constraints are the one where there could already be a
           * constraint about v and w, even though we assume both are fully
           * evaluated since constraint will simply have the form equal(v, w)
           * in the bools, so we would not find it in our search procedure.
           * Thus we must check if this is consistent. *)
          let err = ref false
          in let tv = Interp.type_of_val v
          in let tw = Interp.type_of_val w
          in let tvw = Ast.Product (tv, tw)
          in let twv = Ast.Product (tw, tv)
          in let equal = Ast.equality_func tv
          in let eqvw = Ast.Function (equal, Pair (v, w, tvw), Primitive Bool)
          in let eqwv = Ast.Function (equal, Pair (w, v, twv), Primitive Bool)
          in let add_binding = function
            | None | Some true -> Some true
            | Some false -> err := true; None
          in let bools =
            VM.update eqvw add_binding (VM.update eqwv add_binding bools)
          in if !err
          then None (* Inconsistent *)
          else Some { map; bools; constrs }
end

type unifier = Unifier.t

(* The result of comparing two diffent states, in particular subtracing one
 * state from another *)
type elem_diff = Negated | Positive of state_diff
and state_diff =
  (* bool for elements tracks if this element itself is part of the diff or if
   * it only appears because of a nested diff *)
  StateDiff of (bool * elem_diff) Interp.ElementMap.t
             * Ast.value Interp.AttributeMap.t

let diff_empty : state_diff =
  StateDiff (Interp.ElementMap.empty, Interp.AttributeMap.empty)

let diff_add_elem (e : Interp.ElementMap.key) (d : state_diff)
  (top : state_diff) : state_diff =
  let StateDiff (elems, attrs) = top
  in StateDiff (Interp.ElementMap.add e (false, Positive d) elems, attrs)

let rec diff_of_state (s : Interp.state) =
  let State (elems, attrs) = s
  in StateDiff (
      Interp.ElementMap.map (fun (b : Interp.element_result) ->
        match b with
        | Negated -> (true, Negated)
        | Positive s -> (true, Positive (diff_of_state s))) elems,
      attrs)

(* We assume the differences are disjoint *)
let add_diffs (x : state_diff) (y : state_diff) : state_diff =
  let StateDiff (elems_x, attrs_x) = x
  in let StateDiff (elems_y, attrs_y) = y
  in StateDiff (
      Interp.ElementMap.union (fun _ d _ -> Some d) elems_x elems_y,
      Interp.AttributeMap.union (fun _ v _ -> Some v) attrs_x attrs_y)

(* The evaluate_candidate function both evaluates the value and replaces all
 * Universal variables with Existential ones, because even the Universal values
 * in the candidate can be instantiated *)
let evaluate_candidate (u : unifier) (v : Ast.value) : Ast.value =
  let rec replace_universals (v : Ast.value) : Ast.value =
    match v with
    | Unknown ((Loop _ | Existential _), _) -> v
    | Unknown (Universal i, t) -> Unknown (Existential i, t)
    | Literal (_, _) -> v
    | Function (f, v, t) -> Function (f, replace_universals v, t)
    | Pair (x, y, t) -> Pair (replace_universals x, replace_universals y, t)
    | Constructor (n, c, v) -> Constructor (n, c, replace_universals v)
    | Struct (t, r) -> Struct (t, Ast.FieldMap.map replace_universals r)
    | ListVal (n, v) -> ListVal (n, replace_universals v)
  in Unifier.eval (replace_universals v) u

let lookup_loop (loops : Interp.loop_info Interp.ValueMap.t) (id : int)
  : Ast.value option =
  Interp.ValueMap.fold (fun lst v res ->
    match res with
    | Some res -> Some res
    | None ->
        match v with
        | Interp.AllUnknown n | LastKnown (n, _) ->
            if n = id then Some lst else None
        | AllKnown _ -> None)
    loops
    None

type ('e, 'u) unified_res =
  | NotUnified
  | Equal of 'e
  | Unified of 'u

type unified = (unit, unifier list) unified_res

(* Given a list of options xs and a function f which determines how a value in
 * xs in be satisfied, returns a unified result of NotUnified if no element of
 * xs can be satisfied, Equal if any element of xs is already satisfied, and
 * Unified u with all possibly satisfying unifications otherwise *)
let map_unified (xs : 'a list) (f : 'a -> unified) : unified =
  let rec map (xs : 'a list) : unified =
    match xs with
    | [] -> NotUnified
    | x :: xs ->
        match f x with
        | NotUnified -> map xs
        | Equal () -> Equal ()
        | Unified u ->
            match map xs with
            | NotUnified -> Unified u
            | Equal () -> Equal ()
            | Unified u' -> Unified (u @ u')
  in map xs

(* Attempts to unify two values where at least one of them is an unreduced
 * function. If both are unreduced functions they either do not use the same
 * function or their arguments are not unifiable *)
let add_function_constraint
  (unify : unifier -> Ast.value -> Ast.value -> unified) (u : unifier)
  (cand : Ast.value) (ref : Ast.value) : unified =
  let handle_cases (cases : Ast.result_constraint list list) : unified =
    map_unified cases (fun conds ->
      List.fold_left (fun acc (c : Ast.result_constraint) ->
        let (v, w) =
          match c with
          | IsBool (v, b) -> (v, Ast.Literal (Bool b, Bool))
          | IsConstructor (v, (which, w)) ->
              let n =
                match Interp.type_of_val v with
                | Named n -> n
                | _ -> failwith "Value is constrained to be constructor but not of Named type"
              in (v, Ast.Constructor (n, which, w))
          | IsEqual (v, w) -> (v, w)
        in match acc with
        | NotUnified -> NotUnified
        | Equal () -> unify u v w
        | Unified u ->
            let res_u =
              List.concat (List.filter_map (fun u ->
                match unify u v w with
                | NotUnified -> None
                | Equal () -> Some [u]
                | Unified u -> Some u) u)
            in if List.is_empty res_u
            then NotUnified
            else Unified res_u
      ) (Equal ()) conds)
  in let add_constraint (v : Ast.value) (c : Ast.constr) : unified =
    match Unifier.constrain v c u with
    | None -> NotUnified
    | Some u -> Unified [u]
  in match cand, ref with
  (* Uninterpreted functions generally represent functions that cannot be
   * computed or determined. Therefore, the only way to be equal is for the two
   * values to invoke that same function with equal arguments. By our
   * assumptions, this is not the case. *)
  | Function (Uninterpreted (_, _, _), _, _), _
  | _, Function (Uninterpreted (_, _, _), _, _) -> NotUnified
  | Function (fc, vc, _), Function (fr, vr, _) ->
      (* Try reducing the constraint cand = ref, try both options for which
       * function we try to reduce in case one works while the other doesn't *)
      begin match Ast.reduceFuncConstraint fc vc (IsEqual ref) with
      | Reducible cases -> handle_cases cases
      | Unreducible ->
          match Ast.reduceFuncConstraint fr vr (IsEqual cand) with
          | Reducible cases -> handle_cases cases
          | Unreducible -> add_constraint cand (IsEqual ref)
      end
  | Function (f, v, t), Literal (Bool b, _)
  | Literal (Bool b, _), Function (f, v, t) ->
      (* Try reducing the constraint f(v) = b *)
      begin match Ast.reduceFuncConstraint f v (IsBool b) with
      | Reducible cases -> handle_cases cases
      | Unreducible -> add_constraint (Function (f, v, t)) (IsBool b)
      end
  | Function (f, v, t), Constructor (_, which, x)
  | Constructor (_, which, x), Function (f, v, t) ->
      (* Try reducing the constraint f(v) = which(x) *)
      begin match Ast.reduceFuncConstraint f v (IsConstructor (which, x)) with
      | Reducible cases -> handle_cases cases
      | Unreducible ->
          add_constraint (Function (f, v, t)) (IsConstructor (which, x))
      end
  | Function (f, v, t), other
  | other, Function (f, v, t) ->
      (* Try reducing the constraint f(v) = other *)
      begin match Ast.reduceFuncConstraint f v (IsEqual other) with
      | Reducible cases -> handle_cases cases
      | Unreducible -> add_constraint (Function (f, v, t)) (IsEqual other)
      end
  | _, _ -> failwith "at least one argument to add_function_constraint must be a function"

let unify_values (u : unifier)
  (loops_cand : Interp.loop_info Interp.ValueMap.t)
  (loops_ref : Interp.loop_info Interp.ValueMap.t)
  (cand : Ast.value) (ref : Ast.value) : unified =
  let cand = evaluate_candidate u cand
  in let ref = Unifier.eval ref u
  in let rec unify (u : unifier) (cand : Ast.value) (ref : Ast.value)
    : unified =
    match cand, ref with
    | Literal (c, _), Literal (r, _) ->
        if c = r then Equal () else NotUnified
    | Function (fc, vc, _), Function (fr, vr, _) ->
        if fc = fr
        then
          match unify u vc vr with
          | Equal () -> Equal ()
          (* If vc and vr can be unified (but aren't already equal), we could
           * unify them or we could try to solve the function constraint, so
           * we try that too, what we do based on its return:
           * - NotUnified : return Unified us because we can make the values
           *   equal by unifying vc and vr
           * - Equal : return Equal because we somehow proved equality without
           *   any changes
           * - Unified u' -> return Unified (us @ u') because we can either
           *   just unify vc and vr directly or do whatever unifications u'
           *   contains. *)
          | Unified us ->
              begin match add_function_constraint unify u cand ref with
              | NotUnified -> Unified us
              | Equal () -> Equal ()
              | Unified u' -> Unified (us @ u')
              end
          | NotUnified -> add_function_constraint unify u cand ref
        else add_function_constraint unify u cand ref
    | Pair (xc, yc, _), Pair (xr, yr, _) ->
        begin match unify u xc xr with
        | NotUnified -> NotUnified
        | Equal () -> unify u yc yr
        | Unified u ->
            let res_u =
              List.concat (
                List.filter_map (fun u ->
                  match unify u yc yr with
                  | NotUnified -> None
                  | Equal () -> Some [u]
                  | Unified u -> Some u) u)
            in if List.is_empty res_u
            then NotUnified
            else Unified res_u
        end
    | Constructor (nc, cc, vc), Constructor (nr, cr, vr) ->
        if nc <> nr || cc <> cr
        then NotUnified
        else unify u vc vr
    | Struct (_, cs), Struct (_, rs) ->
        (* By checking that they have equal cardinality and then ensuring that
         * each binding in rs is also a binding in cs we ensure they have the
         * same bindings *)
        if Ast.FieldMap.cardinal cs <> Ast.FieldMap.cardinal rs
        then NotUnified
        else Ast.FieldMap.fold (fun f vr res ->
          match res with
          | NotUnified -> NotUnified
          | Equal () ->
              begin match Ast.FieldMap.find_opt f cs with
              | None -> NotUnified
              | Some vc -> unify u vc vr
              end
          | Unified u ->
              begin match Ast.FieldMap.find_opt f cs with
              | None -> NotUnified
              | Some vc ->
                  let res_u =
                    List.concat (
                      List.filter_map (fun u ->
                        match unify u vc vr with
                        | NotUnified -> None
                        | Equal () -> Some [u]
                        | Unified u -> Some u) u)
                  in begin match res_u with
                  | [] -> NotUnified
                  | _ -> Unified res_u
                  end
              end
          ) rs (Equal ())
    | ListVal (_, vc), ListVal (_, vr) -> unify u vc vr
    | Unknown (Loop c, _), Unknown (Loop r, _) ->
        if c = r then Equal ()
        else
          (* Because we've performed evaluation already variables in the
           * candidate and reference may not have originated from the same
           * side, and so when looking up the lists we check all loops *)
          let list_c =
            match lookup_loop loops_cand c with
            | Some lst -> Some (evaluate_candidate u lst)
            | None ->
                match lookup_loop loops_ref c with
                | Some lst -> Some (Unifier.eval lst u)
                | None -> None
          in let list_r =
            match lookup_loop loops_cand c with
            | Some lst -> Some (evaluate_candidate u lst)
            | None ->
                match lookup_loop loops_ref c with
                | Some lst -> Some (Unifier.eval lst u)
                | None -> None
          in begin match list_c, list_r with
          | Some list_c, Some list_r ->
              begin match unify u list_c list_r with
              | NotUnified -> NotUnified
              | Equal () ->
                  begin match Unifier.add c ref u with
                  | None -> NotUnified
                  | Some u -> Unified [u]
                  end
              | Unified u ->
                  let res_u = List.filter_map (Unifier.add c ref) u
                  in if List.is_empty res_u
                  then NotUnified
                  else Unified res_u
              end
          | _ -> NotUnified
          end
    (* Loop variables cannot unify with anything other than other loop
     * variables because they represent a specific set of unknown values (the
     * values in the unreduced list) *)
    | Unknown (Loop _, _), _ | _, Unknown (Loop _, _) -> NotUnified
    (* Universal variables can only be unified with other universals *)
    (* Note that neither variable has an existing binding as otherwise it would
     * have been replaced by evaluation *)
    | Unknown (Universal c, _), Unknown (Universal r, _) ->
        if c = r then Equal ()
        else begin match Unifier.add c ref u with
        | None -> NotUnified
        | Some u -> Unified [u]
        end
    | Unknown (Existential e, _), Unknown (Universal i, t)
    | Unknown (Universal i, t), Unknown (Existential e, _) ->
        if i = e then Equal ()
        else begin match Unifier.add e (Unknown (Universal i, t)) u with
        | None -> NotUnified
        | Some u -> Unified [u]
        end
    | Unknown (Existential c, _), Unknown (Existential r, _) ->
        if c = r then Equal ()
        else begin match Unifier.add c ref u with
        | None -> NotUnified
        | Some u -> Unified [u]
        end
    | Unknown (Universal _, _), _ | _, Unknown (Universal _, _) -> NotUnified
    | Unknown (Existential i, _), v | v, Unknown (Existential i, _) ->
        begin match Unifier.add i v u with
        | None -> NotUnified
        | Some u -> Unified [u]
        end

    | Literal (_, _),
      (Pair (_, _, _) | Constructor (_, _, _) | Struct (_, _) | ListVal (_, _))
    | (Pair (_, _, _) | Constructor (_, _, _) | Struct (_, _) | ListVal (_, _)),
      Literal (_, _)
    | Pair (_, _, _),
      (Constructor (_, _, _) | Struct (_, _) | ListVal (_, _))
    | (Constructor (_, _, _) | Struct (_, _) | ListVal (_, _)), Pair (_, _, _)
    | Constructor (_, _, _), Struct (_, _)
    | Struct (_, _), Constructor (_, _, _)
    | Struct (_, _), ListVal (_, _)
    | ListVal (_, _), Struct (_, _)
    -> NotUnified

    (* ListVals where the list that was originally looped over was an
     * existential could, in theory, unify with a concrete list, but I don't
     * know that this is worth supporting at this time *)
    | Constructor (_, _, _), ListVal (_, _)
    | ListVal (_, _), Constructor (_, _, _) -> NotUnified

    | _, Function (_, _, _) | Function (_, _, _), _ ->
        add_function_constraint unify u cand ref
  in unify u cand ref

let list_of_res (res : Interp.interp_res) : Interp.interp_state list =
  let rec with_acc (res : Interp.interp_res) acc =
    match res with
    | Err _ -> acc
    | Success s -> s :: acc
    | Both (x, y) | Either (x, y) -> with_acc y (with_acc x acc)
  in with_acc res []

let rec map_append (f : 'a -> 'b) (xs : 'a list) (ys : 'b list) : 'b list =
  match xs with
  | [] -> ys
  | x :: xs -> f x :: map_append f xs ys

let rec concat_map_append (f : 'a -> 'b list) (xs : 'a list) (ys : 'b list) =
  match xs with
  | [] -> ys
  | x :: xs -> (f x) @ (concat_map_append f xs ys)

type interp_state_unifier =
  { u : unifier; init : state_diff; final : state_diff }

let find_satisfying (ref : Interp.interp_state) (cand : Interp.interp_res)
  : interp_state_unifier list =
  let unify_states (u : unifier) ref_loops cand_loops (ref : Interp.state)
    (cand : Interp.state) (can_miss : bool) : (unifier * state_diff) list =
    let rec unify (u : unifier) (ref : Interp.state) (cand : Interp.state)
      : (unifier * state_diff) list option =
      let State (ref_elems, ref_attrs) = ref
      in let State (cand_elems, cand_attrs) = cand
      (* Unifying attributes is straightforward *)
      in let* (attrs_diff, u) =
        Interp.AttributeMap.fold (fun attr ref_val acc ->
          let* (cand_attrs, u) = acc
          in match Interp.AttributeMap.find_opt attr cand_attrs with
          | None ->
              if can_miss then Some (cand_attrs, u) else None
          | Some cand_val ->
              let res =
                List.concat_map (fun u ->
                  match unify_values u cand_loops ref_loops cand_val ref_val with
                  | NotUnified -> []
                  | Equal () -> [u]
                  | Unified u -> u
                ) u
              in if List.is_empty res
              then None
              else Some (Interp.AttributeMap.remove attr cand_attrs, res)
        ) ref_attrs (Some (cand_attrs, [u]))
      (* Unifying elements is more complicated because we can unify the values
       * which are part of the element *)
      in let unified_elems =
        List.concat_map (fun u ->
          Interp.ElementMap.fold (fun (ref_elem, ref_val)
              (ref_bind : Interp.element_result) acc ->
            List.concat_map (fun (cand_elems, diff, u) ->
              (* Search for any elements elem(X) in cand_elems and see if
               * X can unify with ref_val. If so, handle whether the bindings
               * are compatible.
               * Options:
               * - We find an element that exactly matches (i.e., unifies to
               *   Equal) which either we return the diffs of or the nested
               *   states do not unify.
               * - We fine some (0+) elements that can be unified (i.e., unify
               *   to Unified) in which case we try unifying the nested
               *   states
               * Returns a list of update candidate elements, an updated diff,
               * and an updated unifier. *)
              let res =
                Interp.ElementMap.fold (fun (cand_elem, cand_val)
                    (cand_bind : Interp.element_result) res ->
                  match res with
                  | NotUnified -> NotUnified
                  | Equal res -> Equal res
                  | Unified res ->
                      if ref_elem <> cand_elem
                      then Unified res
                      else let new_elems =
                        Interp.ElementMap.remove
                          (cand_elem, cand_val) cand_elems
                      in match
                        unify_values u cand_loops ref_loops cand_val ref_val
                      with
                      | NotUnified -> Unified res
                      | Equal () ->
                          begin match ref_bind, cand_bind with
                          | Negated, Negated -> Equal [(new_elems, diff, u)]
                          | Positive ref_nested, Positive cand_nested ->
                              let elem = (cand_elem, cand_val)
                              in begin match unify u ref_nested cand_nested with
                              | None -> NotUnified
                              | Some nested_res ->
                                  Equal (
                                    List.map 
                                      (fun (u, d) ->
                                        (new_elems, 
                                          diff_add_elem elem d diff, u))
                                      nested_res)
                              end
                          | _, _ -> NotUnified
                          end
                      | Unified u ->
                          begin match ref_bind, cand_bind with
                          | Negated, Negated ->
                              Unified
                                (map_append 
                                  (fun u -> (new_elems, diff, u)) u res)
                          | Positive ref_nested, Positive cand_nested ->
                              let res =
                                concat_map_append (fun u ->
                                  let elem = (cand_elem, cand_val)
                                  in match unify u ref_nested cand_nested with
                                  | None -> []
                                  | Some nested_res ->
                                      List.map (fun (u, d) ->
                                        (new_elems,
                                          diff_add_elem elem d diff, u))
                                        nested_res
                                ) u res
                              in Unified res
                          | _, _ -> Unified res
                          end
                ) cand_elems (Unified [])
              in match res with
              | NotUnified -> []
              | Equal res | Unified res -> res
            ) acc
          ) ref_elems [(cand_elems, diff_empty, u)]
        ) u
      in if List.is_empty unified_elems
      then None
      else
        Some (List.map (fun (elems_diff, diff, u) ->
          (u, add_diffs diff (diff_of_state (State (elems_diff, attrs_diff))))
        ) unified_elems)
    in match unify u ref cand with
    | None -> []
    | Some res -> res
  in let unify_interp_state (ref : Interp.interp_state)
    (cand : Interp.interp_state) : interp_state_unifier list =
    (* Setup our unifier by adding the constraints to it *)
    let ref_loops = ref.loops
    in let cand_loops = cand.loops
    in let u =
      let u = Unifier.empty
      in let* u = Interp.ValueMap.fold (fun v b u ->
        let* u = u
        in Unifier.constrain v (IsBool b) u
      ) ref.bools (Some u)
      in let* u = Interp.ValueMap.fold (fun v b u ->
        let* u = u
        in Unifier.constrain v (IsBool b) u
      ) cand.bools (Some u)
      in let* u = Interp.ValueMap.fold (fun v (which, w) u ->
        let* u = u
        in Unifier.constrain v (IsConstructor (which, w)) u
      ) ref.constrs (Some u)
      in let* u = Interp.ValueMap.fold (fun v (which, w) u ->
        let* u = u
        in Unifier.constrain v (IsConstructor (which, w)) u
      ) cand.constrs (Some u)
      in Some u
    in match u with
    | None -> []
    | Some u ->
      List.fold_left (fun res (u, init) ->
        List.fold_left (fun res (u, final) -> { u; init; final } :: res)
          res (unify_states u ref_loops cand_loops ref.final cand.final false))
        [] (unify_states u ref_loops cand_loops ref.init cand.init true)
  in List.concat_map (unify_interp_state ref) (list_of_res cand)

type interp_res_unifier =
  | Left of interp_res_unifier
  | Right of interp_res_unifier
  | Both of interp_res_unifier * interp_res_unifier
  | Satisfied of Interp.interp_state * interp_state_unifier list
  | Ignored (* The reference solution errored *)

let unify_candidate (ref : Interp.interp_res) (cand : Interp.interp_res)
  : interp_res_unifier option =
  let rec unify (ref : Interp.interp_res) : interp_res_unifier option =
    match ref with
    | Err _ -> Some Ignored
    | Success ref ->
        let res = find_satisfying ref cand
        in if List.is_empty res
        then None
        else Some (Satisfied (ref, res))
    | Both (left, right) ->
        let* left = unify left
        in let* right = unify right
        in Some (Both (left, right))
    | Either (left, right) ->
        begin match unify left with
        | Some left -> Some (Left left)
        | None ->
            begin match unify right with
            | Some right -> Some (Right right)
            | None -> None
            end
        end
  in unify ref

(*
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

let print_verification (v: merged_outcomes option list) : bool =
  List.fold_left (fun success v ->
    match v with
    | None -> Printf.printf "FAILED TO VERIFY\n"; false
    | Some v -> Printf.printf "UNIFIED: %s\n" (outcome_to_string v); success
  ) true v
*)
