type uid = Ast.uid

module Interp(Ast : Ast.Ast_Defs) = struct
  open Ast

  module ValueOrder : Map.OrderedType with type t = value = struct
    type t = value
    let compare : value -> value -> int = compare
  end
  module ValueMap : Map.S with type key = value = Map.Make(ValueOrder)

  (* States are made up of maps of qualifiers. For elements, we store the 
   * element, value, and whether or not it is negated (true = negated) as the
   * key and the value is qualifiers applied to it. For attributes, the key is
   * just the attribute and whether it is negated and this maps to the value and
   * any qualifiers applied to it. *)
  module ElementOrder : Map.OrderedType with type t = element * value * bool = struct
    type t = element * value * bool
    let compare : t -> t -> int = compare
  end
  module ElementMap : Map.S with type key = element * value * bool
    = Map.Make(ElementOrder)

  module AttributeOrder : Map.OrderedType with type t = attribute = struct
    type t = attribute
    let compare : t -> t -> int = compare
  end
  module AttributeMap : Map.S with type key = attribute
    = Map.Make(AttributeOrder)

  type state = State of state ElementMap.t * (value * state) AttributeMap.t
  let init_state = State (ElementMap.empty, AttributeMap.empty)

  let rec add_qual
      ((q, v, qs) : (element * bool, attribute) Either.t * value * state)
      (State (els, ats) : state) : state =
    match q with
    | Left (elem, neg) ->
        let removed = ElementMap.remove (elem, v, not neg) els
        in let added = ElementMap.update (elem, v, neg)
                        (fun cur ->
                          match cur with
                          | None -> Some qs
                          | Some ps -> Some (add_quals qs ps))
                        removed
        in State (added, ats)
    | Right attr ->
        let added = AttributeMap.update attr
                      (fun cur ->
                        match cur with
                        | None -> Some (v, qs)
                        | Some (_, ps) -> Some (v, add_quals qs ps))
                      ats
        in State (els, added)
  and add_quals (State (els, ats) : state) (ps : state) =
    let rec helper els ats state =
      match els with
      | ((el, v, neg), qs) :: tl
        -> helper tl ats (add_qual (Left (el, neg), v, qs) state)
      | [] ->
          match ats with
          | (at, (v, qs)) :: tl
            -> helper [] tl (add_qual (Right at, v, qs) state)
          | [] -> state
    in helper (ElementMap.bindings els) (AttributeMap.bindings ats) ps

  type prg_type = { init : state; final : state; loops : uid ValueMap.t; }
  let init_prg_type = { init = init_state; final = init_state; loops = ValueMap.empty; }

  let new_env = VariableMap.empty

  type 'a error = Ok of 'a
                | Err of string
  type prg_res = (prg_type * value) error

  (* A type representing attempting to find some value in a structure where we
   * may or may not find it or may be able to create the value and returns
   * additional information when it is created*)
  type ('a, 'b) find = NotLocated
                     | Located of 'a
                     | Created of 'a * 'b

  (* A list-like type is any named type defined as n = () + t * n
   * Returns the element type is the give type is list like *)
  let list_like (n : namedTy) : typ option =
    let (nil, cons) = namedTyDef n
    in if not (isUnit nil) then None
    else match cons with
         | Product (hd, Named tl) when tl = n -> Some hd
         | _ -> None

  let val_to_type (v : value) : typ =
    match v with
    | Unknown (_, t) -> t
    | Literal (_, p) -> Primitive p
    | Function (_, _, t) -> t
    | Pair (_, _, t) -> t
    | Constructor (n, _, _) -> Named n
    | Struct (s, _) -> Struct s

  let interpret (s : stmt) (retTy : typ) : prg_res list =
    let rec eval_expr (e : expr) (env : env) : (value * typ) error =
      match e with
      | Function (f, exp) ->
          begin match eval_expr exp env with
          | Err m -> Err m
          | Ok (v, t) ->
              let (argTy, retTy, interp) = funcDef f
              in if t <> argTy
                 then Err "Type error, argument type mismatch"
                 else
                   match interp v with
                   | Reduced w -> Ok (w, retTy)
                   | Stuck -> Ok (Function (f, v, retTy), retTy)
                   | Err msg -> Err msg
          end
      | Literal l ->
          let p = literalTyp l
          in Ok (Literal (l, p), Primitive p)
      | Variable v ->
          begin match VariableMap.find_opt v env with
          | None -> Err "Undefined variable"
          | Some v -> Ok v
          end
      | Pair (x, y) ->
          begin match eval_expr x env, eval_expr y env with
          | Ok (x, tx), Ok (y, ty)
            -> let t : typ = Product (tx, ty) in Ok (Pair (x, y, t), t)
          | Err m, Err n -> Err (m ^ "\n" ^ n)
          | Err m, Ok _ -> Err m
          | Ok _ , Err n -> Err n
          end
      | Env -> Ok (envToVal env, envType)
    (* Returns either the element or the attribute, the value, and attached qualifiers *)
    in let rec eval_qual (q : qual) (env : env)
      : ((element * bool, attribute) Either.t * value * state) error =
      match q with
      | Attribute (_, e, qs) | Element (_, e, qs) ->
          let bq = match q with Attribute (at, _, _) -> Either.Right at
                              | Element   (el, _, _) -> Either.Left (el, false)
                              | _ -> failwith "Match error"
          in begin match eval_expr e env with
          | Err msg -> Err msg
          | Ok (v, _) ->
              match eval_quals qs env with
              | Err msg -> Err msg
              | Ok state -> Ok (bq, v, state)
          end
      | NotElement (el, e) ->
          match eval_expr e env with
          | Err msg -> Err msg
          | Ok (v, _) -> Ok (Left (el, true), v, init_state)
    and eval_quals (qs : qual list) (env : env) : state error =
      match qs with
      | [] -> Ok init_state
      | q :: qs ->
          match eval_qual q env with
          | Err msg -> Err msg
          | Ok qres ->
              match eval_quals qs env with
              | Err msg -> Err msg
              | Ok state -> Ok (add_qual qres state)
    (* Given an attribute AST and the current state, finds the attribute either
     * in the final state or initial state, and (if necessary) adds the
     * desired attribute with an unknown value.
     * Returns the value of the attribute and resulting state *)
    in let get_attribute (a : attr) (s : prg_type) (env : env) : (value * prg_type) error =
      (* The helper traverses an attribute and a state to find the attribute's
       * value (and returns the modified state if needed). Can fail by error or
       * can return Ok NotLocated if it could not find some qualifier needed on
       * the desired path *)
      let rec helper (a : attr) (State (els, ats)) : (value, state) find error =
        match a with
        | AttrAccess a ->
            begin match AttributeMap.find_opt a ats with
            | Some (v, _) -> Ok (Located v)
            | None ->
                let v : value = Unknown (ref (), attributeDef a)
                in Ok (Created (v, State (els, AttributeMap.add a (v, init_state) ats)))
            end
        | OnAttribute (a, at) ->
            begin match AttributeMap.find_opt a ats with
            | None ->
                (* Even if the attribute doens't exist, we could create it
                 * (since it's an attribute), so we do that and see what
                 * happens *)
                begin match helper at init_state with
                | Err msg -> Err msg
                | Ok NotLocated -> Ok NotLocated
                | Ok (Located _) -> failwith "Cannot find attribute in empty state"
                | Ok (Created (v, st)) ->
                    let new_value : value = Unknown (ref (), attributeDef a)
                    in let new_ats = AttributeMap.add a (new_value, st) ats
                    in Ok (Created (v, State (els, new_ats)))
                end
            | Some (av, qs) ->
                match helper at qs with
                | Err msg -> Err msg
                | Ok NotLocated -> Ok NotLocated
                | Ok (Located v) -> Ok (Located v)
                | Ok (Created (v, st)) ->
                    let new_ats = AttributeMap.add a (av, st) ats
                    in Ok (Created (v, State (els, new_ats)))
            end
        | OnElement (el, e, at) ->
            begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok (v, _) ->
                match ElementMap.find_opt (el, v, false) els with
                | None -> Ok NotLocated
                | Some qs ->
                    match helper at qs with
                    | Err msg -> Err msg
                    | Ok NotLocated -> Ok NotLocated
                    | Ok (Located v) -> Ok (Located v)
                    | Ok (Created (v, st)) ->
                        let new_els = ElementMap.add (el, v, false) st els
                        in Ok (Created (v, State (new_els, ats)))
            end
      in match helper a s.final with
         | Err msg -> Err msg
         | Ok (Located v) -> Ok (v, s)
         | Ok (Created (v, new_final)) ->
             (* If we can create a value for the attribute in the final state,
              * we return that unless we can find a value for the attribute
              * in the initial state *)
             begin match helper a s.init with
             | Ok (Located v) -> Ok (v, s)
             | _ -> Ok (v, { init = s.init; final = new_final; loops = s.loops; })
             end
         | Ok NotLocated ->
             match helper a s.init with
             | Err msg -> Err msg
             | Ok NotLocated -> Err "Failed to locate attribute in current state"
             | Ok (Located v) -> Ok (v, s)
             | Ok (Created (v, new_init)) ->
                 Ok (v, { init = new_init; final = s.final; loops = s.loops; })
    (* Either returns whether or not the element is in the state (left) or
     * new initial states assuming the element does and does not exist
     * respectively (right) *)
    in let has_element (e : elem) (s : prg_type) (env : env)
      : (bool, state * state) Either.t error =
      (* Returns whether the given element only has attributes except at the
       * last level, returns an error if there's an error in evaluating the
       * expression on that last level *)
      let rec only_attrs (el : elem) : bool error =
        match el with
        | Element (_, e) | NotElement (_, e) ->
            begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok _ -> Ok true
            end
        | OnElement _ -> Ok false
        | OnAttribute (_, el) -> only_attrs el
      in let rec helper (el : elem) (State (els, ats)) : bool option error =
        match el with
        | Element _ | NotElement _ ->
            let (elm, e, neg)
              = match el with Element (elm, e)    -> (elm, e, false)
                            | NotElement (elm, e) -> (elm, e, true)
                            | _ -> failwith "Match Failure"
            in begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok (v, _) ->
                match ElementMap.find_opt (elm, v, neg) els with
                | Some _ -> Ok (Some true)
                | None ->
                    match ElementMap.find_opt (elm, v, not neg) els with
                    | Some _ -> Ok (Some false)
                    | None -> Ok None
            end
        | OnAttribute (at, q) ->
            begin match AttributeMap.find_opt at ats with
            | None ->
                (* If this attribute doesn't exist but the element being checked
                 * for is on the end of a series of attributes (with no
                 * elements), we could create all the attributes and then create
                 * the positive/negative of the attribute.
                 * Otherwise, if there's an element then we are unable to locate
                 * the desired qualifier *)
                begin match only_attrs q with
                | Err msg -> Err msg
                | Ok true -> Ok None
                | Ok false -> Err "Failed to locate element in state"
                end
            | Some (_, st) -> helper q st
            end
        | OnElement (el, e, q) ->
            begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok (v, _) ->
                match ElementMap.find_opt (el, v, false) els with
                | None -> Err "Failed to locate element in state"
                | Some st -> helper q st
            end
      in let rec add_elem (el : elem) (State (els, ats)) : state * state =
        match el with
        | Element _ | NotElement _ ->
            let (elem, e, neg)
              = match el with Element (elm, e)    -> (elm, e, false)
                            | NotElement (elm, e) -> (elm, e, true)
                            | _ -> failwith "Match Failure"
            in begin match eval_expr e env with
            | Err _ -> failwith "Error evaluating expression"
            | Ok (v, _) ->
                let new_true = ElementMap.add (elem, v, neg) init_state els
                in let new_false = ElementMap.add (elem, v, not neg) init_state els
                in (State (new_true, ats), State (new_false, ats))
            end
        | OnAttribute (at, el) ->
            begin match AttributeMap.find_opt at ats with
            | None ->
                let v : value = Unknown (ref (), attributeDef at)
                in let (new_true, new_false) = add_elem el init_state
                in let ats_true = AttributeMap.add at (v, new_true) ats
                in let ats_false = AttributeMap.add at (v, new_false) ats
                in (State (els, ats_true), State (els, ats_false))
            | Some (v, st) ->
                let (new_true, new_false) = add_elem el st
                in let ats_true = AttributeMap.add at (v, new_true) ats
                in let ats_false = AttributeMap.add at (v, new_false) ats
                in (State (els, ats_true), State (els, ats_false))
            end
        | OnElement (el, e, q) ->
            begin match eval_expr e env with
            | Err _ -> failwith "Error evaluating expression"
            | Ok (v, _) ->
                let st = ElementMap.find (el, v, false) els
                in let (new_true, new_false) = add_elem q st
                in let els_true = ElementMap.add (el, v, false) new_true els
                in let els_false = ElementMap.add (el, v, false) new_false els
                in (State (els_true, ats), State (els_false, ats))
            end
      in match helper e s.final with
      | Err msg -> Err msg
      | Ok (Some b) -> Ok (Left b)
      | Ok None ->
          match helper e s.init with
          | Err msg -> Err msg
          | Ok (Some b) -> Ok (Left b)
          | Ok None -> Ok (Right (add_elem e s.init))
    (* Notes on loops: the bodies should return the special expression "Env",
     * which is used to thread the environment back to the processing here so
     * so that loop can modify the environment outside of it. This does mean
     * you cannot return a value for an entire action from inside a loop *)
    (* Note: ret arg here is the return for the next statement not the loop *)
    in let rec process_loop (var : variable) (lst : value) (elemTy : typ)
                            (body : stmt) (next : stmt) (s : prg_type)
                            (env : env) (ret : typ) : prg_res list =
      match lst with
      | Literal _ | Pair _ | Struct _ ->
          failwith "Loop value has non-list value"
      | Constructor (_, true, _) -> (* Nil case *)
          interp next s env ret
      | Constructor (_, false, Pair (hd, tl, _)) -> (* Cons case *)
          let res_hd = interp body s (VariableMap.add var (hd, elemTy) env) envType
          in List.flatten
              (List.map
                (fun s ->
                  match s with Err msg -> [Err msg]
                  | Ok (s, e) ->
                      process_loop var tl elemTy body next s (envFromVal e) ret)
                res_hd)
      | _ -> (* Loop over an unknown value *)
          (* The way we handle loops over unknown lists is to assign the value
           * we loop over a particular UID which represents the loop variable
           * while we loop over that list. We record this information in the
           * state so we can reconstruct repeat constructs at the end, without
           * having to deal with them during interpretation *)
          (* Identify whether there's already a "loop variable" for looping over
           * this value. If so, use it, otherwise create our own.
           * If we create our own, we also update the map in the state *)
          let (uid, s) =
            match ValueMap.find_opt lst s.loops with
            | Some uid -> (uid, s)
            | None ->
                let uid = ref ()
                in let state = { init  = s.init; final = s.final;
                                 loops = ValueMap.add lst uid s.loops; }
                in (uid, state)
          in let head : value = Unknown (uid, elemTy)
          in let res_loop = interp body s (VariableMap.add var (head, elemTy) env) envType
          in List.flatten
              (List.map
                (fun s ->
                  match s with Err msg -> [Err msg]
                  (* FIXME: We need to replace certain uses of the loop variable
                     with some expression that signals that this is the last
                     element of the list. This should occur everywhere in the
                     environment and anywhere in the state that can be accessed
                     without the loop variable occuring in an element; i.e.
                     anywhere that the loop variable can be accessed from outside
                     the loop should be replaced by tail(val) or perhaps a new
                     unknown value that we add to what we track about loops
                     Otherwise, it's possible for loop variables to escape past
                     the body and we can update the state in ways that are
                     not looped but are indistinguishable from the loop *)
                  | Ok (s, e) -> interp next s (envFromVal e) ret)
                res_loop)
    and interp (b : stmt) (s : prg_type) (env : env) (ret : typ) : prg_res list =
      match b with
      | Action   (var, action, expr, next) ->
          let (arg, in_type, out_type, body) = actionDef action
          in begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              if t <> in_type
              then Err "Incorrect argument type to action" :: []
              else let results = interp body s (VariableMap.singleton arg (v, t)) out_type
              in List.flatten
                  (List.map (fun r ->
                      match r with
                      | Ok (s, v) ->
                          interp next s (VariableMap.add var (v, out_type) env) ret
                      | Err msg -> Err msg :: []) results)
          end
      | Assign   (var, expr, next) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              interp next s (VariableMap.add var (v, t) env) ret
          end
      | Add      (qual, next) ->
          begin match eval_qual qual env with
          | Err msg -> Err msg :: []
          | Ok q ->
              (* Note: Add does not even look at the initial environment,
               * technically we could check it and not add this if it's a
               * duplicate, but that's generally unlikely to be useful and
               * could be cleaned up after the fact if we want.
               *)
              let new_final = add_qual q s.final
              in let new_state = { init = s.init; final = new_final; loops = s.loops }
              in interp next new_state env ret
          end
      | Get      (var, attr, next) ->
          begin match get_attribute attr s env with
          | Err msg -> Err msg :: []
          | Ok (v, new_state) ->
              interp next new_state (VariableMap.add var (v, val_to_type v) env) ret
          end
      (* Contains only needs to handle the addition of one constraint where the
         last level is just an element. Adding attributes is handled by get
         and constraining the values on elements should be handled by
         constraints produced by Cond and Match *)
      | Contains (elem, thn, els) ->
          begin match has_element elem s env with
          | Err msg -> Err msg :: []
          (* If we definitively have or do not have the constraint, take the
           * appropriate branch *)
          | Ok (Left b) ->
              interp (if b then thn else els) s env ret
          (* Otherwise, take both branches in appropriate updated initial states *)
          | Ok (Right (new_init_true, new_init_false)) ->
              (interp thn { init = new_init_true; final = s.final; loops = s.loops; }
                      env ret)
              @
              (interp els { init = new_init_false; final = s.final; loops = s.loops; }
                      env ret)
          end
      (* TODO: For both cond and match, if the result of expression is not
       * a concrete value we could evaluate both branches and track the
       * "constraint" of what we've assumed the value was (this is much like
       * you would do with refinement/dependent types). For the moment I have
       * not done this for simplicity
       *)
      | Cond     (expr, thn, els) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              if not (isTruthType t)
              then Err "Condition is not truthy" :: []
              else match asTruth v with
                   (* If we were to track the constraints, we would do that here *)
                   | None -> Err "Could not evaluate truth of condition" :: []
                   | Some true -> interp thn s env ret
                   | Some false -> interp els s env ret
          end
      | Match    (expr, var, left, right) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              match t with
              | Named n ->
                  begin match v with
                  | Constructor (_, b, v) ->
                      let t = (if b then fst else snd) (namedTyDef n)
                      in interp (if b then left else right) s
                            (VariableMap.add var (v, t) env) ret
                  (* Modify here to track constraints *)
                  | _ -> Err "Could not evaluate to constructor on match" :: []
                  end
              | _ -> Err "Cannot match over non-named type" :: []
          end
      | Loop     (var, expr, body, next) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              match t with
              | Named n ->
                  begin match list_like n with
                  | None -> Err "Cannot loop over non list-like type" :: []
                  | Some elemTy ->
                      process_loop var v elemTy body next s env ret
                  end
              | _ -> Err "Cannot loop over non-list-like type" :: []
          end
      | Fail     msg -> (Err msg) :: []
      | Return   expr ->
          begin match eval_expr expr env with
          | Ok (v, t) ->
              if t <> ret
              then Err "Incorrect return type" :: []
              else Ok (s, v) :: []
          | Err msg -> Err msg :: []
          end
    in interp s init_prg_type new_env retTy
end
